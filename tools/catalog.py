#!/usr/bin/env python3
"""Build catalogs and a dependency graph from source locations and Lean's environment.

Run after installing Lean and (for graphs) Graphviz. The default repository root
is the parent of this script's directory. No dependency revisions are updated.
"""
import argparse
import html
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from collections import OrderedDict

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
parser.add_argument('--github-base', default='', help='Optional GitHub source URL ending in /blob/REF')
parser.add_argument('--skip-build', action='store_true', help='Use an already current lake build')
args = parser.parse_args()
ROOT = args.root.resolve()
GITHUB_BASE = args.github_base.rstrip('/')
if not args.skip_build:
    subprocess.run(['lake', 'build'], cwd=ROOT, check=True)

FILES = ['Basic','Lemmas','Resolvent','Holder','SobolevConst','Constants','Step','Nonlinear','Positivity',
         'Descent','Barrier','OneStep','GroundState','Main','Rate', 'Spectral', 'Sign']
PAPER = {
 'Basic': 'Sections 2, 3.1–3.3 (definitions and constants)',
 'Lemmas': 'Section 3.1 (basic identities)',
 'Resolvent': 'Section 3.2 (the resolvent and the X-norm)',
 'Holder': 'Hölder inequalities used in Lemma 4.3',
 'SobolevConst': 'a Sobolev constant exists on every fixed nonempty mesh',
 'Constants': 'Section 3.3: Lemma 3.1 and Lemma 3.2',
 'Step': 'Section 4.1: Lemma 4.1 and Lemma 4.2',
 'Nonlinear': 'Section 4.2: Lemma 4.3',
 'Positivity': 'Section 4.3: Lemma 4.4',
 'Descent': 'Section 4.4: Lemma 4.5 and Lemma 4.6',
 'Barrier': 'Section 4.5: Lemma 4.7 (energy barrier)',
 'OneStep': 'Section 4.5: Proposition 4.8',
 'GroundState': 'Remark 2.3 / Appendix A (the discrete ground state)',
 'Main': 'Section 5: Theorem 3.4',
 'Spectral': 'μ_max as the largest eigenvalue of -Δ_h; Theorem 5.1 with μ = μ_max; ν attained',
 'Sign': 'Remark 2.3: uniqueness of the minimizer up to sign (irreducibility from the positive resolvent)',
 'Rate': 'Section 5: Theorem 5.1',
}

# Only source locations and definition/structure bodies are read textually.
# Types, docstrings, and dependencies below come from the compiled environment.
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(theorem|lemma|def|structure|abbrev)\s+([^\s(:]+)')


def mask_comments(text):
    """Preserve line positions while masking Lean comments and string literals."""
    out = list(text)
    depth = 0
    quoted = False
    i = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                out[i:i + 2] = '  '
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                out[i:i + 2] = '  '
                depth -= 1
                i += 2
            else:
                if text[i] != '\n':
                    out[i] = ' '
                i += 1
        elif quoted:
            if text[i] == '\\' and i + 1 < len(text):
                out[i:i + 2] = '  '
                i += 2
            else:
                quoted = text[i] != '"'
                if text[i] != '\n':
                    out[i] = ' '
                i += 1
        elif text.startswith('/-', i):
            out[i:i + 2] = '  '
            depth = 1
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out[i:end] = ' ' * (end - i)
            i = end
        elif text[i] == '"':
            quoted = True
            out[i] = ' '
            i += 1
        else:
            i += 1
    if depth or quoted:
        raise ValueError('Unclosed Lean comment or string')
    return ''.join(out)


def parse(fname):
    source = (ROOT / 'GPDYS' / (fname + '.lean')).read_text()
    lines = source.splitlines()
    masked = mask_comments(source).splitlines()
    scope = []
    decls = []
    for i, line in enumerate(masked):
        start = re.fullmatch(r'(namespace|section|noncomputable section)(?:\s+(\S+))?', line)
        if start:
            scope.append((start[1], start[2]))
            continue
        if re.fullmatch(r'end(?:\s+\S+)?', line):
            scope.pop()
            continue
        match = DECL.match(line)
        if not match:
            continue
        kind, name = match.groups()
        full = '.'.join([n for k, n in scope if k == 'namespace'] + [name])
        # Project definitions use indented continuations; stop before the next command/docstring.
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or lines[j].startswith(' ')):
            j += 1
        source_decl = '\n'.join(lines[i:j]).rstrip() if kind in ('def', 'abbrev', 'structure') else ''
        decls.append(dict(file=fname, line=i + 1, kind=kind, name=name, full=full,
                          source=source_decl, body=None, secvars=[]))
    return decls


by_file = OrderedDict((f, parse(f)) for f in FILES)
all_decls = OrderedDict((d['full'], d) for ds in by_file.values() for d in ds)
export = r'''import GPDYS
open Lean Elab Command Meta
run_cmd do
  let env ← getEnv
  let names : List Name := __NAMES__
  let mut queue := names.toArray
  let mut seen : NameSet := {}
  while let some name := queue.back? do
    queue := queue.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.find? name | throwError "missing declaration {name}"
    let deps := ci.getUsedConstantsAsSet.toArray
    for dep in deps do
      if dep.toString.startsWith "GPDYS." || dep.toString.startsWith "_private.GPDYS." then
        queue := queue.push dep
    let requested := names.contains name
    let type ← if requested then
      liftTermElabM do return (← Meta.ppExpr ci.type).pretty
      else pure ""
    let doc ← if requested then findDocString? env name else pure none
    let record := Json.mkObj [
      ("name", Json.str name.toString),
      ("type", Json.str type),
      ("doc", toJson doc),
      ("dependencies", toJson (deps.map Name.toString))]
    liftIO <| IO.println record.compress
'''.replace('__NAMES__', '[' + ', '.join('``' + n for n in all_decls) + ']')
with tempfile.TemporaryDirectory(prefix='gpdys-catalog-') as tmp:
    path = Path(tmp) / 'Export.lean'
    path.write_text(export)
    result = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT,
                            text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    metadata = {}
    for line in result.stdout.splitlines():
        if not line.startswith('{'):
            if line.strip():
                print(line)
            continue
        item = json.loads(line)
        metadata[item['name']] = item

for name, d in all_decls.items():
    m = metadata[name]
    if not m['type'] or '⋯' in m['type']:
        raise ValueError(f'Missing or abbreviated compiler type: {name}')
    d['doc'] = (m['doc'] or '').strip()
    d['full_type'] = name + ' :\n' + m['type']
    d['sig'] = d['source'] or d['full_type']

# Follow actual constant references, collapsing helpers between paper-level results.
uses = {n: set(m['dependencies']) & metadata.keys() for n, m in metadata.items()}
PAPERLEVEL = re.compile(r'\b(Lemma|Theorem|Proposition|Corollary|Remark)\b')
display = [n for n, d in all_decls.items()
           if PAPERLEVEL.search(d['doc']) and d['kind'] in ('theorem', 'lemma')]
display_set = set(display)
edges = set()
for a in display:
    seen = {a}
    stack = list(uses[a])
    while stack:
        b = stack.pop()
        if b in seen:
            continue
        seen.add(b)
        if b in display_set:
            edges.add((b, a))
        else:
            stack.extend(uses.get(b, ()))


def label(full):
    d = all_decls[full]
    match = re.search(r'(Lemma|Theorem|Proposition|Corollary|Remark)\s*(\d+(?:\.\d+)*)?', d['doc'])
    tag = (match[1] + (' ' + match[2] if match[2] else '')) if match else ''
    return (tag + '\\n' if tag else '') + d['name']


colors = {'Main': '#ffd27f', 'Rate': '#ffd27f', 'OneStep': '#c6e5b3',
          'Barrier': '#c6e5b3', 'GroundState': '#d9c7f0'}
dot = ['digraph G {', 'rankdir=BT; node [shape=box, style="rounded,filled", '
       'fontname="Helvetica", fontsize=10, fillcolor="#eeeeee"]; edge [color="#666666"];']
for full in display:
    d = all_decls[full]
    color = colors.get(d['file'], '#e8eef7')
    dot.append(f'  "{full}" [label="{label(full)}", fillcolor="{color}", '
               f'tooltip="{d["file"]}.lean:{d["line"]}"];')
for b, a in sorted(edges):
    dot.append(f'  "{b}" -> "{a}";')
dot.append('}')
(ROOT / 'dependency_graph.dot').write_text('\n'.join(dot) + '\n')
subprocess.run(['dot', '-Tsvg', '-o', str(ROOT / 'dependency_graph.svg'),
                str(ROOT / 'dependency_graph.dot')], check=True)

# ---------- Markdown ----------
md = []
md.append('# Catalog of statements in the Lean formalization\n')
md.append('Every explicitly named source definition, structure, and theorem, with its compiler '
          'docstring and elaborated type. These types include all actual implicit parameters and '
          'hypotheses introduced by `include`; `omit` is respected. Definition and structure '
          'bodies are also shown from source. Generated auxiliary declarations are not listed.\n')
md.append('Regenerate with `python3 tools/catalog.py` after installing Graphviz. '
          'The dependency graph follows compiled constant references through helper declarations.\n')
for f in FILES:
    md.append(f'\n## `GPDYS/{f}.lean` — {PAPER[f]}\n')
    for d in by_file[f]:
        md.append(f'\n### `{d["name"]}`  ({d["kind"]}, line {d["line"]})\n')
        if d['doc']:
            md.append(d['doc'] + '\n')

        body = ''
        if d['body']:
            body = ' :=\n  ' + d['body'] if '\n' in d['body'] or len(d['body']) > 60 else ' := ' + d['body']
        md.append('```lean\n' + d['sig'] + body + '\n```\n')
        if d['source']:
            md.append('*Elaborated type:*\n```lean\n' + d['full_type'] + '\n```\n')
open(os.path.join(ROOT, 'STATEMENTS.md'), 'w').write('\n'.join(md))

# ---------- HTML ----------
def esc(s): return html.escape(s)
h = ['<!doctype html><html><head><meta charset="utf-8"><title>GPDYS formalization — statements</title>',
     '<style>body{font-family:Georgia,serif;max-width:1000px;margin:2em auto;padding:0 1em;line-height:1.45}',
     'pre{background:#f6f8fa;border:1px solid #ddd;border-radius:6px;padding:.6em .9em;overflow-x:auto;font-size:13px;line-height:1.35}',
     'code{font-family:"DejaVu Sans Mono",Menlo,monospace}h2{border-bottom:2px solid #ccc;margin-top:2em}',
     'h3{margin-bottom:.2em;font-family:"DejaVu Sans Mono",monospace;font-size:15px}.meta{color:#666;font-size:13px}',
     '.doc{margin:.3em 0 .5em 0}.sec{color:#444;font-size:13px}details summary{cursor:pointer;color:#345}',
     'nav{columns:2;font-size:14px}</style></head><body>']
h.append('<h1>Statements of the Lean formalization</h1>')
h.append('<p>Source declarations with compiler docstrings and elaborated types, including all '
         'actual implicit parameters and inherited hypotheses. Definition and structure bodies '
         'are also shown. Generated auxiliary declarations are not listed.</p>')
h.append('<p><a href="dependency_graph.svg">Dependency graph of the paper-level results (SVG)</a></p>')
h.append('<nav><ul>')
for f in FILES:
    h.append(f'<li><a href="#{f}"><code>{f}.lean</code></a> — {esc(PAPER[f])}</li>')
h.append('</ul></nav>')
for f in FILES:
    h.append(f'<h2 id="{f}"><code>GPDYS/{f}.lean</code> — {esc(PAPER[f])}</h2>')
    for d in by_file[f]:
        h.append(f'<h3 id="{d["full"]}">{esc(d["name"])}</h3>')
        loc = (f'<a href="{GITHUB_BASE}/GPDYS/{f}.lean#L{d["line"]}">{f}.lean:{d["line"]}</a>' if GITHUB_BASE
               else f'{f}.lean:{d["line"]}')
        h.append(f'<div class="meta">{d["kind"]} · {loc} · <code>{esc(d["full"])}</code></div>')
        if d['doc']:
            doc = esc(d['doc'])
            doc = re.sub(r'`([^`]*)`', r'<code>\1</code>', doc)
            doc = re.sub(r'\*\*([^*]*)\*\*', r'<b>\1</b>', doc)
            h.append(f'<div class="doc">{doc}</div>')
        if d['secvars']:
            h.append('<details class="sec"><summary>section hypotheses</summary><pre>' + esc('\n'.join(d['secvars'])) + '</pre></details>')
        body = ''
        if d['body']:
            body = ' :=\n  ' + d['body'] if '\n' in d['body'] or len(d['body']) > 60 else ' := ' + d['body']
        h.append('<pre><code>' + esc(d['sig'] + body) + '</code></pre>')
        if d['source']:
            h.append('<details><summary>Elaborated type</summary><pre><code>'
                     + esc(d['full_type']) + '</code></pre></details>')
h.append('</body></html>')
open(os.path.join(ROOT, 'STATEMENTS.html'), 'w').write('\n'.join(h))
print(f'{len(all_decls)} declarations, {len(display)} paper-level results, {len(edges)} edges')

# ---------- Interactive dependency graph (HTML) ----------
svg = open(os.path.join(ROOT, 'dependency_graph.svg')).read()
svg = svg[svg.index('<svg'):]
uses_disp = {a: sorted(b for (b, a2) in edges if a2 == a) for a in display}
usedby_disp = {b: sorted(a for (b2, a) in edges if b2 == b) for b in display}
def tag_of(full):
    doc = all_decls[full]['doc'] or ''
    m = re.search(r'(Lemma|Theorem|Proposition|Corollary|Remark)\s*(\d+(?:\.\d+)*)?', doc)
    return (m.group(1) + (' ' + m.group(2) if m.group(2) else '')) if m else ''
info = {}
for full in display:
    d = all_decls[full]
    body = ''
    info[full] = {'name': d['name'], 'file': d['file'], 'line': d['line'], 'doc': d['doc'] or '',
                  'sig': d['sig'], 'secvars': '\n'.join(d['secvars']), 'tag': tag_of(full),
                  'uses': uses_disp.get(full, []), 'usedby': usedby_disp.get(full, [])}
page = r'''<!doctype html><html><head><meta charset="utf-8"><title>GPDYS — interactive dependency graph</title>
<style>
body{margin:0;font-family:Georgia,serif;display:flex;height:100vh;overflow:hidden}
#graph{flex:1;overflow:hidden;background:#fafafa;cursor:grab;position:relative}
#graph svg{width:100%;height:100%}
#graph .node{cursor:pointer}
#graph .node.sel polygon,#graph .node.sel path{stroke:#d33;stroke-width:3}
#graph .node.dep polygon,#graph .node.dep path{stroke:#2a7;stroke-width:3}
#graph .node.user polygon,#graph .node.user path{stroke:#27b;stroke-width:3}
#panel{width:520px;min-width:320px;max-width:60vw;overflow:auto;border-left:1px solid #ccc;padding:14px 18px;background:#fff;font-size:14px;line-height:1.45}
#panel h2{margin:.2em 0 .1em 0;font-size:18px}
#panel .tag{color:#a40;font-weight:bold}
#panel .meta{color:#666;font-size:12px;margin-bottom:.6em}
pre{background:#f6f8fa;border:1px solid #ddd;border-radius:6px;padding:.5em .7em;overflow-x:auto;font-size:12px;line-height:1.35;white-space:pre-wrap}
code{font-family:"DejaVu Sans Mono",Menlo,monospace}
#panel a{color:#246}
.hint{color:#555;font-size:13px}
ul.deps{margin:.2em 0 .6em 1.2em;padding:0}
ul.deps li{margin:.1em 0}
.legend span{display:inline-block;width:12px;height:12px;border:1px solid #888;margin-right:4px;vertical-align:middle}
#tools{position:absolute;top:8px;left:8px;z-index:2;font-size:12px;background:#fff;border:1px solid #ccc;border-radius:6px;padding:4px 8px}
</style></head><body>
<div id="graph"><div id="tools">scroll = zoom · drag = pan · click a node</div>''' + svg + r'''</div>
<div id="panel">
<h2>Dependency graph of the formalization</h2>
<p class="hint">Each box is a declaration whose docstring refers to a result in the paper. Arrows point from a lemma to the results whose proof uses it, so the two main theorems are at the top. Click a box to see the paper reference, the statement in Lean (proof hidden), and its dependencies among the displayed results. Edges follow compiled constant references through helpers; the elaborated types include every inherited hypothesis.</p>
<p class="legend"><span style="background:#ffd27f"></span>Section 5 (Theorems 3.4, 5.1) &nbsp; <span style="background:#c6e5b3"></span>Lemma 4.7 / Prop. 4.8 &nbsp; <span style="background:#d9c7f0"></span>ground state (Remark 2.3) &nbsp; <span style="background:#e8eef7"></span>other lemmas</p>
<p class="hint">Full catalog of all statements: <a href="STATEMENTS.html">STATEMENTS.html</a>.</p>
<div id="detail"></div>
</div>
<script>
const INFO = ''' + json.dumps(info, ensure_ascii=False) + r''';
const GITHUB_BASE = ''' + json.dumps(GITHUB_BASE) + r''';
const svgEl = document.querySelector('#graph svg');
const g0 = svgEl.querySelector('g.graph');
// pan/zoom on the top-level graph group
let scale = 1, tx = 0, ty = 0, dragging = false, sx = 0, sy = 0;
const vb = svgEl.getAttribute('viewBox').split(/\s+/).map(Number);
function apply(){ g0.setAttribute('transform', `translate(${tx} ${ty}) scale(${scale}) ` + (g0.dataset.base||'')); }
g0.dataset.base = g0.getAttribute('transform') || '';
svgEl.addEventListener('wheel', e => { e.preventDefault(); const f = e.deltaY < 0 ? 1.15 : 1/1.15;
  const pt = svgEl.createSVGPoint(); pt.x = e.clientX; pt.y = e.clientY; const p = pt.matrixTransform(svgEl.getScreenCTM().inverse());
  tx = p.x - (p.x - tx) * f; ty = p.y - (p.y - ty) * f; scale *= f; apply(); }, {passive:false});
svgEl.addEventListener('mousedown', e => { dragging = true; sx = e.clientX; sy = e.clientY; });
window.addEventListener('mouseup', () => dragging = false);
window.addEventListener('mousemove', e => { if (!dragging) return; const ctm = svgEl.getScreenCTM();
  tx += (e.clientX - sx) / ctm.a; ty += (e.clientY - sy) / ctm.d; sx = e.clientX; sy = e.clientY; apply(); });
const nodes = {};
svgEl.querySelectorAll('g.node').forEach(n => { const t = n.querySelector('title'); if (t) { nodes[t.textContent] = n; n.addEventListener('click', ev => { ev.stopPropagation(); select(t.textContent); }); } });
function esc(s){ return s.replace(/&/g,'&amp;').replace(/</g,'&lt;'); }
function md(s){ return esc(s).replace(/`([^`]*)`/g,'<code>$1</code>').replace(/\*\*([^*]*)\*\*/g,'<b>$1</b>'); }
function link(full){ const i = INFO[full]; return `<a href="#" data-full="${esc(full).replace(/"/g,'&quot;')}">${i.tag ? i.tag + ': ' : ''}<code>${i.name}</code></a>`; }
function select(full){
  Object.values(nodes).forEach(n => n.classList.remove('sel','dep','user'));
  const i = INFO[full]; if (!i) return;
  nodes[full].classList.add('sel');
  i.uses.forEach(u => nodes[u] && nodes[u].classList.add('dep'));
  i.usedby.forEach(u => nodes[u] && nodes[u].classList.add('user'));
  let h = `<h2><code>${i.name}</code></h2>`;
  if (i.tag) h += `<div class="tag">${i.tag} of the paper</div>`;
  const src = GITHUB_BASE ? `<a href="${GITHUB_BASE}/GPDYS/${i.file}.lean#L${i.line}">GPDYS/${i.file}.lean, line ${i.line}</a>` : `<code>GPDYS/${i.file}.lean</code>, line ${i.line}`;
  h += `<div class="meta">Lean file ${src} · <a href="STATEMENTS.html#${full}">in the catalog</a></div>`;
  if (i.doc) h += `<p>${md(i.doc)}</p>`;
  if (i.secvars) h += `<details><summary class="hint">section hypotheses (shared with neighbouring lemmas)</summary><pre><code>${esc(i.secvars)}</code></pre></details>`;
  h += `<pre><code>${esc(i.sig)}</code></pre>`;
  if (i.uses.length) h += `<div><b>Uses</b> (green):</div><ul class="deps">` + i.uses.map(u => `<li>${link(u)}</li>`).join('') + `</ul>`;
  if (i.usedby.length) h += `<div><b>Used by</b> (blue):</div><ul class="deps">` + i.usedby.map(u => `<li>${link(u)}</li>`).join('') + `</ul>`;
  const detail = document.getElementById('detail');
  detail.innerHTML = h;
  detail.querySelectorAll('a[data-full]').forEach(a => {
    a.addEventListener('click', event => { event.preventDefault(); select(a.dataset.full); });
  });
}
select('GPDYS.Setting.main_theorem');
</script></body></html>'''
open(os.path.join(ROOT, 'dependency_graph.html'), 'w').write(page)
print('interactive graph written')
