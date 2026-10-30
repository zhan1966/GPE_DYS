#!/usr/bin/env python3
"""Run GPDYS/Axioms.lean and reject missing results or unexpected axioms.

Run `lake build` first. This script also checks project Lean sources for forbidden
proof shortcuts and permits only linter-disabling set_option commands.
"""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
FORBIDDEN = re.compile(r'\b(?:axiom|sorry|admit|native_decide|unsafe|implemented_by)\b')


def check_sources():
    errors = []
    sources = [ROOT / 'GPDYS.lean', *sorted((ROOT / 'GPDYS').glob('*.lean'))]
    for path in sources:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            match = FORBIDDEN.search(line)
            if match:
                errors.append(f'{path.relative_to(ROOT)}:{number}: {match[0]}')
            if re.search(r'\bset_option\b', line) and not re.fullmatch(
                r'\s*set_option linter\.[\w.]+ false(?: in)?\s*', line
            ):
                errors.append(f'{path.relative_to(ROOT)}:{number}: unexpected set_option')
    return errors


def check_output(output, expected):
    errors = []
    found = set()
    for match in re.finditer(r"'(.+?)' depends on axioms:\s*\[([^\]]*)\]", output):
        name, body = match.groups()
        found.add(name)
        axioms = {part.strip() for part in body.split(',') if part.strip()}
        if axioms - ALLOWED:
            errors.append(f'{name}: unexpected axioms {sorted(axioms - ALLOWED)}')
    for match in re.finditer(r"'(.+?)' does not depend on any axioms", output):
        found.add(match[1])
    if found != expected:
        errors.append(f'Audit result mismatch: missing {sorted(expected - found)}, '
                      f'extra {sorted(found - expected)}')
    return errors


def main():
    errors = check_sources()
    audit = ROOT / 'GPDYS' / 'Axioms.lean'
    expected = set(re.findall(r'^#print axioms (\S+)$', audit.read_text(), re.MULTILINE))
    if not expected:
        errors.append('Axioms.lean contains no audit commands')
    if errors:
        sys.exit('\n'.join(errors))
    result = subprocess.run(['lake', 'env', 'lean', 'GPDYS/Axioms.lean'], cwd=ROOT,
                            text=True, capture_output=True)
    print(result.stdout, end='')
    if result.stderr:
        print(result.stderr, end='', file=sys.stderr)
    if result.returncode:
        sys.exit(result.returncode)
    errors = check_output(result.stdout, expected)
    if errors:
        sys.exit('\n'.join(errors))
    print(f'Integrity check passed for {len(expected)} audited results.')


if __name__ == '__main__':
    main()
