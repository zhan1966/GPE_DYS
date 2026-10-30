# Lean 4 formalization of convergence of DYS I for the GP ground state

This project formalizes the fixed-mesh convergence analysis in

> J. Li, S. Zheng, X. Zhang, *Global convergence of an efficient splitting method for the
> defocusing Gross–Pitaevskii ground state problem*, arXiv:2609.13509,
> <https://arxiv.org/abs/2609.13509>.

Repository: <https://github.com/zhan1966/GPE_DYS>. The Lean code was written with AI assistance
(Claude, Anthropic) and independently reviewed with a second AI system (OpenAI Codex) against the
paper; every proof is checked by the Lean kernel (see the axiom audit below). See `CITATION.cff`
for how to cite.

Lean `v4.35.0` and Mathlib tag `v4.35.0` are pinned in `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`. The paper itself is not included. Equation references below follow the
reviewed manuscript: DYS I is (1.6), the discrete inner product is (2.3), and the energy is (2.4).

## What is formalized

* **Theorem 3.4:** `GPDYS.Setting.main_theorem` proves positivity of every normalized iterate,
  convergence to a positive global minimizer, convergence of the energy, and uniqueness among
  nonnegative minimizers and among nonnegative critical points.
* **Theorem 5.1:** `GPDYS.Setting.rate_theorem'` obtains the limiting positive critical point from
  Theorem 3.4 and proves the lower bound on `ν`, positivity of `ν`, `0 < η < 1`, and both geometric
  estimates (5.6). Its parameter `μ ≥ 0` is any upper bound for the Rayleigh quotient of `-Δ_h`;
  `GPDYS.Setting.rate_theorem_μmax` (in `Spectral.lean`) instantiates it with `μ_max`, the largest
  eigenvalue of `-Δ_h` (`μmax`, proved to be attained, to be an eigenvalue, and to dominate every
  eigenvalue), so that `η` is literally the paper's rate. `nu_attained` shows that `ν` is a minimum.
  `rate_theorem` is the conditional version: its section hypotheses include convergence to a
  specified positive normalized critical point `p`.
* **Remark 2.3:** `GPDYS.Setting.exists_groundState` proves existence of a positive normalized
  critical point, global minimality, and uniqueness among nonnegative critical points.
  `eq_of_nonneg_le_energy` proves uniqueness among nonnegative minimizers, and
  `GPDYS.Setting.exists_groundState_sign` (in `Sign.lean`) adds uniqueness up to an overall sign:
  every minimizer of `E_h` on `𝓜` is `u_GS` or `-u_GS`. The irreducibility of `S` needed for this
  is derived from the entrywise positivity of the resolvent (`S_irreducible`).
* **Intermediate estimates:** Lemmas 3.1, 3.2, 4.1–4.7 and Proposition 4.8 are represented by the
  declarations below. Conjunctions are often split across declarations, and many norm estimates
  use squared norms. Routine consequences, such as multiplying the bounds on `λ` by `γ > 0`,
  are not always separate named declarations.

Vectors are functions `ι → ℝ` on a finite index type. `GPDYS.Setting` assumes positive weights,
nonnegative potential, `β > 0`, a symmetric positive semidefinite stiffness matrix with nonpositive
off-diagonal entries and an entrywise positive resolvent, and a discrete Sobolev inequality.
These are the **fixed-mesh** properties from Lemma 2.2. The project does not construct the finite
element/finite difference matrices or prove that a family of meshes admits a common Sobolev
constant. Thus it proves convergence from the abstract discretization properties, rather than
formalizing Assumption 2.1 and its implication to Lemma 2.2.

## Files and correspondence with the paper

All theorem names in the table are in `GPDYS.Setting`, except `GPDYS.exists_sobolev_const`.

| File | Main declarations or contents | Paper |
|---|---|---|
| `GPDYS/Basic.lean` | `Setting`; weighted norms; `energy`, `nonlin`, `gradE`, `lam`, `g`; `GX`, `resolvent`, `nrmXsq`, `nrmGsq`; `step`, `R`, `lyap`, `iter`, `uiter`; data constants and `Conditions` | Sections 2–3 |
| `GPDYS/Lemmas.lean` | Bilinearity, Cauchy–Schwarz, energy and normalization identities | Section 3.1 |
| `GPDYS/Resolvent.lean` | Invertibility, self-adjointness, norm bounds, contraction and norm equivalence | (3.5)–(3.7), (5.3) |
| `GPDYS/Holder.lean` | Weighted Hölder estimates | Lemma 4.3 |
| `GPDYS/SobolevConst.lean` | `exists_sobolev_const` on a fixed nonempty mesh | Fixed-mesh counterpart of Lemma 2.2(iii) |
| `GPDYS/Constants.lean` | `conditions_of_le_γmax`, `le_γmax_of_conditions`, `lyap_init_le_E0`; `kin_le_two_E0`, `h1norm_le`, `wnorm6_sq_le_P0`, `sq_le_U0`, `nrm2_cube_le`, `wnorm4p4_le_min`, `nrm2_nonlin_le`, `inner_nonlin_self_le`, `lam_le_two_D` | Lemmas 3.1–3.2 |
| `GPDYS/Step.lean` | `GX_step`, `GX_step_sub`, `GX_delta`, `radial_identity`; `energy_identity`, `residual_identity` | Lemmas 4.1–4.2 |
| `GPDYS/Nonlinear.lean` | `taylorT_le`, `abs_inner_nonlin_sub_le` | Lemma 4.3 |
| `GPDYS/Positivity.lean` | `step_pos`, `one_sub_inner_step_le`, `inner_step_le_nrm2`, `nrm2_step_le_one`, `nrm2sq_delta_le_two_mul`, `nrm2sq_delta_le`, `abs_R_le` | Lemma 4.4 |
| `GPDYS/Descent.lean` | `conditional_descent`, `descent_equality_case`; `gradX_sq_le`, `nrmGsq_step_sub_le`; `energy_step_le_of_small` | Lemmas 4.5–4.6; auxiliary for Lemma 4.7 |
| `GPDYS/Barrier.lean` | `energy_barrier` and continuation lemmas | Lemma 4.7 |
| `GPDYS/OneStep.lean` | `onestep_pos`, `onestep_radial`, `onestep_energy`, `onestep_drop`, `onestep_drop'` | Proposition 4.8 |
| `GPDYS/GroundState.lean` | `picone`, `critical_pos`, `energy_le_of_critical`, `eq_of_nonneg_le_energy`, `eq_of_critical_nonneg` | Remark 2.3 |
| `GPDYS/Main.lean` | `invariant`, `drop_summable`, `main_theorem`, `exists_groundState` | Theorem 3.4 |
| `GPDYS/Rate.lean` | `hess`, `nu`, `nu_ge`, `local_quadratic_growth`, `local_PL`, `rate_theorem`, `rate_theorem'` | Theorem 5.1 |
| `GPDYS/Spectral.lean` | `μmax`, the largest eigenvalue of `-Δ_h` (attained, an eigenvalue, dominates all eigenvalues); Theorem 5.1 with `μ = μ_max` (`rate_theorem_μmax`); `ν` is attained (`nu_attained`) | Theorem 5.1 |
| `GPDYS/Sign.lean` | irreducibility of `S` from the positive resolvent; uniqueness of the minimizer up to sign (`exists_groundState_sign`) | Remark 2.3 |
| `GPDYS/Axioms.lean` | Axiom reports for nine results | Integrity audit |

The data constants `E0`, `P0`, `U0`, `B0`, `D`, `B1`, `C0`, `L0`, and `γmax` have the paper's
formulas (3.9)–(3.14); `Conditions` is (C1)–(C4), (3.15), with `γ > 0` supplied separately.

## Where the formal proof deviates from the text

* **Fixed-mesh scope.** `Setting.sobolev` has no mesh-family parameter, so the mesh-independent
  part of Lemma 2.2(iii) and the refinement discussion of Remark 3.3 are outside its scope.
  `SobolevConst.lean` supplies a possibly mesh-dependent constant for any positive weights and
  positive semidefinite stiffness matrix on a nonempty finite index type. The formal proofs
  need only `Λd ≥ 0`; the paper's quadratic-root argument invokes `Λd > 0` from positive
  definiteness. `C4_identity` also handles `Λd = 0` without dividing by it.
* **Norms and total functions.** The project uses explicit weighted sums and their square roots,
  with `nrmXsq` and `nrmGsq` for squared norms, rather than installing these as Lean norm instances.
  `normalize 0 = 0` is a total-function convention; the one-step hypotheses and `iter_ne_zero`
  exclude zero on the analyzed orbit. Convergence is in the usual finite product topology, which
  agrees with convergence in the weighted norm.
* **Extrema and dimension.** Finite `⨅`/`⨆` expressions give `wmin`, `Vinf`, `Λd`, and `mGS`.
  They are minima/maxima on a nonempty mesh; their empty-index value is zero. Normalization
  entails nonemptiness, while `exists_groundState` needs it as an assumption. For the local rate,
  `2 ≤ Fintype.card ι` is exactly the paper's `N ≥ 2`. `nu` is defined by `sInf`, and
  `exists_unit_tangent` and `bddBelow_nu_set` justify its use, and `nu_attained` (`Spectral.lean`)
  shows that the infimum is attained, so `ν` is the paper's minimum.
* **Spectral arguments.** `Resolvent.lean` proves (3.5)–(3.7), the contraction in Lemma 4.4,
  and (5.3) by substituting `v = GX γ y`, where `y = resolvent γ v`. For (5.3) and the rate,
  `μ_max` is replaced by any `μ ≥ 0` satisfying `kin v ≤ μ * nrm2sq v` for all `v`.
  `exists_kin_bound` gives such a bound, and `Spectral.lean` defines `μmax` as the maximum of the
  Rayleigh quotient and proves that it is the largest eigenvalue of `-Δ_h` (`μmax_isEigenvalue`,
  `eigenvalue_le_μmax`); `rate_theorem_μmax` is Theorem 5.1 with this `μ_max`.
* **Taylor and nonlinear estimates.** `taylorT` is the energy difference minus the linear term
  in (4.2). The proof uses its exact polynomial expansion `taylorT_eq`, without the integral
  representation. The pointwise and Sobolev lemmas prove the corresponding remainder bounds
  directly, rather than separately formalizing the Jacobian inequalities (4.12)–(4.13).
* **Energy barrier, Lemma 4.7.** The paper differentiates the continued energy at `θ = 0`.
  `energy_step_le_of_small` instead uses the crude constant `C1 = Vinf + 3β/wmin` and the condition
  `γ(28D + 2C1) ≤ 1` to prove `E_h(u⁺) ≤ E_h(u) + 2D R²` without an energy hypothesis on `u⁺`.
  Applying this to the scaled step establishes the initial part of the continuation. This extra
  smallness condition is used only there; it is not an additional assumption of `energy_barrier`
  or either main theorem. The remaining continuity, supremum, and equality-case arguments follow
  the paper. Matrix-inverse continuity uses Mathlib's `continuousAt_matrix_inv`.
* **Ground-state facts.** The paper invokes Perron–Frobenius and hidden convexity. Here positivity
  follows from the positive resolvent, while the discrete Picone inequality gives
  `E_h(v) ≥ E_h(u) + (β/4) ∑ᵢ wᵢ(vᵢ² - uᵢ²)²` for normalized positive critical `u` and
  nonnegative normalized `v`. Together with `energy_abs_le`, this proves global minimality and
  uniqueness among nonnegative minimizers. Existence comes from an accumulation point of the
  iteration. Uniqueness up to sign (`Sign.lean`) uses the irreducibility of `S`, derived from the
  entrywise positive resolvent: a block-diagonal `M + S` would have a block-diagonal inverse.
* **Local rate.** Exact expansions `energy_sub_eq` and `inner_g_sub_eq`, followed by a tangential
  Hessian-form lower bound, replace the paper's chart and Hessian-continuity argument. The local
  growth and PL estimates are the consequences in the original coordinates deduced after (5.8),
  not the chart-space statement (5.8) itself. `rate_theorem'` packages convergence and the rate;
  global minimality of its positive critical point follows from `energy_le_of_critical`.

## Reading the statements

[STATEMENTS.md](STATEMENTS.md) and [STATEMENTS.html](STATEMENTS.html) contain each explicitly
named source declaration and its docstring. The types are exported by Lean, so they include all
implicit parameters and hypotheses actually retained by `include` and `omit`. Definitions and
structure fields are also shown from source. In Lean, a `variable` declaration alone does **not**
add every variable to every theorem: occurrence, proof use, and `include`/`omit` determine the type.

Open [dependency_graph.html](dependency_graph.html) locally for an interactive graph, or use
[dependency_graph.svg](dependency_graph.svg). Arrows point from a result to results that use it.
Edges follow compiled constant references through helper declarations; they do not establish
logical necessity of a dependency. The DOT source is also included. The redundant PNG is ignored.

To regenerate the catalogs and graphs, install Python 3 and Graphviz (`dot`), then run:

```sh
python3 tools/catalog.py
```

The generator builds the project first and infers its root from its own location. Optional
`--github-base https://github.com/OWNER/REPO/blob/REF` adds source links to the HTML. There are no
Python package dependencies.

## Building and checking

Install Lean using [the official installation instructions](https://lean-lang.org/install/).
From the repository root:

```sh
lake exe cache get
lake build
lake env lean GPDYS/Axioms.lean
python3 tools/check_axioms.py
```

The first command downloads the Mathlib cache. Preserve `lake-manifest.json`; do not use
`lake update` for routine builds, since it resolves dependencies again.

The nine axiom reports must contain only `propext`, `Classical.choice`, and `Quot.sound`.
`tools/check_axioms.py` fails on unexpected axioms, missing audit results, or forbidden source
constructs. GitHub Actions runs `lake build` and this check on pushes and pull requests, using
[leanprover/lean-action](https://github.com/leanprover/lean-action).

For interactive reading, open the repository in VS Code with the Lean 4 extension. Hover over a
name to see its type; place the cursor in a proof to inspect its goals in the Lean Infoview.
Machine-specific notes are kept in the ignored `LOCAL_SETUP.md`.

## License

This project is licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE).
