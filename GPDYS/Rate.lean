import GPDYS.Main

/-!
# Local linear convergence (Theorem 5.1)

Let `p = u_GS` be the discrete ground state, `λ_GS = λ(p)`, `m_GS = minᵢ pᵢ`, and
`ℋ = -Δ_h + n'(p) - λ_GS I`, (5.4). Let `ν` be the minimum of `⟪w, ℋ w⟫_h` over the unit
tangent vectors `w ∈ 𝓜`, `⟪p, w⟫_h = 0`. Then `ν ≥ 2β m_GS² > 0` and, with `μ` a bound for the
Rayleigh quotient of `-Δ_h` (in the paper, its largest eigenvalue `μ_max`) and
`η = min{γν/(4(1+γμ)), 1/2}`, (5.5), the Lyapunov function decays geometrically once the
iterates are close to `p`, (5.6).

The local estimates deduced after (5.8) in the paper, `E_h(u) - E_GS ≥ (ν/4)‖u - p‖₂²` and
`E_h(u) - E_GS ≤ (1/ν)‖g(u)‖₂²` for `u ∈ 𝓜` near `p`, are obtained here without the chart and
without derivatives, from the two exact expansions in `h = u - p`
(valid for all `u ∈ 𝓜`):

* `E_h(u) - E_h(p) = ½⟪h, ℋ h⟫_h + β ∑ wᵢ pᵢ hᵢ³ + (β/4) ∑ wᵢ hᵢ⁴`,
* `⟪g(u), h⟫_h = ⟪h, ℋ h⟫_h + ⟪ρ, h⟫_h - ½‖h‖₂² ⟪ℋ h + ρ, u⟫_h`, `ρ = β(3 p h² + h³)`,

together with `⟪h, ℋ h⟫_h ≥ ν‖h‖₂² - O(‖h‖₂³)`, which follows from the definition of `ν` applied
to the tangential part of `h`.
-/

open Finset Filter Topology

noncomputable section

namespace GPDYS

/-- `m_GS = minᵢ pᵢ` on a nonempty mesh; the empty-index value is zero. -/
def mGS {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := ⨅ i, p i

/-- The rate `η = min{γν/(4(1+γμ)), 1/2}`, (5.5). -/
def η (γ μ ν : ℝ) : ℝ := min (γ * ν / (4 * (1 + γ * μ))) (1 / 2)

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- The operator `ℋ = -Δ_h + n'(p) - λ(p) I` of (5.4), applied to `w`. -/
def hess (p w : ι → ℝ) : ι → ℝ := P.negLap w + P.nonlin' p w - P.lam p • w

/-- The quadratic form `⟪w, ℋ w⟫_h`. -/
def hessForm (p w : ι → ℝ) : ℝ := P.inner w (P.hess p w)

/-- The infimum of `⟪w, ℋ w⟫_h` over unit tangent vectors.
For a positive critical point and `2 ≤ Fintype.card ι`, `exists_unit_tangent` and
`bddBelow_nu_set` justify the infimum used in the rate theorem. Attainment as a minimum
is proved by `nu_attained` in `Spectral.lean`. The empty-set value is zero. -/
def nu (p : ι → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ w : ι → ℝ, P.nrm2sq w = 1 ∧ P.inner p w = 0 ∧ x = P.hessForm p w}

/-! ### The Hessian form and the constant `ν` -/

theorem hessForm_eq (p w : ι → ℝ) :
    P.hessForm p w = P.kin w + P.pot w + 3 * P.β * (∑ i, P.w i * (p i ^ 2 * w i ^ 2))
      - P.lam p * P.nrm2sq w := by
  unfold hessForm hess
  rw [inner_sub_right, inner_add_right, inner_smul_right, ← kin_eq_inner, ← nrm2sq_def]
  have h : P.inner w (P.nonlin' p w)
      = P.pot w + 3 * P.β * ∑ i, P.w i * (p i ^ 2 * w i ^ 2) := by
    simp only [inner_def, pot, nonlin']
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h]; ring

/-- The Rayleigh bound of a positive critical point (via the discrete Picone inequality):
`⟪w, A_p w⟫_h ≥ λ(p) ‖w‖₂²` for every `w`, where `A_p = -Δ_h + V + β diag(p²)`. -/
theorem rayleigh_of_critical {p : ι → ℝ} (hp : P.nrm2sq p = 1) (hpos : ∀ i, 0 < p i)
    (hg : P.g p = 0) (w : ι → ℝ) :
    P.lam p * P.nrm2sq w ≤ P.kin w + P.pot w + P.β * ∑ i, P.w i * (p i ^ 2 * w i ^ 2) := by
  have hpic := P.picone hpos w
  have hneg := P.negLap_eq_of_critical hg
  -- `(S p)ᵢ = wᵢ (λ(p) pᵢ - Vᵢ pᵢ - β pᵢ³)`
  have hSp : ∀ i, (P.S.mulVec p) i = (P.lam p * p i - (P.V i * p i + P.β * p i ^ 3)) * P.w i := by
    intro i
    have h1 : P.negLap p i = P.lam p * p i - (P.V i * p i + P.β * p i ^ 3) := by
      rw [hneg]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nonlin_apply]
    rw [negLap_apply, div_eq_iff (P.w_pos i).ne'] at h1
    exact h1
  -- the Picone sum is `λ(p) ‖w‖₂² - ⟪V w, w⟫_h - β ∑ᵢ wᵢ pᵢ² wᵢ²`
  have hsum : ∑ i, (w i ^ 2 / p i) * (P.S.mulVec p) i
      = P.lam p * P.nrm2sq w - P.pot w - P.β * ∑ i, P.w i * (p i ^ 2 * w i ^ 2) := by
    rw [nrm2sq_eq_sum, pot, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSp i]
    have := (hpos i).ne'
    field_simp
    ring
  -- (`hp` is not needed for this inequality)
  have _ := hp
  linarith

omit [DecidableEq ι] P in
theorem mGS_le (p : ι → ℝ) (i : ι) : mGS p ≤ p i := Finite.ciInf_le p i

omit [DecidableEq ι] P in
theorem mGS_pos [Nonempty ι] {p : ι → ℝ} (hpos : ∀ i, 0 < p i) : 0 < mGS p := by
  obtain ⟨i0, hi0⟩ := Finite.exists_min p
  exact lt_of_lt_of_le (hpos i0) (le_ciInf hi0)

/-- Theorem 5.1: `⟪w, ℋ w⟫_h ≥ 2β m_GS² ‖w‖₂²` for every `w`. -/
theorem hessForm_ge {p : ι → ℝ} (hp : P.nrm2sq p = 1) (hpos : ∀ i, 0 < p i) (hg : P.g p = 0)
    (w : ι → ℝ) : 2 * P.β * (mGS p) ^ 2 * P.nrm2sq w ≤ P.hessForm p w := by
  have := P.nonempty_of_nrm2sq_eq_one hp
  have hm := mGS_pos hpos
  have hray := P.rayleigh_of_critical hp hpos hg w
  have hβ := P.β_pos
  rw [hessForm_eq]
  -- `m_GS² ‖w‖₂² ≤ ∑ᵢ wᵢ pᵢ² wᵢ²`
  have hsum : (mGS p) ^ 2 * P.nrm2sq w ≤ ∑ i, P.w i * (p i ^ 2 * w i ^ 2) := by
    rw [nrm2sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (mGS p) ^ 2 ≤ p i ^ 2 := pow_le_pow_left₀ hm.le (mGS_le p i) 2
    have h2 : 0 ≤ P.w i * w i ^ 2 := mul_nonneg (P.w_pos i).le (sq_nonneg _)
    calc (mGS p) ^ 2 * (P.w i * w i ^ 2) ≤ p i ^ 2 * (P.w i * w i ^ 2) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = P.w i * (p i ^ 2 * w i ^ 2) := by ring
  have := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 2 * P.β)
  linarith

/-- For `N ≥ 2` there is a unit vector orthogonal to `p`. -/
theorem exists_unit_tangent (hcard : 2 ≤ Fintype.card ι) {p : ι → ℝ} (hpos : ∀ i, 0 < p i) :
    ∃ w : ι → ℝ, P.nrm2sq w = 1 ∧ P.inner p w = 0 := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card ι)
  -- `v = (wⱼ pⱼ) eᵢ - (wᵢ pᵢ) eⱼ` is orthogonal to `p` and nonzero
  set v : ι → ℝ := (P.w j * p j) • Pi.single i 1 - (P.w i * p i) • Pi.single j 1 with hv
  have hsingle : ∀ k : ι, P.inner p (Pi.single k 1) = P.w k * p k := by
    intro k
    rw [inner_def]
    simp [Pi.single_apply]
  have hinner : P.inner p v = 0 := by
    rw [hv, inner_sub_right, inner_smul_right, inner_smul_right, hsingle, hsingle]
    ring
  have hv0 : v ≠ 0 := by
    intro h0
    have hi := congrFun h0 i
    rw [hv] at hi
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same,
      Pi.single_eq_of_ne hij, Pi.zero_apply] at hi
    have := mul_pos (P.w_pos j) (hpos j)
    linarith
  refine ⟨P.normalize v, P.nrm2sq_normalize hv0, ?_⟩
  rw [normalize_def, inner_smul_right, hinner, mul_zero]

/-- Theorem 5.1: `ν ≥ 2β m_GS²`. -/
theorem nu_ge (hcard : 2 ≤ Fintype.card ι) {p : ι → ℝ} (hp : P.nrm2sq p = 1)
    (hpos : ∀ i, 0 < p i) (hg : P.g p = 0) : 2 * P.β * (mGS p) ^ 2 ≤ P.nu p := by
  obtain ⟨w, hw1, hw2⟩ := P.exists_unit_tangent hcard hpos
  apply le_csInf
  · exact ⟨_, w, hw1, hw2, rfl⟩
  · rintro x ⟨w, hw1, hw2, rfl⟩
    have := P.hessForm_ge hp hpos hg w
    rw [hw1, mul_one] at this
    exact this

/-- `ν > 0`. -/
theorem nu_pos (hcard : 2 ≤ Fintype.card ι) {p : ι → ℝ} (hp : P.nrm2sq p = 1)
    (hpos : ∀ i, 0 < p i) (hg : P.g p = 0) : 0 < P.nu p := by
  have := P.nonempty_of_nrm2sq_eq_one hp
  have hm := mGS_pos hpos
  have hβ := P.β_pos
  exact lt_of_lt_of_le (by positivity) (P.nu_ge hcard hp hpos hg)

/-- `n'(p)` is linear in its second argument. -/
theorem nonlin'_add (p u v : ι → ℝ) : P.nonlin' p (u + v) = P.nonlin' p u + P.nonlin' p v := by
  funext i; simp only [nonlin', Pi.add_apply]; ring

theorem nonlin'_smul (p : ι → ℝ) (c : ℝ) (v : ι → ℝ) :
    P.nonlin' p (c • v) = c • P.nonlin' p v := by
  funext i; simp only [nonlin', Pi.smul_apply, smul_eq_mul]; ring

/-- `n'(p)` is a diagonal operator, hence `h`-self-adjoint. -/
theorem inner_nonlin'_comm (p x y : ι → ℝ) :
    P.inner x (P.nonlin' p y) = P.inner (P.nonlin' p x) y := by
  simp only [inner_def, nonlin']
  refine Finset.sum_congr rfl fun i _ => ?_; ring

/-- `ℋ` is linear. -/
theorem hess_add (p u v : ι → ℝ) : P.hess p (u + v) = P.hess p u + P.hess p v := by
  unfold hess
  rw [negLap_add, nonlin'_add, smul_add]
  abel

theorem hess_smul (p : ι → ℝ) (c : ℝ) (v : ι → ℝ) : P.hess p (c • v) = c • P.hess p v := by
  unfold hess
  rw [negLap_smul, nonlin'_smul, smul_sub, smul_add, smul_comm c (P.lam p) v]

@[simp] theorem hess_zero (p : ι → ℝ) : P.hess p 0 = 0 := by
  have := P.hess_smul p 0 0
  rwa [zero_smul, zero_smul] at this

/-- `ℋ` is `h`-self-adjoint: `⟪x, ℋ y⟫_h = ⟪ℋ x, y⟫_h`. -/
theorem inner_hess_comm (p x y : ι → ℝ) : P.inner x (P.hess p y) = P.inner (P.hess p x) y := by
  unfold hess
  rw [inner_sub_right, inner_add_right, inner_sub_left, inner_add_left, inner_smul_right,
    inner_smul_left, inner_negLap_comm, inner_nonlin'_comm]

/-- Homogeneity of the Hessian form. -/
theorem hessForm_smul (p : ι → ℝ) (c : ℝ) (w : ι → ℝ) :
    P.hessForm p (c • w) = c ^ 2 * P.hessForm p w := by
  unfold hessForm
  rw [hess_smul, inner_smul_left, inner_smul_right]; ring

@[simp] theorem hessForm_zero (p : ι → ℝ) : P.hessForm p 0 = 0 := by
  unfold hessForm; simp

/-- The set defining `ν` is bounded below by `2β m_GS²`. -/
theorem bddBelow_nu_set {p : ι → ℝ} (hp : P.nrm2sq p = 1) (hpos : ∀ i, 0 < p i)
    (hg : P.g p = 0) :
    BddBelow {x : ℝ | ∃ w : ι → ℝ, P.nrm2sq w = 1 ∧ P.inner p w = 0 ∧ x = P.hessForm p w} := by
  refine ⟨2 * P.β * (mGS p) ^ 2, ?_⟩
  rintro x ⟨w, hw1, hw2, rfl⟩
  have := P.hessForm_ge hp hpos hg w
  rw [hw1, mul_one] at this
  exact this

/-- `⟪w, ℋ w⟫_h ≥ ν ‖w‖₂²` for every tangent vector `w` (`⟪p, w⟫_h = 0`). -/
theorem hessForm_ge_nu {p : ι → ℝ} (hp : P.nrm2sq p = 1) (hpos : ∀ i, 0 < p i) (hg : P.g p = 0)
    {w : ι → ℝ} (hw : P.inner p w = 0) : P.nu p * P.nrm2sq w ≤ P.hessForm p w := by
  by_cases hw0 : w = 0
  · subst hw0
    simp [nrm2sq_eq_sum]
  · have hc := P.nrm2_pos_of_ne_zero hw0
    have hc2 : P.nrm2 w ^ 2 = P.nrm2sq w := P.nrm2_sq w
    -- the normalized vector `w / ‖w‖₂` is a unit tangent vector
    have hw' : P.nrm2sq ((P.nrm2 w)⁻¹ • w) = 1 := by
      rw [nrm2sq_smul, ← hc2]; field_simp
    have hw'' : P.inner p ((P.nrm2 w)⁻¹ • w) = 0 := by rw [inner_smul_right, hw, mul_zero]
    have hle : P.nu p ≤ P.hessForm p ((P.nrm2 w)⁻¹ • w) :=
      csInf_le (P.bddBelow_nu_set hp hpos hg) ⟨_, hw', hw'', rfl⟩
    rw [hessForm_smul] at hle
    have h := mul_le_mul_of_nonneg_left hle (sq_nonneg (P.nrm2 w))
    have e : P.nrm2 w ^ 2 * ((P.nrm2 w)⁻¹ ^ 2 * P.hessForm p w) = P.hessForm p w := by
      field_simp
    rw [← hc2]
    linarith

/-! ### Exact expansions around the ground state -/

/-- Exact energy expansion used here to prove Theorem 5.1, for `u, p ∈ 𝓜` with `p` critical
and `h = u - p`:
`E_h(u) - E_h(p) = ½⟪h, ℋ h⟫_h + β ∑ wᵢ pᵢ hᵢ³ + (β/4) ∑ wᵢ hᵢ⁴`. -/
theorem energy_sub_eq {p u : ι → ℝ} (hp : P.nrm2sq p = 1) (hg : P.g p = 0)
    (hu : P.nrm2sq u = 1) :
    P.energy u - P.energy p
      = (1 / 2) * P.hessForm p (u - p)
        + P.β * (∑ i, P.w i * (p i * (u i - p i) ^ 3))
        + P.β / 4 * (∑ i, P.w i * (u i - p i) ^ 4) := by
  -- the Taylor expansion (4.3) at `p` in the direction `h = u - p`
  have hT := P.taylorE p (u - p)
  rw [add_sub_cancel, inner_gradE_eq, hg, inner_zero_left, add_zero,
    P.inner_sub_self_eq hp hu, taylorT_eq] at hT
  -- the second Taylor sum in terms of the elementary sums
  have hsum : ∑ i, P.w i * ((u - p) i ^ 2 * (3 * p i ^ 2 + 2 * p i * (u - p) i + (u - p) i ^ 2 / 2))
      = 3 * ∑ i, P.w i * (p i ^ 2 * (u i - p i) ^ 2)
        + 2 * ∑ i, P.w i * (p i * (u i - p i) ^ 3)
        + (1 / 2) * ∑ i, P.w i * (u i - p i) ^ 4 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]
    ring
  have hpot : P.pot (u - p) = ∑ i, P.w i * (P.V i * (u i - p i) ^ 2) := by
    unfold pot; simp only [Pi.sub_apply]
  simp only [Pi.sub_apply] at hT
  rw [hessForm_eq, hpot]
  linear_combination hT + P.β / 2 * hsum

/-- The vector `ρ = β(3 p h² + h³)`. -/
def rho (p h : ι → ℝ) : ι → ℝ := fun i => P.β * (3 * p i * h i ^ 2 + h i ^ 3)

/-- `∇E_h(u) = λ(p) u + ℋ h + ρ` for `h = u - p`, `p` critical. -/
theorem gradE_eq_of_critical {p u : ι → ℝ} (hg : P.g p = 0) :
    P.gradE u = P.lam p • u + P.hess p (u - p) + P.rho p (u - p) := by
  have hneg := P.negLap_eq_of_critical hg
  have hu : P.negLap u = P.negLap p + P.negLap (u - p) := by
    rw [← negLap_add, add_sub_cancel]
  rw [gradE_def, hu, hneg]
  funext i
  simp only [hess, rho, nonlin', nonlin_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- Exact expansion used here to prove Theorem 5.1: `⟪g(u), h⟫_h`,
using `⟪u, h⟫_h = ½‖h‖₂²`:
`⟪g(u), h⟫_h = ⟪h, ℋ h⟫_h + ⟪ρ, h⟫_h - ½‖h‖₂² ⟪ℋ h + ρ, u⟫_h`. -/
theorem inner_g_sub_eq {p u : ι → ℝ} (hp : P.nrm2sq p = 1) (hg : P.g p = 0)
    (hu : P.nrm2sq u = 1) :
    P.inner (P.g u) (u - p)
      = P.hessForm p (u - p) + P.inner (P.rho p (u - p)) (u - p)
        - (1 / 2) * P.nrm2sq (u - p) * P.inner (P.hess p (u - p) + P.rho p (u - p)) u := by
  have hgrad := P.gradE_eq_of_critical (u := u) hg
  -- `λ(u) = λ(p) + ⟪ℋ h + ρ, u⟫_h`
  have hlam : P.lam u = P.lam p + P.inner (P.hess p (u - p) + P.rho p (u - p)) u := by
    have e : P.lam u = P.inner (P.gradE u) u := rfl
    rw [e, hgrad, inner_add_left, inner_add_left, inner_smul_left, ← nrm2sq_def, hu,
      inner_add_left]
    ring
  -- `⟪u, h⟫_h = ½‖h‖₂²`
  have huh : P.inner u (u - p) = (1 / 2) * P.nrm2sq (u - p) := by
    rw [inner_sub_right, ← nrm2sq_def, hu, nrm2sq_sub, hu, hp]; ring
  have h1 : P.inner (P.g u) (u - p)
      = P.inner (P.gradE u) (u - p) - P.lam u * P.inner u (u - p) := by
    unfold g; rw [inner_sub_left, inner_smul_left]
  have h2 : P.inner (P.gradE u) (u - p)
      = P.lam p * P.inner u (u - p) + P.inner (P.hess p (u - p)) (u - p)
        + P.inner (P.rho p (u - p)) (u - p) := by
    rw [hgrad, inner_add_left, inner_add_left, inner_smul_left]
  have h3 : P.hessForm p (u - p) = P.inner (P.hess p (u - p)) (u - p) := by
    unfold hessForm; rw [inner_comm]
  rw [h1, h2, h3, hlam, huh]
  ring

/-- `ℋ p = 2β p³` for a critical point `p`. -/
theorem hess_self {p : ι → ℝ} (hg : P.g p = 0) :
    P.hess p p = (2 * P.β) • fun i => p i ^ 3 := by
  funext i
  simp only [hess, P.negLap_eq_of_critical hg, nonlin', nonlin_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Decomposition of the Hessian form along `h = (h - c p) + c p`. -/
theorem hessForm_decomp (p h : ι → ℝ) (c : ℝ) :
    P.hessForm p h = P.hessForm p (h - c • p) + 2 * c * P.inner (h - c • p) (P.hess p p)
      + c ^ 2 * P.inner p (P.hess p p) := by
  have e : h = (h - c • p) + c • p := (sub_add_cancel h (c • p)).symm
  conv_lhs => rw [e]
  unfold hessForm
  rw [hess_add, hess_smul]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
  rw [P.inner_hess_comm p p (h - c • p), P.inner_comm (P.hess p p) (h - c • p)]
  ring

/-- The elementary inequality behind `hessForm_sub_ge`. -/
theorem hessForm_sub_ge_aux {ν β N3 R HT X Y c : ℝ}
    (hc : c = -(1 / 2) * R ^ 2) (hnu : ν * (R ^ 2 - c ^ 2) ≤ HT) (hY : 0 ≤ Y)
    (hX : |X| ≤ R * (2 * β * N3)) :
    ν * R ^ 2 - ν / 4 * (R ^ 2) ^ 2 - 2 * β * N3 * R ^ 3 ≤ HT + 2 * c * X + c ^ 2 * Y := by
  subst hc
  have h1 : -(|-(1 / 2) * R ^ 2| * |X|) ≤ (-(1 / 2) * R ^ 2) * X := by
    rw [← abs_mul]; exact neg_abs_le _
  rw [abs_of_nonpos (by nlinarith)] at h1
  have h2 := mul_le_mul_of_nonneg_left hX (by positivity : (0 : ℝ) ≤ (1 / 2) * R ^ 2)
  have h3 : 0 ≤ (-(1 / 2) * R ^ 2) ^ 2 * Y := mul_nonneg (sq_nonneg _) hY
  nlinarith [h1, h2, h3, hnu]

/-- The tangential lower bound: `⟪h, ℋ h⟫_h ≥ ν‖h‖₂² - (ν/4)‖h‖₂⁴ - 2β‖p³‖₂ ‖h‖₂³`
for `h = u - p` with `u, p ∈ 𝓜`. -/
theorem hessForm_sub_ge {p u : ι → ℝ} (hp : P.nrm2sq p = 1) (hpos : ∀ i, 0 < p i)
    (hg : P.g p = 0) (hu : P.nrm2sq u = 1) :
    P.nu p * P.nrm2sq (u - p) - P.nu p / 4 * (P.nrm2sq (u - p)) ^ 2
        - 2 * P.β * P.nrm2 (fun i => p i ^ 3) * P.nrm2 (u - p) ^ 3
      ≤ P.hessForm p (u - p) := by
  have hβ := P.β_pos
  have hN3 := P.nrm2_nonneg (fun i => p i ^ 3)
  have hN : P.nrm2sq (u - p) = P.nrm2 (u - p) ^ 2 := (P.nrm2_sq _).symm
  have hc : P.inner p (u - p) = -(1 / 2) * P.nrm2sq (u - p) := P.inner_sub_self_eq hp hu
  -- the tangential part `hT = h - c p`, `c = ⟪p, h⟫_h`
  have horth : P.inner p (u - p - P.inner p (u - p) • p) = 0 := by
    rw [inner_sub_right, inner_smul_right, ← nrm2sq_def, hp]; ring
  have hnu := P.hessForm_ge_nu hp hpos hg horth
  have hNT : P.nrm2sq (u - p - P.inner p (u - p) • p)
      = P.nrm2sq (u - p) - P.inner p (u - p) ^ 2 := by
    rw [nrm2sq_sub, nrm2sq_smul, hp, inner_smul_right, P.inner_comm (u - p) p]; ring
  rw [hNT] at hnu
  have hdec := P.hessForm_decomp p (u - p) (P.inner p (u - p))
  -- `⟪p, ℋ p⟫_h = 2β ∑ᵢ wᵢ pᵢ⁴ ≥ 0`
  have hY : 0 ≤ P.inner p (P.hess p p) := by
    rw [P.hess_self hg, inner_smul_right, inner_def]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    have := hpos i; have := P.w_pos i
    positivity
  -- `|⟪hT, ℋ p⟫_h| ≤ 2β ‖hT‖₂ ‖p³‖₂ ≤ 2β ‖h‖₂ ‖p³‖₂`
  have hX : |P.inner (u - p - P.inner p (u - p) • p) (P.hess p p)|
      ≤ P.nrm2 (u - p) * (2 * P.β * P.nrm2 (fun i => p i ^ 3)) := by
    have hT_le : P.nrm2 (u - p - P.inner p (u - p) • p) ≤ P.nrm2 (u - p) := by
      rw [nrm2_le_nrm2_iff, hNT]
      nlinarith [sq_nonneg (P.inner p (u - p))]
    have hcs := P.abs_inner_le_nrm2_mul_nrm2 (u - p - P.inner p (u - p) • p) (fun i => p i ^ 3)
    rw [P.hess_self hg, inner_smul_right, abs_mul, abs_of_pos (by positivity)]
    calc 2 * P.β * |P.inner (u - p - P.inner p (u - p) • p) fun i => p i ^ 3|
        ≤ 2 * P.β * (P.nrm2 (u - p - P.inner p (u - p) • p) * P.nrm2 fun i => p i ^ 3) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ ≤ 2 * P.β * (P.nrm2 (u - p) * P.nrm2 fun i => p i ^ 3) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT_le hN3) (by positivity)
      _ = P.nrm2 (u - p) * (2 * P.β * P.nrm2 fun i => p i ^ 3) := by ring
  rw [hN] at hnu hc
  rw [hdec, hN]
  exact hessForm_sub_ge_aux hc hnu hY hX

/-! ### The local estimates deduced after (5.8) -/

/-- The pointwise bound `vᵢ² ≤ K ‖v‖₂²` with `K = 1/w_min`. -/
theorem exists_sq_bound [Nonempty ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ v : ι → ℝ, ∀ i, v i ^ 2 ≤ K * P.nrm2sq v := by
  have hw := P.wmin_pos
  refine ⟨1 / P.wmin, by positivity, fun v i => ?_⟩
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hw]
  calc v i ^ 2 * P.wmin ≤ v i ^ 2 * P.w i :=
        mul_le_mul_of_nonneg_left (P.wmin_le i) (sq_nonneg _)
    _ = P.w i * v i ^ 2 := by ring
    _ ≤ P.nrm2sq v := P.w_mul_sq_le_nrm2sq v i

/-- `|pᵢ hᵢ| ≤ K ‖h‖₂` for a unit vector `p`. -/
theorem abs_mul_le_of_unit {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ v : ι → ℝ, ∀ i, v i ^ 2 ≤ K * P.nrm2sq v) {p : ι → ℝ} (hp : P.nrm2sq p = 1)
    (h : ι → ℝ) (i : ι) : |p i * h i| ≤ K * P.nrm2 h := by
  apply abs_le_of_sq_le_sq _ (mul_nonneg hK0 (P.nrm2_nonneg h))
  have h1 := hK p i
  rw [hp, mul_one] at h1
  have h2 := hK h i
  rw [mul_pow, mul_pow, nrm2_sq]
  calc p i ^ 2 * h i ^ 2 ≤ K * (K * P.nrm2sq h) := mul_le_mul h1 h2 (sq_nonneg _) hK0
    _ = K ^ 2 * P.nrm2sq h := by ring

/-- `|∑ᵢ wᵢ pᵢ hᵢ³| ≤ K ‖h‖₂³` for a unit vector `p`. -/
theorem abs_sum_cube_le {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ v : ι → ℝ, ∀ i, v i ^ 2 ≤ K * P.nrm2sq v) {p : ι → ℝ} (hp : P.nrm2sq p = 1)
    (h : ι → ℝ) : |∑ i, P.w i * (p i * h i ^ 3)| ≤ K * P.nrm2 h ^ 3 := by
  have hN := P.nrm2_sq h
  calc |∑ i, P.w i * (p i * h i ^ 3)| ≤ ∑ i, |P.w i * (p i * h i ^ 3)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, P.w i * h i ^ 2 * |p i * h i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show P.w i * (p i * h i ^ 3) = (P.w i * h i ^ 2) * (p i * h i) by ring, abs_mul,
          abs_of_nonneg (mul_nonneg (P.w_pos i).le (sq_nonneg (h i)))]
    _ ≤ ∑ i, P.w i * h i ^ 2 * (K * P.nrm2 h) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (P.abs_mul_le_of_unit hK0 hK hp h i)
            (mul_nonneg (P.w_pos i).le (sq_nonneg _))
    _ = P.nrm2sq h * (K * P.nrm2 h) := by rw [← Finset.sum_mul, ← nrm2sq_eq_sum]
    _ = K * P.nrm2 h ^ 3 := by rw [← hN]; ring

/-- `∑ᵢ wᵢ hᵢ⁴ ≤ K ‖h‖₂⁴`. -/
theorem sum_pow_four_le {K : ℝ} (hK : ∀ v : ι → ℝ, ∀ i, v i ^ 2 ≤ K * P.nrm2sq v)
    (h : ι → ℝ) : ∑ i, P.w i * h i ^ 4 ≤ K * P.nrm2sq h ^ 2 := by
  calc ∑ i, P.w i * h i ^ 4 = ∑ i, P.w i * h i ^ 2 * h i ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ ∑ i, P.w i * h i ^ 2 * (K * P.nrm2sq h) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hK h i) (mul_nonneg (P.w_pos i).le (sq_nonneg _))
    _ = P.nrm2sq h * (K * P.nrm2sq h) := by rw [← Finset.sum_mul, ← nrm2sq_eq_sum]
    _ = K * P.nrm2sq h ^ 2 := by ring

/-- Theorem 5.1, local quadratic growth deduced after (5.8): there is `r > 0` such that
`(ν/4)‖u - p‖₂² ≤ E_h(u) - E_h(p)` for every `u ∈ 𝓜` with `‖u - p‖₂ ≤ r`. -/
theorem local_quadratic_growth [Nonempty ι] (hcard : 2 ≤ Fintype.card ι) {p : ι → ℝ}
    (hp : P.nrm2sq p = 1) (hpos : ∀ i, 0 < p i) (hg : P.g p = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : ι → ℝ, P.nrm2sq u = 1 → P.nrm2 (u - p) ≤ r →
      P.nu p / 4 * P.nrm2sq (u - p) ≤ P.energy u - P.energy p := by
  have hν := P.nu_pos hcard hp hpos hg
  have hβ := P.β_pos
  have hN3 := P.nrm2_nonneg (fun i => p i ^ 3)
  obtain ⟨K, hK0, hK⟩ := P.exists_sq_bound
  -- the constant `C` collecting the cubic terms
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = P.β * P.nrm2 (fun i => p i ^ 3) + P.β * K + P.nu p / 8 := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC]; positivity
  refine ⟨min 1 (P.nu p / (4 * C)), lt_min one_pos (by positivity), fun u hu hr => ?_⟩
  have hr1 : P.nrm2 (u - p) ≤ 1 := hr.trans (min_le_left _ _)
  have hr2 : P.nrm2 (u - p) * (4 * C) ≤ P.nu p :=
    (le_div_iff₀ (by positivity)).mp (hr.trans (min_le_right _ _))
  have hR := P.nrm2_nonneg (u - p)
  have hN : P.nrm2sq (u - p) = P.nrm2 (u - p) ^ 2 := (P.nrm2_sq _).symm
  have hE := P.energy_sub_eq hp hg hu
  have hH := P.hessForm_sub_ge hp hpos hg hu
  have h3 := P.abs_sum_cube_le hK0.le hK hp (u - p)
  have hS4 : 0 ≤ ∑ i, P.w i * (u - p) i ^ 4 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (P.w_pos i).le (by positivity)
  simp only [Pi.sub_apply] at h3 hS4
  rw [hN] at hH ⊢
  rw [hE]
  have h3' := mul_le_mul_of_nonneg_left (abs_le.mp h3).1 hβ.le
  have hS4' := mul_nonneg (by positivity : (0 : ℝ) ≤ P.β / 4) hS4
  have hR4 : P.nrm2 (u - p) ^ 4 ≤ P.nrm2 (u - p) ^ 3 :=
    pow_le_pow_of_le_one hR hr1 (by norm_num)
  have hR4' := mul_le_mul_of_nonneg_left hR4 (by positivity : (0 : ℝ) ≤ P.nu p / 8)
  have hCR := mul_le_mul_of_nonneg_right hr2 (sq_nonneg (P.nrm2 (u - p)))
  rw [hC] at hCR
  linarith

/-- `‖-Δ_h v‖₂ ≤ μ ‖v‖₂` under the Rayleigh bound `⟪·,-Δ_h ·⟫_h ≤ μ ‖·‖₂²`. -/
theorem nrm2_negLap_le {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ∀ x, P.kin x ≤ μ * P.nrm2sq x) (v : ι → ℝ) :
    P.nrm2 (P.negLap v) ≤ μ * P.nrm2 v := by
  apply P.nrm2_le_of_nrm2sq_le (mul_nonneg hμ0 (P.nrm2_nonneg v))
  rw [mul_pow, nrm2_sq]
  calc P.nrm2sq (P.negLap v) ≤ μ * P.kin v := P.nrm2sq_negLap_le hμ0 hμ v
    _ ≤ μ * (μ * P.nrm2sq v) := mul_le_mul_of_nonneg_left (hμ v) hμ0
    _ = μ ^ 2 * P.nrm2sq v := by ring

/-- `‖n'(p) v‖₂ ≤ (‖V‖_∞ + 3βK) ‖v‖₂` if `pᵢ² ≤ K`. -/
theorem nrm2_nonlin'_le [Nonempty ι] {K : ℝ} (hK0 : 0 ≤ K) {p : ι → ℝ} (hpK : ∀ i, p i ^ 2 ≤ K)
    (v : ι → ℝ) : P.nrm2 (P.nonlin' p v) ≤ (P.Vinf + 3 * P.β * K) * P.nrm2 v := by
  have hβ := P.β_pos
  have hV := P.Vinf_nonneg
  apply P.nrm2_le_of_nrm2sq_le (mul_nonneg (by positivity) (P.nrm2_nonneg v))
  rw [mul_pow, nrm2_sq, nrm2sq_eq_sum, nrm2sq_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : 0 ≤ P.V i + 3 * P.β * p i ^ 2 := by have := P.V_nonneg i; positivity
  have h2 : P.V i + 3 * P.β * p i ^ 2 ≤ P.Vinf + 3 * P.β * K := by
    have := P.le_Vinf i
    have := mul_le_mul_of_nonneg_left (hpK i) (by positivity : (0 : ℝ) ≤ 3 * P.β)
    linarith
  have h3 : (P.V i + 3 * P.β * p i ^ 2) ^ 2 ≤ (P.Vinf + 3 * P.β * K) ^ 2 :=
    pow_le_pow_left₀ h1 h2 2
  have h4 := mul_le_mul_of_nonneg_right h3 (mul_nonneg (P.w_pos i).le (sq_nonneg (v i)))
  simp only [nonlin']
  rw [mul_pow]
  linarith

/-- The operator bound `‖ℋ v‖₂ ≤ (μ + ‖V‖_∞ + 3βK + λ(p)) ‖v‖₂`. -/
theorem nrm2_hess_le [Nonempty ι] {μ K : ℝ} (hμ0 : 0 ≤ μ) (hμ : ∀ x, P.kin x ≤ μ * P.nrm2sq x)
    (hK0 : 0 ≤ K) {p : ι → ℝ} (hpK : ∀ i, p i ^ 2 ≤ K) (v : ι → ℝ) :
    P.nrm2 (P.hess p v) ≤ (μ + P.Vinf + 3 * P.β * K + P.lam p) * P.nrm2 v := by
  unfold hess
  have h1 := P.nrm2_sub_le (P.negLap v + P.nonlin' p v) (P.lam p • v)
  have h2 := P.nrm2_add_le (P.negLap v) (P.nonlin' p v)
  have h3 := P.nrm2_negLap_le hμ0 hμ v
  have h4 := P.nrm2_nonlin'_le hK0 hpK v
  have h5 : P.nrm2 (P.lam p • v) = P.lam p * P.nrm2 v := by
    rw [nrm2_smul, abs_of_nonneg (P.lam_nonneg p)]
  linarith

/-- `‖ρ‖₂ ≤ βK(3‖h‖₂² + ‖h‖₂³)` for a unit vector `p`. -/
theorem nrm2_rho_le {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ v : ι → ℝ, ∀ i, v i ^ 2 ≤ K * P.nrm2sq v)
    {p : ι → ℝ} (hp : P.nrm2sq p = 1) (h : ι → ℝ) :
    P.nrm2 (P.rho p h) ≤ P.β * K * (3 * P.nrm2 h ^ 2 + P.nrm2 h ^ 3) := by
  have hβ := P.β_pos
  have hR := P.nrm2_nonneg h
  have hN := P.nrm2_sq h
  -- the pointwise bound `|ρᵢ| ≤ βK(3‖h‖₂ + ‖h‖₂²) |hᵢ|`
  have hpt : ∀ i, |P.rho p h i| ≤ P.β * K * (3 * P.nrm2 h + P.nrm2 h ^ 2) * |h i| := by
    intro i
    have hph := P.abs_mul_le_of_unit hK0 hK hp h i
    have hh2 : h i ^ 2 ≤ K * P.nrm2 h ^ 2 := by rw [hN]; exact hK h i
    have hin : |3 * (p i * h i) + h i ^ 2| ≤ 3 * (K * P.nrm2 h) + K * P.nrm2 h ^ 2 := by
      calc |3 * (p i * h i) + h i ^ 2| ≤ |3 * (p i * h i)| + |h i ^ 2| := abs_add_le _ _
        _ = 3 * |p i * h i| + h i ^ 2 := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonneg (sq_nonneg (h i))]
        _ ≤ 3 * (K * P.nrm2 h) + K * P.nrm2 h ^ 2 := by linarith
    simp only [rho]
    rw [show P.β * (3 * p i * h i ^ 2 + h i ^ 3)
        = P.β * ((3 * (p i * h i) + h i ^ 2) * h i) by ring, abs_mul, abs_mul, abs_of_pos hβ]
    calc P.β * (|3 * (p i * h i) + h i ^ 2| * |h i|)
        ≤ P.β * ((3 * (K * P.nrm2 h) + K * P.nrm2 h ^ 2) * |h i|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hin (abs_nonneg _)) hβ.le
      _ = P.β * K * (3 * P.nrm2 h + P.nrm2 h ^ 2) * |h i| := by ring
  apply P.nrm2_le_of_nrm2sq_le (by positivity)
  have hsq : P.nrm2sq (P.rho p h)
      ≤ (P.β * K * (3 * P.nrm2 h + P.nrm2 h ^ 2)) ^ 2 * P.nrm2sq h := by
    rw [nrm2sq_eq_sum, nrm2sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : P.rho p h i ^ 2 ≤ (P.β * K * (3 * P.nrm2 h + P.nrm2 h ^ 2)) ^ 2 * h i ^ 2 := by
      calc P.rho p h i ^ 2 = |P.rho p h i| ^ 2 := (sq_abs _).symm
        _ ≤ (P.β * K * (3 * P.nrm2 h + P.nrm2 h ^ 2) * |h i|) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hpt i) 2
        _ = (P.β * K * (3 * P.nrm2 h + P.nrm2 h ^ 2)) ^ 2 * h i ^ 2 := by rw [mul_pow, sq_abs]
    have := mul_le_mul_of_nonneg_left h1 (P.w_pos i).le
    linarith
  rw [← hN] at hsq
  calc P.nrm2sq (P.rho p h) ≤ _ := hsq
    _ = (P.β * K * (3 * P.nrm2 h ^ 2 + P.nrm2 h ^ 3)) ^ 2 := by ring

/-- `⟪ρ, h⟫_h = β (3 ∑ᵢ wᵢ pᵢ hᵢ³ + ∑ᵢ wᵢ hᵢ⁴)`. -/
theorem inner_rho_eq (p h : ι → ℝ) :
    P.inner (P.rho p h) h
      = P.β * (3 * ∑ i, P.w i * (p i * h i ^ 3) + ∑ i, P.w i * h i ^ 4) := by
  simp only [inner_def, rho]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- Theorem 5.1, local Polyak–Łojasiewicz inequality deduced after (5.8): there is `r > 0` such that
`E_h(u) - E_h(p) ≤ (1/ν)‖g(u)‖₂²` for every `u ∈ 𝓜` with `‖u - p‖₂ ≤ r`. -/
theorem local_PL [Nonempty ι] (hcard : 2 ≤ Fintype.card ι) {p : ι → ℝ}
    (hp : P.nrm2sq p = 1) (hpos : ∀ i, 0 < p i) (hg : P.g p = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ u : ι → ℝ, P.nrm2sq u = 1 → P.nrm2 (u - p) ≤ r →
      P.energy u - P.energy p ≤ (1 / P.nu p) * P.nrm2sq (P.g u) := by
  have hν := P.nu_pos hcard hp hpos hg
  have hβ := P.β_pos
  have hN3 := P.nrm2_nonneg (fun i => p i ^ 3)
  obtain ⟨K, hK0, hK⟩ := P.exists_sq_bound
  obtain ⟨μ, hμ0, hμ⟩ := P.exists_kin_bound
  have hpK : ∀ i, p i ^ 2 ≤ K := fun i => by have := hK p i; rwa [hp, mul_one] at this
  -- the operator bound for `ℋ`
  obtain ⟨L, hL0, hL⟩ : ∃ L : ℝ, 0 ≤ L ∧ ∀ v, P.nrm2 (P.hess p v) ≤ L * P.nrm2 v :=
    ⟨μ + P.Vinf + 3 * P.β * K + P.lam p,
      by have := P.Vinf_nonneg; have := P.lam_nonneg p; positivity,
      fun v => P.nrm2_hess_le hμ0 hμ hK0.le hpK v⟩
  -- the constant `C` collecting the higher-order terms
  obtain ⟨C, hC⟩ : ∃ C : ℝ,
      C = P.nu p / 8 + P.β * P.nrm2 (fun i => p i ^ 3) + 4 * P.β * K + L / 2 := ⟨_, rfl⟩
  have hC0 : 0 < C := by rw [hC]; positivity
  refine ⟨min 1 (P.nu p / (4 * C)), lt_min one_pos (by positivity), fun u hu hr => ?_⟩
  have hr1 : P.nrm2 (u - p) ≤ 1 := hr.trans (min_le_left _ _)
  have hr2 : P.nrm2 (u - p) * (4 * C) ≤ P.nu p :=
    (le_div_iff₀ (by positivity)).mp (hr.trans (min_le_right _ _))
  have hR := P.nrm2_nonneg (u - p)
  have hN : P.nrm2sq (u - p) = P.nrm2 (u - p) ^ 2 := (P.nrm2_sq _).symm
  -- the two exact expansions and the tangential bound
  have hE := P.energy_sub_eq hp hg hu
  have hI := P.inner_g_sub_eq hp hg hu
  have hH := P.hessForm_sub_ge hp hpos hg hu
  have hρ := P.inner_rho_eq p (u - p)
  have h3 := P.abs_sum_cube_le hK0.le hK hp (u - p)
  have hS4 : 0 ≤ ∑ i, P.w i * (u - p) i ^ 4 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (P.w_pos i).le (by positivity)
  simp only [Pi.sub_apply] at hρ h3 hS4
  -- the bound on `⟪ℋ h + ρ, u⟫_h`
  have hQ : |P.inner (P.hess p (u - p) + P.rho p (u - p)) u|
      ≤ L * P.nrm2 (u - p) + P.β * K * (3 * P.nrm2 (u - p) ^ 2 + P.nrm2 (u - p) ^ 3) := by
    have h1 := P.abs_inner_le_nrm2_mul_nrm2 (P.hess p (u - p) + P.rho p (u - p)) u
    rw [P.nrm2_eq_one_of_nrm2sq hu, mul_one] at h1
    have h2 := P.nrm2_add_le (P.hess p (u - p)) (P.rho p (u - p))
    have h4 := hL (u - p)
    have h5 := P.nrm2_rho_le hK0.le hK hp (u - p)
    linarith
  -- `⟪g(u), h⟫_h - (E_h(u) - E_h(p)) ≥ (ν/4) ‖h‖₂²`
  have key : P.nu p / 4 * P.nrm2 (u - p) ^ 2
      ≤ P.inner (P.g u) (u - p) - (P.energy u - P.energy p) := by
    rw [hI, hE, hρ, hN]
    rw [hN] at hH
    have h3' := mul_le_mul_of_nonneg_left (abs_le.mp h3).1 (by positivity : (0 : ℝ) ≤ 2 * P.β)
    have hS4' := mul_nonneg hβ.le hS4
    have hQ1 : P.nrm2 (u - p) ^ 2 * P.inner (P.hess p (u - p) + P.rho p (u - p)) u
        ≤ P.nrm2 (u - p) ^ 2 * |P.inner (P.hess p (u - p) + P.rho p (u - p)) u| := by
      have := le_abs_self
        (P.nrm2 (u - p) ^ 2 * P.inner (P.hess p (u - p) + P.rho p (u - p)) u)
      rwa [abs_mul, abs_of_nonneg (sq_nonneg _)] at this
    have hQ2 := mul_le_mul_of_nonneg_left hQ (sq_nonneg (P.nrm2 (u - p)))
    have hR4 : P.nrm2 (u - p) ^ 4 ≤ P.nrm2 (u - p) ^ 3 :=
      pow_le_pow_of_le_one hR hr1 (by norm_num)
    have hR5 : P.nrm2 (u - p) ^ 5 ≤ P.nrm2 (u - p) ^ 3 :=
      pow_le_pow_of_le_one hR hr1 (by norm_num)
    have hR4' := mul_le_mul_of_nonneg_left hR4
      (by positivity : (0 : ℝ) ≤ P.nu p / 8 + 3 * P.β * K / 2)
    have hR5' := mul_le_mul_of_nonneg_left hR5 (by positivity : (0 : ℝ) ≤ P.β * K / 2)
    have hCR := mul_le_mul_of_nonneg_right hr2 (sq_nonneg (P.nrm2 (u - p)))
    rw [hC] at hCR
    linarith
  -- conclusion: `E_h(u) - E_h(p) ≤ ‖g(u)‖₂ ‖h‖₂ - (ν/4)‖h‖₂² ≤ ‖g(u)‖₂²/ν`
  have hcs := P.inner_le_nrm2_mul_nrm2 (P.g u) (u - p)
  have hG := P.nrm2_sq (P.g u)
  rw [← hG, div_mul_eq_mul_div, one_mul, le_div_iff₀ hν]
  have h1 : P.energy u - P.energy p
      ≤ P.nrm2 (P.g u) * P.nrm2 (u - p) - P.nu p / 4 * P.nrm2 (u - p) ^ 2 := by linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hν.le
  nlinarith [sq_nonneg (P.nrm2 (P.g u) - P.nu p / 2 * P.nrm2 (u - p))]

/-! ### Theorem 5.1 -/

section RateTheorem

variable [Nonempty ι] (hcard : 2 ≤ Fintype.card ι) {u0 : ι → ℝ} (hu0 : ∀ i, 0 < u0 i)
  (hn : P.nrm2 u0 = 1) {γ : ℝ} (hγ : 0 < γ) (hγm : γ ≤ P.γmax u0)
  {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ∀ v, P.kin v ≤ μ * P.nrm2sq v)
  {p : ι → ℝ} (hp : P.nrm2sq p = 1) (hpos : ∀ i, 0 < p i) (hg : P.g p = 0)
  (hconv : Tendsto (P.uiter γ u0) atTop (𝓝 p))
include hcard hu0 hn hγ hγm hμ0 hμ hp hpos hg hconv

set_option linter.unusedSectionVars false in
/-- The iterates are eventually within any distance `r > 0` of `p`. -/
theorem eventually_close {r : ℝ} (hr : 0 < r) :
    ∃ K : ℕ, ∀ k, K ≤ k → P.nrm2 (P.uiter γ u0 k - p) ≤ r := by
  have h1 : Tendsto (fun k => P.uiter γ u0 k - p) atTop (𝓝 0) := by
    have := hconv.sub_const p
    rwa [sub_self] at this
  have h2 : Tendsto (fun k => P.nrm2 (P.uiter γ u0 k - p)) atTop (𝓝 0) := by
    have h3 := (P.nrm2_continuous.tendsto 0).comp h1
    rw [show P.nrm2 0 = 0 from (P.nrm2_eq_zero_iff 0).mpr rfl] at h3
    exact h3
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h2).2 r hr)
  exact ⟨K, fun k hk => (hK k hk).le⟩

set_option linter.unusedSectionVars false in
/-- `0 < η`; the upper bound is `η_lt_one`. -/
theorem η_pos : 0 < η γ μ (P.nu p) := by
  have hν := P.nu_pos hcard hp hpos hg
  unfold η
  exact lt_min (by positivity) (by norm_num)

set_option linter.unusedSectionVars false in
theorem η_lt_one : η γ μ (P.nu p) < 1 := by
  unfold η
  exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)

/-- Theorem 5.1, first inequality of (5.6): there is `K` such that for `k ≥ K`,
`𝓛^{k+1} - E_GS ≤ (1 - η)(𝓛^k - E_GS)`. -/
theorem rate_step :
    ∃ K : ℕ, ∀ k, K ≤ k →
      P.lyap γ (P.iter γ u0 (k + 1)) - P.energy p
        ≤ (1 - η γ μ (P.nu p)) * (P.lyap γ (P.iter γ u0 k) - P.energy p) := by
  have hν := P.nu_pos hcard hp hpos hg
  have hη1 : η γ μ (P.nu p) ≤ γ * P.nu p / (4 * (1 + γ * μ)) := min_le_left _ _
  have hη2 : η γ μ (P.nu p) ≤ 1 / 2 := min_le_right _ _
  have hm : 0 < 1 + γ * μ := by positivity
  have hη1' : η γ μ (P.nu p) * (4 * (1 + γ * μ)) ≤ γ * P.nu p :=
    (le_div_iff₀ (by positivity)).mp hη1
  obtain ⟨r, hr, hPL⟩ := P.local_PL hcard hp hpos hg
  obtain ⟨K, hK⟩ := P.eventually_close hcard hu0 hn hγ hγm hμ0 hμ hp hpos hg hconv hr
  refine ⟨K, fun k hk => ?_⟩
  have hz := P.iter_ne_zero hu0 hn hγ hγm k
  have hu : P.nrm2sq (P.uiter γ u0 k) = 1 := P.nrm2sq_normalize hz
  have h1 := hPL _ hu (hK k hk)
  have h2 := P.nrm2sq_le_mul_nrmXsq hγ.le hμ0 hμ (P.g (P.uiter γ u0 k))
  have h3 := P.drop hu0 hn hγ hγm k
  have hD0 : 0 ≤ P.energy (P.uiter γ u0 k) - P.energy p := by
    have := P.energy_le_of_critical hp hpos hg hu; linarith
  have hlyap : P.lyap γ (P.iter γ u0 k)
      = P.energy (P.uiter γ u0 k) + (P.R γ (P.iter γ u0 k)) ^ 2 / γ := by
    rw [lyap_def, uiter_def]
  -- `ν (E_h(u) - E_h(p)) ≤ (1 + γμ) ‖g(u)‖_X²`
  have h4 : P.nu p * (P.energy (P.uiter γ u0 k) - P.energy p)
      ≤ (1 + γ * μ) * P.nrmXsq γ (P.g (P.uiter γ u0 k)) := by
    have h5 := mul_le_mul_of_nonneg_left h1 hν.le
    have e : P.nu p * (1 / P.nu p * P.nrm2sq (P.g (P.uiter γ u0 k)))
        = P.nrm2sq (P.g (P.uiter γ u0 k)) := by
      field_simp
    linarith
  -- `4 η (E_h(u) - E_h(p)) ≤ γ ‖g(u)‖_X²`
  have h6 : 4 * η γ μ (P.nu p) * (P.energy (P.uiter γ u0 k) - P.energy p)
      ≤ γ * P.nrmXsq γ (P.g (P.uiter γ u0 k)) := by
    have h7 := mul_le_mul_of_nonneg_right hη1' hD0
    have h8 := mul_le_mul_of_nonneg_left h4 hγ.le
    have h9 : (4 * η γ μ (P.nu p) * (P.energy (P.uiter γ u0 k) - P.energy p)) * (1 + γ * μ)
        ≤ (γ * P.nrmXsq γ (P.g (P.uiter γ u0 k))) * (1 + γ * μ) := by linarith
    exact le_of_mul_le_mul_right h9 hm
  -- `η R²/γ ≤ R²/(2γ)`
  have h10 : η γ μ (P.nu p) * ((P.R γ (P.iter γ u0 k)) ^ 2 / γ)
      ≤ (P.R γ (P.iter γ u0 k)) ^ 2 / (2 * γ) := by
    have := mul_le_mul_of_nonneg_right hη2
      (by positivity : (0 : ℝ) ≤ (P.R γ (P.iter γ u0 k)) ^ 2 / γ)
    have e : (P.R γ (P.iter γ u0 k)) ^ 2 / (2 * γ)
        = 1 / 2 * ((P.R γ (P.iter γ u0 k)) ^ 2 / γ) := by
      field_simp
    linarith
  rw [hlyap] at h3 ⊢
  linarith

/-- **Theorem 5.1**, conditional form: assume the section hypotheses, including
convergence of the iterates to the positive normalized critical point `p`, and a Rayleigh
bound `μ ≥ 0`. Then there is an index `K` such that for every `k ≥ K`,
`𝓛^{k+1} - E_GS ≤ (1-η)(𝓛^k - E_GS)` and
`E_h(u^k) - E_GS + (R^k)²/γ + (ν/4)‖u^k - u_GS‖₂² ≤ 2(1-η)^{k-K}(𝓛^K - E_GS)`. -/
theorem rate_theorem :
    ∃ K : ℕ, ∀ k, K ≤ k →
      (P.lyap γ (P.iter γ u0 (k + 1)) - P.energy p
        ≤ (1 - η γ μ (P.nu p)) * (P.lyap γ (P.iter γ u0 k) - P.energy p)) ∧
      (P.energy (P.uiter γ u0 k) - P.energy p + (P.R γ (P.iter γ u0 k)) ^ 2 / γ
          + P.nu p / 4 * P.nrm2sq (P.uiter γ u0 k - p)
        ≤ 2 * (1 - η γ μ (P.nu p)) ^ (k - K) * (P.lyap γ (P.iter γ u0 K) - P.energy p)) := by
  have hη1 := P.η_lt_one hcard hu0 hn hγ hγm hμ0 hμ hp hpos hg hconv
  obtain ⟨K₁, hK₁⟩ := P.rate_step hcard hu0 hn hγ hγm hμ0 hμ hp hpos hg hconv
  obtain ⟨r₂, hr₂, hQG⟩ := P.local_quadratic_growth hcard hp hpos hg
  obtain ⟨K₂, hK₂⟩ := P.eventually_close hcard hu0 hn hγ hγm hμ0 hμ hp hpos hg hconv hr₂
  refine ⟨max K₁ K₂, fun k hk => ?_⟩
  have hk1 : K₁ ≤ k := le_of_max_le_left hk
  have hk2 : K₂ ≤ k := le_of_max_le_right hk
  refine ⟨hK₁ k hk1, ?_⟩
  -- geometric decay from `K = max K₁ K₂` on
  have hind : ∀ n : ℕ, P.lyap γ (P.iter γ u0 (max K₁ K₂ + n)) - P.energy p
      ≤ (1 - η γ μ (P.nu p)) ^ n * (P.lyap γ (P.iter γ u0 (max K₁ K₂)) - P.energy p) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hK₁ (max K₁ K₂ + n) (by omega)
      rw [← add_assoc]
      calc P.lyap γ (P.iter γ u0 (max K₁ K₂ + n + 1)) - P.energy p
          ≤ (1 - η γ μ (P.nu p)) * (P.lyap γ (P.iter γ u0 (max K₁ K₂ + n)) - P.energy p) := h
        _ ≤ (1 - η γ μ (P.nu p)) * ((1 - η γ μ (P.nu p)) ^ n
              * (P.lyap γ (P.iter γ u0 (max K₁ K₂)) - P.energy p)) :=
            mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (1 - η γ μ (P.nu p)) ^ (n + 1)
              * (P.lyap γ (P.iter γ u0 (max K₁ K₂)) - P.energy p) := by ring
  have hmain := hind (k - max K₁ K₂)
  rw [Nat.add_sub_of_le hk] at hmain
  have hz := P.iter_ne_zero hu0 hn hγ hγm k
  have hu : P.nrm2sq (P.uiter γ u0 k) = 1 := P.nrm2sq_normalize hz
  have hq := hQG _ hu (hK₂ k hk2)
  have hlyap : P.lyap γ (P.iter γ u0 k)
      = P.energy (P.uiter γ u0 k) + (P.R γ (P.iter γ u0 k)) ^ 2 / γ := by
    rw [lyap_def, uiter_def]
  have hR0 : 0 ≤ (P.R γ (P.iter γ u0 k)) ^ 2 / γ := by positivity
  rw [hlyap] at hmain
  linarith

end RateTheorem

/-- **Theorem 5.1**, self-contained form: under the hypotheses of Theorem 3.4, `N ≥ 2`, and
any Rayleigh bound `μ` for `-Δ_h`, the iterates converge to the discrete ground state `u_GS`,
the constant `ν` satisfies `ν ≥ 2β m_GS² > 0`, `0 < η < 1`, and the geometric decay (5.6) holds
from some index `K` on. -/
theorem rate_theorem' [Nonempty ι] (hcard : 2 ≤ Fintype.card ι) {u0 : ι → ℝ}
    (hu0 : ∀ i, 0 < u0 i) (hn : P.nrm2 u0 = 1) {γ : ℝ} (hγ : 0 < γ) (hγm : γ ≤ P.γmax u0)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ∀ v, P.kin v ≤ μ * P.nrm2sq v) :
    ∃ uGS : ι → ℝ, (∀ i, 0 < uGS i) ∧ P.nrm2 uGS = 1 ∧ P.g uGS = 0 ∧
      Tendsto (P.uiter γ u0) atTop (𝓝 uGS) ∧
      2 * P.β * (mGS uGS) ^ 2 ≤ P.nu uGS ∧ 0 < P.nu uGS ∧
      0 < η γ μ (P.nu uGS) ∧ η γ μ (P.nu uGS) < 1 ∧
      ∃ K : ℕ, ∀ k, K ≤ k →
        (P.lyap γ (P.iter γ u0 (k + 1)) - P.energy uGS
          ≤ (1 - η γ μ (P.nu uGS)) * (P.lyap γ (P.iter γ u0 k) - P.energy uGS)) ∧
        (P.energy (P.uiter γ u0 k) - P.energy uGS + (P.R γ (P.iter γ u0 k)) ^ 2 / γ
            + P.nu uGS / 4 * P.nrm2sq (P.uiter γ u0 k - uGS)
          ≤ 2 * (1 - η γ μ (P.nu uGS)) ^ (k - K)
              * (P.lyap γ (P.iter γ u0 K) - P.energy uGS)) := by
  obtain ⟨_, uGS, hpos, hn1, hg, _, _, _, hconv, _⟩ := P.main_theorem hu0 hn hγ hγm
  have hp : P.nrm2sq uGS = 1 := P.nrm2sq_eq_one_of_nrm2 hn1
  refine ⟨uGS, hpos, hn1, hg, hconv, P.nu_ge hcard hp hpos hg, P.nu_pos hcard hp hpos hg,
    P.η_pos hcard hu0 hn hγ hγm hμ0 hμ hp hpos hg hconv,
    P.η_lt_one hcard hu0 hn hγ hγm hμ0 hμ hp hpos hg hconv,
    P.rate_theorem hcard hu0 hn hγ hγm hμ0 hμ hp hpos hg hconv⟩

end Setting

end GPDYS

end
