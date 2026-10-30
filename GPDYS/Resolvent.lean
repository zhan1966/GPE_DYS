import GPDYS.Lemmas

/-!
# The resolvent `G_X⁻¹ = (M + γ S)⁻¹ M` and the `X`-norm

This file proves the facts about the metric matrix `G_X = I - γΔ_h`, its resolvent and the
norms `‖·‖_X`, `‖·‖_𝒢` that the paper derives from the spectral decomposition in §3.2:

* `M + γ S` is invertible for `γ ≥ 0`, `G_X G_X⁻¹ = G_X⁻¹ G_X = I`;
* `G_X⁻¹` is `h`-self-adjoint, so `⟪·,·⟫_X` is a symmetric positive semidefinite form;
* the bounds (3.5): `0 < ‖v‖_X ≤ ‖v‖₂` for `v ≠ 0` and `‖G_X⁻¹ v‖₂ ≤ ‖v‖_X`;
* the bounds (3.6): `0 ≤ ‖v‖₂² - ‖v‖_X² ≤ γ ⟪v, -Δ_h v⟫_h`;
* (3.7): `‖G_X v‖_X = ‖v‖_𝒢`;
* the contraction used in Lemma 4.4: `‖(a I + (1-a) G_X⁻¹) u‖₂ ≤ ‖u‖₂` for `-1 ≤ a ≤ 0`;
* the norm equivalence (5.3): `‖v‖₂² ≤ (1 + γ μ) ‖v‖_X²` if `⟪·,-Δ_h ·⟫_h ≤ μ ‖·‖₂²`;
* entrywise positivity of the resolvent (Lemma 2.2 (ii)).

All proofs avoid the eigendecomposition: with `y := G_X⁻¹ v` one has `v = y + γ(-Δ_h y)` and
every quantity becomes an explicit quadratic expression in `y`.
-/

open Finset Matrix

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-! ### Invertibility of `M + γ S` -/

theorem dot_M_mulVec (x y : ι → ℝ) : x ⬝ᵥ (P.M *ᵥ y) = P.inner x y := by
  rw [M_mulVec, inner_def, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_; ring

theorem dot_MS_mulVec (γ : ℝ) (x : ι → ℝ) :
    x ⬝ᵥ ((P.M + γ • P.S) *ᵥ x) = P.nrm2sq x + γ * P.kin x := by
  rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, dot_M_mulVec, nrm2sq_def,
    kin_def, smul_eq_mul]

theorem MS_mulVec_eq_zero {γ : ℝ} (hγ : 0 ≤ γ) {x : ι → ℝ} (h : (P.M + γ • P.S) *ᵥ x = 0) :
    x = 0 := by
  have h1 := P.dot_MS_mulVec γ x
  rw [h, dotProduct_zero] at h1
  have h2 := P.nrm2sq_nonneg x
  have h3 : 0 ≤ γ * P.kin x := mul_nonneg hγ (P.kin_nonneg x)
  exact (P.nrm2sq_eq_zero_iff x).mp (by linarith)

theorem MS_mulVec_injective {γ : ℝ} (hγ : 0 ≤ γ) :
    Function.Injective (fun x : ι → ℝ => (P.M + γ • P.S) *ᵥ x) := by
  intro x y hxy
  have : (P.M + γ • P.S) *ᵥ (x - y) = 0 := by
    rw [mulVec_sub]; rw [show (P.M + γ • P.S) *ᵥ x = (P.M + γ • P.S) *ᵥ y from hxy, sub_self]
  exact sub_eq_zero.mp (P.MS_mulVec_eq_zero hγ this)

theorem MS_det_ne_zero {γ : ℝ} (hγ : 0 ≤ γ) : (P.M + γ • P.S).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  exact hv (P.MS_mulVec_eq_zero hγ hMv)

theorem MS_isUnit_det {γ : ℝ} (hγ : 0 ≤ γ) : IsUnit (P.M + γ • P.S).det :=
  isUnit_iff_ne_zero.mpr (P.MS_det_ne_zero hγ)

theorem M_mulVec_injective : Function.Injective (fun x : ι → ℝ => P.M *ᵥ x) := by
  intro x y hxy
  have hxy' : (fun i => P.w i * x i) = fun i => P.w i * y i := by
    rw [← M_mulVec, ← M_mulVec]; exact hxy
  funext i
  exact mul_left_cancel₀ (P.w_pos i).ne' (congrFun hxy' i)

/-! ### `G_X G_X⁻¹ = G_X⁻¹ G_X = I` -/

theorem resolvent_def (γ : ℝ) (v : ι → ℝ) :
    P.resolvent γ v = (P.M + γ • P.S)⁻¹ *ᵥ (P.M *ᵥ v) := rfl

theorem MS_mulVec_resolvent {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) :
    (P.M + γ • P.S) *ᵥ (P.resolvent γ v) = P.M *ᵥ v := by
  rw [resolvent_def, mulVec_mulVec, Matrix.mul_nonsing_inv _ (P.MS_isUnit_det hγ), one_mulVec]

theorem M_mulVec_GX (γ : ℝ) (v : ι → ℝ) : P.M *ᵥ (P.GX γ v) = (P.M + γ • P.S) *ᵥ v := by
  rw [GX_def, mulVec_add, mulVec_smul, M_mulVec_negLap, add_mulVec, smul_mulVec]

theorem GX_resolvent {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : P.GX γ (P.resolvent γ v) = v := by
  apply P.M_mulVec_injective
  simp only
  rw [M_mulVec_GX, MS_mulVec_resolvent P hγ]

theorem resolvent_GX {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : P.resolvent γ (P.GX γ v) = v := by
  apply P.MS_mulVec_injective hγ
  simp only
  rw [MS_mulVec_resolvent P hγ, M_mulVec_GX]

theorem GX_injective {γ : ℝ} (hγ : 0 ≤ γ) : Function.Injective (P.GX γ) := by
  intro x y hxy
  have := congrArg (P.resolvent γ) hxy
  rwa [resolvent_GX P hγ, resolvent_GX P hγ] at this

theorem GX_eq_iff {γ : ℝ} (hγ : 0 ≤ γ) (v x : ι → ℝ) : P.GX γ x = v ↔ x = P.resolvent γ v := by
  constructor
  · intro h; rw [← h, resolvent_GX P hγ]
  · intro h; rw [h, GX_resolvent P hγ]

theorem resolvent_zero_eq (v : ι → ℝ) : P.resolvent 0 v = v := by
  have h := P.resolvent_GX (le_refl 0) v
  rw [GX_def, zero_smul, add_zero] at h
  exact h

theorem resolvent_add (γ : ℝ) (u v : ι → ℝ) :
    P.resolvent γ (u + v) = P.resolvent γ u + P.resolvent γ v := by
  simp only [resolvent_def, mulVec_add]

theorem resolvent_sub (γ : ℝ) (u v : ι → ℝ) :
    P.resolvent γ (u - v) = P.resolvent γ u - P.resolvent γ v := by
  simp only [resolvent_def, mulVec_sub]

theorem resolvent_smul (γ c : ℝ) (v : ι → ℝ) : P.resolvent γ (c • v) = c • P.resolvent γ v := by
  simp only [resolvent_def, mulVec_smul]

theorem resolvent_neg (γ : ℝ) (v : ι → ℝ) : P.resolvent γ (-v) = - P.resolvent γ v := by
  simp only [resolvent_def, mulVec_neg]

@[simp] theorem resolvent_zero (γ : ℝ) : P.resolvent γ 0 = 0 := by
  simp only [resolvent_def, mulVec_zero]

/-! ### Expansions in terms of `y = G_X⁻¹ v` -/

/-- `‖y + γ(-Δ_h y)‖₂² = ‖y‖₂² + 2γ ⟪y,-Δ_h y⟫_h + γ² ‖-Δ_h y‖₂²`. -/
theorem nrm2sq_GX (γ : ℝ) (y : ι → ℝ) :
    P.nrm2sq (P.GX γ y) = P.nrm2sq y + 2 * γ * P.kin y + γ ^ 2 * P.nrm2sq (P.negLap y) := by
  rw [GX_def, nrm2sq_add, nrm2sq_smul, inner_smul_right, ← kin_eq_inner]; ring

/-- `⟪y, -Δ_h(-Δ_h y)⟫_h = ‖-Δ_h y‖₂²`. -/
theorem dotS_negLap_self (y : ι → ℝ) : y ⬝ᵥ (P.S *ᵥ (P.negLap y)) = P.nrm2sq (P.negLap y) := by
  rw [← inner_negLap, inner_negLap_comm, nrm2sq_def]

/-- `⟪G_X y, -Δ_h G_X y⟫_h = ⟪y,-Δ_h y⟫_h + 2γ‖-Δ_h y‖₂² + γ² ⟪-Δ_h y, -Δ_h(-Δ_h y)⟫_h`. -/
theorem kin_GX (γ : ℝ) (y : ι → ℝ) :
    P.kin (P.GX γ y) = P.kin y + 2 * γ * P.nrm2sq (P.negLap y) + γ ^ 2 * P.kin (P.negLap y) := by
  rw [GX_def, kin_add, kin_smul, dotS_smul_right, dotS_negLap_self]; ring

theorem inner_GX_left_self (γ : ℝ) (y : ι → ℝ) :
    P.inner (P.GX γ y) y = P.nrm2sq y + γ * P.kin y := by
  rw [GX_inner, nrm2sq_def, kin_def]

/-! ### The `X`-inner product -/

theorem innerX_def (γ : ℝ) (u v : ι → ℝ) : P.innerX γ u v = P.inner u (P.resolvent γ v) := rfl

theorem nrmXsq_def (γ : ℝ) (v : ι → ℝ) : P.nrmXsq γ v = P.inner v (P.resolvent γ v) := rfl

/-- `‖v‖_X² = ‖y‖₂² + γ ⟪y,-Δ_h y⟫_h` with `y = G_X⁻¹ v`. -/
theorem nrmXsq_eq {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) :
    P.nrmXsq γ v = P.nrm2sq (P.resolvent γ v) + γ * P.kin (P.resolvent γ v) := by
  have h := P.inner_GX_left_self γ (P.resolvent γ v)
  rw [P.GX_resolvent hγ v] at h
  rw [nrmXsq_def]; exact h

/-- Every vector is `G_X y` for `y = G_X⁻¹ v`. -/
theorem exists_eq_GX {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : ∃ y, P.GX γ y = v :=
  ⟨_, P.GX_resolvent hγ v⟩

/-- `‖G_X v‖_X² = ‖v‖_𝒢²`, (3.7). -/
theorem nrmXsq_GX {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : P.nrmXsq γ (P.GX γ v) = P.nrmGsq γ v := by
  rw [nrmXsq_def, resolvent_GX P hγ, GX_inner, nrmGsq_def, nrm2sq_def, kin_def]

/-- `⟪u, G_X v⟫_X = ⟪u, v⟫_h`. -/
theorem innerX_GX_right {γ : ℝ} (hγ : 0 ≤ γ) (u v : ι → ℝ) :
    P.innerX γ u (P.GX γ v) = P.inner u v := by
  rw [innerX_def, resolvent_GX P hγ]


/-- `h`-self-adjointness of the resolvent: `⟪u, G_X⁻¹ v⟫_h = ⟪G_X⁻¹ u, v⟫_h`. -/
theorem innerX_comm {γ : ℝ} (hγ : 0 ≤ γ) (u v : ι → ℝ) : P.innerX γ u v = P.innerX γ v u := by
  rw [innerX_def, innerX_def]
  conv_lhs => rw [← P.GX_resolvent hγ u]
  conv_rhs => rw [← P.GX_resolvent hγ v]
  rw [GX_inner, GX_inner, inner_comm, dotS_comm]

theorem innerX_add_left (γ : ℝ) (u v x : ι → ℝ) :
    P.innerX γ (u + v) x = P.innerX γ u x + P.innerX γ v x := by
  simp only [innerX_def, inner_add_left]

theorem innerX_add_right (γ : ℝ) (u v x : ι → ℝ) :
    P.innerX γ x (u + v) = P.innerX γ x u + P.innerX γ x v := by
  simp only [innerX_def, resolvent_add, inner_add_right]

theorem innerX_smul_left (γ c : ℝ) (u x : ι → ℝ) : P.innerX γ (c • u) x = c * P.innerX γ u x := by
  simp only [innerX_def, inner_smul_left]

theorem innerX_smul_right (γ c : ℝ) (u x : ι → ℝ) :
    P.innerX γ x (c • u) = c * P.innerX γ x u := by
  simp only [innerX_def, resolvent_smul, inner_smul_right]

theorem innerX_sub_left (γ : ℝ) (u v x : ι → ℝ) :
    P.innerX γ (u - v) x = P.innerX γ u x - P.innerX γ v x := by
  simp only [innerX_def, inner_sub_left]

theorem innerX_neg_left (γ : ℝ) (u x : ι → ℝ) : P.innerX γ (-u) x = - P.innerX γ u x := by
  simp only [innerX_def, inner_neg_left]

theorem nrmXsq_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : 0 ≤ P.nrmXsq γ v := by
  rw [nrmXsq_eq P hγ]
  have := P.nrm2sq_nonneg (P.resolvent γ v); have := P.kin_nonneg (P.resolvent γ v)
  positivity

theorem nrmXsq_smul (γ c : ℝ) (v : ι → ℝ) : P.nrmXsq γ (c • v) = c ^ 2 * P.nrmXsq γ v := by
  rw [nrmXsq_def, nrmXsq_def, resolvent_smul, inner_smul_left, inner_smul_right]; ring

theorem nrmXsq_neg (γ : ℝ) (v : ι → ℝ) : P.nrmXsq γ (-v) = P.nrmXsq γ v := by
  rw [nrmXsq_def, nrmXsq_def, resolvent_neg, inner_neg_left, inner_neg_right, neg_neg]

/-- Cauchy–Schwarz in `X`: `⟪u, v⟫_X² ≤ ‖u‖_X² ‖v‖_X²`. -/
theorem innerX_sq_le {γ : ℝ} (hγ : 0 ≤ γ) (u v : ι → ℝ) :
    (P.innerX γ u v) ^ 2 ≤ P.nrmXsq γ u * P.nrmXsq γ v :=
  sq_le_of_psd (P.innerX γ) (P.innerX_add_left γ) (P.innerX_smul_left γ) (P.innerX_comm hγ)
    (P.nrmXsq_nonneg hγ) u v

/-- Triangle inequality for `‖·‖_X`. -/
theorem sqrt_nrmXsq_add_le {γ : ℝ} (hγ : 0 ≤ γ) (u v : ι → ℝ) :
    Real.sqrt (P.nrmXsq γ (u + v)) ≤ Real.sqrt (P.nrmXsq γ u) + Real.sqrt (P.nrmXsq γ v) := by
  have hexp : P.nrmXsq γ (u + v) = P.nrmXsq γ u + 2 * P.innerX γ u v + P.nrmXsq γ v := by
    simp only [nrmXsq_def, innerX_def, resolvent_add, inner_add_left, inner_add_right]
    have := P.innerX_comm hγ v u
    simp only [innerX_def] at this
    rw [this]; ring
  have hcs : P.innerX γ u v ≤ Real.sqrt (P.nrmXsq γ u) * Real.sqrt (P.nrmXsq γ v) := by
    rw [← Real.sqrt_mul (P.nrmXsq_nonneg hγ u)]
    apply Real.le_sqrt_of_sq_le
    exact P.innerX_sq_le hγ u v
  rw [Real.sqrt_le_left (by positivity)]
  rw [hexp]
  have hu := Real.sq_sqrt (P.nrmXsq_nonneg hγ u)
  have hv := Real.sq_sqrt (P.nrmXsq_nonneg hγ v)
  nlinarith [hu, hv, hcs]

/-! ### The bounds (3.5), (3.6), (3.7) -/

/-- `‖v‖_X² ≤ ‖v‖₂²`, (3.5). -/
theorem nrmXsq_le_nrm2sq {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : P.nrmXsq γ v ≤ P.nrm2sq v := by
  obtain ⟨y, rfl⟩ := P.exists_eq_GX hγ v
  rw [nrmXsq_GX P hγ, nrmGsq_def, nrm2sq_GX]
  have := P.nrm2sq_nonneg (P.negLap y)
  have := P.kin_nonneg y
  nlinarith

/-- `‖v‖_X > 0` for `v ≠ 0`, (3.5). -/
theorem nrmXsq_pos {γ : ℝ} (hγ : 0 ≤ γ) {v : ι → ℝ} (hv : v ≠ 0) : 0 < P.nrmXsq γ v := by
  obtain ⟨y, rfl⟩ := P.exists_eq_GX hγ v
  have hy : y ≠ 0 := by rintro rfl; exact hv (P.GX_zero γ)
  rw [nrmXsq_GX P hγ, nrmGsq_def]
  have := P.nrm2sq_pos_of_ne_zero hy
  have := P.kin_nonneg y
  nlinarith

/-- `‖G_X⁻¹ v‖₂² ≤ ‖v‖_X²`, (3.5). -/
theorem nrm2sq_resolvent_le_nrmXsq {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) :
    P.nrm2sq (P.resolvent γ v) ≤ P.nrmXsq γ v := by
  rw [nrmXsq_eq P hγ]
  have := P.kin_nonneg (P.resolvent γ v); nlinarith

/-- Upper bound in (3.6): `‖v‖₂² - ‖v‖_X² ≤ γ ⟪v, -Δ_h v⟫_h`.
The lower bound is `nrmXsq_le_nrm2sq`. -/
theorem nrm2sq_sub_nrmXsq_le {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) :
    P.nrm2sq v - P.nrmXsq γ v ≤ γ * P.kin v := by
  obtain ⟨y, rfl⟩ := P.exists_eq_GX hγ v
  rw [nrmXsq_GX P hγ, nrmGsq_def, nrm2sq_GX, kin_GX]
  have := P.nrm2sq_nonneg (P.negLap y)
  have := P.kin_nonneg (P.negLap y)
  have h3 : 0 ≤ γ ^ 2 * P.nrm2sq (P.negLap y) := by positivity
  have h4 : 0 ≤ γ ^ 3 * P.kin (P.negLap y) := by positivity
  nlinarith

/-- `‖v‖_X² ≤ ‖v‖_𝒢²`. -/
theorem nrmXsq_le_nrmGsq {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : P.nrmXsq γ v ≤ P.nrmGsq γ v :=
  (P.nrmXsq_le_nrm2sq hγ v).trans (P.nrm2sq_le_nrmGsq hγ v)

/-! ### The contraction used in Lemma 4.4 -/

/-- For `-1 ≤ a ≤ 0`, the operator `a I + (1 - a) G_X⁻¹` is a contraction in `‖·‖₂`. -/
theorem nrm2sq_contraction {γ a : ℝ} (hγ : 0 ≤ γ) (ha : -1 ≤ a) (ha' : a ≤ 0) (u : ι → ℝ) :
    P.nrm2sq (a • u + (1 - a) • P.resolvent γ u) ≤ P.nrm2sq u := by
  obtain ⟨y, rfl⟩ := P.exists_eq_GX hγ u
  rw [resolvent_GX P hγ]
  have hcomb : a • P.GX γ y + (1 - a) • y = y + (a * γ) • P.negLap y := by
    rw [GX_def]; simp only [smul_add, smul_smul]; module
  rw [hcomb, nrm2sq_add, nrm2sq_smul, inner_smul_right, ← kin_eq_inner, nrm2sq_GX]
  have h1 := P.kin_nonneg y
  have h2 := P.nrm2sq_nonneg (P.negLap y)
  have h3 : 0 ≤ 2 * γ * (1 - a) * P.kin y := by
    have : 0 ≤ 1 - a := by linarith
    positivity
  have h4 : 0 ≤ γ ^ 2 * (1 - a ^ 2) * P.nrm2sq (P.negLap y) := by
    have : 0 ≤ 1 - a ^ 2 := by nlinarith
    positivity
  nlinarith

/-! ### Norm equivalence (5.3) -/

/-- `‖-Δ_h y‖₂² ≤ μ ⟪y,-Δ_h y⟫_h` if `⟪·,-Δ_h ·⟫_h ≤ μ ‖·‖₂²`. -/
theorem nrm2sq_negLap_le {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ : ∀ x, P.kin x ≤ μ * P.nrm2sq x)
    (y : ι → ℝ) : P.nrm2sq (P.negLap y) ≤ μ * P.kin y := by
  have hcs := P.dotS_sq_le y (P.negLap y)
  rw [dotS_negLap_self] at hcs
  have h1 := hμ (P.negLap y)
  have h2 := P.nrm2sq_nonneg (P.negLap y)
  have h3 := P.kin_nonneg y
  by_cases h0 : P.nrm2sq (P.negLap y) = 0
  · rw [h0]; positivity
  · have hpos : 0 < P.nrm2sq (P.negLap y) := lt_of_le_of_ne h2 (Ne.symm h0)
    have : P.nrm2sq (P.negLap y) ^ 2 ≤ (μ * P.kin y) * P.nrm2sq (P.negLap y) := by
      calc P.nrm2sq (P.negLap y) ^ 2 ≤ P.kin y * P.kin (P.negLap y) := hcs
        _ ≤ P.kin y * (μ * P.nrm2sq (P.negLap y)) :=
            mul_le_mul_of_nonneg_left h1 h3
        _ = (μ * P.kin y) * P.nrm2sq (P.negLap y) := by ring
    rw [sq] at this
    exact le_of_mul_le_mul_right this hpos

/-- `‖v‖₂² ≤ (1 + γ μ) ‖v‖_X²` if `⟪·,-Δ_h ·⟫_h ≤ μ ‖·‖₂²`, (5.3). -/
theorem nrm2sq_le_mul_nrmXsq {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ0 : 0 ≤ μ)
    (hμ : ∀ x, P.kin x ≤ μ * P.nrm2sq x) (v : ι → ℝ) :
    P.nrm2sq v ≤ (1 + γ * μ) * P.nrmXsq γ v := by
  obtain ⟨y, rfl⟩ := P.exists_eq_GX hγ v
  rw [nrmXsq_GX P hγ, nrmGsq_def, nrm2sq_GX]
  have h1 := hμ y
  have h2 := P.nrm2sq_negLap_le hμ0 hμ y
  have h3 := P.kin_nonneg y
  have h4 : γ * P.kin y ≤ γ * (μ * P.nrm2sq y) := mul_le_mul_of_nonneg_left h1 hγ
  have h5 : γ ^ 2 * P.nrm2sq (P.negLap y) ≤ γ ^ 2 * (μ * P.kin y) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  nlinarith

/-! ### Entrywise positivity of the resolvent (Lemma 2.2 (ii)) -/

theorem resolvent_apply (γ : ℝ) (b : ι → ℝ) (i : ι) :
    P.resolvent γ b i = ∑ j, (P.M + γ • P.S)⁻¹ i j * (P.w j * b j) := by
  rw [resolvent_def, M_mulVec, mulVec, dotProduct]

/-- A positive matrix maps a nonnegative nonzero vector to a positive vector. -/
theorem resolvent_pos_of_nonneg {γ : ℝ} (hγ : 0 < γ) {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i)
    (hb0 : b ≠ 0) (i : ι) : 0 < P.resolvent γ b i := by
  rw [resolvent_apply]
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hb0
  have hj0' : 0 < b j0 := lt_of_le_of_ne (hb j0) (fun h => hj0 (by simpa using h.symm))
  have hterm : ∀ j, 0 ≤ (P.M + γ • P.S)⁻¹ i j * (P.w j * b j) := fun j =>
    mul_nonneg (P.resolvent_pos γ hγ i j).le (mul_nonneg (P.w_pos j).le (hb j))
  have hpos : 0 < (P.M + γ • P.S)⁻¹ i j0 * (P.w j0 * b j0) :=
    mul_pos (P.resolvent_pos γ hγ i j0) (mul_pos (P.w_pos j0) hj0')
  calc (0 : ℝ) < (P.M + γ • P.S)⁻¹ i j0 * (P.w j0 * b j0) := hpos
    _ ≤ ∑ j, (P.M + γ • P.S)⁻¹ i j * (P.w j * b j) :=
        Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ j0)

theorem resolvent_nonneg_of_nonneg {γ : ℝ} (hγ : 0 ≤ γ) {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (i : ι) :
    0 ≤ P.resolvent γ b i := by
  rcases lt_or_eq_of_le hγ with hγ' | hγ'
  · by_cases hb0 : b = 0
    · subst hb0; simp
    · exact (P.resolvent_pos_of_nonneg hγ' hb hb0 i).le
  · subst hγ'; rw [resolvent_zero_eq]; exact hb i

end Setting

end GPDYS

end
