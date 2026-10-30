import GPDYS.Nonlinear
import GPDYS.Positivity

/-!
# Conditional descent and the projected gradient (§4.4, Lemmas 4.5 and 4.6)

* Lemma 4.5 (conditional descent): under the hypotheses of Lemma 4.4, (C3), and
  `E_h(u⁺) ≤ E₀`, one has `γ(𝓛(z) - 𝓛(z⁺)) ≥ (5/16)‖δ‖_𝒢² + (3/4)R²`, (4.17), and the right
  side vanishes only if `R = 0` and `g(u) = 0`, in which case `z⁺ = z`.
* Lemma 4.6: `γ²‖g(u)‖_X² ≤ (5/4)‖δ‖_𝒢² + 10γD R²` and `‖z⁺ - z‖_𝒢² ≤ ‖δ‖_𝒢² + R²`, (4.24).
* A crude version of the energy estimate (4.22) valid without any energy bound on `u⁺`
  (`energy_step_le_of_small`): if `γ(28D + 2C₁) ≤ 1`, where `C₁ = ‖V‖_∞ + 3β/w_min`, then
  `E_h(u⁺) ≤ E_h(u) + 2D R²`. It replaces the derivative computation of Lemma 4.7 in the
  energy barrier argument: it shows that the energy of the new direction stays below `E₀`
  for small step sizes.
-/

open Finset Matrix

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- The crude constant `C₁ = ‖V‖_∞ + 3β/w_min`. -/
def C1 : ℝ := P.Vinf + 3 * P.β / P.wmin

/-- The crude pointwise bound on the Taylor remainder for arbitrary unit vectors:
`𝒯(u, u⁺ - u) ≤ ½ C₁ ‖u⁺ - u‖₂²`, using only `vᵢ² ≤ 1/w_min` for `‖v‖₂ = 1`. -/
theorem taylorT_le_crude [Nonempty ι] {u up : ι → ℝ} (hu : P.nrm2sq u = 1)
    (hup : P.nrm2sq up = 1) :
    P.taylorT u (up - u) ≤ (1 / 2) * P.C1 * P.nrm2sq (up - u) := by
  rw [taylorT_eq, nrm2sq_eq_sum]
  have hw : ∀ i, 0 ≤ P.w i := fun i => (P.w_pos i).le
  have hwmin := P.wmin_pos
  -- `vᵢ² ≤ 1/w_min` for a unit vector `v`
  have hsq : ∀ v : ι → ℝ, P.nrm2sq v = 1 → ∀ i, v i ^ 2 ≤ 1 / P.wmin := by
    intro v hv i
    have h := P.w_mul_sq_le_nrm2sq v i
    rw [hv] at h
    have hwi := P.wmin_le i
    rw [le_div_iff₀ hwmin]
    have := mul_le_mul_of_nonneg_left hwi (sq_nonneg (v i))
    linarith
  -- the potential term: `Vᵢ ≤ ‖V‖_∞`
  have hV : ∑ i, P.w i * (P.V i * (up - u) i ^ 2) ≤ P.Vinf * ∑ i, P.w i * (up - u) i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := P.le_Vinf i
    have h2 := hw i
    have h3 := sq_nonneg ((up - u) i)
    calc P.w i * (P.V i * (up - u) i ^ 2) ≤ P.w i * (P.Vinf * (up - u) i ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ h2
          exact mul_le_mul_of_nonneg_right h1 h3
      _ = P.Vinf * (P.w i * (up - u) i ^ 2) := by ring
  -- the cubic term: `3uᵢ² + 2uᵢδᵢ + δᵢ²/2 ≤ 2uᵢ² + (u⁺ᵢ)² ≤ 3/w_min`
  have hβ : ∑ i, P.w i * ((up - u) i ^ 2 * (3 * u i ^ 2
        + 2 * u i * (up - u) i + (up - u) i ^ 2 / 2))
      ≤ 3 / P.wmin * ∑ i, P.w i * (up - u) i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := hsq u hu i
    have h2 := hsq up hup i
    have h3 := hw i
    simp only [Pi.sub_apply]
    have key : 3 * u i ^ 2 + 2 * u i * (up i - u i) + (up i - u i) ^ 2 / 2 ≤ 3 / P.wmin := by
      have e : 3 / P.wmin = 2 * (1 / P.wmin) + 1 / P.wmin := by ring
      rw [e]
      nlinarith [sq_nonneg (u i - up i)]
    have h4 := sq_nonneg (up i - u i)
    calc P.w i * ((up i - u i) ^ 2 * (3 * u i ^ 2 + 2 * u i * (up i - u i) + (up i - u i) ^ 2 / 2))
        ≤ P.w i * ((up i - u i) ^ 2 * (3 / P.wmin)) := by
          apply mul_le_mul_of_nonneg_left _ h3
          exact mul_le_mul_of_nonneg_left key h4
      _ = 3 / P.wmin * (P.w i * (up i - u i) ^ 2) := by ring
  have hβpos := P.β_pos
  calc (1 / 2) * ∑ i, P.w i * (P.V i * (up - u) i ^ 2)
        + P.β / 2 * ∑ i, P.w i * ((up - u) i ^ 2 * (3 * u i ^ 2
          + 2 * u i * (up - u) i + (up - u) i ^ 2 / 2))
      ≤ (1 / 2) * (P.Vinf * ∑ i, P.w i * (up - u) i ^ 2)
        + P.β / 2 * (3 / P.wmin * ∑ i, P.w i * (up - u) i ^ 2) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hV (by norm_num)
          · exact mul_le_mul_of_nonneg_left hβ (by positivity)
    _ = (1 / 2) * P.C1 * ∑ i, P.w i * (up - u) i ^ 2 := by unfold C1; ring

/-- `γ |xᵀ S y| ≤ √(γ xᵀ S x) √(γ yᵀ S y)` for `γ ≥ 0`. -/
theorem mul_abs_dotS_le {γ : ℝ} (hγ : 0 ≤ γ) (x y : ι → ℝ) :
    γ * |x ⬝ᵥ (P.S *ᵥ y)| ≤ Real.sqrt (γ * P.kin x) * Real.sqrt (γ * P.kin y) := by
  have hcs := P.abs_dotS_le x y
  calc γ * |x ⬝ᵥ (P.S *ᵥ y)| = Real.sqrt γ * Real.sqrt γ * |x ⬝ᵥ (P.S *ᵥ y)| := by
        rw [Real.mul_self_sqrt hγ]
    _ ≤ Real.sqrt γ * Real.sqrt γ * (Real.sqrt (P.kin x) * Real.sqrt (P.kin y)) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = Real.sqrt (γ * P.kin x) * Real.sqrt (γ * P.kin y) := by
        rw [Real.sqrt_mul hγ, Real.sqrt_mul hγ]; ring

/-- Symmetry of the `𝒢`-inner product: `⟪x, G_X y⟫_h = ⟪G_X x, y⟫_h`. -/
theorem inner_GX_symm (γ : ℝ) (x y : ι → ℝ) :
    P.inner x (P.GX γ y) = P.inner (P.GX γ x) y := by
  rw [inner_GX, GX_inner]

/-- `d - (⟪u, G_X d⟫_h / ‖u‖_𝒢²) u` is `𝒢`-orthogonal to `u`. -/
theorem inner_GX_perp (γ : ℝ) {u : ι → ℝ} (hq : P.nrmGsq γ u ≠ 0) (d : ι → ℝ) :
    P.inner u (P.GX γ (d - (P.inner u (P.GX γ d) / P.nrmGsq γ u) • u)) = 0 := by
  rw [GX_sub, GX_smul, inner_sub_right, inner_smul_right, inner_GX_self, div_mul_cancel₀ _ hq,
    sub_self]

theorem perp_inner_GX (γ : ℝ) {u : ι → ℝ} (hq : P.nrmGsq γ u ≠ 0) (d : ι → ℝ) :
    P.inner (d - (P.inner u (P.GX γ d) / P.nrmGsq γ u) • u) (P.GX γ u) = 0 := by
  rw [inner_GX_symm, inner_comm, inner_GX_perp P γ hq d]

/-- Pythagoras for the `𝒢`-orthogonal decomposition of `d` along `u`. -/
theorem nrmGsq_eq_perp_add (γ : ℝ) {u : ι → ℝ} (hq : P.nrmGsq γ u ≠ 0) (d : ι → ℝ) :
    P.nrmGsq γ d = P.nrmGsq γ (d - (P.inner u (P.GX γ d) / P.nrmGsq γ u) • u)
      + (P.inner u (P.GX γ d) / P.nrmGsq γ u) ^ 2 * P.nrmGsq γ u := by
  have h := P.nrmGsq_add γ (d - (P.inner u (P.GX γ d) / P.nrmGsq γ u) • u)
    ((P.inner u (P.GX γ d) / P.nrmGsq γ u) • u)
  rw [sub_add_cancel, GX_smul, inner_smul_right, perp_inner_GX P γ hq d, nrmGsq_smul] at h
  rw [h]; ring

/-- Expansion of `‖a - b‖_X²`. -/
theorem nrmXsq_sub_eq {γ : ℝ} (hγ : 0 ≤ γ) (a b : ι → ℝ) :
    P.nrmXsq γ (a - b) = P.nrmXsq γ a - 2 * P.innerX γ a b + P.nrmXsq γ b := by
  simp only [nrmXsq_def, innerX_def, resolvent_sub, inner_sub_left, inner_sub_right]
  have := P.innerX_comm hγ b a
  simp only [innerX_def] at this
  rw [this]; ring

/-- Expansion of `‖a - b‖_𝒢²`. -/
theorem nrmGsq_sub (γ : ℝ) (a b : ι → ℝ) :
    P.nrmGsq γ (a - b) = P.nrmGsq γ a - 2 * P.inner a (P.GX γ b) + P.nrmGsq γ b := by
  simp only [nrmGsq_def, nrm2sq_sub, kin_sub, inner_GX]; ring

section Lemma45a

variable [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ} (hγ : 0 < γ)
  (hC2 : γ * P.D u0 ≤ 1 / 128) (hC4 : γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1)
  {z : ι → ℝ} (hz : z ≠ 0) (hpos : ∀ i, 0 < P.normalize z i)
  (hE : P.energy (P.normalize z) ≤ P.E0 u0)
  (hz1 : 1 - 3 * γ * P.D u0 ≤ P.nrm2 z) (hz2 : P.nrm2 z ≤ 1)
include hγ hC2 hC4 hz hpos hE hz1 hz2

-- The hypotheses of Lemma 4.4 are shared by all assertions of this section (via `include`).
set_option linter.unusedSectionVars false

/-- (4.19), first line: `γ|⟪-Δ_h u, δ⟫_h| ≤ √(2γD) ‖δ‖_𝒢`. -/
theorem abs_dotS_u_delta_le :
    γ * |P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z)|
      ≤ Real.sqrt (2 * γ * P.D u0) * Real.sqrt (P.nrmGsq γ (P.delta γ z)) := by
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hkin := P.kin_le_two_E0 hu hE
  have hED := P.E0_le_D u0
  have h1 : γ * P.kin (P.normalize z) ≤ 2 * γ * P.D u0 := by
    have := mul_le_mul_of_nonneg_left (hkin.trans (by linarith : 2 * P.E0 u0 ≤ 2 * P.D u0)) hγ.le
    linarith
  have h2 : γ * P.kin (P.delta γ z) ≤ P.nrmGsq γ (P.delta γ z) := P.mul_kin_le_nrmGsq _
  calc γ * |P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z)|
      ≤ Real.sqrt (γ * P.kin (P.normalize z)) * Real.sqrt (γ * P.kin (P.delta γ z)) :=
        P.mul_abs_dotS_le hγ.le _ _
    _ ≤ Real.sqrt (2 * γ * P.D u0) * Real.sqrt (P.nrmGsq γ (P.delta γ z)) :=
        mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)

/-- `½‖δ‖₂² ≤ √(3γD/2) ‖δ‖_𝒢`, from `‖δ‖₂² ≤ 6γD` and `‖δ‖₂ ≤ ‖δ‖_𝒢`. -/
theorem half_nrm2sq_delta_le :
    1 / 2 * P.nrm2sq (P.delta γ z)
      ≤ Real.sqrt (3 / 2) * Real.sqrt (γ * P.D u0) * Real.sqrt (P.nrmGsq γ (P.delta γ z)) := by
  have hn6 := P.nrm2sq_delta_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hD : 0 ≤ P.D u0 := (P.E0_nonneg u0).trans (P.E0_le_D u0)
  have hγD : 0 ≤ γ * P.D u0 := mul_nonneg hγ.le hD
  have hn0 := P.nrm2sq_nonneg (P.delta γ z)
  have hG2nn := P.nrmGsq_nonneg hγ.le (P.delta γ z)
  have hnG := P.nrm2sq_le_nrmGsq hγ.le (P.delta γ z)
  have hr : 0 ≤ Real.sqrt (3 / 2) * Real.sqrt (γ * P.D u0)
      * Real.sqrt (P.nrmGsq γ (P.delta γ z)) := by positivity
  apply le_of_sq_le_sq _ hr
  have e : (Real.sqrt (3 / 2) * Real.sqrt (γ * P.D u0) * Real.sqrt (P.nrmGsq γ (P.delta γ z))) ^ 2
      = 3 / 2 * (γ * P.D u0) * P.nrmGsq γ (P.delta γ z) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3 / 2), Real.sq_sqrt hγD,
      Real.sq_sqrt hG2nn]
  rw [e]
  linarith [mul_le_mul hn6 hnG hn0 (by positivity : (0:ℝ) ≤ 6 * γ * P.D u0)]

/-- (4.21): `|‖z⁺‖₂ - ‖z‖₂| ≤ |R| + (8/3) √(γD) ‖δ‖_𝒢`. -/
theorem abs_nrm2_step_sub_le :
    |P.nrm2 (P.step γ z) - P.nrm2 z|
      ≤ |P.R γ z| + 8 / 3 * Real.sqrt (γ * P.D u0) * Real.sqrt (P.nrmGsq γ (P.delta γ z)) := by
  have hzp := P.step_ne_zero hγ hC2 hC4 hz hpos hE hz1 hz2
  have hrad := P.radial_identity hγ.le hz hzp
  have hcp1 := P.nrm2_step_le_one hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcp0 := P.nrm2_nonneg (P.step γ z)
  have hS := P.abs_dotS_u_delta_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hH := P.half_nrm2sq_delta_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hD : 0 ≤ P.D u0 := (P.E0_nonneg u0).trans (P.E0_le_D u0)
  have hγD : 0 ≤ γ * P.D u0 := mul_nonneg hγ.le hD
  have hkin := P.kin_nonneg (P.normalize z)
  have hn0 := P.nrm2sq_nonneg (P.delta γ z)
  have h2s : Real.sqrt (2 * γ * P.D u0) = Real.sqrt 2 * Real.sqrt (γ * P.D u0) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_assoc]
  rw [h2s] at hS
  have hsqrt2 : Real.sqrt 2 ≤ 1.415 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsqrt32 : Real.sqrt (3 / 2) ≤ 1.225 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  set cp := P.nrm2 (P.step γ z) with hcp
  set c := P.nrm2 z with hc
  set n := P.nrm2sq (P.delta γ z) with hn
  set s := Real.sqrt (γ * P.D u0) with hs
  set G := Real.sqrt (P.nrmGsq γ (P.delta γ z)) with hG
  set Y := P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z) with hY
  set K := 1 + γ * P.kin (P.normalize z) with hK
  set A := γ * Y - 1 / 2 * n with hA
  have hK1 : 1 ≤ K := by rw [hK]; linarith [mul_nonneg hγ.le hkin]
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hsG : 0 ≤ s * G := mul_nonneg hs0 hG0
  -- `|A| ≤ (√2 + √(3/2)) s G`
  have hA' : |A| ≤ Real.sqrt 2 * s * G + Real.sqrt (3 / 2) * s * G := by
    rw [hA]
    calc |γ * Y - 1 / 2 * n| ≤ |γ * Y| + |1 / 2 * n| := abs_sub _ _
      _ = γ * |Y| + 1 / 2 * n := by
          rw [abs_mul, abs_of_pos hγ, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / 2 * n)]
      _ ≤ _ := add_le_add hS hH
  -- the radial identity: `K (c⁺ - c) = -R - c⁺ A`
  have hrad' : K * (cp - c) = - P.R γ z - cp * A := hrad
  have hX : |cp - c| ≤ |P.R γ z| + |A| := by
    have e1 : |K * (cp - c)| = K * |cp - c| := by rw [abs_mul, abs_of_pos (by linarith)]
    have e2 : |K * (cp - c)| ≤ |P.R γ z| + cp * |A| := by
      rw [hrad']
      calc |- P.R γ z - cp * A| ≤ |- P.R γ z| + |cp * A| := abs_sub _ _
        _ = |P.R γ z| + cp * |A| := by rw [abs_neg, abs_mul, abs_of_nonneg hcp0]
    have e3 : cp * |A| ≤ |A| := mul_le_of_le_one_left (abs_nonneg _) hcp1
    have e4 : |cp - c| ≤ K * |cp - c| := le_mul_of_one_le_left (abs_nonneg _) hK1
    linarith
  calc |cp - c| ≤ |P.R γ z| + |A| := hX
    _ ≤ |P.R γ z| + (Real.sqrt 2 * s * G + Real.sqrt (3 / 2) * s * G) := by linarith
    _ = |P.R γ z| + (Real.sqrt 2 + Real.sqrt (3 / 2)) * (s * G) := by ring
    _ ≤ |P.R γ z| + 8 / 3 * (s * G) := by
        have : (Real.sqrt 2 + Real.sqrt (3 / 2)) * (s * G) ≤ 8 / 3 * (s * G) :=
          mul_le_mul_of_nonneg_right (by linarith) hsG
        linarith
    _ = |P.R γ z| + 8 / 3 * s * G := by ring

/-- Auxiliary used here for Lemma 4.7: if `γ(28D + 2C₁) ≤ 1` then
`E_h(u⁺) ≤ E_h(u) + 2D R²`. -/
theorem energy_step_le_of_small (hsmall : γ * (28 * P.D u0 + 2 * P.C1) ≤ 1) :
    P.energy (P.normalize (P.step γ z))
      ≤ P.energy (P.normalize z) + 2 * P.D u0 * (P.R γ z) ^ 2 := by
  have hzp := P.step_ne_zero hγ hC2 hC4 hz hpos hE hz1 hz2
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hup : P.nrm2sq (P.normalize (P.step γ z)) = 1 := P.nrm2sq_normalize hzp
  have hid := P.energy_identity hγ.le hz hzp
  have hcp1 := P.nrm2_step_le_one hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcp2 := P.nrm2_step_ge hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcp0 := P.nrm2_nonneg (P.step γ z)
  have hX := P.abs_nrm2_step_sub_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hS := P.abs_dotS_u_delta_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hT : P.taylorT (P.normalize z) (P.delta γ z)
      ≤ 1 / 2 * P.C1 * P.nrm2sq (P.delta γ z) := P.taylorT_le_crude hu hup
  have hD : 0 ≤ P.D u0 := (P.E0_nonneg u0).trans (P.E0_le_D u0)
  have hγD : 0 ≤ γ * P.D u0 := mul_nonneg hγ.le hD
  have hC1 : 0 ≤ P.C1 := by
    unfold C1; have := P.Vinf_nonneg; have := P.β_pos; have := P.wmin_pos; positivity
  have hn0 := P.nrm2sq_nonneg (P.delta γ z)
  have hk0 := P.kin_nonneg (P.delta γ z)
  have hG2nn : 0 ≤ P.nrmGsq γ (P.delta γ z) := P.nrmGsq_nonneg hγ.le _
  have hnG : P.nrm2sq (P.delta γ z) ≤ P.nrmGsq γ (P.delta γ z) := P.nrm2sq_le_nrmGsq hγ.le _
  have hGG : Real.sqrt (P.nrmGsq γ (P.delta γ z)) ^ 2 = P.nrmGsq γ (P.delta γ z) :=
    Real.sq_sqrt hG2nn
  have hss : Real.sqrt (γ * P.D u0) ^ 2 = γ * P.D u0 := Real.sq_sqrt hγD
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h2s : Real.sqrt (2 * γ * P.D u0) = Real.sqrt 2 * Real.sqrt (γ * P.D u0) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_assoc]
  rw [h2s] at hS
  -- (i) the quadratic terms: `≥ (½ - 3γD) ‖δ‖_𝒢²`
  have hA : (1 / 2 - 3 * γ * P.D u0) * P.nrmGsq γ (P.delta γ z)
      ≤ (P.nrm2 (P.step γ z) + 1) / 2 * P.nrm2sq (P.delta γ z)
        + γ * (P.nrm2 (P.step γ z) - 1 / 2) * P.kin (P.delta γ z) := by
    rw [nrmGsq_def]
    have e1 : 0 ≤ P.nrm2sq (P.delta γ z) * (P.nrm2 (P.step γ z) / 2 + 3 * γ * P.D u0) :=
      mul_nonneg hn0 (by linarith)
    have e2 : 0 ≤ γ * P.kin (P.delta γ z) * (P.nrm2 (P.step γ z) - 1 + 3 * γ * P.D u0) :=
      mul_nonneg (mul_nonneg hγ.le hk0) (by linarith)
    linarith
  set cp := P.nrm2 (P.step γ z) with hcp
  set c := P.nrm2 z with hc
  set n := P.nrm2sq (P.delta γ z) with hn
  set k := P.kin (P.delta γ z) with hk
  set G2 := P.nrmGsq γ (P.delta γ z) with hG2def
  set G := Real.sqrt G2 with hG
  set s := Real.sqrt (γ * P.D u0) with hs
  set r2 := Real.sqrt 2 with hr2def
  set Rz := P.R γ z with hR
  set T := P.taylorT (P.normalize z) (P.delta γ z) with hT_def
  set Y := P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z) with hY
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hr20 : 0 ≤ r2 := Real.sqrt_nonneg _
  -- (ii) the mixed term: `|γ(c⁺ - c)⟪-Δ_h u, δ⟫_h| ≤ (|R| + (8/3) s G)(√2 s G)`
  have hB0 : |γ * (cp - c) * Y| ≤ (|Rz| + 8 / 3 * s * G) * (r2 * s * G) := by
    rw [abs_mul, abs_mul, abs_of_pos hγ]
    calc γ * |cp - c| * |Y| = |cp - c| * (γ * |Y|) := by ring
      _ ≤ (|Rz| + 8 / 3 * s * G) * (r2 * s * G) :=
        mul_le_mul hX hS (by positivity) (by positivity)
  have hB : -((|Rz| + 8 / 3 * s * G) * (r2 * s * G)) ≤ γ * (cp - c) * Y := by
    linarith [neg_abs_le (γ * (cp - c) * Y)]
  have hsG : r2 * (s ^ 2 * G ^ 2) = r2 * (γ * P.D u0 * G2) := by rw [hss, hGG]
  -- Young: `√2 s G |R| ≤ ¼ G² + 2γD R²`
  have hprod : r2 ^ 2 * s ^ 2 * |Rz| ^ 2 = 2 * (γ * P.D u0) * Rz ^ 2 := by
    rw [hr2, hss, sq_abs]
  have hY : r2 * s * G * |Rz| ≤ 1 / 4 * G2 + 2 * (γ * P.D u0) * Rz ^ 2 := by
    linarith [sq_nonneg (G / 2 - r2 * s * |Rz|)]
  -- (iii) the remainder: `γ𝒯 ≤ ½ γ C₁ ‖δ‖_𝒢²`
  have hT' : γ * T ≤ 1 / 2 * γ * P.C1 * G2 := by
    have h1 := mul_le_mul_of_nonneg_left hT hγ.le
    have h2 : γ * P.C1 * n ≤ γ * P.C1 * G2 :=
      mul_le_mul_of_nonneg_left hnG (mul_nonneg hγ.le hC1)
    linarith
  -- the coefficients: `(8/3)√2 γD ≤ 4γD` and `¼ - 7γD - ½γC₁ ≥ 0`
  have hc1 : r2 * (γ * P.D u0 * G2) ≤ 3 / 2 * (γ * P.D u0 * G2) :=
    mul_le_mul_of_nonneg_right hsqrt2 (mul_nonneg hγD hG2nn)
  have hc2 : 0 ≤ (1 / 4 - 7 * (γ * P.D u0) - 1 / 2 * (γ * P.C1)) * G2 :=
    mul_nonneg (by linarith) hG2nn
  have key : 0 ≤ γ * (P.energy (P.normalize z) - P.energy (P.normalize (P.step γ z))
      + 2 * P.D u0 * Rz ^ 2) := by
    linarith
  have := (mul_nonneg_iff_of_pos_left hγ).mp key
  linarith

end Lemma45a

section Lemma45

variable [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ} (hγ : 0 < γ)
  (hC2 : γ * P.D u0 ≤ 1 / 128) (hC3 : γ * P.L0 u0 ≤ 1 / 8)
  (hC4 : γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1)
  {z : ι → ℝ} (hz : z ≠ 0) (hpos : ∀ i, 0 < P.normalize z i)
  (hE : P.energy (P.normalize z) ≤ P.E0 u0)
  (hz1 : 1 - 3 * γ * P.D u0 ≤ P.nrm2 z) (hz2 : P.nrm2 z ≤ 1)
  (hEp : P.energy (P.normalize (P.step γ z)) ≤ P.E0 u0)
include hγ hC2 hC3 hC4 hz hpos hE hz1 hz2 hEp

-- The hypotheses are shared by all assertions of this section (via `include`).
set_option linter.unusedSectionVars false

/-- (4.22): the energy drop `γ(E_h(u) - E_h(u⁺)) ≥ (7/16 - 10γD)‖δ‖_𝒢² - (1/5)R²`. -/
theorem energy_drop :
    γ * (P.energy (P.normalize z) - P.energy (P.normalize (P.step γ z)))
      ≥ (7 / 16 - 10 * γ * P.D u0) * P.nrmGsq γ (P.delta γ z) - (1 / 5) * (P.R γ z) ^ 2 := by
  have hzp := P.step_ne_zero hγ hC2 hC4 hz hpos hE hz1 hz2
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hup : P.nrm2sq (P.normalize (P.step γ z)) = 1 := P.nrm2sq_normalize hzp
  have hid := P.energy_identity hγ.le hz hzp
  have hcp1 := P.nrm2_step_le_one hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcp2 := P.nrm2_step_ge hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcp0 := P.nrm2_nonneg (P.step γ z)
  have hX := P.abs_nrm2_step_sub_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hS := P.abs_dotS_u_delta_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hT : γ * P.taylorT (P.normalize z) (P.delta γ z)
      ≤ 1 / 16 * P.nrmGsq γ (P.delta γ z) := P.taylorT_le hu hup hE hEp hγ.le hC3
  have hD : 0 ≤ P.D u0 := (P.E0_nonneg u0).trans (P.E0_le_D u0)
  have hγD : 0 ≤ γ * P.D u0 := mul_nonneg hγ.le hD
  have hn0 := P.nrm2sq_nonneg (P.delta γ z)
  have hk0 := P.kin_nonneg (P.delta γ z)
  have hG2nn : 0 ≤ P.nrmGsq γ (P.delta γ z) := P.nrmGsq_nonneg hγ.le _
  have hGG : Real.sqrt (P.nrmGsq γ (P.delta γ z)) ^ 2 = P.nrmGsq γ (P.delta γ z) :=
    Real.sq_sqrt hG2nn
  have hss : Real.sqrt (γ * P.D u0) ^ 2 = γ * P.D u0 := Real.sq_sqrt hγD
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have h2s : Real.sqrt (2 * γ * P.D u0) = Real.sqrt 2 * Real.sqrt (γ * P.D u0) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_assoc]
  rw [h2s] at hS
  -- (i) the quadratic terms: `≥ (½ - 3γD) ‖δ‖_𝒢²`
  have hA : (1 / 2 - 3 * γ * P.D u0) * P.nrmGsq γ (P.delta γ z)
      ≤ (P.nrm2 (P.step γ z) + 1) / 2 * P.nrm2sq (P.delta γ z)
        + γ * (P.nrm2 (P.step γ z) - 1 / 2) * P.kin (P.delta γ z) := by
    rw [nrmGsq_def]
    have e1 : 0 ≤ P.nrm2sq (P.delta γ z) * (P.nrm2 (P.step γ z) / 2 + 3 * γ * P.D u0) :=
      mul_nonneg hn0 (by linarith)
    have e2 : 0 ≤ γ * P.kin (P.delta γ z) * (P.nrm2 (P.step γ z) - 1 + 3 * γ * P.D u0) :=
      mul_nonneg (mul_nonneg hγ.le hk0) (by linarith)
    linarith
  set cp := P.nrm2 (P.step γ z) with hcp
  set c := P.nrm2 z with hc
  set n := P.nrm2sq (P.delta γ z) with hn
  set k := P.kin (P.delta γ z) with hk
  set G2 := P.nrmGsq γ (P.delta γ z) with hG2def
  set G := Real.sqrt G2 with hG
  set s := Real.sqrt (γ * P.D u0) with hs
  set r2 := Real.sqrt 2 with hr2def
  set Rz := P.R γ z with hR
  set T := P.taylorT (P.normalize z) (P.delta γ z) with hT_def
  set Y := P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z) with hY
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hr20 : 0 ≤ r2 := Real.sqrt_nonneg _
  -- (ii) the mixed term
  have hB0 : |γ * (cp - c) * Y| ≤ (|Rz| + 8 / 3 * s * G) * (r2 * s * G) := by
    rw [abs_mul, abs_mul, abs_of_pos hγ]
    calc γ * |cp - c| * |Y| = |cp - c| * (γ * |Y|) := by ring
      _ ≤ (|Rz| + 8 / 3 * s * G) * (r2 * s * G) :=
        mul_le_mul hX hS (by positivity) (by positivity)
  have hB : -((|Rz| + 8 / 3 * s * G) * (r2 * s * G)) ≤ γ * (cp - c) * Y := by
    linarith [neg_abs_le (γ * (cp - c) * Y)]
  have hsG : r2 * (s ^ 2 * G ^ 2) = r2 * (γ * P.D u0 * G2) := by rw [hss, hGG]
  -- Young in the form of the paper: `√2 s G |R| ≤ (1/5) R² + (5/2) γD G²`
  have hprod : r2 ^ 2 * s ^ 2 * G ^ 2 = 2 * (γ * P.D u0) * G2 := by rw [hr2, hss, hGG]
  have hY : r2 * s * G * |Rz| ≤ 1 / 5 * Rz ^ 2 + 5 / 2 * (γ * P.D u0) * G2 := by
    linarith [sq_nonneg (2 * |Rz| - 5 * (r2 * s * G)), sq_abs Rz]
  -- the coefficients
  have hc1 : r2 * (γ * P.D u0 * G2) ≤ 3 / 2 * (γ * P.D u0 * G2) :=
    mul_le_mul_of_nonneg_right hsqrt2 (mul_nonneg hγD hG2nn)
  have hc2 : 0 ≤ γ * P.D u0 * G2 := mul_nonneg hγD hG2nn
  rw [ge_iff_le]
  linarith

/-- (4.23): the residual bound `(R⁺)² ≤ 8γ²D² R² + (128/25) γD ‖δ‖_𝒢²`. -/
theorem residual_sq_le :
    (P.R γ (P.step γ z)) ^ 2
      ≤ 8 * γ ^ 2 * P.D u0 ^ 2 * (P.R γ z) ^ 2
        + 128 / 25 * γ * P.D u0 * P.nrmGsq γ (P.delta γ z) := by
  have hzp := P.step_ne_zero hγ hC2 hC4 hz hpos hE hz1 hz2
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hup : P.nrm2sq (P.normalize (P.step γ z)) = 1 := P.nrm2sq_normalize hzp
  have hres := P.residual_identity hγ.le hz hzp
  have hcp1 := P.nrm2_step_le_one hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcp2 := P.nrm2_step_ge hγ hC2 hC4 hz hpos hE hz1 hz2
  have hX := P.abs_nrm2_step_sub_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hH := P.half_nrm2sq_delta_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hN : |P.inner (P.nonlin (P.normalize (P.step γ z)) - P.nonlin (P.normalize z))
      (P.normalize (P.step γ z))| ≤ 3 * P.B0 u0 * P.nrm2 (P.delta γ z) :=
    P.abs_inner_nonlin_sub_le hu hup hE hEp
  have hD : 0 ≤ P.D u0 := (P.E0_nonneg u0).trans (P.E0_le_D u0)
  have hγD : 0 ≤ γ * P.D u0 := mul_nonneg hγ.le hD
  have hB0D := P.B0_le_D u0
  have hED := P.E0_le_D u0
  have hkinu := P.kin_le_two_E0 hu hE
  have hkinup := P.kin_le_two_E0 hup hEp
  have hkinu0 := P.kin_nonneg (P.normalize z)
  have hkinup0 := P.kin_nonneg (P.normalize (P.step γ z))
  have hγkinu := mul_le_mul_of_nonneg_left hkinu hγ.le
  have hγkinup := mul_le_mul_of_nonneg_left hkinup hγ.le
  have hγE := mul_le_mul_of_nonneg_left hED hγ.le
  have hn0 := P.nrm2sq_nonneg (P.delta γ z)
  have hG2nn : 0 ≤ P.nrmGsq γ (P.delta γ z) := P.nrmGsq_nonneg hγ.le _
  have hnG : P.nrm2sq (P.delta γ z) ≤ P.nrmGsq γ (P.delta γ z) := P.nrm2sq_le_nrmGsq hγ.le _
  have hGG : Real.sqrt (P.nrmGsq γ (P.delta γ z)) ^ 2 = P.nrmGsq γ (P.delta γ z) :=
    Real.sq_sqrt hG2nn
  have hss : Real.sqrt (γ * P.D u0) ^ 2 = γ * P.D u0 := Real.sq_sqrt hγD
  have hsqrt2 : Real.sqrt 2 ≤ 14143 / 10000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsqrt32 : Real.sqrt (3 / 2) ≤ 1531 / 1250 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hs_le : Real.sqrt (γ * P.D u0) ≤ 177 / 2000 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num; linarith⟩
  -- `‖δ‖₂ ≤ ‖δ‖_𝒢`
  have hnrm : P.nrm2 (P.delta γ z) ≤ Real.sqrt (P.nrmGsq γ (P.delta γ z)) :=
    Real.sqrt_le_sqrt hnG
  -- the kinetic cross terms: `γ|⟪-Δ_h u, u⁺⟫_h| ≤ 2γD` and `γ|⟪-Δ_h δ, u⁺⟫_h| ≤ ‖δ‖_𝒢 √(2γD)`
  have hY2 : γ * |P.normalize z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z))| ≤ 2 * γ * P.D u0 := by
    have h := P.mul_abs_dotS_le hγ.le (P.normalize z) (P.normalize (P.step γ z))
    have h1 : Real.sqrt (γ * P.kin (P.normalize z)) ≤ Real.sqrt (2 * γ * P.D u0) :=
      Real.sqrt_le_sqrt (by linarith [hγkinu, hγE])
    have h2 : Real.sqrt (γ * P.kin (P.normalize (P.step γ z))) ≤ Real.sqrt (2 * γ * P.D u0) :=
      Real.sqrt_le_sqrt (by linarith [hγkinup, hγE])
    have h3 : Real.sqrt (2 * γ * P.D u0) * Real.sqrt (2 * γ * P.D u0) = 2 * γ * P.D u0 :=
      Real.mul_self_sqrt (by positivity)
    calc γ * |P.normalize z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z))| ≤ _ := h
      _ ≤ Real.sqrt (2 * γ * P.D u0) * Real.sqrt (2 * γ * P.D u0) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = 2 * γ * P.D u0 := h3
  have hY3 : γ * |P.delta γ z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z))|
      ≤ Real.sqrt (P.nrmGsq γ (P.delta γ z)) * (Real.sqrt 2 * Real.sqrt (γ * P.D u0)) := by
    have h := P.mul_abs_dotS_le hγ.le (P.delta γ z) (P.normalize (P.step γ z))
    have h1 : Real.sqrt (γ * P.kin (P.delta γ z)) ≤ Real.sqrt (P.nrmGsq γ (P.delta γ z)) :=
      Real.sqrt_le_sqrt (P.mul_kin_le_nrmGsq _)
    have h2 : Real.sqrt (γ * P.kin (P.normalize (P.step γ z)))
        ≤ Real.sqrt 2 * Real.sqrt (γ * P.D u0) := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (by linarith [hγkinup, hγE])
    exact h.trans (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hcpm1 : |P.nrm2 (P.step γ z) - 1| ≤ 3 * γ * P.D u0 := by
    rw [abs_le]; constructor <;> linarith
  set cp := P.nrm2 (P.step γ z) with hcp
  set c := P.nrm2 z with hc
  set n := P.nrm2sq (P.delta γ z) with hn
  set G2 := P.nrmGsq γ (P.delta γ z) with hG2def
  set G := Real.sqrt G2 with hG
  set s := Real.sqrt (γ * P.D u0) with hs
  set r2 := Real.sqrt 2 with hr2def
  set t32 := Real.sqrt (3 / 2) with ht32
  set Rz := P.R γ z with hR
  set Rp := P.R γ (P.step γ z) with hRp
  set Y2 := P.normalize z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z)) with hY2def
  set Y3 := P.delta γ z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z)) with hY3def
  set N := P.inner (P.nonlin (P.normalize (P.step γ z)) - P.nonlin (P.normalize z))
    (P.normalize (P.step γ z)) with hNdef
  set nd := P.nrm2 (P.delta γ z) with hnd
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hG0 : 0 ≤ G := Real.sqrt_nonneg _
  have hr20 : 0 ≤ r2 := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t32 := Real.sqrt_nonneg _
  have hnd0 : 0 ≤ nd := P.nrm2_nonneg _
  -- bounds on the four terms of the residual identity
  have hb1 : |-(1 / 2) * n| ≤ t32 * s * G := by
    rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2), abs_of_nonneg hn0]
    linarith
  have hb2 : |γ * (cp - c) * Y2| ≤ (|Rz| + 8 / 3 * s * G) * (2 * γ * P.D u0) := by
    rw [abs_mul, abs_mul, abs_of_pos hγ]
    calc γ * |cp - c| * |Y2| = |cp - c| * (γ * |Y2|) := by ring
      _ ≤ _ := mul_le_mul hX hY2 (by positivity) (by positivity)
  have hb3 : |γ * (cp - 1) * Y3| ≤ 3 * γ * P.D u0 * (G * (r2 * s)) := by
    rw [abs_mul, abs_mul, abs_of_pos hγ]
    calc γ * |cp - 1| * |Y3| = |cp - 1| * (γ * |Y3|) := by ring
      _ ≤ _ := mul_le_mul hcpm1 hY3 (by positivity) (by positivity)
  have hb4 : |γ * N| ≤ 3 * γ * P.D u0 * G := by
    rw [abs_mul, abs_of_pos hγ]
    have h1 : γ * |N| ≤ γ * (3 * P.B0 u0 * nd) := mul_le_mul_of_nonneg_left hN hγ.le
    have h2 : P.B0 u0 * nd ≤ P.D u0 * G := mul_le_mul hB0D hnrm hnd0 hD
    have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hγ.le)
    linarith
  have habs0 : |-(1 / 2) * n - γ * (cp - c) * Y2 - γ * (cp - 1) * Y3 + γ * N|
      ≤ |-(1 / 2) * n| + |γ * (cp - c) * Y2| + |γ * (cp - 1) * Y3| + |γ * N| := by
    calc |-(1 / 2) * n - γ * (cp - c) * Y2 - γ * (cp - 1) * Y3 + γ * N|
        ≤ |-(1 / 2) * n - γ * (cp - c) * Y2 - γ * (cp - 1) * Y3| + |γ * N| := abs_add_le _ _
      _ ≤ |-(1 / 2) * n - γ * (cp - c) * Y2| + |γ * (cp - 1) * Y3| + |γ * N| :=
          add_le_add (abs_sub _ _) le_rfl
      _ ≤ |-(1 / 2) * n| + |γ * (cp - c) * Y2| + |γ * (cp - 1) * Y3| + |γ * N| := by
          have := abs_sub (-(1 / 2) * n) (γ * (cp - c) * Y2)
          linarith
  -- the sum of the bounds is `≤ 2γD|R| + (8/5) s G`
  have hr2γD : r2 * (γ * P.D u0) ≤ 14143 / 10000 * (1 / 128) :=
    mul_le_mul hsqrt2 hC2 hγD (by norm_num)
  have hcoef : t32 + 16 / 3 * (γ * P.D u0) + 3 * (r2 * (γ * P.D u0)) + 3 * s ≤ 8 / 5 := by
    linarith
  have hsG0 : 0 ≤ s * G := mul_nonneg hs0 hG0
  have hs2G : s ^ 2 * G = γ * P.D u0 * G := by rw [hss]
  have hsum : t32 * s * G + (|Rz| + 8 / 3 * s * G) * (2 * γ * P.D u0)
      + 3 * γ * P.D u0 * (G * (r2 * s)) + 3 * γ * P.D u0 * G
      ≤ 2 * γ * P.D u0 * |Rz| + 8 / 5 * (s * G) := by
    have := mul_le_mul_of_nonneg_right hcoef hsG0
    linarith
  have hRp_abs : |Rp| ≤ 2 * γ * P.D u0 * |Rz| + 8 / 5 * (s * G) := by
    rw [hres]
    linarith
  have hZ0 : 0 ≤ 2 * γ * P.D u0 * |Rz| + 8 / 5 * (s * G) := by positivity
  have hsq : Rp ^ 2 ≤ (2 * γ * P.D u0 * |Rz| + 8 / 5 * (s * G)) ^ 2 := by
    rw [← sq_abs Rp]; exact pow_le_pow_left₀ (abs_nonneg _) hRp_abs 2
  have e1 : (γ * P.D u0) ^ 2 * |Rz| ^ 2 = γ ^ 2 * P.D u0 ^ 2 * Rz ^ 2 := by rw [sq_abs]; ring
  have e2 : s ^ 2 * G ^ 2 = γ * P.D u0 * G2 := by rw [hss, hGG]
  linarith [sq_nonneg (2 * γ * P.D u0 * |Rz| - 8 / 5 * (s * G))]

/-- Lemma 4.5, (4.17): `γ(𝓛(z) - 𝓛(z⁺)) ≥ (5/16)‖δ‖_𝒢² + (3/4)R²`. -/
theorem conditional_descent :
    γ * (P.lyap γ z - P.lyap γ (P.step γ z))
      ≥ 5 / 16 * P.nrmGsq γ (P.delta γ z) + 3 / 4 * (P.R γ z) ^ 2 := by
  have hdrop := P.energy_drop hγ hC2 hC3 hC4 hz hpos hE hz1 hz2 hEp
  have hres := P.residual_sq_le hγ hC2 hC3 hC4 hz hpos hE hz1 hz2 hEp
  have hD : 0 ≤ P.D u0 := (P.E0_nonneg u0).trans (P.E0_le_D u0)
  have hγD : 0 ≤ γ * P.D u0 := mul_nonneg hγ.le hD
  have hG2nn : 0 ≤ P.nrmGsq γ (P.delta γ z) := P.nrmGsq_nonneg hγ.le _
  have e : γ * (P.lyap γ z - P.lyap γ (P.step γ z))
      = γ * (P.energy (P.normalize z) - P.energy (P.normalize (P.step γ z)))
        + (P.R γ z) ^ 2 - (P.R γ (P.step γ z)) ^ 2 := by
    rw [lyap_def, lyap_def]; field_simp; ring
  have h1 : 0 ≤ (1 / 8 - 378 / 25 * (γ * P.D u0)) * P.nrmGsq γ (P.delta γ z) :=
    mul_nonneg (by linarith) hG2nn
  have h2 : γ * P.D u0 * (γ * P.D u0) ≤ 1 / 128 * (1 / 128) :=
    mul_le_mul hC2 hC2 hγD (by norm_num)
  have h3 : 0 ≤ (1 / 20 - 8 * (γ * P.D u0) ^ 2) * (P.R γ z) ^ 2 :=
    mul_nonneg (by linarith [h2]) (sq_nonneg _)
  rw [ge_iff_le, e]
  linarith [hdrop, hres, h1, h3]

end Lemma45

/-- Lemma 4.5, equality case: if `δ = 0` and `R = 0` then `g(u) = 0` and `z⁺ = z`.
(For `γ = 0` one has `z⁺ = u` and `δ = 0` for every `z`, so `γ > 0` is needed for `g(u) = 0`.) -/
theorem descent_equality_case {γ : ℝ} (hγ : 0 < γ) {z : ι → ℝ} (hz : z ≠ 0)
    (hzp : P.step γ z ≠ 0) (hδ : P.delta γ z = 0) (hR : P.R γ z = 0) :
    P.g (P.normalize z) = 0 ∧ P.step γ z = z := by
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hdec := P.step_sub_decomp hγ.le hz hzp
  rw [hδ, smul_zero, zero_add] at hdec
  have hG := P.GX_step_sub hγ.le hz
  rw [hR, zero_smul, zero_add, hdec, GX_smul] at hG
  -- `(‖z⁺‖₂ - ‖z‖₂) ⟪G_X u, u⟫_h = -γ ⟪g(u), u⟫_h = 0`
  have hinner := congrArg (fun v => P.inner v (P.normalize z)) hG
  simp only [inner_smul_left, inner_neg_left, GX_inner, P.inner_g_self hu, mul_zero,
    neg_zero] at hinner
  rw [← nrm2sq_def, hu, ← kin_def] at hinner
  have hkin := P.kin_nonneg (P.normalize z)
  have hpos : 0 < 1 + γ * P.kin (P.normalize z) := by positivity
  have hc : P.nrm2 (P.step γ z) - P.nrm2 z = 0 := by
    rcases mul_eq_zero.mp hinner with h | h
    · exact h
    · linarith
  rw [hc, zero_smul] at hdec hG
  refine ⟨?_, sub_eq_zero.mp hdec⟩
  rw [eq_comm, neg_eq_zero] at hG
  exact (smul_eq_zero.mp hG).resolve_left hγ.ne'

/-- Conversely, if `R = 0` and `g(u) = 0` then `z⁺ = z` (used in the barrier argument). -/
theorem step_eq_self_of_R_g {γ : ℝ} (hγ : 0 ≤ γ) {z : ι → ℝ} (hz : z ≠ 0)
    (hR : P.R γ z = 0) (hg : P.g (P.normalize z) = 0) : P.step γ z = z := by
  have hG := P.GX_step_sub hγ hz
  rw [hR, hg, zero_smul, smul_zero, add_zero, neg_zero] at hG
  have h : P.GX γ (P.step γ z - z) = P.GX γ 0 := by rw [hG, GX_zero]
  exact sub_eq_zero.mp (P.GX_injective hγ h)

section Lemma46

variable [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ} (hγ : 0 < γ)
  (hC2 : γ * P.D u0 ≤ 1 / 128) (hC4 : γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1)
  {z : ι → ℝ} (hz : z ≠ 0) (hpos : ∀ i, 0 < P.normalize z i)
  (hE : P.energy (P.normalize z) ≤ P.E0 u0)
  (hz1 : 1 - 3 * γ * P.D u0 ≤ P.nrm2 z) (hz2 : P.nrm2 z ≤ 1)
include hγ hC2 hC4 hz hpos hE hz1 hz2

/-- The radial identity in the form `‖u‖_𝒢² (‖z⁺‖₂ - ‖z‖₂) = -R - ‖z⁺‖₂ ⟪u, G_X δ⟫_h`. -/
theorem nrmGsq_mul_nrm2_sub :
    P.nrmGsq γ (P.normalize z) * (P.nrm2 (P.step γ z) - P.nrm2 z)
      = - P.R γ z - P.nrm2 (P.step γ z) * P.inner (P.normalize z) (P.GX γ (P.delta γ z)) := by
  have hzp := P.step_ne_zero hγ hC2 hC4 hz hpos hE hz1 hz2
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hup : P.nrm2sq (P.normalize (P.step γ z)) = 1 := P.nrm2sq_normalize hzp
  have hrad := P.radial_identity hγ.le hz hzp
  have hud : P.inner (P.normalize z) (P.delta γ z) = -(1 / 2) * P.nrm2sq (P.delta γ z) :=
    P.inner_sub_self_eq hu hup
  rw [inner_GX, hud, nrmGsq_def, hu]
  linear_combination hrad

/-- The decomposition `z⁺ - z = ‖z⁺‖₂ δ⊥ - (R/‖u‖_𝒢²) u`, where
`δ⊥ = δ - (⟪u, G_X δ⟫_h/‖u‖_𝒢²) u` is the `𝒢`-orthogonal part of `δ`. -/
theorem step_sub_eq_perp :
    P.step γ z - z
      = P.nrm2 (P.step γ z) • (P.delta γ z
          - (P.inner (P.normalize z) (P.GX γ (P.delta γ z)) / P.nrmGsq γ (P.normalize z))
            • P.normalize z)
        - (P.R γ z / P.nrmGsq γ (P.normalize z)) • P.normalize z := by
  have hzp := P.step_ne_zero hγ hC2 hC4 hz hpos hE hz1 hz2
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hq : P.nrmGsq γ (P.normalize z) ≠ 0 := by
    rw [nrmGsq_def, hu]; have := P.kin_nonneg (P.normalize z); positivity
  have hs := P.nrmGsq_mul_nrm2_sub hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcoef : P.nrm2 (P.step γ z) - P.nrm2 z
      = (- P.R γ z - P.nrm2 (P.step γ z) * P.inner (P.normalize z) (P.GX γ (P.delta γ z)))
        / P.nrmGsq γ (P.normalize z) := by
    rw [eq_div_iff hq]; linear_combination hs
  rw [P.step_sub_decomp hγ.le hz hzp, hcoef]
  module

/-- Lemma 4.6, first bound of (4.24): `γ²‖g(u)‖_X² ≤ (5/4)‖δ‖_𝒢² + 10γD R²`. -/
theorem gradX_sq_le :
    γ ^ 2 * P.nrmXsq γ (P.g (P.normalize z))
      ≤ 5 / 4 * P.nrmGsq γ (P.delta γ z) + 10 * γ * P.D u0 * (P.R γ z) ^ 2 := by
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hkin := P.kin_nonneg (P.normalize z)
  have hkin2 := P.kin_le_two_E0 hu hE
  have hED := P.E0_le_D u0
  have hqeq : P.nrmGsq γ (P.normalize z) = 1 + γ * P.kin (P.normalize z) := by
    rw [nrmGsq_def, hu]
  have hq1 : 1 ≤ P.nrmGsq γ (P.normalize z) := by rw [hqeq]; linarith [mul_nonneg hγ.le hkin]
  have hq0 : 0 < P.nrmGsq γ (P.normalize z) := by linarith
  have hq : P.nrmGsq γ (P.normalize z) ≠ 0 := hq0.ne'
  have hcp1 := P.nrm2_step_le_one hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcp0 := P.nrm2_nonneg (P.step γ z)
  have hD : 0 ≤ P.D u0 := (P.E0_nonneg u0).trans (P.E0_le_D u0)
  have hG := P.GX_step_sub hγ.le hz
  rw [P.step_sub_eq_perp hγ hC2 hC4 hz hpos hE hz1 hz2, GX_sub, GX_smul, GX_smul] at hG
  have hdecomp := P.nrmGsq_eq_perp_add γ hq (P.delta γ z)
  have hXdp := P.nrmXsq_GX hγ.le (P.delta γ z
    - (P.inner (P.normalize z) (P.GX γ (P.delta γ z)) / P.nrmGsq γ (P.normalize z))
      • P.normalize z)
  have hXu1 : P.innerX γ (P.normalize z) (P.GX γ (P.normalize z)) = 1 := by
    rw [innerX_GX_right P hγ.le, ← nrm2sq_def, hu]
  have hXGu : P.nrmXsq γ (P.GX γ (P.normalize z)) = P.nrmGsq γ (P.normalize z) :=
    P.nrmXsq_GX hγ.le _
  have hXu : P.nrmXsq γ (P.normalize z) ≤ 1 := by
    have := P.nrmXsq_le_nrm2sq hγ.le (P.normalize z); rwa [hu] at this
  have hγkin := mul_le_mul_of_nonneg_left hkin2 hγ.le
  have hγE := mul_le_mul_of_nonneg_left hED hγ.le
  set q := P.nrmGsq γ (P.normalize z) with hqdef
  set u := P.normalize z with hu_def
  set I := P.inner u (P.GX γ (P.delta γ z)) with hI
  set dp := P.delta γ z - (I / q) • u with hdp
  set cp := P.nrm2 (P.step γ z) with hcp
  set Rz := P.R γ z with hR
  set v := u - (1 / q) • P.GX γ u with hv
  -- `γ g(u) = -(c⁺ G_X δ⊥ + R v)` with `v = u - G_X u / ‖u‖_𝒢²`
  have hgu : γ • P.g u = -(cp • P.GX γ dp + Rz • v) := by
    rw [hv]; linear_combination (norm := module) hG
  -- `‖v‖_X² = ‖u‖_X² - 1/‖u‖_𝒢² ≤ 1 - 1/‖u‖_𝒢² ≤ ‖u‖_𝒢² - 1 = γ⟪u,-Δ_h u⟫_h ≤ 2γD`
  have hv2 : P.nrmXsq γ v ≤ 2 * γ * P.D u0 := by
    have e : P.nrmXsq γ v = P.nrmXsq γ u - 2 * (1 / q) + (1 / q) ^ 2 * q := by
      rw [hv, P.nrmXsq_sub_eq hγ.le, innerX_smul_right, nrmXsq_smul, hXu1, hXGu]
      ring
    have e2 : (1 / q) ^ 2 * q = 1 / q := by
      rw [sq, mul_assoc, one_div, inv_mul_cancel₀ hq, mul_one]
    have h3 : 2 - q ≤ 1 / q := by
      rw [le_div_iff₀ hq0]; linarith [sq_nonneg (q - 1)]
    have h4 : q - 1 ≤ 2 * γ * P.D u0 := by
      rw [hqeq]; linarith
    rw [e, e2]; linarith
  -- the triangle inequality in `X`
  have hW : P.nrmXsq γ (γ • P.g u) = P.nrmXsq γ (cp • P.GX γ dp + Rz • v) := by
    rw [hgu, nrmXsq_neg]
  have htri := P.sqrt_nrmXsq_add_le hγ.le (cp • P.GX γ dp) (Rz • v)
  have hA2 : P.nrmXsq γ (cp • P.GX γ dp) = cp ^ 2 * P.nrmGsq γ dp := by
    rw [nrmXsq_smul, hXdp]
  have hB2 : P.nrmXsq γ (Rz • v) = Rz ^ 2 * P.nrmXsq γ v := P.nrmXsq_smul γ Rz v
  have hS0 := P.nrmXsq_nonneg hγ.le (cp • P.GX γ dp + Rz • v)
  have hA0 := P.nrmXsq_nonneg hγ.le (cp • P.GX γ dp)
  have hB0 := P.nrmXsq_nonneg hγ.le (Rz • v)
  set S := Real.sqrt (P.nrmXsq γ (cp • P.GX γ dp + Rz • v)) with hS
  set A := Real.sqrt (P.nrmXsq γ (cp • P.GX γ dp)) with hA
  set B := Real.sqrt (P.nrmXsq γ (Rz • v)) with hB
  have hS2 : S ^ 2 = P.nrmXsq γ (cp • P.GX γ dp + Rz • v) := Real.sq_sqrt hS0
  have hA2' : A ^ 2 = P.nrmXsq γ (cp • P.GX γ dp) := Real.sq_sqrt hA0
  have hB2' : B ^ 2 = P.nrmXsq γ (Rz • v) := Real.sq_sqrt hB0
  have hSnn : 0 ≤ S := Real.sqrt_nonneg _
  have hsq : S ^ 2 ≤ (A + B) ^ 2 := pow_le_pow_left₀ hSnn htri 2
  have hyoung : (A + B) ^ 2 ≤ 5 / 4 * A ^ 2 + 5 * B ^ 2 := by
    linarith [sq_nonneg (A / 2 - 2 * B)]
  have hdp0 := P.nrmGsq_nonneg hγ.le dp
  have hcp2 : cp ^ 2 * P.nrmGsq γ dp ≤ P.nrmGsq γ dp :=
    mul_le_of_le_one_left hdp0 (pow_le_one₀ hcp0 hcp1)
  have hdpδ : P.nrmGsq γ dp ≤ P.nrmGsq γ (P.delta γ z) := by
    have : 0 ≤ (I / q) ^ 2 * q := by positivity
    linarith
  have hRv : Rz ^ 2 * P.nrmXsq γ v ≤ Rz ^ 2 * (2 * γ * P.D u0) :=
    mul_le_mul_of_nonneg_left hv2 (sq_nonneg _)
  have hfinal : P.nrmXsq γ (γ • P.g u)
      ≤ 5 / 4 * P.nrmGsq γ (P.delta γ z) + 10 * γ * P.D u0 * Rz ^ 2 := by
    rw [hW, ← hS2]; linarith
  rw [nrmXsq_smul] at hfinal
  exact hfinal

/-- Lemma 4.6, second bound of (4.24): `‖z⁺ - z‖_𝒢² ≤ ‖δ‖_𝒢² + R²`. -/
theorem nrmGsq_step_sub_le :
    P.nrmGsq γ (P.step γ z - z) ≤ P.nrmGsq γ (P.delta γ z) + (P.R γ z) ^ 2 := by
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hkin := P.kin_nonneg (P.normalize z)
  have hq1 : 1 ≤ P.nrmGsq γ (P.normalize z) := by
    rw [nrmGsq_def, hu]; linarith [mul_nonneg hγ.le hkin]
  have hq0 : 0 < P.nrmGsq γ (P.normalize z) := by linarith
  have hq : P.nrmGsq γ (P.normalize z) ≠ 0 := hq0.ne'
  have hcp1 := P.nrm2_step_le_one hγ hC2 hC4 hz hpos hE hz1 hz2
  have hcp0 := P.nrm2_nonneg (P.step γ z)
  have hdecomp := P.nrmGsq_eq_perp_add γ hq (P.delta γ z)
  have hperp := P.perp_inner_GX γ hq (P.delta γ z)
  rw [P.step_sub_eq_perp hγ hC2 hC4 hz hpos hE hz1 hz2, nrmGsq_sub,
    nrmGsq_smul, nrmGsq_smul, GX_smul, inner_smul_right, inner_smul_left, hperp]
  set q := P.nrmGsq γ (P.normalize z) with hqdef
  set I := P.inner (P.normalize z) (P.GX γ (P.delta γ z)) with hI
  set cp := P.nrm2 (P.step γ z) with hcp
  set dp := P.delta γ z - (I / q) • P.normalize z with hdp
  have hdp0 := P.nrmGsq_nonneg hγ.le dp
  have h1 : cp ^ 2 * P.nrmGsq γ dp ≤ P.nrmGsq γ dp :=
    mul_le_of_le_one_left hdp0 (pow_le_one₀ hcp0 hcp1)
  have h2 : (P.R γ z / q) ^ 2 * q = (P.R γ z) ^ 2 / q := by
    field_simp
  have h3 : (P.R γ z) ^ 2 / q ≤ (P.R γ z) ^ 2 := div_le_self (sq_nonneg _) hq1
  have h4 : 0 ≤ (I / q) ^ 2 * q := by positivity
  rw [h2]
  linarith

end Lemma46

end Setting

end GPDYS

end
