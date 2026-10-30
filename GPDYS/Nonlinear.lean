import GPDYS.Constants
import GPDYS.Step

/-!
# Estimates for the explicit part (§4.2, Lemma 4.3)

For unit vectors `u, u⁺` of energy at most `E₀` and `δ = u⁺ - u`, Lemma 4.3 bounds the Taylor
remainder `𝒯(u, δ)` and the difference `⟪n(u⁺) - n(u), u⁺⟫_h`:

* `γ 𝒯(u, δ) ≤ (1/16) ‖δ‖_𝒢²` under (C3), by whichever of the pointwise bound (4.12) and the
  Sobolev bound (4.13) is better;
* `|⟪n(u⁺) - n(u), u⁺⟫_h| ≤ 3 B₀ ‖δ‖₂`.

The remainder is handled through its explicit polynomial form (`taylorT_eq`) instead of the
integral representation (4.2); the pointwise and Sobolev bounds are the ones of the paper.
-/

open Finset

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- The elementary inequality behind (4.13), for `0 ≤ x ≤ y` and an arbitrary real `C₀`
(no sign condition on `C₀` is needed):
`C₀ x y ≤ (C₀ + 2 max{C₀ - 1/4, 0}²) x² + (y² - x²)/8`. -/
theorem sobolev_quadratic_bound_aux (C0 : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    C0 * x * y ≤ (C0 + 2 * (max (C0 - 1 / 4) 0) ^ 2) * x ^ 2 + (y ^ 2 - x ^ 2) / 8 := by
  rcases le_or_gt (1 / 4) C0 with h | h
  · -- `C₀ ≥ 1/4`: the difference is `(y - 4 C₀ x)² / 8`
    rw [max_eq_left (by linarith)]
    nlinarith [sq_nonneg (y - 4 * C0 * x)]
  · -- `C₀ < 1/4`: the difference is `(y - x) ((y + x)/8 - C₀ x)`
    rw [max_eq_right (by linarith)]
    have h1 : 0 ≤ y - x := sub_nonneg.2 hxy
    have h2 : 0 ≤ (y + x) / 8 - C0 * x := by nlinarith
    nlinarith [mul_nonneg h1 h2]

section Lemma43

variable {u0 : ι → ℝ} {u up : ι → ℝ}
  (hu : P.nrm2sq u = 1) (hup : P.nrm2sq up = 1)
  (hEu : P.energy u ≤ P.E0 u0) (hEup : P.energy up ≤ P.E0 u0)
include hu hup hEu hEup

/-- The Taylor-remainder consequence of the pointwise Jacobian bound (4.12):
 `𝒯(u, δ) ≤ ½ (‖V‖_∞ + 3β U₀) ‖δ‖₂²`. -/
theorem taylorT_le_pointwise [Nonempty ι] :
    P.taylorT u (up - u) ≤ (1 / 2) * (P.Vinf + 3 * P.β * P.U0 u0) * P.nrm2sq (up - u) := by
  rw [taylorT_eq, nrm2sq_eq_sum]
  have hw : ∀ i, 0 ≤ P.w i := fun i => (P.w_pos i).le
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
  -- the cubic term: `3uᵢ² + 2uᵢδᵢ + δᵢ²/2 = (3/2)uᵢ² + uᵢu⁺ᵢ + (u⁺ᵢ)²/2 ≤ 2uᵢ² + (u⁺ᵢ)² ≤ 3U₀`
  have hβ : ∑ i, P.w i * ((up - u) i ^ 2 * (3 * u i ^ 2
        + 2 * u i * (up - u) i + (up - u) i ^ 2 / 2))
      ≤ 3 * P.U0 u0 * ∑ i, P.w i * (up - u) i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := P.sq_le_U0 hu hEu i
    have h2 := P.sq_le_U0 hup hEup i
    have h3 := hw i
    simp only [Pi.sub_apply]
    have key : 3 * u i ^ 2 + 2 * u i * (up i - u i) + (up i - u i) ^ 2 / 2 ≤ 3 * P.U0 u0 := by
      nlinarith [sq_nonneg (u i - up i)]
    have h4 := sq_nonneg (up i - u i)
    calc P.w i * ((up i - u i) ^ 2 * (3 * u i ^ 2 + 2 * u i * (up i - u i) + (up i - u i) ^ 2 / 2))
        ≤ P.w i * ((up i - u i) ^ 2 * (3 * P.U0 u0)) := by
          apply mul_le_mul_of_nonneg_left _ h3
          exact mul_le_mul_of_nonneg_left key h4
      _ = 3 * P.U0 u0 * (P.w i * (up i - u i) ^ 2) := by ring
  have hβpos := P.β_pos
  calc (1 / 2) * ∑ i, P.w i * (P.V i * (up - u) i ^ 2)
        + P.β / 2 * ∑ i, P.w i * ((up - u) i ^ 2 * (3 * u i ^ 2
          + 2 * u i * (up - u) i + (up - u) i ^ 2 / 2))
      ≤ (1 / 2) * (P.Vinf * ∑ i, P.w i * (up - u) i ^ 2)
        + P.β / 2 * (3 * P.U0 u0 * ∑ i, P.w i * (up - u) i ^ 2) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hV (by norm_num)
          · exact mul_le_mul_of_nonneg_left hβ (by positivity)
    _ = (1 / 2) * (P.Vinf + 3 * P.β * P.U0 u0) * ∑ i, P.w i * (up - u) i ^ 2 := by ring

/-- The Taylor-remainder consequence of the first Jacobian bound in (4.13):
`𝒯(u, δ) ≤ ½ (‖V‖_∞ ‖δ‖₂² + C₀ ‖δ‖₂ ‖δ‖_{1,h})`, with `‖δ‖_{1,h} = √(⟪δ,-Δ_h δ⟫_h + ‖δ‖₂²)`. -/
theorem taylorT_le_sobolev [Nonempty ι] :
    P.taylorT u (up - u) ≤ (1 / 2) * (P.Vinf * P.nrm2sq (up - u)
      + P.C0 u0 * P.nrm2 (up - u) * Real.sqrt (P.kin (up - u) + P.nrm2sq (up - u))) := by
  rw [taylorT_eq]
  set d := up - u with hd
  have hw : ∀ i, 0 ≤ P.w i := fun i => (P.w_pos i).le
  -- the potential term: `Vᵢ ≤ ‖V‖_∞`
  have hV : ∑ i, P.w i * (P.V i * d i ^ 2) ≤ P.Vinf * P.nrm2sq d := by
    rw [nrm2sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 := P.le_Vinf i
    have h2 := hw i
    have h3 := sq_nonneg (d i)
    calc P.w i * (P.V i * d i ^ 2) ≤ P.w i * (P.Vinf * d i ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ h2
          exact mul_le_mul_of_nonneg_right h1 h3
      _ = P.Vinf * (P.w i * d i ^ 2) := by ring
  -- Hölder: `∑ w u² δ² ≤ ‖u‖₆² ‖δ‖₃² ≤ P₀ ‖δ‖₃²`, and the same for `u⁺`
  have hA : ∑ i, P.w i * (u i ^ 2 * d i ^ 2) ≤ P.P0 u0 * wnorm3 P.w d ^ 2 :=
    calc ∑ i, P.w i * (u i ^ 2 * d i ^ 2) ≤ wnorm6 P.w u ^ 2 * wnorm3 P.w d ^ 2 :=
          holder_six_three P.w hw u d
      _ ≤ P.P0 u0 * wnorm3 P.w d ^ 2 :=
          mul_le_mul_of_nonneg_right (P.wnorm6_sq_le_P0 hu hEu) (sq_nonneg _)
  have hB : ∑ i, P.w i * (up i ^ 2 * d i ^ 2) ≤ P.P0 u0 * wnorm3 P.w d ^ 2 :=
    calc ∑ i, P.w i * (up i ^ 2 * d i ^ 2) ≤ wnorm6 P.w up ^ 2 * wnorm3 P.w d ^ 2 :=
          holder_six_three P.w hw up d
      _ ≤ P.P0 u0 * wnorm3 P.w d ^ 2 :=
          mul_le_mul_of_nonneg_right (P.wnorm6_sq_le_P0 hup hEup) (sq_nonneg _)
  -- pointwise: `δ² (3u² + 2uδ + δ²/2) ≤ 2u²δ² + (u⁺)²δ²` (the difference is `δ²(u - u⁺)²/2`)
  have hterm : ∑ i, P.w i * (d i ^ 2 * (3 * u i ^ 2 + 2 * u i * d i + d i ^ 2 / 2))
      ≤ 2 * ∑ i, P.w i * (u i ^ 2 * d i ^ 2) + ∑ i, P.w i * (up i ^ 2 * d i ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hdi : d i = up i - u i := by simp [hd]
    have h1 : 2 * (P.w i * (u i ^ 2 * d i ^ 2)) + P.w i * (up i ^ 2 * d i ^ 2)
        - P.w i * (d i ^ 2 * (3 * u i ^ 2 + 2 * u i * d i + d i ^ 2 / 2))
        = P.w i * d i ^ 2 * (u i - up i) ^ 2 / 2 := by
      rw [hdi]; ring
    have h2 : 0 ≤ P.w i * d i ^ 2 * (u i - up i) ^ 2 / 2 := by
      have := hw i
      positivity
    linarith
  -- Hölder and Sobolev: `‖δ‖₃² ≤ ‖δ‖₂ ‖δ‖₆ ≤ ‖δ‖₂ C_S ‖δ‖_{1,h}`
  have h3 : wnorm3 P.w d ^ 2 ≤ P.nrm2 d * (P.CS * Real.sqrt (P.kin d + P.nrm2sq d)) :=
    calc wnorm3 P.w d ^ 2 ≤ wnorm2 P.w d * wnorm6 P.w d := wnorm3_sq_le P.w hw d
      _ ≤ wnorm2 P.w d * (P.CS * Real.sqrt (P.kin d + P.nrm2sq d)) :=
          mul_le_mul_of_nonneg_left (P.sobolev d) (Real.sqrt_nonneg _)
  have hP0 := P.P0_nonneg u0
  have hβ := P.β_pos
  have hβterm : ∑ i, P.w i * (d i ^ 2 * (3 * u i ^ 2 + 2 * u i * d i + d i ^ 2 / 2))
      ≤ 3 * P.P0 u0 * (P.nrm2 d * (P.CS * Real.sqrt (P.kin d + P.nrm2sq d))) :=
    calc ∑ i, P.w i * (d i ^ 2 * (3 * u i ^ 2 + 2 * u i * d i + d i ^ 2 / 2))
        ≤ 2 * (P.P0 u0 * wnorm3 P.w d ^ 2) + P.P0 u0 * wnorm3 P.w d ^ 2 := by linarith
      _ = 3 * P.P0 u0 * wnorm3 P.w d ^ 2 := by ring
      _ ≤ 3 * P.P0 u0 * (P.nrm2 d * (P.CS * Real.sqrt (P.kin d + P.nrm2sq d))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
  calc (1 / 2) * ∑ i, P.w i * (P.V i * d i ^ 2)
        + P.β / 2 * ∑ i, P.w i * (d i ^ 2 * (3 * u i ^ 2 + 2 * u i * d i + d i ^ 2 / 2))
      ≤ (1 / 2) * (P.Vinf * P.nrm2sq d)
        + P.β / 2 * (3 * P.P0 u0 * (P.nrm2 d * (P.CS * Real.sqrt (P.kin d + P.nrm2sq d)))) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hV (by norm_num)
          · exact mul_le_mul_of_nonneg_left hβterm (by positivity)
    _ = (1 / 2) * (P.Vinf * P.nrm2sq d
        + P.C0 u0 * P.nrm2 d * Real.sqrt (P.kin d + P.nrm2sq d)) := by
          unfold C0; ring

/-- Lemma 4.3, first inequality (4.11): `γ 𝒯(u, δ) ≤ (1/16) ‖δ‖_𝒢²` under (C3). -/
theorem taylorT_le [Nonempty ι] {γ : ℝ} (hγ : 0 ≤ γ) (hC3 : γ * P.L0 u0 ≤ 1 / 8) :
    γ * P.taylorT u (up - u) ≤ (1 / 16) * P.nrmGsq γ (up - u) := by
  have hT1 := P.taylorT_le_pointwise hu hup hEu hEup
  have hT2 := P.taylorT_le_sobolev hu hup hEu hEup
  set d := up - u with hd
  have hVinf := P.Vinf_nonneg
  have hβ := P.β_pos
  have hkin := P.kin_nonneg d
  have hn2 := P.nrm2sq_nonneg d
  have hn := P.nrm2_nonneg d
  have hG : P.nrmGsq γ d = P.nrm2sq d + γ * P.kin d := P.nrmGsq_def γ d
  have hmax : 0 ≤ 2 * (max (P.C0 u0 - 1 / 4) 0) ^ 2 := by positivity
  have hL0 : P.L0 u0 = P.Vinf
      + min (3 * P.β * P.U0 u0) (P.C0 u0 + 2 * (max (P.C0 u0 - 1 / 4) 0) ^ 2) := rfl
  rw [hG]
  rcases le_total (3 * P.β * P.U0 u0) (P.C0 u0 + 2 * (max (P.C0 u0 - 1 / 4) 0) ^ 2) with h | h
  · -- the pointwise bound is the better one: `γ (‖V‖_∞ + 3βU₀) ≤ 1/8`
    rw [hL0, min_eq_left h] at hC3
    have h1 : γ * P.taylorT u d ≤ γ * ((1 / 2) * (P.Vinf + 3 * P.β * P.U0 u0) * P.nrm2sq d) :=
      mul_le_mul_of_nonneg_left hT1 hγ
    have h2 : γ * (P.Vinf + 3 * P.β * P.U0 u0) * P.nrm2sq d ≤ (1 / 8) * P.nrm2sq d :=
      mul_le_mul_of_nonneg_right hC3 hn2
    have h3 : 0 ≤ γ * P.kin d := mul_nonneg hγ hkin
    nlinarith
  · -- the Sobolev bound is the better one: `γ (‖V‖_∞ + C₀ + 2 max{C₀ - 1/4, 0}²) ≤ 1/8`
    rw [hL0, min_eq_right h] at hC3
    set x := P.nrm2 d with hx
    set y := Real.sqrt (P.kin d + P.nrm2sq d) with hy
    have hx2 : x ^ 2 = P.nrm2sq d := P.nrm2_sq d
    have hy2 : y ^ 2 = P.kin d + P.nrm2sq d := Real.sq_sqrt (by positivity)
    have hxy : x ≤ y := by
      rw [hx, hy, nrm2_def]
      exact Real.sqrt_le_sqrt (by linarith)
    have hq := sobolev_quadratic_bound_aux (P.C0 u0) hn hxy
    rw [hx2, hy2] at hq
    have h1 : γ * P.taylorT u d ≤ γ * ((1 / 2) * (P.Vinf * P.nrm2sq d + P.C0 u0 * x * y)) :=
      mul_le_mul_of_nonneg_left hT2 hγ
    have h2 : γ * (P.Vinf + (P.C0 u0 + 2 * (max (P.C0 u0 - 1 / 4) 0) ^ 2)) * P.nrm2sq d
        ≤ (1 / 8) * P.nrm2sq d :=
      mul_le_mul_of_nonneg_right hC3 hn2
    have h3 : γ * (P.C0 u0 * x * y)
        ≤ γ * ((P.C0 u0 + 2 * (max (P.C0 u0 - 1 / 4) 0) ^ 2) * P.nrm2sq d + P.kin d / 8) :=
      mul_le_mul_of_nonneg_left (by linarith) hγ
    nlinarith

/-- The mixed cubes: `‖a b²‖₂ ≤ min{P₀^{3/2}, U₀}` for unit vectors `a, b` of energy at most `E₀`
(here applied to the pairs `(u, u⁺)`, `(u⁺, u)` and `(u⁺, u⁺)`). -/
theorem nrm2_mixed_cube_le [Nonempty ι] :
    P.nrm2 (fun i => u i * up i ^ 2) ≤ min (P.P0 u0 ^ ((3 : ℝ) / 2)) (P.U0 u0) := by
  have hw : ∀ i, 0 ≤ P.w i := fun i => (P.w_pos i).le
  have hP0 := P.P0_nonneg u0
  have hU0 : 0 ≤ P.U0 u0 :=
    le_trans (sq_nonneg _) (P.sq_le_U0 hu hEu (Classical.arbitrary ι))
  have hsum : P.nrm2sq (fun i => u i * up i ^ 2) = ∑ i, P.w i * (u i ^ 2 * (up i ^ 2) ^ 2) := by
    simp only [nrm2sq_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  refine le_min ?_ ?_
  · -- Hölder: `∑ w u² (u⁺)⁴ ≤ ‖u‖₆² ‖(u⁺)²‖₃² = ‖u‖₆² (‖u⁺‖₆²)² ≤ P₀³`
    apply P.nrm2_le_of_nrm2sq_le (Real.rpow_nonneg hP0 _)
    rw [hsum]
    have h1 : ∑ i, P.w i * (u i ^ 2 * (up i ^ 2) ^ 2)
        ≤ wnorm6 P.w u ^ 2 * wnorm3 P.w (fun i => up i ^ 2) ^ 2 :=
      holder_six_three P.w hw u (fun i => up i ^ 2)
    rw [wnorm3_sq_eq P.w hw up] at h1
    have h2 := P.wnorm6_sq_le_P0 hu hEu
    have h3 := P.wnorm6_sq_le_P0 hup hEup
    have h6 : 0 ≤ wnorm6 P.w up ^ 2 := sq_nonneg _
    have hpow : (P.P0 u0 ^ ((3 : ℝ) / 2)) ^ 2 = P.P0 u0 ^ 3 := by
      rw [← Real.rpow_mul_natCast hP0]
      norm_num
    rw [hpow]
    calc ∑ i, P.w i * (u i ^ 2 * (up i ^ 2) ^ 2) ≤ wnorm6 P.w u ^ 2 * (wnorm6 P.w up ^ 2) ^ 2 := h1
      _ ≤ P.P0 u0 * P.P0 u0 ^ 2 :=
          mul_le_mul h2 (pow_le_pow_left₀ h6 h3 2) (by positivity) hP0
      _ = P.P0 u0 ^ 3 := by ring
  · -- pointwise: `u² (u⁺)⁴ ≤ U₀² (u⁺)²` and `‖u⁺‖₂ = 1`
    apply P.nrm2_le_of_nrm2sq_le hU0
    rw [hsum]
    have hup' : ∑ i, P.w i * up i ^ 2 = 1 := by rw [← nrm2sq_eq_sum]; exact hup
    calc ∑ i, P.w i * (u i ^ 2 * (up i ^ 2) ^ 2)
        ≤ ∑ i, P.w i * (P.U0 u0 * (P.U0 u0 * up i ^ 2)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := P.sq_le_U0 hu hEu i
          have h2 := P.sq_le_U0 hup hEup i
          have hsq := sq_nonneg (up i)
          apply mul_le_mul_of_nonneg_left _ (hw i)
          calc u i ^ 2 * (up i ^ 2) ^ 2 = u i ^ 2 * up i ^ 2 * up i ^ 2 := by ring
            _ ≤ P.U0 u0 * P.U0 u0 * up i ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ hsq
              exact mul_le_mul h1 h2 hsq hU0
            _ = P.U0 u0 * (P.U0 u0 * up i ^ 2) := by ring
      _ = P.U0 u0 ^ 2 * ∑ i, P.w i * up i ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ = P.U0 u0 ^ 2 := by rw [hup']; ring

/-- Lemma 4.3, second inequality (4.11): `|⟪n(u⁺) - n(u), u⁺⟫_h| ≤ 3 B₀ ‖δ‖₂`. -/
theorem abs_inner_nonlin_sub_le [Nonempty ι] :
    |P.inner (P.nonlin up - P.nonlin u) up| ≤ 3 * P.B0 u0 * P.nrm2 (up - u) := by
  have hβ := P.β_pos
  have hVinf := P.Vinf_nonneg
  have hn := P.nrm2_nonneg (up - u)
  -- `⟪n(u⁺) - n(u), u⁺⟫_h = ⟪δ, V u⁺⟫_h + β ⟪δ, (u⁺)³⟫_h + β ⟪δ, u (u⁺)²⟫_h + β ⟪δ, u⁺ u²⟫_h`,
  -- from `(u⁺)³ - u³ = (u⁺ - u) ((u⁺)² + u u⁺ + u²)`
  have hid : P.inner (P.nonlin up - P.nonlin u) up
      = P.inner (up - u) (fun i => P.V i * up i) + P.β * P.inner (up - u) (fun i => up i ^ 3)
        + P.β * P.inner (up - u) (fun i => u i * up i ^ 2)
        + P.β * P.inner (up - u) (fun i => up i * u i ^ 2) := by
    simp only [inner_def, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, nonlin_apply]
    ring
  -- the four norms: `‖V u⁺‖₂ ≤ ‖V‖_∞`, `‖(u⁺)³‖₂, ‖u (u⁺)²‖₂, ‖u⁺ u²‖₂ ≤ min{P₀^{3/2}, U₀}`
  have hm := P.nrm2_cube_le hup hEup
  have hm2 := P.nrm2_mixed_cube_le hu hup hEu hEup
  have hm3 : P.nrm2 (fun i => up i * u i ^ 2) ≤ min (P.P0 u0 ^ ((3 : ℝ) / 2)) (P.U0 u0) :=
    P.nrm2_mixed_cube_le hup hu hEup hEu
  have hV : P.nrm2 (fun i => P.V i * up i) ≤ P.Vinf := by
    have := P.nrm2_Vmul_le up
    rwa [P.nrm2_eq_one_of_nrm2sq hup, mul_one] at this
  set m := min (P.P0 u0 ^ ((3 : ℝ) / 2)) (P.U0 u0) with hm_def
  have hm0 : 0 ≤ m := le_trans (P.nrm2_nonneg _) hm
  have hB0 : P.B0 u0 = P.Vinf + P.β * m := rfl
  -- Cauchy–Schwarz for each term
  have key : ∀ (f : ι → ℝ) (c : ℝ), P.nrm2 f ≤ c →
      |P.inner (up - u) f| ≤ P.nrm2 (up - u) * c := fun f c hc =>
    le_trans (P.abs_inner_le_nrm2_mul_nrm2 _ _) (mul_le_mul_of_nonneg_left hc hn)
  have k1 := key _ _ hV
  have k2 := key _ _ hm
  have k3 := key _ _ hm2
  have k4 := key _ _ hm3
  rw [hid, hB0]
  have habs : |P.inner (up - u) (fun i => P.V i * up i) + P.β * P.inner (up - u) (fun i => up i ^ 3)
        + P.β * P.inner (up - u) (fun i => u i * up i ^ 2)
        + P.β * P.inner (up - u) (fun i => up i * u i ^ 2)|
      ≤ |P.inner (up - u) (fun i => P.V i * up i)| + P.β * |P.inner (up - u) (fun i => up i ^ 3)|
        + P.β * |P.inner (up - u) (fun i => u i * up i ^ 2)|
        + P.β * |P.inner (up - u) (fun i => up i * u i ^ 2)| := by
    calc _ ≤ |P.inner (up - u) (fun i => P.V i * up i) + P.β * P.inner (up - u) (fun i => up i ^ 3)
        + P.β * P.inner (up - u) (fun i => u i * up i ^ 2)|
        + |P.β * P.inner (up - u) (fun i => up i * u i ^ 2)| := abs_add_le _ _
      _ ≤ |P.inner (up - u) (fun i => P.V i * up i)| + |P.β * P.inner (up - u) (fun i => up i ^ 3)|
        + |P.β * P.inner (up - u) (fun i => u i * up i ^ 2)|
        + |P.β * P.inner (up - u) (fun i => up i * u i ^ 2)| :=
          add_le_add_left (abs_add_three _ _ _) _
      _ = _ := by rw [abs_mul, abs_mul, abs_mul, abs_of_pos hβ]
  have e2 := mul_le_mul_of_nonneg_left k2 hβ.le
  have e3 := mul_le_mul_of_nonneg_left k3 hβ.le
  have e4 := mul_le_mul_of_nonneg_left k4 hβ.le
  -- `‖V‖_∞ + 3βm ≤ 3 (‖V‖_∞ + βm) = 3 B₀`, as `‖V‖_∞ ≥ 0`
  have e5 : 0 ≤ P.nrm2 (up - u) * P.Vinf := mul_nonneg hn hVinf
  nlinarith

end Lemma43

/-- The elementary inequality behind (4.13): for `0 ≤ x ≤ y`,
`C₀ x y ≤ (C₀ + 2 max{C₀ - 1/4, 0}²) x² + (y² - x²)/8`. -/
theorem sobolev_quadratic_bound (C0 : ℝ) (hC0 : 0 ≤ C0) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    C0 * x * y ≤ (C0 + 2 * (max (C0 - 1 / 4) 0) ^ 2) * x ^ 2 + (y ^ 2 - x ^ 2) / 8 :=
  sobolev_quadratic_bound_aux C0 hx hxy

end Setting

end GPDYS

end
