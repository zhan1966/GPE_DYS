import GPDYS.Constants
import GPDYS.Step

/-!
# Positivity and the radial interval (§4.3, Lemma 4.4)

Under (C2), (C4) and the hypotheses (4.14) on `z`, namely `u > 0`, `E_h(u) ≤ E₀` and
`1 - 3γD ≤ ‖z‖₂ ≤ 1`, one step gives `z⁺ > 0` componentwise and (4.15):
`1 - 3γD ≤ ⟪u, z⁺⟫_h ≤ ‖z⁺‖₂ ≤ 1`, `‖δ‖₂² ≤ 2(1 - ⟪u, z⁺⟫_h) ≤ 6γD` and `|R| ≤ 3γD`.
-/

open Finset Matrix

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- Componentwise bound on the explicit part: `nᵢ(u) ≤ B₁ uᵢ` for `u > 0` with `E_h(u) ≤ E₀`. -/
theorem nonlin_le_B1_mul [Nonempty ι] {u0 u : ι → ℝ} (hu : P.nrm2sq u = 1)
    (hE : P.energy u ≤ P.E0 u0) (hpos : ∀ i, 0 < u i) (i : ι) :
    P.nonlin u i ≤ P.B1 u0 * u i := by
  rw [nonlin_apply]
  show P.V i * u i + P.β * u i ^ 3 ≤ (P.Vinf + P.β * P.U0 u0) * u i
  have h1 := P.le_Vinf i
  have h2 := P.sq_le_U0 hu hE i
  have h3 := hpos i
  have h4 := P.β_pos
  have e1 : P.V i * u i ≤ P.Vinf * u i := mul_le_mul_of_nonneg_right h1 h3.le
  have e2 : P.β * u i ^ 3 ≤ P.β * P.U0 u0 * u i := by
    have : u i ^ 3 = u i ^ 2 * u i := by ring
    rw [this, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h4.le) h3.le
  linarith

/-- Componentwise bound on the Laplacian: `(-Δ_h u)ᵢ ≤ Λ_d uᵢ` for `u > 0`. -/
theorem negLap_le_Λd_mul {u : ι → ℝ} (hpos : ∀ i, 0 < u i) (i : ι) :
    P.negLap u i ≤ P.Λd * u i := by
  rw [negLap_apply]
  have hw := P.w_pos i
  have hui := hpos i
  have hS : (P.S *ᵥ u) i ≤ P.S i i * u i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have : ∑ j ∈ Finset.univ.erase i, P.S i j * u j ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      exact mul_nonpos_of_nonpos_of_nonneg (P.S_offdiag i j (Ne.symm hji)) (hpos j).le
    linarith
  have hΛ := P.le_Λd i
  rw [div_le_iff₀ hw]
  calc (P.S *ᵥ u) i ≤ P.S i i * u i := hS
    _ = (P.S i i / P.w i) * u i * P.w i := by field_simp
    _ ≤ P.Λd * u i * P.w i := by
        apply mul_le_mul_of_nonneg_right _ hw.le
        exact mul_le_mul_of_nonneg_right hΛ hui.le

/-- `n(u) ≥ 0` for `u ≥ 0`. -/
theorem nonlin_nonneg {u : ι → ℝ} (hpos : ∀ i, 0 ≤ u i) (i : ι) : 0 ≤ P.nonlin u i := by
  rw [nonlin_apply]
  have := P.V_nonneg i; have := P.β_pos; have := hpos i
  positivity

/-- (4.16): `z⁺ = (‖z‖₂ - 1) u + (2 - ‖z‖₂) G_X⁻¹ u - γ G_X⁻¹ n(u)`. -/
theorem step_eq {γ : ℝ} {z : ι → ℝ} (hz : z ≠ 0) :
    P.step γ z = (P.nrm2 z - 1) • P.normalize z
      + (2 - P.nrm2 z) • P.resolvent γ (P.normalize z)
      - γ • P.resolvent γ (P.nonlin (P.normalize z)) := by
  have key : ∀ (c : ℝ) (u n : ι → ℝ),
      c • u + P.resolvent γ ((2 : ℝ) • u - c • u - γ • n) - u
        = (c - 1) • u + (2 - c) • P.resolvent γ u - γ • P.resolvent γ n := by
    intro c u n
    rw [show (2 : ℝ) • u - c • u - γ • n = (2 - c) • u - γ • n by module,
      resolvent_sub, resolvent_smul, resolvent_smul]
    module
  have h := key (P.nrm2 z) (P.normalize z) (P.nonlin (P.normalize z))
  rw [P.nrm2_smul_normalize hz] at h
  rw [step, xi]
  exact h

section Lemma44

variable [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ} (hγ : 0 < γ)
  (hC2 : γ * P.D u0 ≤ 1 / 128) (hC4 : γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1)
  {z : ι → ℝ} (hz : z ≠ 0) (hpos : ∀ i, 0 < P.normalize z i)
  (hE : P.energy (P.normalize z) ≤ P.E0 u0)
  (hz1 : 1 - 3 * γ * P.D u0 ≤ P.nrm2 z) (hz2 : P.nrm2 z ≤ 1)
include hγ hC2 hC4 hz hpos hE hz1 hz2

-- The hypotheses of Lemma 4.4 are deliberately shared by all of its assertions (via `include`),
-- even by those which do not need every one of them.
set_option linter.unusedSectionVars false

/-- `G_X z⁺ ≥ 0` componentwise, by (C4). -/
theorem GX_step_nonneg (i : ι) : 0 ≤ P.GX γ (P.step γ z) i := by
  rw [P.GX_step hγ.le hz]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hn := P.nonlin_le_B1_mul hu hE hpos i
  have hL := P.negLap_le_Λd_mul hpos i
  have hΛ := P.Λd_nonneg
  have hD : 0 ≤ P.D u0 := add_nonneg (P.E0_nonneg u0) (P.B0_nonneg u0)
  have hui := hpos i
  have hc1 : 0 ≤ 1 - P.nrm2 z := by linarith
  have hc2 : 1 - P.nrm2 z ≤ 3 * γ * P.D u0 := by linarith
  have e1 : γ * P.nonlin (P.normalize z) i ≤ γ * P.B1 u0 * P.normalize z i := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hn hγ.le
  have e2 : γ * (1 - P.nrm2 z) * P.negLap (P.normalize z) i
      ≤ 3 * γ ^ 2 * P.D u0 * P.Λd * P.normalize z i := by
    calc γ * (1 - P.nrm2 z) * P.negLap (P.normalize z) i
        ≤ γ * (1 - P.nrm2 z) * (P.Λd * P.normalize z i) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ ≤ γ * (3 * γ * P.D u0) * (P.Λd * P.normalize z i) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hc2 hγ.le
      _ = 3 * γ ^ 2 * P.D u0 * P.Λd * P.normalize z i := by ring
  have e3 : 0 ≤ P.normalize z i * (1 - (γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd)) :=
    mul_nonneg hui.le (by linarith)
  linarith

/-- `G_X z⁺ ≠ 0`, by (C2). -/
theorem GX_step_ne_zero : P.GX γ (P.step γ z) ≠ 0 := by
  intro h0
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have key : P.inner (P.GX γ (P.step γ z)) (P.normalize z)
      = 1 - γ * P.inner (P.nonlin (P.normalize z)) (P.normalize z)
        - γ * (1 - P.nrm2 z) * P.kin (P.normalize z) := by
    rw [P.GX_step hγ.le hz, inner_sub_left, inner_sub_left, inner_smul_left, inner_smul_left,
      negLap_inner, ← nrm2sq_def, hu, kin_def]
  rw [h0, inner_zero_left] at key
  have h1 := P.inner_nonlin_self_le hu hE
  have h2 := P.B0_le_D u0
  have h3 := P.kin_le_two_E0 hu hE
  have h4 := P.E0_le_D u0
  have hD : 0 ≤ P.D u0 := add_nonneg (P.E0_nonneg u0) (P.B0_nonneg u0)
  have hc1 : 0 ≤ 1 - P.nrm2 z := by linarith
  have hc2 : 1 - P.nrm2 z ≤ 3 * γ * P.D u0 := by linarith
  have hkin := P.kin_nonneg (P.normalize z)
  have e1 : γ * P.inner (P.nonlin (P.normalize z)) (P.normalize z) ≤ γ * P.D u0 :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hγ.le
  have e2 : γ * (1 - P.nrm2 z) * P.kin (P.normalize z)
      ≤ γ * (3 * γ * P.D u0) * (2 * P.D u0) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hc2 hγ.le) (h3.trans (by linarith)) hkin
      (by positivity)
  have e4 : 0 ≤ γ * P.D u0 := by positivity
  have e5 : (γ * P.D u0) * (γ * P.D u0) ≤ (1 / 128) * (1 / 128) :=
    mul_le_mul hC2 hC2 e4 (by norm_num)
  nlinarith

/-- Lemma 4.4: `z⁺ > 0` componentwise. -/
theorem step_pos (i : ι) : 0 < P.step γ z i := by
  have h := P.resolvent_pos_of_nonneg hγ (P.GX_step_nonneg hγ hC2 hC4 hz hpos hE hz1 hz2)
    (P.GX_step_ne_zero hγ hC2 hC4 hz hpos hE hz1 hz2) i
  rwa [P.resolvent_GX hγ.le] at h

theorem step_ne_zero : P.step γ z ≠ 0 :=
  GPDYS.ne_zero_of_pos (P.step_pos hγ hC2 hC4 hz hpos hE hz1 hz2)

/-- Lemma 4.4: `‖z⁺‖₂ ≤ 1`. -/
theorem nrm2_step_le_one : P.nrm2 (P.step γ z) ≤ 1 := by
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hD : 0 ≤ P.D u0 := add_nonneg (P.E0_nonneg u0) (P.B0_nonneg u0)
  have hstep := P.step_eq (γ := γ) hz
  have hspos := P.step_pos hγ hC2 hC4 hz hpos hE hz1 hz2
  have hres : ∀ i, 0 ≤ P.resolvent γ (P.nonlin (P.normalize z)) i :=
    P.resolvent_nonneg_of_nonneg hγ.le (P.nonlin_nonneg (fun i => (hpos i).le))
  have hle : ∀ i, P.step γ z i
      ≤ ((P.nrm2 z - 1) • P.normalize z + (2 - P.nrm2 z) • P.resolvent γ (P.normalize z)) i := by
    intro i
    rw [hstep]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := mul_nonneg hγ.le (hres i)
    linarith
  have h1 := P.nrm2sq_le_nrm2sq_of_le (fun i => (hspos i).le) hle
  have h2 := P.nrm2sq_contraction hγ.le (a := P.nrm2 z - 1) (by linarith) (by linarith)
    (P.normalize z)
  rw [show (1 - (P.nrm2 z - 1)) = 2 - P.nrm2 z by ring, hu] at h2
  apply P.nrm2_le_of_nrm2sq_le zero_le_one
  rw [one_pow]
  exact h1.trans h2

/-- `1 - ⟪u, z⁺⟫_h = (2 - ‖z‖₂)(1 - ‖u‖_X²) + γ ⟪G_X⁻¹ u, n(u)⟫_h`. -/
theorem one_sub_inner_step_eq :
    1 - P.inner (P.normalize z) (P.step γ z)
      = (2 - P.nrm2 z) * (1 - P.nrmXsq γ (P.normalize z))
        + γ * P.inner (P.resolvent γ (P.normalize z)) (P.nonlin (P.normalize z)) := by
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hsym : P.inner (P.normalize z) (P.resolvent γ (P.nonlin (P.normalize z)))
      = P.inner (P.resolvent γ (P.normalize z)) (P.nonlin (P.normalize z)) := by
    have := P.innerX_comm hγ.le (P.normalize z) (P.nonlin (P.normalize z))
    rw [innerX_def, innerX_def] at this
    rw [this, inner_comm]
  rw [P.step_eq hz, inner_sub_right, inner_add_right, inner_smul_right, inner_smul_right,
    inner_smul_right, ← nrm2sq_def, hu, ← nrmXsq_def, hsym]
  ring

/-- Lemma 4.4: `0 ≤ 1 - ⟪u, z⁺⟫_h`. -/
theorem one_sub_inner_step_nonneg : 0 ≤ 1 - P.inner (P.normalize z) (P.step γ z) := by
  rw [P.one_sub_inner_step_eq hγ hC2 hC4 hz hpos hE hz1 hz2]
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have h1 : P.nrmXsq γ (P.normalize z) ≤ 1 := by
    have := P.nrmXsq_le_nrm2sq hγ.le (P.normalize z); rwa [hu] at this
  have h2 : 0 ≤ P.inner (P.resolvent γ (P.normalize z)) (P.nonlin (P.normalize z)) := by
    rw [inner_def]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (P.w_pos i).le (mul_nonneg
      (P.resolvent_nonneg_of_nonneg hγ.le (fun j => (hpos j).le) i)
      (P.nonlin_nonneg (fun j => (hpos j).le) i))
  have h3 : 0 ≤ 2 - P.nrm2 z := by linarith
  have := mul_nonneg h3 (sub_nonneg.mpr h1)
  have := mul_nonneg hγ.le h2
  linarith

/-- Lemma 4.4: `1 - ⟪u, z⁺⟫_h ≤ 3γD`. -/
theorem one_sub_inner_step_le : 1 - P.inner (P.normalize z) (P.step γ z) ≤ 3 * γ * P.D u0 := by
  rw [P.one_sub_inner_step_eq hγ hC2 hC4 hz hpos hE hz1 hz2]
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hE0 := P.E0_nonneg u0
  have hB0 := P.B0_nonneg u0
  have hE0D := P.E0_le_D u0
  have hD : 0 ≤ P.D u0 := add_nonneg hE0 hB0
  have h1 : 1 - P.nrmXsq γ (P.normalize z) ≤ γ * (2 * P.E0 u0) := by
    have := P.nrm2sq_sub_nrmXsq_le hγ.le (P.normalize z)
    rw [hu] at this
    exact this.trans (mul_le_mul_of_nonneg_left (P.kin_le_two_E0 hu hE) hγ.le)
  have h1' : 0 ≤ 1 - P.nrmXsq γ (P.normalize z) := by
    have := P.nrmXsq_le_nrm2sq hγ.le (P.normalize z); rw [hu] at this; linarith
  have h2 : P.inner (P.resolvent γ (P.normalize z)) (P.nonlin (P.normalize z)) ≤ P.B0 u0 := by
    have hcs := P.inner_le_nrm2_mul_nrm2 (P.resolvent γ (P.normalize z))
      (P.nonlin (P.normalize z))
    have hr : P.nrm2 (P.resolvent γ (P.normalize z)) ≤ 1 := by
      apply P.nrm2_le_of_nrm2sq_le zero_le_one
      rw [one_pow]
      calc P.nrm2sq (P.resolvent γ (P.normalize z))
          ≤ P.nrmXsq γ (P.normalize z) := P.nrm2sq_resolvent_le_nrmXsq hγ.le _
        _ ≤ P.nrm2sq (P.normalize z) := P.nrmXsq_le_nrm2sq hγ.le _
        _ = 1 := hu
    have hn := P.nrm2_nonlin_le hu hE
    have hn0 := P.nrm2_nonneg (P.nonlin (P.normalize z))
    calc P.inner (P.resolvent γ (P.normalize z)) (P.nonlin (P.normalize z))
        ≤ P.nrm2 (P.resolvent γ (P.normalize z)) * P.nrm2 (P.nonlin (P.normalize z)) := hcs
      _ ≤ 1 * P.B0 u0 := mul_le_mul hr hn hn0 zero_le_one
      _ = P.B0 u0 := one_mul _
  have hc1 : 0 ≤ 1 - P.nrm2 z := by linarith
  have hc2 : 1 - P.nrm2 z ≤ 3 * γ * P.D u0 := by linarith
  have h3 : (2 - P.nrm2 z) * (1 - P.nrmXsq γ (P.normalize z))
      ≤ (1 + 3 * γ * P.D u0) * (γ * (2 * P.E0 u0)) :=
    mul_le_mul (by linarith) h1 h1' (by positivity)
  have h4 : γ * P.inner (P.resolvent γ (P.normalize z)) (P.nonlin (P.normalize z))
      ≤ γ * P.B0 u0 := mul_le_mul_of_nonneg_left h2 hγ.le
  have h5 : γ * P.D u0 * (γ * P.D u0) ≤ (1 / 128) * (γ * P.D u0) :=
    mul_le_mul_of_nonneg_right hC2 (by positivity)
  have h6 : γ * P.D u0 * (γ * P.E0 u0) ≤ γ * P.D u0 * (γ * P.D u0) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE0D hγ.le) (by positivity)
  have h7 : γ * P.E0 u0 ≤ γ * P.D u0 := mul_le_mul_of_nonneg_left hE0D hγ.le
  have h8 : γ * P.D u0 = γ * P.E0 u0 + γ * P.B0 u0 := by
    show γ * (P.E0 u0 + P.B0 u0) = _; ring
  nlinarith

/-- Lemma 4.4: `⟪u, z⁺⟫_h ≤ ‖z⁺‖₂`. -/
theorem inner_step_le_nrm2 : P.inner (P.normalize z) (P.step γ z) ≤ P.nrm2 (P.step γ z) := by
  have := P.inner_le_nrm2_mul_nrm2 (P.normalize z) (P.step γ z)
  rwa [P.nrm2_normalize hz, one_mul] at this

/-- Lemma 4.4: `1 - 3γD ≤ ‖z⁺‖₂`. -/
theorem nrm2_step_ge : 1 - 3 * γ * P.D u0 ≤ P.nrm2 (P.step γ z) := by
  have h1 := P.one_sub_inner_step_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have h2 := P.inner_step_le_nrm2 hγ hC2 hC4 hz hpos hE hz1 hz2
  linarith

/-- Lemma 4.4: `‖δ‖₂² ≤ 2 (1 - ⟪u, z⁺⟫_h)`. -/
theorem nrm2sq_delta_le_two_mul :
    P.nrm2sq (P.delta γ z) ≤ 2 * (1 - P.inner (P.normalize z) (P.step γ z)) := by
  have hzp := P.step_ne_zero hγ hC2 hC4 hz hpos hE hz1 hz2
  rw [P.nrm2sq_delta_eq hz hzp]
  have hn1 := P.nrm2_step_le_one hγ hC2 hC4 hz hpos hE hz1 hz2
  have hnpos := P.nrm2_pos_of_ne_zero hzp
  have hi := P.one_sub_inner_step_le hγ hC2 hC4 hz hpos hE hz1 hz2
  have hD : 0 ≤ P.D u0 := add_nonneg (P.E0_nonneg u0) (P.B0_nonneg u0)
  have hipos : 0 ≤ P.inner (P.normalize z) (P.step γ z) := by linarith
  have : P.inner (P.normalize z) (P.step γ z)
      ≤ P.inner (P.normalize z) (P.step γ z) / P.nrm2 (P.step γ z) := by
    rw [le_div_iff₀ hnpos]
    exact mul_le_of_le_one_right hipos hn1
  linarith

/-- Lemma 4.4: `‖δ‖₂² ≤ 6γD`. -/
theorem nrm2sq_delta_le : P.nrm2sq (P.delta γ z) ≤ 6 * γ * P.D u0 := by
  have h1 := P.nrm2sq_delta_le_two_mul hγ hC2 hC4 hz hpos hE hz1 hz2
  have h2 := P.one_sub_inner_step_le hγ hC2 hC4 hz hpos hE hz1 hz2
  linarith

/-- Lemma 4.4: `|R| ≤ 3γD`. -/
theorem abs_R_le : |P.R γ z| ≤ 3 * γ * P.D u0 := by
  rw [R_def]
  have hu : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have h1 := P.lam_nonneg (P.normalize z)
  have h2 := P.lam_le_two_D hu hE
  have hD : 0 ≤ P.D u0 := add_nonneg (P.E0_nonneg u0) (P.B0_nonneg u0)
  have h3 : 0 ≤ γ * P.lam (P.normalize z) := mul_nonneg hγ.le h1
  have h4 : γ * P.lam (P.normalize z) ≤ γ * (2 * P.D u0) := mul_le_mul_of_nonneg_left h2 hγ.le
  have h5 : 0 ≤ γ * P.D u0 := mul_nonneg hγ.le hD
  rw [abs_le]
  constructor <;> linarith

end Lemma44

end Setting

end GPDYS

end
