import GPDYS.Barrier

/-!
# The one-step estimates (Proposition 4.8)

Under `0 < γ ≤ γ_max` and the hypotheses `z ≠ 0`, `u > 0`, `1 - 3γD ≤ ‖z‖₂ ≤ 1`,
`𝓛(z) ≤ E₀`, one step gives `z⁺ > 0`, `1 - 3γD ≤ ‖z⁺‖₂ ≤ 1`, `E_h(u⁺) ≤ E₀`, and the drops
(4.31): `𝓛(z) - 𝓛(z⁺) ≥ ¼γ‖g(u)‖_X² + R²/(2γ)` and `𝓛(z) - 𝓛(z⁺) ≥ (5/(16γ))‖z⁺ - z‖_𝒢²`.
-/

open Finset

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

section Prop48

variable [Nonempty ι] {u0 : ι → ℝ} (hu0 : u0 ≠ 0) {γ : ℝ} (hγ : 0 < γ) (hγm : γ ≤ P.γmax u0)
  {z : ι → ℝ} (hz : z ≠ 0) (hpos : ∀ i, 0 < P.normalize z i)
  (hz1 : 1 - 3 * γ * P.D u0 ≤ P.nrm2 z) (hz2 : P.nrm2 z ≤ 1)
  (hL : P.lyap γ z ≤ P.E0 u0)
include hu0 hγ hγm hz hpos hz1 hz2 hL

omit hz hpos hz1 hz2 hL in
/-- The step-size conditions (C2)–(C4), unpacked. -/
theorem onestep_conditions :
    γ * P.D u0 ≤ 1 / 128 ∧ γ * P.L0 u0 ≤ 1 / 8 ∧
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 := by
  obtain ⟨_, h2, h3, h4⟩ := P.conditions_of_le_γmax u0 hu0 hγ hγm
  exact ⟨h2, h3, h4⟩

omit [Nonempty ι] hu0 hγm hz hpos hz1 hz2 in
/-- `E_h(u) ≤ E₀`. -/
theorem onestep_energy_le : P.energy (P.normalize z) ≤ P.E0 u0 :=
  (P.energy_le_lyap hγ z).trans hL

/-- Proposition 4.8: positivity of `z⁺`. -/
theorem onestep_pos (i : ι) : 0 < P.step γ z i := by
  obtain ⟨h2, _, h4⟩ := P.onestep_conditions hu0 hγ hγm
  exact P.step_pos hγ h2 h4 hz hpos (P.onestep_energy_le hγ hL) hz1 hz2 i

/-- Proposition 4.8: the radial interval for `z⁺`. -/
theorem onestep_radial : 1 - 3 * γ * P.D u0 ≤ P.nrm2 (P.step γ z) ∧ P.nrm2 (P.step γ z) ≤ 1 := by
  obtain ⟨h2, _, h4⟩ := P.onestep_conditions hu0 hγ hγm
  have hE := P.onestep_energy_le hγ hL
  exact ⟨P.nrm2_step_ge hγ h2 h4 hz hpos hE hz1 hz2, P.nrm2_step_le_one hγ h2 h4 hz hpos hE hz1 hz2⟩

/-- Proposition 4.8: `E_h(u⁺) ≤ E₀`, by the energy barrier. -/
theorem onestep_energy : P.energy (P.normalize (P.step γ z)) ≤ P.E0 u0 := by
  obtain ⟨h2, h3, h4⟩ := P.onestep_conditions hu0 hγ hγm
  exact P.energy_barrier hu0 hγ h2 h3 h4 hz hpos hz1 hz2 hL

/-- Proposition 4.8, (4.31) first inequality:
`𝓛(z) - 𝓛(z⁺) ≥ ¼ γ ‖g(u)‖_X² + R²/(2γ)`. -/
theorem onestep_drop :
    P.lyap γ z - P.lyap γ (P.step γ z)
      ≥ 1 / 4 * γ * P.nrmXsq γ (P.g (P.normalize z)) + (P.R γ z) ^ 2 / (2 * γ) := by
  obtain ⟨h2, h3, h4⟩ := P.onestep_conditions hu0 hγ hγm
  have hE := P.onestep_energy_le hγ hL
  have hEp := P.onestep_energy hu0 hγ hγm hz hpos hz1 hz2 hL
  have hcd := P.conditional_descent hγ h2 h3 h4 hz hpos hE hz1 hz2 hEp
  have hgf := P.gradX_sq_le hγ h2 h4 hz hpos hE hz1 hz2
  -- γ(𝓛 - 𝓛⁺) ≥ ¼γ²‖g‖_X² + (¾ - (5/2)γD) R² ≥ ¼γ²‖g‖_X² + ½R²
  have hD : 0 ≤ P.D u0 := (P.D_pos u0 hu0).le
  have hR : 0 ≤ (P.R γ z) ^ 2 := sq_nonneg _
  have key : γ * (P.lyap γ z - P.lyap γ (P.step γ z))
      ≥ 1 / 4 * γ ^ 2 * P.nrmXsq γ (P.g (P.normalize z)) + 1 / 2 * (P.R γ z) ^ 2 := by
    have h5 : 5 / 2 * (γ * P.D u0) * (P.R γ z) ^ 2 ≤ 5 / 2 * (1 / 128) * (P.R γ z) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hR
      linarith
    nlinarith
  have hγ' : 0 < γ := hγ
  rw [ge_iff_le]
  apply le_of_mul_le_mul_left _ hγ'
  have e : γ * (1 / 4 * γ * P.nrmXsq γ (P.g (P.normalize z)) + (P.R γ z) ^ 2 / (2 * γ))
      = 1 / 4 * γ ^ 2 * P.nrmXsq γ (P.g (P.normalize z)) + 1 / 2 * (P.R γ z) ^ 2 := by
    field_simp
  rw [e]; exact key

/-- Proposition 4.8, (4.31) second inequality: `𝓛(z) - 𝓛(z⁺) ≥ (5/(16γ)) ‖z⁺ - z‖_𝒢²`. -/
theorem onestep_drop' :
    P.lyap γ z - P.lyap γ (P.step γ z) ≥ 5 / (16 * γ) * P.nrmGsq γ (P.step γ z - z) := by
  obtain ⟨h2, h3, h4⟩ := P.onestep_conditions hu0 hγ hγm
  have hE := P.onestep_energy_le hγ hL
  have hEp := P.onestep_energy hu0 hγ hγm hz hpos hz1 hz2 hL
  have hcd := P.conditional_descent hγ h2 h3 h4 hz hpos hE hz1 hz2 hEp
  have hgs := P.nrmGsq_step_sub_le hγ h2 h4 hz hpos hE hz1 hz2
  have hR : 0 ≤ (P.R γ z) ^ 2 := sq_nonneg _
  have key : γ * (P.lyap γ z - P.lyap γ (P.step γ z))
      ≥ 5 / 16 * P.nrmGsq γ (P.step γ z - z) := by nlinarith
  have hγ' : 0 < γ := hγ
  rw [ge_iff_le]
  apply le_of_mul_le_mul_left _ hγ'
  have e : γ * (5 / (16 * γ) * P.nrmGsq γ (P.step γ z - z))
      = 5 / 16 * P.nrmGsq γ (P.step γ z - z) := by
    field_simp
  rw [e]; exact key

end Prop48

end Setting

end GPDYS

end
