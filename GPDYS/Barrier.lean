import GPDYS.Descent

/-!
# The energy barrier (§4.5, Lemma 4.7)

Lemma 4.5 assumes that the new direction `u⁺` has energy at most `E₀`. The energy barrier
argument removes this assumption by a continuation in which the step size and the radial
deviation of the input are scaled by the same factor `θ ∈ [0,1]`:
`z_θ = (1 - θ(1 - ‖z‖₂)) u`, step size `θγ`, (4.27)–(4.29). Writing `φ(θ) = E_h(u_θ⁺)`:

* `φ` is continuous on `[0,1]`, `φ(0) = E_h(u) ≤ E₀` and `φ(1) = E_h(u⁺)`;
* the residual and the Lyapunov function scale as `R_θ(z_θ) = θR`, `𝓛_θ(z_θ) ≤ 𝓛(z) ≤ E₀`
  (4.30);
* for small `θ`, `φ(θ) ≤ E₀` (by the crude estimate `energy_step_le_of_small`, which replaces
  the derivative computation of the paper);
* if `φ(θ) ≤ E₀` for some `θ ∈ (0,1]`, then the conditional descent gives
  `φ(θ) ≤ E_h(u) + θR²/(4γ) - (5/(16θγ))‖δ_θ‖_𝒢²`, so that `φ(θ) < E₀` unless `R = 0` and
  `δ_θ = 0`, in which case `g(u) = 0` and `φ ≡ E_h(u)`.

A supremum argument on `{θ ∈ [0,1] : φ(θ) ≤ E₀}` then shows `φ(1) ≤ E₀`, which is Lemma 4.7.
-/

open Finset Matrix Set

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- The continuation `z_θ = (1 - θ(1 - ‖z‖₂)) u`, (4.27). -/
def zcont (z : ι → ℝ) (θ : ℝ) : ι → ℝ := (1 - θ * (1 - P.nrm2 z)) • P.normalize z

/-- One step of size `θγ` from `z_θ`, (4.29). -/
def stepcont (γ : ℝ) (z : ι → ℝ) (θ : ℝ) : ι → ℝ := P.step (θ * γ) (P.zcont z θ)

/-- `φ(θ) = E_h(u_θ⁺)`. -/
def φcont (γ : ℝ) (z : ι → ℝ) (θ : ℝ) : ℝ := P.energy (P.normalize (P.stepcont γ z θ))

section Continuation

variable {z : ι → ℝ} (hz : z ≠ 0) (hz2 : P.nrm2 z ≤ 1)
include hz hz2

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false in
/-- `‖z_θ‖₂ = 1 - θ(1 - ‖z‖₂)` for `θ ∈ [0,1]`, (4.28). -/
theorem nrm2_zcont {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    P.nrm2 (P.zcont z θ) = 1 - θ * (1 - P.nrm2 z) := by
  have hc : 0 ≤ 1 - θ * (1 - P.nrm2 z) := by
    have := P.nrm2_nonneg z
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hz2)]
  rw [zcont, nrm2_smul, P.nrm2_normalize hz, abs_of_nonneg hc, mul_one]

/-- `1 - θ(1 - ‖z‖₂) > 0` for `θ ∈ [0,1]` and `z ≠ 0`. -/
theorem zcont_coeff_pos {θ : ℝ} (hθ1 : θ ≤ 1) :
    0 < 1 - θ * (1 - P.nrm2 z) := by
  have := P.nrm2_pos_of_ne_zero hz
  nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hz2)]

theorem zcont_ne_zero {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : P.zcont z θ ≠ 0 := by
  intro h
  have h1 := P.nrm2_zcont hz hz2 hθ0 hθ1
  rw [h, (P.nrm2_eq_zero_iff 0).mpr rfl] at h1
  have := P.zcont_coeff_pos hz hz2 hθ1
  linarith

set_option linter.unusedVariables false in
/-- The normalized vector of `z_θ` is `u`. -/
theorem normalize_zcont {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    P.normalize (P.zcont z θ) = P.normalize z := by
  rw [zcont, P.normalize_smul _ (P.zcont_coeff_pos hz hz2 hθ1),
    P.normalize_eq_self (P.nrm2_normalize hz)]

/-- `z_1 = z`. -/
theorem zcont_one : P.zcont z 1 = z := by
  rw [zcont, show (1 : ℝ) - 1 * (1 - P.nrm2 z) = P.nrm2 z by ring, P.nrm2_smul_normalize hz]

/-- `z_0⁺ = u` (a step of size `0` from `u` returns `u`). -/
theorem stepcont_zero (γ : ℝ) : P.stepcont γ z 0 = P.normalize z := by
  have hu : P.normalize (P.normalize z) = P.normalize z :=
    P.normalize_eq_self (P.nrm2_normalize hz)
  simp only [stepcont, zcont, step, xi, zero_mul, sub_zero, one_smul, zero_smul, hu,
    resolvent_zero_eq]
  module

/-- `z_1⁺ = z⁺`. -/
theorem stepcont_one (γ : ℝ) : P.stepcont γ z 1 = P.step γ z := by
  rw [stepcont, P.zcont_one hz hz2, one_mul]

/-- The residual scales: `R_{θγ}(z_θ) = θ R(z)`, (4.30). -/
theorem R_zcont (γ : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    P.R (θ * γ) (P.zcont z θ) = θ * P.R γ z := by
  rw [R_def, R_def, P.nrm2_zcont hz hz2 hθ0 hθ1, P.normalize_zcont hz hz2 hθ0 hθ1]
  ring

/-- The Lyapunov function of the scaled input: `𝓛_{θγ}(z_θ) = E_h(u) + θ R²/γ`, (4.30). -/
theorem lyap_zcont {γ : ℝ} (hγ : 0 < γ) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    P.lyap (θ * γ) (P.zcont z θ) = P.energy (P.normalize z) + θ * (P.R γ z) ^ 2 / γ := by
  rw [lyap_def, P.R_zcont hz hz2 γ hθ0.le hθ1, P.normalize_zcont hz hz2 hθ0.le hθ1]
  congr 1
  have := hθ0.ne'
  have := hγ.ne'
  field_simp

/-- Explicit form of `z_θ⁺` on `[0,1]`:
`z_θ⁺ = z_θ - u + G_{θγ}⁻¹ (2u - z_θ - θγ n(u))`. -/
theorem stepcont_eq (γ : ℝ) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    P.stepcont γ z θ = P.zcont z θ - P.normalize z
      + P.resolvent (θ * γ) ((2 : ℝ) • P.normalize z - P.zcont z θ
          - (θ * γ) • P.nonlin (P.normalize z)) := by
  rw [stepcont, step, xi, P.normalize_zcont hz hz2 hθ0 hθ1]
  abel

/-- Continuity of the resolvent in the step size: `θ ↦ (M + θγS)⁻¹` is continuous on `[0,1]`
(for `γ ≥ 0`), since `det (M + θγ S) ≠ 0` there. -/
theorem continuousOn_inv_MS {γ : ℝ} (hγ : 0 ≤ γ) :
    ContinuousOn (fun θ : ℝ => (P.M + (θ * γ) • P.S)⁻¹) (Icc 0 1) := by
  intro θ hθ
  have hθγ : 0 ≤ θ * γ := mul_nonneg hθ.1 hγ
  have hdet := P.MS_det_ne_zero hθγ
  have hA : Continuous (fun θ : ℝ => P.M + (θ * γ) • P.S) := by fun_prop
  have hinv : ContinuousAt Inv.inv (P.M + (θ * γ) • P.S) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hcomp : ContinuousAt (Inv.inv ∘ fun θ : ℝ => P.M + (θ * γ) • P.S) θ :=
    ContinuousAt.comp (f := fun θ : ℝ => P.M + (θ * γ) • P.S) hinv hA.continuousAt
  exact hcomp.continuousWithinAt

/-- `θ ↦ z_θ⁺` is continuous on `[0,1]`. -/
theorem stepcont_continuousOn {γ : ℝ} (hγ : 0 ≤ γ) :
    ContinuousOn (P.stepcont γ z) (Icc 0 1) := by
  have hzc : Continuous (P.zcont z) := by
    unfold zcont; fun_prop
  have hb : Continuous (fun θ : ℝ => P.M *ᵥ ((2 : ℝ) • P.normalize z - P.zcont z θ
      - (θ * γ) • P.nonlin (P.normalize z))) := by
    apply continuous_const.matrix_mulVec
    fun_prop
  have hmul : Continuous (fun p : Matrix ι ι ℝ × (ι → ℝ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hres : ContinuousOn (fun θ : ℝ => P.resolvent (θ * γ) ((2 : ℝ) • P.normalize z
      - P.zcont z θ - (θ * γ) • P.nonlin (P.normalize z))) (Icc 0 1) := by
    intro θ hθ
    have hA := P.continuousOn_inv_MS hz hz2 hγ θ hθ
    have hpair := hA.prodMk hb.continuousWithinAt
    exact hmul.continuousAt.comp_continuousWithinAt hpair
  refine ContinuousOn.congr ?_ (fun θ hθ => P.stepcont_eq hz hz2 γ hθ.1 hθ.2)
  exact ((hzc.sub continuous_const).continuousOn).add hres

end Continuation

/-- The energy `E_h` is a continuous function on `ι → ℝ`. -/
theorem energy_continuous : Continuous P.energy := by
  unfold energy kin H pot wnorm4p4
  fun_prop

/-- The projected gradient `g` is a continuous function on `ι → ℝ`. -/
theorem g_continuous : Continuous P.g := by
  unfold g lam gradE inner winner negLap nonlin
  fun_prop

/-- `‖·‖₂` is continuous. -/
theorem nrm2_continuous : Continuous P.nrm2 := by
  unfold nrm2 wnorm2 wnorm2sq winner
  fun_prop

/-- `normalize` is continuous at every nonzero vector. -/
theorem normalize_continuousAt {z : ι → ℝ} (hz : z ≠ 0) : ContinuousAt P.normalize z := by
  unfold normalize
  have h1 : ContinuousAt (fun v => (P.nrm2 v)⁻¹) z :=
    (P.nrm2_continuous.continuousAt).inv₀ (P.nrm2_pos_of_ne_zero hz).ne'
  exact h1.smul continuousAt_id

section Barrier

variable [Nonempty ι] {u0 : ι → ℝ} (hu0 : u0 ≠ 0) {γ : ℝ} (hγ : 0 < γ)
  (hC2 : γ * P.D u0 ≤ 1 / 128) (hC3 : γ * P.L0 u0 ≤ 1 / 8)
  (hC4 : γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1)
  {z : ι → ℝ} (hz : z ≠ 0) (hpos : ∀ i, 0 < P.normalize z i)
  (hz1 : 1 - 3 * γ * P.D u0 ≤ P.nrm2 z) (hz2 : P.nrm2 z ≤ 1)
  (hL : P.lyap γ z ≤ P.E0 u0)
include hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL

set_option linter.unusedSectionVars false

/-- Conditions used in Lemma 4.7: for `θ ∈ (0,1]`, (C2)–(C4) hold for `θγ`,
and `1 - 3θγD ≤ ‖z_θ‖₂ ≤ 1`. Positivity and the energy bound are proved separately. -/
theorem zcont_hyp {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (θ * γ) * P.D u0 ≤ 1 / 128 ∧ (θ * γ) * P.L0 u0 ≤ 1 / 8 ∧
      (θ * γ) * P.B1 u0 + 3 * (θ * γ) ^ 2 * P.D u0 * P.Λd ≤ 1 ∧
      1 - 3 * (θ * γ) * P.D u0 ≤ P.nrm2 (P.zcont z θ) ∧ P.nrm2 (P.zcont z θ) ≤ 1 := by
  have hD := P.D_pos u0 hu0
  have hL0 := P.L0_pos u0 hu0
  have hB := P.B1_pos u0 hu0
  have hΛ := P.Λd_nonneg
  have hθγ : 0 ≤ θ * γ := by positivity
  have h1 : θ * γ ≤ γ := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc (θ * γ) * P.D u0 ≤ γ * P.D u0 := mul_le_mul_of_nonneg_right h1 hD.le
      _ ≤ 1 / 128 := hC2
  · calc (θ * γ) * P.L0 u0 ≤ γ * P.L0 u0 := mul_le_mul_of_nonneg_right h1 hL0.le
      _ ≤ 1 / 8 := hC3
  · have e1 : (θ * γ) * P.B1 u0 ≤ γ * P.B1 u0 := mul_le_mul_of_nonneg_right h1 hB.le
    have e2 : 3 * (θ * γ) ^ 2 * P.D u0 * P.Λd ≤ 3 * γ ^ 2 * P.D u0 * P.Λd := by
      have h2 : (θ * γ) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ hθγ h1 2
      have h3 : 0 ≤ P.D u0 * P.Λd := by positivity
      nlinarith
    linarith
  · rw [P.nrm2_zcont hz hz2 hθ0.le hθ1]
    have : θ * (1 - P.nrm2 z) ≤ θ * (3 * γ * P.D u0) :=
      mul_le_mul_of_nonneg_left (by linarith) hθ0.le
    nlinarith
  · rw [P.nrm2_zcont hz hz2 hθ0.le hθ1]
    nlinarith [mul_nonneg hθ0.le (sub_nonneg.mpr hz2)]

/-- `E_h(u) ≤ E₀`. -/
theorem energy_normalize_le : P.energy (P.normalize z) ≤ P.E0 u0 :=
  (P.energy_le_lyap hγ z).trans hL

/-- `z_θ⁺ ≠ 0` for every `θ ∈ [0,1]`. -/
theorem stepcont_ne_zero {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : P.stepcont γ z θ ≠ 0 := by
  rcases hθ0.eq_or_lt with h | h
  · rw [← h, P.stepcont_zero hz hz2]
    intro h0
    have := P.nrm2_normalize hz
    rw [h0, (P.nrm2_eq_zero_iff 0).mpr rfl] at this
    exact zero_ne_one this
  · obtain ⟨h2, h3, h4, h5, h6⟩ := P.zcont_hyp hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL h hθ1
    have hpos' : ∀ i, 0 < P.normalize (P.zcont z θ) i := by
      rw [P.normalize_zcont hz hz2 h.le hθ1]; exact hpos
    have hE' : P.energy (P.normalize (P.zcont z θ)) ≤ P.E0 u0 := by
      rw [P.normalize_zcont hz hz2 h.le hθ1]
      exact P.energy_normalize_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
    exact P.step_ne_zero (mul_pos h hγ) h2 h4 (P.zcont_ne_zero hz hz2 h.le hθ1) hpos' hE' h5 h6

/-- Lemma 4.7: `φ` is continuous on `[0,1]`. -/
theorem φcont_continuousOn : ContinuousOn (P.φcont γ z) (Icc 0 1) := by
  intro θ hθ
  have h1 := P.stepcont_continuousOn hz hz2 hγ.le θ hθ
  have h2 := P.normalize_continuousAt
    (P.stepcont_ne_zero hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL hθ.1 hθ.2)
  exact P.energy_continuous.continuousAt.comp_continuousWithinAt
    (h2.comp_continuousWithinAt h1)

/-- `φ(0) ≤ E₀`, using the identity `φ(0) = E_h(u)`. -/
theorem φcont_zero_le : P.φcont γ z 0 ≤ P.E0 u0 := by
  unfold φcont
  rw [P.stepcont_zero hz hz2, P.normalize_eq_self (P.nrm2_normalize hz)]
  exact P.energy_normalize_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL

/-- `C₁ > 0`. -/
theorem C1_pos : 0 < P.C1 := by
  unfold C1
  have := P.Vinf_nonneg; have := P.β_pos; have := P.wmin_pos
  positivity

/-- For small `θ`, `φ(θ) ≤ E₀`: the threshold `θ₁ = min{1, 1/(γ(28D + 2C₁))} > 0` works. -/
theorem φcont_le_of_small {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ min 1 (1 / (γ * (28 * P.D u0 + 2 * P.C1)))) : P.φcont γ z θ ≤ P.E0 u0 := by
  rcases hθ0.eq_or_lt with h | h
  · rw [← h]; exact P.φcont_zero_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
  · have hθ1' : θ ≤ 1 := hθ1.trans (min_le_left _ _)
    have hC1 := P.C1_pos hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
    have hD := P.D_pos u0 hu0
    have hK : 0 < γ * (28 * P.D u0 + 2 * P.C1) := by positivity
    have hθ2 : θ ≤ 1 / (γ * (28 * P.D u0 + 2 * P.C1)) := hθ1.trans (min_le_right _ _)
    have hsmall : (θ * γ) * (28 * P.D u0 + 2 * P.C1) ≤ 1 := by
      rw [le_div_iff₀ hK] at hθ2; linarith [hθ2]
    obtain ⟨h2, h3, h4, h5, h6⟩ := P.zcont_hyp hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL h hθ1'
    have hE := P.energy_normalize_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
    have hpos' : ∀ i, 0 < P.normalize (P.zcont z θ) i := by
      rw [P.normalize_zcont hz hz2 h.le hθ1']; exact hpos
    have hE' : P.energy (P.normalize (P.zcont z θ)) ≤ P.E0 u0 := by
      rw [P.normalize_zcont hz hz2 h.le hθ1']; exact hE
    have key := P.energy_step_le_of_small (mul_pos h hγ) h2 h4
      (P.zcont_ne_zero hz hz2 h.le hθ1') hpos' hE' h5 h6 hsmall
    rw [P.normalize_zcont hz hz2 h.le hθ1', P.R_zcont hz hz2 γ h.le hθ1'] at key
    have hlyap : P.energy (P.normalize z) + (P.R γ z) ^ 2 / γ ≤ P.E0 u0 := hL
    have h2D : 2 * P.D u0 * (θ * P.R γ z) ^ 2 ≤ (P.R γ z) ^ 2 / γ := by
      rw [le_div_iff₀ hγ]
      have hθsq : θ ^ 2 ≤ 1 := by nlinarith
      have hγD : 0 ≤ γ * P.D u0 := by positivity
      have : 2 * (γ * P.D u0) * θ ^ 2 ≤ 1 := by nlinarith
      have hR2 := sq_nonneg (P.R γ z)
      calc 2 * P.D u0 * (θ * P.R γ z) ^ 2 * γ
          = (2 * (γ * P.D u0) * θ ^ 2) * (P.R γ z) ^ 2 := by ring
        _ ≤ 1 * (P.R γ z) ^ 2 := mul_le_mul_of_nonneg_right this hR2
        _ = (P.R γ z) ^ 2 := one_mul _
    show P.energy (P.normalize (P.step (θ * γ) (P.zcont z θ))) ≤ P.E0 u0
    linarith

/-- If `φ(θ) ≤ E₀` for some `θ ∈ (0,1]`, then
`φ(θ) ≤ E_h(u) + θ R²/(4γ) - (5/(16 θγ)) ‖δ_θ‖_𝒢²`, by the conditional descent. -/
theorem φcont_le_of_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hφ : P.φcont γ z θ ≤ P.E0 u0) :
    P.φcont γ z θ ≤ P.energy (P.normalize z) + θ * (P.R γ z) ^ 2 / (4 * γ)
      - 5 / (16 * (θ * γ)) * P.nrmGsq (θ * γ) (P.delta (θ * γ) (P.zcont z θ)) := by
  obtain ⟨h2, h3, h4, h5, h6⟩ := P.zcont_hyp hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL hθ0 hθ1
  have hE := P.energy_normalize_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
  have hpos' : ∀ i, 0 < P.normalize (P.zcont z θ) i := by
    rw [P.normalize_zcont hz hz2 hθ0.le hθ1]; exact hpos
  have hE' : P.energy (P.normalize (P.zcont z θ)) ≤ P.E0 u0 := by
    rw [P.normalize_zcont hz hz2 hθ0.le hθ1]; exact hE
  have hθγ : 0 < θ * γ := mul_pos hθ0 hγ
  have hcd := P.conditional_descent hθγ h2 h3 h4 (P.zcont_ne_zero hz hz2 hθ0.le hθ1) hpos' hE'
    h5 h6 hφ
  rw [P.lyap_zcont hz hz2 hγ hθ0 hθ1, P.R_zcont hz hz2 γ hθ0.le hθ1] at hcd
  have hel : P.energy (P.normalize (P.step (θ * γ) (P.zcont z θ)))
      ≤ P.lyap (θ * γ) (P.step (θ * γ) (P.zcont z θ)) := P.energy_le_lyap hθγ _
  show P.energy (P.normalize (P.step (θ * γ) (P.zcont z θ))) ≤ _
  set G := P.nrmGsq (θ * γ) (P.delta (θ * γ) (P.zcont z θ)) with hG
  set L := P.lyap (θ * γ) (P.step (θ * γ) (P.zcont z θ)) with hLdef
  set E := P.energy (P.normalize z) with hEdef
  set R := P.R γ z with hRdef
  have hne := hθγ.ne'
  have key : E + θ * R ^ 2 / (4 * γ) - 5 / (16 * (θ * γ)) * G - L
      = (θ * γ * (E + θ * R ^ 2 / γ - L) - (5 / 16 * G + 3 / 4 * (θ * R) ^ 2)) / (θ * γ) := by
    field_simp
    ring
  have hnn : 0 ≤ E + θ * R ^ 2 / (4 * γ) - 5 / (16 * (θ * γ)) * G - L := by
    rw [key]
    apply div_nonneg _ hθγ.le
    linarith
  linarith

/-- Strict version: if `φ(θ) ≤ E₀` for some `θ ∈ (0,1]` and not (`R = 0` and `g(u) = 0`),
then `φ(θ) < E₀`. -/
theorem φcont_lt_of_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hφ : P.φcont γ z θ ≤ P.E0 u0)
    (hne : ¬ (P.R γ z = 0 ∧ P.g (P.normalize z) = 0)) : P.φcont γ z θ < P.E0 u0 := by
  have h := P.φcont_le_of_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL hθ0 hθ1 hφ
  have hθγ : 0 < θ * γ := mul_pos hθ0 hγ
  set G := P.nrmGsq (θ * γ) (P.delta (θ * γ) (P.zcont z θ)) with hG
  have hG0 : 0 ≤ G := P.nrmGsq_nonneg hθγ.le _
  have hlyap : P.energy (P.normalize z) + (P.R γ z) ^ 2 / γ ≤ P.E0 u0 := hL
  have hE := P.energy_normalize_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
  by_cases hR : P.R γ z = 0
  · by_cases hG' : G = 0
    · exfalso
      apply hne
      refine ⟨hR, ?_⟩
      have hδ : P.delta (θ * γ) (P.zcont z θ) = 0 := (P.nrmGsq_eq_zero_iff hθγ.le _).mp hG'
      have hR' : P.R (θ * γ) (P.zcont z θ) = 0 := by
        rw [P.R_zcont hz hz2 γ hθ0.le hθ1, hR, mul_zero]
      have hzp : P.step (θ * γ) (P.zcont z θ) ≠ 0 :=
        P.stepcont_ne_zero hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL hθ0.le hθ1
      have := (P.descent_equality_case hθγ (P.zcont_ne_zero hz hz2 hθ0.le hθ1) hzp hδ hR').1
      rwa [P.normalize_zcont hz hz2 hθ0.le hθ1] at this
    · have hGpos : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hG')
      have h5 : 0 < 5 / (16 * (θ * γ)) * G := by positivity
      rw [hR] at h
      have e : θ * (0 : ℝ) ^ 2 / (4 * γ) = 0 := by ring
      rw [e] at h
      linarith
  · have hRpos : 0 < (P.R γ z) ^ 2 := by positivity
    have hlt : θ * (P.R γ z) ^ 2 / (4 * γ) < (P.R γ z) ^ 2 / γ := by
      rw [div_lt_div_iff₀ (by positivity) hγ]
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) (mul_pos hRpos hγ).le, mul_pos hRpos hγ]
    have h5 : 0 ≤ 5 / (16 * (θ * γ)) * G := by positivity
    linarith

/-- If `R = 0` and `g(u) = 0`, then `φ(θ) = E_h(u)` for every `θ ∈ [0,1]`.
The proof first uses `step_eq_self_of_R_g` to show `z_θ⁺ = z_θ`. -/
theorem φcont_eq_of_R_g (hR : P.R γ z = 0) (hg : P.g (P.normalize z) = 0) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : P.φcont γ z θ = P.energy (P.normalize z) := by
  have hR' : P.R (θ * γ) (P.zcont z θ) = 0 := by
    rw [P.R_zcont hz hz2 γ hθ0 hθ1, hR, mul_zero]
  have hg' : P.g (P.normalize (P.zcont z θ)) = 0 := by
    rw [P.normalize_zcont hz hz2 hθ0 hθ1]; exact hg
  have hθγ : 0 ≤ θ * γ := mul_nonneg hθ0 hγ.le
  have hstep := P.step_eq_self_of_R_g hθγ (P.zcont_ne_zero hz hz2 hθ0 hθ1) hR' hg'
  unfold φcont stepcont
  rw [hstep, P.normalize_zcont hz hz2 hθ0 hθ1]

/-- Lemma 4.7 (energy barrier): `E_h(u⁺) ≤ E₀`. -/
theorem energy_barrier : P.energy (P.normalize (P.step γ z)) ≤ P.E0 u0 := by
  have h1 : P.energy (P.normalize (P.step γ z)) = P.φcont γ z 1 := by
    unfold φcont; rw [P.stepcont_one hz hz2]
  rw [h1]
  by_cases hcase : P.R γ z = 0 ∧ P.g (P.normalize z) = 0
  · rw [P.φcont_eq_of_R_g hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL hcase.1 hcase.2 zero_le_one
      le_rfl]
    exact P.energy_normalize_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
  · set A : Set ℝ := {θ | θ ∈ Icc (0 : ℝ) 1 ∧ P.φcont γ z θ ≤ P.E0 u0} with hA
    have hcont := P.φcont_continuousOn hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
    have hclosed : IsClosed A :=
      hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have h0A : (0 : ℝ) ∈ A :=
      ⟨⟨le_rfl, zero_le_one⟩, P.φcont_zero_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL⟩
    have hne : A.Nonempty := ⟨0, h0A⟩
    have hbdd : BddAbove A := ⟨1, fun θ hθ => hθ.1.2⟩
    set s := sSup A with hs
    have hsA : s ∈ A := hclosed.csSup_mem hne hbdd
    have hs0 : 0 ≤ s := le_csSup hbdd h0A
    have hs1 : s ≤ 1 := csSup_le hne (fun θ hθ => hθ.1.2)
    have hs_eq : s = 1 := by
      by_contra hne1
      have hlt : s < 1 := lt_of_le_of_ne hs1 hne1
      rcases hs0.eq_or_lt with h | h
      · -- `s = 0`: the threshold `θ₁ > 0` lies in `A`
        set θ₁ := min 1 (1 / (γ * (28 * P.D u0 + 2 * P.C1))) with hθ₁
        have hθ₁pos : 0 < θ₁ := by
          apply lt_min one_pos
          apply div_pos one_pos
          have := P.D_pos u0 hu0
          have := P.C1_pos hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL
          positivity
        have hθ₁A : θ₁ ∈ A := ⟨⟨hθ₁pos.le, min_le_left _ _⟩,
          P.φcont_le_of_small hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL hθ₁pos.le le_rfl⟩
        have := le_csSup hbdd hθ₁A
        rw [← hs, ← h] at this
        linarith
      · -- `s > 0`: `φ(s) < E₀`, so by continuity `A` contains points to the right of `s`
        have hφs : P.φcont γ z s < P.E0 u0 :=
          P.φcont_lt_of_le hu0 hγ hC2 hC3 hC4 hz hpos hz1 hz2 hL h hs1 hsA.2 hcase
        have hc := hcont s ⟨hs0, hs1⟩
        rw [Metric.continuousWithinAt_iff] at hc
        obtain ⟨δ, hδ, hδ'⟩ := hc (P.E0 u0 - P.φcont γ z s) (by linarith)
        set θ := min (s + δ / 2) 1 with hθ
        have hθs : s < θ := lt_min (by linarith) hlt
        have hθ1 : θ ≤ 1 := min_le_right _ _
        have hθ0 : 0 ≤ θ := hs0.trans hθs.le
        have hdist : dist θ s < δ := by
          rw [Real.dist_eq, abs_lt]
          constructor
          · linarith
          · have : θ ≤ s + δ / 2 := min_le_left _ _
            linarith
        have hφθ := hδ' ⟨hθ0, hθ1⟩ hdist
        rw [Real.dist_eq, abs_lt] at hφθ
        have hθA : θ ∈ A := ⟨⟨hθ0, hθ1⟩, by linarith [hφθ.2]⟩
        have := le_csSup hbdd hθA
        rw [← hs] at this
        linarith
    have := hsA.2
    rwa [hs_eq] at this

end Barrier

end Setting

end GPDYS

end
