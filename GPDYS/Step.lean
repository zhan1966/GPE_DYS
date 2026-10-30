import GPDYS.Resolvent

/-!
# Exact identities for one step (§4, Lemmas 4.1 and 4.2)

One step of the scheme maps `z ≠ 0` to `u = z/‖z‖₂`, `𝐱` and `z⁺ = z + 𝐱 - u`; if `z⁺ ≠ 0`
we write `u⁺ = z⁺/‖z⁺‖₂` and `δ = u⁺ - u`. This file proves

* the chord identities (4.1): `⟪u, δ⟫_h = -½‖δ‖₂²` and `‖δ‖₂² = 2(1 - ⟪u, u⁺⟫_h)`;
* the Taylor expansion (4.3) of the energy with the remainder `𝒯(u, δ)` of (4.2), and the
  explicit polynomial form of `𝒯`;
* Lemma 4.1 (step identities): (4.4), (4.5), (4.6), (4.7), (4.8);
* Lemma 4.2 (energy and residual identities): (4.9), (4.10).
-/

open Finset Matrix

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- The change of direction `δ = u⁺ - u` of one step. -/
def delta (γ : ℝ) (z : ι → ℝ) : ι → ℝ := P.normalize (P.step γ z) - P.normalize z

/-- The Taylor remainder `𝒯(u, d) = H(u + d) - H(u) - ⟪n(u), d⟫_h` of the explicit part of the
energy, (4.2). -/
def taylorT (u d : ι → ℝ) : ℝ := P.H (u + d) - P.H u - P.inner (P.nonlin u) d

/-! ### Chord identities (4.1) -/

/-- `⟪u, u⁺ - u⟫_h = -½ ‖u⁺ - u‖₂²` for unit vectors `u, u⁺`. -/
theorem inner_sub_self_eq {u up : ι → ℝ} (hu : P.nrm2sq u = 1) (hup : P.nrm2sq up = 1) :
    P.inner u (up - u) = -(1 / 2) * P.nrm2sq (up - u) := by
  rw [inner_sub_right, nrm2sq_sub, hu, hup, ← nrm2sq_def, hu, P.inner_comm up u]; ring

/-- `‖u⁺ - u‖₂² = 2 (1 - ⟪u, u⁺⟫_h)` for unit vectors `u, u⁺`. -/
theorem nrm2sq_sub_eq {u up : ι → ℝ} (hu : P.nrm2sq u = 1) (hup : P.nrm2sq up = 1) :
    P.nrm2sq (up - u) = 2 * (1 - P.inner u up) := by
  rw [nrm2sq_sub, hu, hup, P.inner_comm up u]; ring

/-- `‖δ‖₂² = 2 (1 - ⟪u, z⁺⟫_h / ‖z⁺‖₂)`, the second form in (4.1). -/
theorem nrm2sq_delta_eq {γ : ℝ} {z : ι → ℝ} (hz : z ≠ 0) (hzp : P.step γ z ≠ 0) :
    P.nrm2sq (P.delta γ z)
      = 2 * (1 - P.inner (P.normalize z) (P.step γ z) / P.nrm2 (P.step γ z)) := by
  unfold delta
  rw [P.nrm2sq_sub_eq (P.nrm2sq_normalize hz) (P.nrm2sq_normalize hzp),
    P.normalize_def (P.step γ z), inner_smul_right, div_eq_inv_mul]

/-! ### The Taylor expansion of the energy (4.2), (4.3) -/

/-- The explicit polynomial form of the remainder:
`𝒯(u, d) = ½ ∑ᵢ wᵢ Vᵢ dᵢ² + (β/2) ∑ᵢ wᵢ dᵢ² (3uᵢ² + 2uᵢdᵢ + ½dᵢ²)`. -/
theorem taylorT_eq (u d : ι → ℝ) :
    P.taylorT u d = (1 / 2) * ∑ i, P.w i * (P.V i * d i ^ 2)
      + P.β / 2 * ∑ i, P.w i * (d i ^ 2 * (3 * u i ^ 2 + 2 * u i * d i + d i ^ 2 / 2)) := by
  unfold taylorT H pot wnorm4p4 inner winner
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Pi.add_apply,
    nonlin_apply]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The Taylor expansion (4.3):
`E_h(u + d) - E_h(u) = ⟪∇E_h(u), d⟫_h + ½ ⟪d, -Δ_h d⟫_h + 𝒯(u, d)`. -/
theorem taylorE (u d : ι → ℝ) :
    P.energy (u + d) - P.energy u
      = P.inner (P.gradE u) d + (1 / 2) * P.kin d + P.taylorT u d := by
  unfold taylorT
  rw [energy_def, energy_def, kin_add, gradE_def, inner_add_left, negLap_inner]
  ring

/-! ### Auxiliary identities for `G_X` -/

/-- `G_X z = ‖z‖₂ u + ‖z‖₂ γ (-Δ_h u)` for `z ≠ 0` and `u = z/‖z‖₂`. -/
theorem GX_eq_nrm2_smul (γ : ℝ) {z : ι → ℝ} (hz : z ≠ 0) :
    P.GX γ z = P.nrm2 z • P.normalize z + (P.nrm2 z * γ) • P.negLap (P.normalize z) := by
  conv_lhs => rw [← P.nrm2_smul_normalize hz]
  rw [GX_smul, GX_def, smul_add, smul_smul]

/-- The first identity of (4.4) with `z = c • u` substituted: for any scalar `c` and vector `u`,
`G_X (c u + G_X⁻¹(2u - c u - γ n(u)) - u) = u - γ n(u) - γ (1 - c) (-Δ_h u)`. -/
theorem GX_step_aux {γ : ℝ} (hγ : 0 ≤ γ) (c : ℝ) (u : ι → ℝ) :
    P.GX γ (c • u + P.resolvent γ ((2 : ℝ) • u - c • u - γ • P.nonlin u) - u)
      = u - γ • P.nonlin u - (γ * (1 - c)) • P.negLap u := by
  rw [GX_sub, GX_add, P.GX_resolvent hγ, GX_smul, GX_def]
  module

/-! ### Lemma 4.1: step identities -/

section StepIdentities

variable {γ : ℝ} (hγ : 0 ≤ γ) {z : ι → ℝ} (hz : z ≠ 0)
include hγ hz

/-- Lemma 4.1, (4.4) first identity: `G_X z⁺ = u - γ n(u) - γ(1 - ‖z‖₂)(-Δ_h u)`. -/
theorem GX_step :
    P.GX γ (P.step γ z) = P.normalize z - γ • P.nonlin (P.normalize z)
      - (γ * (1 - P.nrm2 z)) • P.negLap (P.normalize z) := by
  have h := P.GX_step_aux hγ (P.nrm2 z) (P.normalize z)
  rwa [P.nrm2_smul_normalize hz] at h

/-- (4.7): `G_X (z⁺ - z) = (1 - ‖z‖₂) u - γ ∇E_h(u)`. -/
theorem GX_step_sub_eq :
    P.GX γ (P.step γ z - z)
      = (1 - P.nrm2 z) • P.normalize z - γ • P.gradE (P.normalize z) := by
  rw [GX_sub, P.GX_step hγ hz, P.GX_eq_nrm2_smul γ hz, gradE_def]
  module

/-- Lemma 4.1, (4.4) second identity: `G_X (z⁺ - z) = -(R u + γ g(u))`. -/
theorem GX_step_sub :
    P.GX γ (P.step γ z - z) = -(P.R γ z • P.normalize z + γ • P.g (P.normalize z)) := by
  rw [P.GX_step_sub_eq hγ hz, gradE_eq_lam_smul_add_g, R_def]
  module

set_option linter.unusedSectionVars false in
/-- (4.8): `z⁺ - z = ‖z⁺‖₂ δ + (‖z⁺‖₂ - ‖z‖₂) u`. -/
theorem step_sub_decomp (hzp : P.step γ z ≠ 0) :
    P.step γ z - z = P.nrm2 (P.step γ z) • P.delta γ z
      + (P.nrm2 (P.step γ z) - P.nrm2 z) • P.normalize z := by
  have hzu : z = P.nrm2 z • P.normalize z := (P.nrm2_smul_normalize hz).symm
  have hzpu : P.step γ z = P.nrm2 (P.step γ z) • P.normalize (P.step γ z) :=
    (P.nrm2_smul_normalize hzp).symm
  unfold delta
  linear_combination (norm := module) hzpu - hzu

/-- Lemma 4.1, (4.5): `‖z⁺‖₂ G_X δ = (1 - ‖z⁺‖₂) u - γ ∇E_h(u) - γ(‖z⁺‖₂ - ‖z‖₂)(-Δ_h u)`. -/
theorem GX_delta (hzp : P.step γ z ≠ 0) :
    P.nrm2 (P.step γ z) • P.GX γ (P.delta γ z)
      = (1 - P.nrm2 (P.step γ z)) • P.normalize z - γ • P.gradE (P.normalize z)
        - (γ * (P.nrm2 (P.step γ z) - P.nrm2 z)) • P.negLap (P.normalize z) := by
  have h1 := P.GX_step_sub_eq hγ hz
  rw [P.step_sub_decomp hγ hz hzp, GX_add, GX_smul, GX_smul, P.GX_def γ (P.normalize z)] at h1
  linear_combination (norm := module) h1

/-- Lemma 4.1, (4.6): `(1 + γ⟪u,-Δ_h u⟫_h)(‖z⁺‖₂ - ‖z‖₂) = -R - ‖z⁺‖₂ (γ⟪-Δ_h u, δ⟫_h - ½‖δ‖₂²)`. -/
theorem radial_identity (hzp : P.step γ z ≠ 0) :
    (1 + γ * P.kin (P.normalize z)) * (P.nrm2 (P.step γ z) - P.nrm2 z)
      = - P.R γ z - P.nrm2 (P.step γ z)
          * (γ * (P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z)) - (1 / 2) * P.nrm2sq (P.delta γ z)) := by
  have hu1 : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hup1 : P.nrm2sq (P.normalize (P.step γ z)) = 1 := P.nrm2sq_normalize hzp
  have hud : P.inner (P.normalize z) (P.delta γ z) = -(1 / 2) * P.nrm2sq (P.delta γ z) :=
    P.inner_sub_self_eq hu1 hup1
  -- `⟪G_X(z⁺ - z), u⟫_h = -R` from (4.4)
  have h1 : P.inner (P.GX γ (P.step γ z - z)) (P.normalize z) = - P.R γ z := by
    rw [P.GX_step_sub hγ hz, inner_neg_left, inner_add_left, inner_smul_left, inner_smul_left,
      ← nrm2sq_def, hu1, P.inner_g_self hu1]
    ring
  -- the same inner product computed from (4.8)
  have h2 : P.inner (P.GX γ (P.step γ z - z)) (P.normalize z)
      = P.nrm2 (P.step γ z) * (-(1 / 2) * P.nrm2sq (P.delta γ z)
          + γ * (P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z)))
        + (P.nrm2 (P.step γ z) - P.nrm2 z) * (1 + γ * P.kin (P.normalize z)) := by
    rw [P.step_sub_decomp hγ hz hzp, GX_add, GX_smul, GX_smul, inner_add_left, inner_smul_left,
      inner_smul_left, GX_inner, GX_inner, ← nrm2sq_def, hu1, ← kin_def,
      P.dotS_comm (P.delta γ z), P.inner_comm (P.delta γ z), hud]
  rw [h1] at h2
  linear_combination -h2

/-! ### Lemma 4.2: energy and residual identities -/

/-- Lemma 4.2, (4.9): the energy identity
`γ(E_h(u) - E_h(u⁺)) = ((‖z⁺‖₂+1)/2)‖δ‖₂² + γ(‖z⁺‖₂ - ½)⟪δ,-Δ_h δ⟫_h
  + γ(‖z⁺‖₂ - ‖z‖₂)⟪-Δ_h u, δ⟫_h - γ 𝒯(u, δ)`. -/
theorem energy_identity (hzp : P.step γ z ≠ 0) :
    γ * (P.energy (P.normalize z) - P.energy (P.normalize (P.step γ z)))
      = (P.nrm2 (P.step γ z) + 1) / 2 * P.nrm2sq (P.delta γ z)
        + γ * (P.nrm2 (P.step γ z) - 1 / 2) * P.kin (P.delta γ z)
        + γ * (P.nrm2 (P.step γ z) - P.nrm2 z) * (P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z))
        - γ * P.taylorT (P.normalize z) (P.delta γ z) := by
  have hu1 : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hup1 : P.nrm2sq (P.normalize (P.step γ z)) = 1 := P.nrm2sq_normalize hzp
  have hud : P.inner (P.normalize z) (P.delta γ z) = -(1 / 2) * P.nrm2sq (P.delta γ z) :=
    P.inner_sub_self_eq hu1 hup1
  -- (4.5) tested against `δ`
  have hA : P.nrm2 (P.step γ z) * (P.nrm2sq (P.delta γ z) + γ * P.kin (P.delta γ z))
      = (1 - P.nrm2 (P.step γ z)) * (-(1 / 2) * P.nrm2sq (P.delta γ z))
        - γ * P.inner (P.gradE (P.normalize z)) (P.delta γ z)
        - γ * (P.nrm2 (P.step γ z) - P.nrm2 z)
            * (P.normalize z ⬝ᵥ (P.S *ᵥ P.delta γ z)) := by
    have h := congrArg (fun v => P.inner v (P.delta γ z)) (P.GX_delta hγ hz hzp)
    simp only [inner_smul_left, inner_sub_left, GX_inner, negLap_inner] at h
    rw [← nrm2sq_def, ← kin_def, hud] at h
    linear_combination h
  -- the Taylor expansion (4.3) with `d = δ`, `u + δ = u⁺`
  have hB := P.taylorE (P.normalize z) (P.delta γ z)
  rw [show P.normalize z + P.delta γ z = P.normalize (P.step γ z) by unfold delta; abel] at hB
  linear_combination -hA - γ * hB

/-- Lemma 4.2, (4.10): the residual identity
`R⁺ = -½‖δ‖₂² - γ(‖z⁺‖₂ - ‖z‖₂)⟪-Δ_h u, u⁺⟫_h - γ(‖z⁺‖₂ - 1)⟪-Δ_h δ, u⁺⟫_h
  + γ⟪n(u⁺) - n(u), u⁺⟫_h`. -/
theorem residual_identity (hzp : P.step γ z ≠ 0) :
    P.R γ (P.step γ z)
      = -(1 / 2) * P.nrm2sq (P.delta γ z)
        - γ * (P.nrm2 (P.step γ z) - P.nrm2 z)
            * (P.normalize z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z)))
        - γ * (P.nrm2 (P.step γ z) - 1)
            * (P.delta γ z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z)))
        + γ * P.inner (P.nonlin (P.normalize (P.step γ z)) - P.nonlin (P.normalize z))
            (P.normalize (P.step γ z)) := by
  have hu1 : P.nrm2sq (P.normalize z) = 1 := P.nrm2sq_normalize hz
  have hup1 : P.nrm2sq (P.normalize (P.step γ z)) = 1 := P.nrm2sq_normalize hzp
  have hD : P.nrm2sq (P.delta γ z)
      = 2 * (1 - P.inner (P.normalize z) (P.normalize (P.step γ z))) :=
    P.nrm2sq_sub_eq hu1 hup1
  have hlam : P.lam (P.normalize (P.step γ z)) = P.kin (P.normalize (P.step γ z))
      + P.inner (P.nonlin (P.normalize (P.step γ z))) (P.normalize (P.step γ z)) := by
    rw [lam_eq, inner_nonlin_self]; ring
  have hup : P.normalize (P.step γ z) = P.normalize z + P.delta γ z := by unfold delta; abel
  have hkin : P.kin (P.normalize (P.step γ z))
      = P.normalize z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z))
        + P.delta γ z ⬝ᵥ (P.S *ᵥ P.normalize (P.step γ z)) := by
    rw [kin_def, ← dotS_add_left, ← hup]
  -- (4.4) tested against `u⁺`, with `z⁺ = ‖z⁺‖₂ u⁺` on the left
  have hG := congrArg (fun v => P.inner v (P.normalize (P.step γ z))) (P.GX_step hγ hz)
  rw [P.GX_eq_nrm2_smul γ hzp] at hG
  simp only [inner_add_left, inner_sub_left, inner_smul_left, negLap_inner] at hG
  rw [← nrm2sq_def, hup1, ← kin_def, hkin] at hG
  rw [R_def, hlam, inner_sub_left, hkin]
  linear_combination hG + (1 / 2) * hD

end StepIdentities

end Setting

end GPDYS

end
