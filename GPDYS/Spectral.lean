import GPDYS.Rate

/-!
# The largest eigenvalue `μ_max` of `-Δ_h`, and the attainment of `ν`

Theorem 5.1 of the paper uses `μ_max`, the largest eigenvalue of `-Δ_h`, and defines `ν` as a
minimum over the unit tangent vectors at the ground state. `Rate.lean` proves the theorem for an
arbitrary Rayleigh bound `μ` and defines `ν` as an infimum. This file closes the gap:

* `μmax` is defined as the maximum of the Rayleigh quotient `⟪v,-Δ_h v⟫_h` over `v ∈ 𝓜`; it is
  attained (`μmax_attained`), it is an eigenvalue of `-Δ_h` (`μmax_isEigenvalue`), every eigenvalue
  of `-Δ_h` is at most `μmax` (`eigenvalue_le_μmax`), and `⟪v,-Δ_h v⟫_h ≤ μmax ‖v‖₂²` for all `v`
  (`kin_le_μmax`), so `μmax` is the largest eigenvalue of `-Δ_h` in the sense of the paper;
* `rate_theorem_μmax` is Theorem 5.1 with `μ = μ_max`, i.e. with the paper's rate
  `η = min{γν/(4(1+γμ_max)), 1/2}`;
* `nu_attained` shows that the infimum defining `ν` is a minimum.
-/

open Finset Filter Topology

noncomputable section

namespace GPDYS

/-- If `2 t c + t² d ≤ 0` for every real `t`, then `c = 0`
(the first variation of a quadratic with a maximum at `t = 0` vanishes). -/
theorem eq_zero_of_forall_two_mul_add_sq_mul_le {c d : ℝ}
    (h : ∀ t : ℝ, 2 * t * c + t ^ 2 * d ≤ 0) : c = 0 := by
  by_contra hc
  -- test with `t = c / (d² + 1)`
  have hs : 0 < d ^ 2 + 1 := by positivity
  have hc2 : 0 < c ^ 2 := by positivity
  have ht := h (c / (d ^ 2 + 1))
  have e : 2 * (c / (d ^ 2 + 1)) * c + (c / (d ^ 2 + 1)) ^ 2 * d
      = c ^ 2 * (2 * d ^ 2 + d + 2) / (d ^ 2 + 1) ^ 2 := by
    field_simp
    ring
  rw [e, div_le_iff₀ (by positivity), zero_mul] at ht
  have hq : 0 < 2 * d ^ 2 + d + 2 := by nlinarith [sq_nonneg (d + 1 / 4)]
  have := mul_pos hc2 hq
  linarith

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- On a nonempty mesh, `μ_max = max {⟪v, -Δ_h v⟫_h : v ∈ 𝓜}` is the largest eigenvalue
of `-Δ_h`. The empty-set value is zero. -/
def μmax : ℝ := sSup {x : ℝ | ∃ v : ι → ℝ, P.nrm2sq v = 1 ∧ x = P.kin v}

/-- The kinetic form is continuous. -/
theorem kin_continuous : Continuous P.kin := by
  unfold kin
  fun_prop

/-- The Rayleigh quotient attains its maximum on the sphere. -/
theorem exists_kin_max [Nonempty ι] :
    ∃ v : ι → ℝ, P.nrm2sq v = 1 ∧ ∀ w : ι → ℝ, P.nrm2sq w = 1 → P.kin w ≤ P.kin v := by
  -- the sphere is compact and nonempty, and `kin` is continuous
  have hne : ({v : ι → ℝ | P.nrm2sq v = 1} : Set (ι → ℝ)).Nonempty := by
    have h1 : (fun _ : ι => (1 : ℝ)) ≠ 0 := ne_zero_of_pos (fun _ => one_pos)
    exact ⟨P.normalize (fun _ => 1), P.nrm2sq_normalize h1⟩
  obtain ⟨v, hv, hmax⟩ := P.sphere_isCompact.exists_isMaxOn hne P.kin_continuous.continuousOn
  exact ⟨v, hv, fun w hw => hmax hw⟩

/-- If `vm ∈ 𝓜` maximizes the Rayleigh quotient on `𝓜`, then `μ_max = ⟪vm, -Δ_h vm⟫_h`. -/
theorem μmax_eq_kin_of_max {vm : ι → ℝ} (hvm : P.nrm2sq vm = 1)
    (hmax : ∀ w : ι → ℝ, P.nrm2sq w = 1 → P.kin w ≤ P.kin vm) : P.μmax = P.kin vm := by
  unfold μmax
  apply IsGreatest.csSup_eq
  refine ⟨⟨vm, hvm, rfl⟩, ?_⟩
  rintro x ⟨w, hw, rfl⟩
  exact hmax w hw

/-- `μ_max` is attained: `μ_max = ⟪v, -Δ_h v⟫_h` for some `v ∈ 𝓜`. -/
theorem μmax_attained [Nonempty ι] : ∃ v : ι → ℝ, P.nrm2sq v = 1 ∧ P.kin v = P.μmax := by
  obtain ⟨vm, hvm, hmax⟩ := P.exists_kin_max
  exact ⟨vm, hvm, (P.μmax_eq_kin_of_max hvm hmax).symm⟩

/-- The Rayleigh bound `⟪v, -Δ_h v⟫_h ≤ μ_max ‖v‖₂²` for every `v`. -/
theorem kin_le_μmax [Nonempty ι] (v : ι → ℝ) : P.kin v ≤ P.μmax * P.nrm2sq v := by
  obtain ⟨vm, hvm, hmax⟩ := P.exists_kin_max
  rw [P.μmax_eq_kin_of_max hvm hmax]
  by_cases hv : v = 0
  · subst hv
    simp [kin_def, nrm2sq_eq_sum]
  · -- scale: `v = ‖v‖₂ u` with `u = v / ‖v‖₂ ∈ 𝓜`
    have hu : P.nrm2sq (P.normalize v) = 1 := P.nrm2sq_normalize hv
    have h1 := hmax _ hu
    have h2 : P.kin v = P.nrm2 v ^ 2 * P.kin (P.normalize v) := by
      conv_lhs => rw [← P.nrm2_smul_normalize hv]
      rw [kin_smul]
    rw [h2, ← nrm2_sq]
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg (P.nrm2 v))
    linarith

theorem μmax_nonneg [Nonempty ι] : 0 ≤ P.μmax := by
  obtain ⟨v, _, hv⟩ := P.μmax_attained
  rw [← hv]
  exact P.kin_nonneg v

open Matrix in
/-- `μ_max` is an eigenvalue of `-Δ_h`: `-Δ_h v = μ_max v` for a maximizer `v ∈ 𝓜` of the
Rayleigh quotient. -/
theorem μmax_isEigenvalue [Nonempty ι] :
    ∃ v : ι → ℝ, P.nrm2sq v = 1 ∧ P.negLap v = P.μmax • v := by
  obtain ⟨vm, hvm, hmax⟩ := P.exists_kin_max
  have hμ : P.μmax = P.kin vm := P.μmax_eq_kin_of_max hvm hmax
  refine ⟨vm, hvm, ?_⟩
  -- first variation: `vmᵀ S w = μ_max ⟪vm, w⟫_h` for every `w`
  have key : ∀ w : ι → ℝ, vm ⬝ᵥ (P.S *ᵥ w) - P.μmax * P.inner vm w = 0 := by
    intro w
    apply eq_zero_of_forall_two_mul_add_sq_mul_le (d := P.kin w - P.μmax * P.nrm2sq w)
    intro t
    have h1 := P.kin_le_μmax (vm + t • w)
    rw [kin_add, kin_smul, dotS_smul_right, nrm2sq_add, nrm2sq_smul, inner_smul_right, hvm] at h1
    linarith
  have key2 : ∀ w : ι → ℝ, P.inner (P.negLap vm - P.μmax • vm) w = 0 := by
    intro w
    rw [inner_sub_left, inner_smul_left, negLap_inner]
    exact key w
  have h0 : P.nrm2sq (P.negLap vm - P.μmax • vm) = 0 := by
    rw [nrm2sq_def]
    exact key2 _
  rw [nrm2sq_eq_zero_iff, sub_eq_zero] at h0
  exact h0

/-- Every eigenvalue of `-Δ_h` is at most `μ_max`. -/
theorem eigenvalue_le_μmax [Nonempty ι] {v : ι → ℝ} (hv : v ≠ 0) {l : ℝ}
    (h : P.negLap v = l • v) : l ≤ P.μmax := by
  have h1 := P.kin_le_μmax v
  rw [kin_eq_inner, h, inner_smul_right, ← nrm2sq_def] at h1
  exact le_of_mul_le_mul_right h1 (P.nrm2sq_pos_of_ne_zero hv)

/-- **Theorem 5.1** with `μ = μ_max`, the largest eigenvalue of `-Δ_h`, exactly as in the paper:
the iterates converge to the discrete ground state `u_GS`, `ν ≥ 2β m_GS² > 0`, the rate
`η = min{γν/(4(1+γμ_max)), 1/2}` satisfies `0 < η < 1`, and (5.6) holds from some index `K` on. -/
theorem rate_theorem_μmax [Nonempty ι] (hcard : 2 ≤ Fintype.card ι) {u0 : ι → ℝ}
    (hu0 : ∀ i, 0 < u0 i) (hn : P.nrm2 u0 = 1) {γ : ℝ} (hγ : 0 < γ) (hγm : γ ≤ P.γmax u0) :
    ∃ uGS : ι → ℝ, (∀ i, 0 < uGS i) ∧ P.nrm2 uGS = 1 ∧ P.g uGS = 0 ∧
      Tendsto (P.uiter γ u0) atTop (𝓝 uGS) ∧
      2 * P.β * (mGS uGS) ^ 2 ≤ P.nu uGS ∧ 0 < P.nu uGS ∧
      0 < η γ P.μmax (P.nu uGS) ∧ η γ P.μmax (P.nu uGS) < 1 ∧
      ∃ K : ℕ, ∀ k, K ≤ k →
        (P.lyap γ (P.iter γ u0 (k + 1)) - P.energy uGS
          ≤ (1 - η γ P.μmax (P.nu uGS)) * (P.lyap γ (P.iter γ u0 k) - P.energy uGS)) ∧
        (P.energy (P.uiter γ u0 k) - P.energy uGS + (P.R γ (P.iter γ u0 k)) ^ 2 / γ
            + P.nu uGS / 4 * P.nrm2sq (P.uiter γ u0 k - uGS)
          ≤ 2 * (1 - η γ P.μmax (P.nu uGS)) ^ (k - K)
              * (P.lyap γ (P.iter γ u0 K) - P.energy uGS)) :=
  P.rate_theorem' hcard hu0 hn hγ hγm P.μmax_nonneg P.kin_le_μmax

/-- The Hessian form `w ↦ ⟪w, ℋ w⟫_h` is continuous. -/
theorem hessForm_continuous (p : ι → ℝ) : Continuous (P.hessForm p) := by
  unfold hessForm hess nonlin' negLap lam gradE nonlin inner winner
  fun_prop

/-- `w ↦ ⟪p, w⟫_h` is continuous. -/
theorem inner_continuous (p : ι → ℝ) : Continuous (fun w => P.inner p w) := by
  unfold inner winner
  fun_prop

/-- `ν` is attained: it is the minimum of `⟪w, ℋ w⟫_h` over the unit tangent vectors `w ∈ 𝓜`,
`⟪p, w⟫_h = 0`, as in the paper. -/
theorem nu_attained (hcard : 2 ≤ Fintype.card ι) {p : ι → ℝ} (hp : P.nrm2sq p = 1)
    (hpos : ∀ i, 0 < p i) (hg : P.g p = 0) :
    ∃ w : ι → ℝ, P.nrm2sq w = 1 ∧ P.inner p w = 0 ∧ P.hessForm p w = P.nu p := by
  have := P.nonempty_of_nrm2sq_eq_one hp
  -- the set of unit tangent vectors is compact and nonempty
  have hT : IsCompact {w : ι → ℝ | P.nrm2sq w = 1 ∧ P.inner p w = 0} := by
    rw [Set.ofPred_and]
    exact P.sphere_isCompact.inter_right
      (isClosed_eq (P.inner_continuous p) continuous_const)
  have hne : ({w : ι → ℝ | P.nrm2sq w = 1 ∧ P.inner p w = 0} : Set (ι → ℝ)).Nonempty := by
    obtain ⟨w, hw1, hw2⟩ := P.exists_unit_tangent hcard hpos
    exact ⟨w, hw1, hw2⟩
  obtain ⟨w0, hw0, hmin⟩ := hT.exists_isMinOn hne (P.hessForm_continuous p).continuousOn
  refine ⟨w0, hw0.1, hw0.2, ?_⟩
  unfold nu
  apply le_antisymm
  · -- the minimum over the unit tangent vectors is a lower bound of the set defining `ν`
    apply le_csInf
    · exact ⟨_, w0, hw0.1, hw0.2, rfl⟩
    · rintro x ⟨w, hw1, hw2, rfl⟩
      exact hmin ⟨hw1, hw2⟩
  · exact csInf_le (P.bddBelow_nu_set hp hpos hg) ⟨w0, hw0.1, hw0.2, rfl⟩

end Setting

end GPDYS

end
