import GPDYS.OneStep
import GPDYS.GroundState

/-!
# Global convergence to the discrete ground state (Theorem 3.4)

The invariance (5.1), the summability of the descent terms, the accumulation points and the
identification of the limit (§5).
-/

open Finset Filter Topology

noncomputable section

namespace GPDYS

/-! ### Two elementary facts about real sequences -/

/-- If `f ^ 2 → 0` then `f → 0`. -/
theorem tendsto_zero_of_sq_tendsto_zero {α : Type*} {l : Filter α} {f : α → ℝ}
    (h : Tendsto (fun x => f x ^ 2) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have h4 : Tendsto (fun x => Real.sqrt (f x ^ 2)) l (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h4
  refine h4.congr fun x => ?_
  simp [Real.sqrt_sq_eq_abs]

/-- If `c * f → 0` with `c ≠ 0` then `f → 0`. -/
theorem tendsto_zero_of_const_mul_tendsto_zero {α : Type*} {l : Filter α} {f : α → ℝ} {c : ℝ}
    (hc : c ≠ 0) (h : Tendsto (fun x => c * f x) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  have h2 := h.const_mul c⁻¹
  rw [mul_zero] at h2
  refine h2.congr fun x => ?_
  exact inv_mul_cancel_left₀ hc (f x)

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- `‖·‖₂²` is continuous. -/
theorem nrm2sq_continuous : Continuous P.nrm2sq := by
  have h : P.nrm2sq = fun v => ∑ i, P.w i * v i ^ 2 := funext P.nrm2sq_eq_sum
  rw [h]
  exact continuous_finsetSum Finset.univ fun i _ =>
    continuous_const.mul ((continuous_apply i).pow 2)

/-- `vᵀ S v` as a double sum. -/
theorem kin_eq_sum_sum (v : ι → ℝ) : P.kin v = ∑ i, ∑ j, P.S i j * (v i * v j) :=
  P.kin_eq_double_sum v

/-- A Rayleigh-quotient bound for the discrete Laplacian: there is `μ ≥ 0` with
`⟪v, -Δ_h v⟫_h ≤ μ ‖v‖₂²` for all `v` (in the paper, `μ_max` is the largest eigenvalue). -/
theorem exists_kin_bound [Nonempty ι] : ∃ μ : ℝ, 0 ≤ μ ∧ ∀ v, P.kin v ≤ μ * P.nrm2sq v := by
  -- `μ := (∑ᵢⱼ |Sᵢⱼ|) / w_min`, since `vᵢ vⱼ ≤ (vᵢ² + vⱼ²)/2 ≤ ‖v‖₂² / w_min`
  have hw := P.wmin_pos
  refine ⟨(∑ i, ∑ j, |P.S i j|) / P.wmin, ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      hw.le
  · intro v
    have hsq : ∀ i, v i ^ 2 ≤ P.nrm2sq v / P.wmin := by
      intro i
      rw [le_div_iff₀ hw]
      calc v i ^ 2 * P.wmin ≤ v i ^ 2 * P.w i :=
            mul_le_mul_of_nonneg_left (P.wmin_le i) (sq_nonneg _)
        _ = P.w i * v i ^ 2 := by ring
        _ ≤ P.nrm2sq v := P.w_mul_sq_le_nrm2sq v i
    have hRHS : (∑ i, ∑ j, |P.S i j|) / P.wmin * P.nrm2sq v
        = ∑ i, ∑ j, |P.S i j| * (P.nrm2sq v / P.wmin) := by
      rw [div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hRHS, kin_eq_sum_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h1 : P.S i j * (v i * v j) ≤ |P.S i j| * (|v i| * |v j|) := by
      calc P.S i j * (v i * v j) ≤ |P.S i j * (v i * v j)| := le_abs_self _
        _ = |P.S i j| * (|v i| * |v j|) := by rw [abs_mul, abs_mul]
    have h2 : |v i| * |v j| ≤ P.nrm2sq v / P.wmin := by
      have h3 := two_mul_le_add_sq |v i| |v j|
      rw [sq_abs, sq_abs] at h3
      have h4 := hsq i
      have h5 := hsq j
      linarith
    calc P.S i j * (v i * v j) ≤ |P.S i j| * (|v i| * |v j|) := h1
      _ ≤ |P.S i j| * (P.nrm2sq v / P.wmin) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

/-- The sphere `𝓜` is compact. -/
theorem sphere_isCompact [Nonempty ι] : IsCompact {v : ι → ℝ | P.nrm2sq v = 1} := by
  -- closed (as a level set of a continuous function) and bounded (`|vᵢ| ≤ √(1/w_min)`)
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_eq P.nrm2sq_continuous continuous_const
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨Real.sqrt (1 / P.wmin), fun v hv => ?_⟩
    have hv' : P.nrm2sq v = 1 := hv
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    have h1 := P.w_mul_sq_le_nrm2sq v i
    rw [hv'] at h1
    have hwmin := P.wmin_pos
    rw [le_div_iff₀ hwmin]
    calc v i ^ 2 * P.wmin ≤ v i ^ 2 * P.w i :=
          mul_le_mul_of_nonneg_left (P.wmin_le i) (sq_nonneg _)
      _ = P.w i * v i ^ 2 := by ring
      _ ≤ 1 := h1


section MainTheorem

variable [Nonempty ι] {u0 : ι → ℝ} (hu0 : ∀ i, 0 < u0 i) (hn : P.nrm2 u0 = 1)
  {γ : ℝ} (hγ : 0 < γ) (hγm : γ ≤ P.γmax u0)
include hu0 hn hγ hγm

/-- Theorem 3.4, the invariant (5.1): for every `k`,
`u^k > 0`, `1 - 3γD ≤ ‖z^k‖₂ ≤ 1` and `𝓛^k ≤ E₀`. -/
theorem invariant (k : ℕ) :
    (∀ i, 0 < P.uiter γ u0 k i) ∧ 1 - 3 * γ * P.D u0 ≤ P.nrm2 (P.iter γ u0 k) ∧
      P.nrm2 (P.iter γ u0 k) ≤ 1 ∧ P.lyap γ (P.iter γ u0 k) ≤ P.E0 u0 := by
  have hu0' : u0 ≠ 0 := GPDYS.ne_zero_of_pos hu0
  have hD := P.D_pos u0 hu0'
  induction k with
  | zero =>
    rw [uiter_def, iter_zero, P.normalize_eq_self hn, hn]
    refine ⟨hu0, ?_, le_refl _,
      P.lyap_init_le_E0 u0 hn hγ (P.conditions_of_le_γmax u0 hu0' hγ hγm)⟩
    have := mul_pos hγ hD
    linarith
  | succ k ih =>
    obtain ⟨hpos, hz1, hz2, hL⟩ := ih
    rw [uiter_def] at hpos
    -- `z^k ≠ 0` since `u^k = z^k/‖z^k‖₂ > 0`
    have hz : P.iter γ u0 k ≠ 0 := by
      intro h0
      obtain ⟨i⟩ := ‹Nonempty ι›
      have hi := hpos i
      rw [h0] at hi
      simp [normalize_def] at hi
    rw [uiter_def, iter_succ]
    have hpos' := P.onestep_pos hu0' hγ hγm hz hpos hz1 hz2 hL
    have hrad := P.onestep_radial hu0' hγ hγm hz hpos hz1 hz2 hL
    have hdrop := P.onestep_drop hu0' hγ hγm hz hpos hz1 hz2 hL
    have hstep_ne : P.step γ (P.iter γ u0 k) ≠ 0 := GPDYS.ne_zero_of_pos hpos'
    refine ⟨P.normalize_pos hstep_ne hpos', hrad.1, hrad.2, ?_⟩
    have h1 : 0 ≤ 1 / 4 * γ * P.nrmXsq γ (P.g (P.normalize (P.iter γ u0 k))) := by
      have := P.nrmXsq_nonneg hγ.le (P.g (P.normalize (P.iter γ u0 k)))
      positivity
    have h2 : 0 ≤ (P.R γ (P.iter γ u0 k)) ^ 2 / (2 * γ) := by positivity
    linarith

theorem iter_ne_zero (k : ℕ) : P.iter γ u0 k ≠ 0 := by
  obtain ⟨hpos, -, -, -⟩ := P.invariant hu0 hn hγ hγm k
  intro h0
  rw [uiter_def, h0] at hpos
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi := hpos i
  simp [normalize_def] at hi

/-- Theorem 3.4, the drop (5.2): `𝓛^k - 𝓛^{k+1} ≥ ¼γ‖g(u^k)‖_X² + (R^k)²/(2γ)`. -/
theorem drop (k : ℕ) :
    P.lyap γ (P.iter γ u0 k) - P.lyap γ (P.iter γ u0 (k + 1))
      ≥ 1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k)) + (P.R γ (P.iter γ u0 k)) ^ 2 / (2 * γ) := by
  have hu0' : u0 ≠ 0 := GPDYS.ne_zero_of_pos hu0
  obtain ⟨hpos, hz1, hz2, hL⟩ := P.invariant hu0 hn hγ hγm k
  rw [uiter_def] at hpos ⊢
  rw [iter_succ]
  exact P.onestep_drop hu0' hγ hγm (P.iter_ne_zero hu0 hn hγ hγm k) hpos hz1 hz2 hL

/-- Theorem 3.4: every finite partial sum
`∑_{k < m} (¼γ‖g^k‖_X² + (R^k)²/(2γ))` is at most `𝓛⁰`. -/
theorem sum_drop_le (m : ℕ) :
    ∑ k ∈ range m, (1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k))
      + (P.R γ (P.iter γ u0 k)) ^ 2 / (2 * γ)) ≤ P.lyap γ u0 := by
  -- the sum telescopes: `∑_{k<m} (𝓛^k - 𝓛^{k+1}) = 𝓛⁰ - 𝓛^m ≤ 𝓛⁰`
  have h1 : ∑ k ∈ range m, (1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k))
      + (P.R γ (P.iter γ u0 k)) ^ 2 / (2 * γ))
      ≤ ∑ k ∈ range m, (P.lyap γ (P.iter γ u0 k) - P.lyap γ (P.iter γ u0 (k + 1))) :=
    Finset.sum_le_sum fun k _ => P.drop hu0 hn hγ hγm k
  have h3 : ∑ k ∈ range m, (P.lyap γ (P.iter γ u0 k) - P.lyap γ (P.iter γ u0 (k + 1)))
      = P.lyap γ (P.iter γ u0 0) - P.lyap γ (P.iter γ u0 m) :=
    Finset.sum_range_sub' (fun k => P.lyap γ (P.iter γ u0 k)) m
  have h2 : 0 ≤ P.lyap γ (P.iter γ u0 m) :=
    (P.energy_nonneg _).trans (P.energy_le_lyap hγ _)
  rw [iter_zero] at h3
  linarith

/-- The descent terms `¼γ‖g^k‖_X² + (R^k)²/(2γ)` are summable. -/
theorem drop_summable :
    Summable (fun k => 1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k))
      + (P.R γ (P.iter γ u0 k)) ^ 2 / (2 * γ)) :=
  summable_of_sum_range_le
    (fun k => by
      have := P.nrmXsq_nonneg hγ.le (P.g (P.uiter γ u0 k))
      positivity)
    (P.sum_drop_le hu0 hn hγ hγm)

/-- `‖g(u^k)‖_X² → 0`. -/
theorem nrmXsq_g_tendsto_zero :
    Tendsto (fun k => P.nrmXsq γ (P.g (P.uiter γ u0 k))) atTop (𝓝 0) := by
  have hsum := (P.drop_summable hu0 hn hγ hγm).tendsto_atTop_zero
  have h1 : Tendsto (fun k => 1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k))) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => ?_) (fun k => ?_) hsum
    · have := P.nrmXsq_nonneg hγ.le (P.g (P.uiter γ u0 k))
      positivity
    · have : 0 ≤ (P.R γ (P.iter γ u0 k)) ^ 2 / (2 * γ) := by positivity
      linarith
  exact tendsto_zero_of_const_mul_tendsto_zero (by positivity) h1

/-- `R^k → 0`. -/
theorem R_tendsto_zero : Tendsto (fun k => P.R γ (P.iter γ u0 k)) atTop (𝓝 0) := by
  have hsum := (P.drop_summable hu0 hn hγ hγm).tendsto_atTop_zero
  have h1 : Tendsto (fun k => (2 * γ)⁻¹ * (P.R γ (P.iter γ u0 k)) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => by positivity) (fun k => ?_) hsum
    have := P.nrmXsq_nonneg hγ.le (P.g (P.uiter γ u0 k))
    have : 0 ≤ 1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k)) := by positivity
    rw [inv_mul_eq_div]
    linarith
  exact tendsto_zero_of_sq_tendsto_zero
    (tendsto_zero_of_const_mul_tendsto_zero (by positivity) h1)

/-- Theorem 3.4: `g(u^k) → 0`. -/
theorem g_tendsto_zero : Tendsto (fun k => P.g (P.uiter γ u0 k)) atTop (𝓝 0) := by
  -- `‖g^k‖₂² ≤ (1 + γμ) ‖g^k‖_X² → 0`, then componentwise `wᵢ (g^k)ᵢ² ≤ ‖g^k‖₂²`
  obtain ⟨μ, hμ0, hμ⟩ := P.exists_kin_bound
  have hX := P.nrmXsq_g_tendsto_zero hu0 hn hγ hγm
  have h2 : Tendsto (fun k => P.nrm2sq (P.g (P.uiter γ u0 k))) atTop (𝓝 0) := by
    have h3 := hX.const_mul (1 + γ * μ)
    rw [mul_zero] at h3
    exact squeeze_zero (fun k => P.nrm2sq_nonneg _)
      (fun k => P.nrm2sq_le_mul_nrmXsq hγ.le hμ0 hμ _) h3
  rw [tendsto_pi_nhds]
  intro i
  simp only [Pi.zero_apply]
  apply tendsto_zero_of_sq_tendsto_zero
  have h4 : Tendsto (fun k => (P.w i)⁻¹ * P.nrm2sq (P.g (P.uiter γ u0 k))) atTop (𝓝 0) := by
    have := h2.const_mul (P.w i)⁻¹
    rwa [mul_zero] at this
  refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) h4
  have hw := P.w_pos i
  have h5 := P.w_mul_sq_le_nrm2sq (P.g (P.uiter γ u0 k)) i
  rw [← div_eq_inv_mul, le_div_iff₀ hw]
  linarith

/-- Theorem 3.4: every accumulation point of `(u^k)`
is a nonnegative critical point of `E_h` on `𝓜`. -/
theorem accumulation_point_critical {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) {ustar : ι → ℝ}
    (hlim : Tendsto (fun j => P.uiter γ u0 (ns j)) atTop (𝓝 ustar)) :
    P.nrm2sq ustar = 1 ∧ (∀ i, 0 ≤ ustar i) ∧ P.g ustar = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · -- `‖u^{n_j}‖₂² = 1` and `‖·‖₂²` is continuous
    have h1 : Tendsto (fun j => P.nrm2sq (P.uiter γ u0 (ns j))) atTop (𝓝 (P.nrm2sq ustar)) :=
      (P.nrm2sq_continuous.tendsto ustar).comp hlim
    have h2 : Tendsto (fun j => P.nrm2sq (P.uiter γ u0 (ns j))) atTop (𝓝 1) := by
      have h3 : (fun j => P.nrm2sq (P.uiter γ u0 (ns j))) = fun _ => (1 : ℝ) := by
        funext j
        rw [uiter_def, P.nrm2sq_normalize (P.iter_ne_zero hu0 hn hγ hγm (ns j))]
      rw [h3]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  · -- `u^{n_j} > 0` componentwise
    intro i
    have h1 := tendsto_pi_nhds.mp hlim i
    exact ge_of_tendsto' h1 fun j => ((P.invariant hu0 hn hγ hγm (ns j)).1 i).le
  · -- `g(u^{n_j}) → g(u*)` by continuity and `g(u^{n_j}) → 0`
    have h1 : Tendsto (fun j => P.g (P.uiter γ u0 (ns j))) atTop (𝓝 (P.g ustar)) :=
      (P.g_continuous.tendsto ustar).comp hlim
    have h2 : Tendsto (fun j => P.g (P.uiter γ u0 (ns j))) atTop (𝓝 0) :=
      (P.g_tendsto_zero hu0 hn hγ hγm).comp hns
    exact tendsto_nhds_unique h1 h2

/-- The normalized iterates lie on the sphere `𝓜`. -/
theorem uiter_mem_sphere (k : ℕ) : P.uiter γ u0 k ∈ {v : ι → ℝ | P.nrm2sq v = 1} :=
  show P.nrm2sq (P.uiter γ u0 k) = 1 from
    P.nrm2sq_normalize (P.iter_ne_zero hu0 hn hγ hγm k)

/-- Existence of an accumulation point. -/
theorem exists_accumulation_point :
    ∃ ustar : ι → ℝ, ∃ ns : ℕ → ℕ, StrictMono ns ∧
      Tendsto (fun j => P.uiter γ u0 (ns j)) atTop (𝓝 ustar) := by
  obtain ⟨a, -, φ, hφ, hlim⟩ :=
    P.sphere_isCompact.tendsto_subseq (P.uiter_mem_sphere hu0 hn hγ hγm)
  exact ⟨a, φ, hφ, hlim⟩

/-- **Theorem 3.4** (global convergence to the discrete ground state). Under
Assumption 2.1 (through Lemma 2.2), for a positive normalized initial vector `u⁰` and a step
size `0 < γ ≤ γ_max`, the iterates `u^k = z^k/‖z^k‖₂` of (DYS I) are positive for every `k`,
and converge to the discrete ground state `u_GS`, the unique positive global minimizer of `E_h`
on `𝓜`, which is also the unique nonnegative critical point of `E_h|_𝓜`; moreover
`E_h(u^k) → E_h(u_GS) = min_𝓜 E_h`. -/
theorem main_theorem :
    (∀ k i, 0 < P.uiter γ u0 k i) ∧
    ∃ uGS : ι → ℝ,
      (∀ i, 0 < uGS i) ∧ P.nrm2 uGS = 1 ∧ P.g uGS = 0 ∧
      (∀ v, P.nrm2 v = 1 → P.energy uGS ≤ P.energy v) ∧
      (∀ v, P.nrm2 v = 1 → (∀ i, 0 ≤ v i) → P.energy v ≤ P.energy uGS → v = uGS) ∧
      (∀ v, P.nrm2 v = 1 → (∀ i, 0 ≤ v i) → P.g v = 0 → v = uGS) ∧
      Tendsto (P.uiter γ u0) atTop (𝓝 uGS) ∧
      Tendsto (fun k => P.energy (P.uiter γ u0 k)) atTop (𝓝 (P.energy uGS)) := by
  have hinv := P.invariant hu0 hn hγ hγm
  refine ⟨fun k i => (hinv k).1 i, ?_⟩
  -- an accumulation point `u*`: a nonnegative, hence positive, critical point on `𝓜`
  obtain ⟨ustar, ns, hns, hlim⟩ := P.exists_accumulation_point hu0 hn hγ hγm
  obtain ⟨hs1, hs2, hs3⟩ :=
    P.accumulation_point_critical hu0 hn hγ hγm hns.tendsto_atTop hlim
  have hpos : ∀ i, 0 < ustar i := P.critical_pos hs1 hs2 hs3
  -- the whole sequence converges to `u*`: every subsequence has a further subsequence
  -- converging to a nonnegative critical point, which must be `u*` by uniqueness
  have hconv : Tendsto (P.uiter γ u0) atTop (𝓝 ustar) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ms hms
    obtain ⟨v, -, φ, hφ, hvlim⟩ :=
      P.sphere_isCompact.tendsto_subseq
        (fun j => P.uiter_mem_sphere hu0 hn hγ hγm (ms j))
    refine ⟨φ, ?_⟩
    have hcomp : Tendsto (fun n => ms (φ n)) atTop atTop := hms.comp hφ.tendsto_atTop
    have hvlim' : Tendsto (fun n => P.uiter γ u0 (ms (φ n))) atTop (𝓝 v) := hvlim
    obtain ⟨hv1, hv2, hv3⟩ := P.accumulation_point_critical hu0 hn hγ hγm hcomp hvlim'
    have hveq : v = ustar := P.eq_of_critical_nonneg hs1 hs2 hs3 hv1 hv2 hv3
    rw [hveq] at hvlim'
    exact hvlim'
  refine ⟨ustar, hpos, P.nrm2_eq_one_of_nrm2sq hs1, hs3, ?_, ?_, ?_, hconv, ?_⟩
  · intro v hv
    exact P.energy_le_of_critical hs1 hpos hs3 (P.nrm2sq_eq_one_of_nrm2 hv)
  · intro v hv hvnn hE
    exact P.eq_of_nonneg_le_energy hs1 hpos hs3 (P.nrm2sq_eq_one_of_nrm2 hv) hvnn hE
  · intro v hv hvnn hg
    exact P.eq_of_critical_nonneg hs1 hs2 hs3 (P.nrm2sq_eq_one_of_nrm2 hv) hvnn hg
  · exact (P.energy_continuous.tendsto ustar).comp hconv

end MainTheorem

/-- **Corollary** (the discrete ground state, Remark 2.3). There is a positive `u_GS ∈ 𝓜` which
is a critical point of `E_h|_𝓜`, the global minimizer of `E_h` on `𝓜`, and the unique
nonnegative critical point. It is obtained from Theorem 3.4 as the limit of the iteration
started from the normalized constant vector with the step size `γ_max`. -/
theorem exists_groundState [Nonempty ι] :
    ∃ uGS : ι → ℝ, (∀ i, 0 < uGS i) ∧ P.nrm2 uGS = 1 ∧ P.g uGS = 0 ∧
      (∀ v, P.nrm2 v = 1 → P.energy uGS ≤ P.energy v) ∧
      (∀ v, P.nrm2 v = 1 → (∀ i, 0 ≤ v i) → P.g v = 0 → v = uGS) := by
  set one : ι → ℝ := fun _ => 1 with hone_def
  have hone : one ≠ 0 := by
    intro h
    have := congrFun h (Classical.arbitrary ι)
    simp [hone_def] at this
  set u0 := P.normalize one with hu0_def
  have hu0 : ∀ i, 0 < u0 i := P.normalize_pos hone (fun _ => one_pos)
  have hn : P.nrm2 u0 = 1 := P.nrm2_normalize hone
  have hu0' : u0 ≠ 0 := GPDYS.ne_zero_of_pos hu0
  have hγ : 0 < P.γmax u0 := P.γmax_pos u0 hu0'
  obtain ⟨_, uGS, h1, h2, h3, h4, _, h6, _, _⟩ := P.main_theorem hu0 hn hγ le_rfl
  exact ⟨uGS, h1, h2, h3, h4, h6⟩

end Setting

end GPDYS

end
