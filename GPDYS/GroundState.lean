import GPDYS.Resolvent
import GPDYS.Constants

/-!
# The discrete ground state (Remark 2.3 and Appendix A)

The facts about the discrete ground state used in the convergence proof, namely that every
nonnegative critical point of `E_h` on the sphere `𝓜` is strictly positive, is the global
minimizer of `E_h` on `𝓜`, and is the only nonnegative critical point. The paper quotes these
facts from the literature (Perron–Frobenius for irreducible M-matrices and the hidden convexity
of the energy in the density variables). Here they are proven directly from the properties of
Lemma 2.2 by means of a discrete Picone inequality (as in Hauck–Peterseim):

* `picone`: for `u > 0` and any `v`, `vᵀ S v ≥ ∑ᵢ (vᵢ²/uᵢ)(S u)ᵢ`;
* `energy_abs_le`: `E_h(|v|) ≤ E_h(v)`, by the sign condition on the off-diagonal entries;
* `critical_pos`: a nonnegative critical point is positive, by the entrywise positivity of
  the resolvent `(M + γS)⁻¹`;
* `energy_ge_of_critical`: if `u > 0` is a critical point then
  `E_h(v) ≥ E_h(u) + (β/4) ∑ᵢ wᵢ (vᵢ² - uᵢ²)²` for every nonnegative `v ∈ 𝓜`,
  which gives global minimality and uniqueness.
-/

open Finset Matrix

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- `vᵀ S v` written as a double sum. -/
theorem kin_eq_double_sum (v : ι → ℝ) :
    P.kin v = ∑ i, ∑ j, P.S i j * (v i * v j) := by
  rw [kin_def, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The discrete Picone inequality used here to prove Remark 2.3.
For `u > 0` componentwise and any `v`,
`∑ᵢ (vᵢ²/uᵢ) (S u)ᵢ ≤ vᵀ S v`. -/
theorem picone {u : ι → ℝ} (hu : ∀ i, 0 < u i) (v : ι → ℝ) :
    ∑ i, (v i ^ 2 / u i) * (P.S *ᵥ u) i ≤ P.kin v := by
  have hS : ∀ i j, P.S j i = P.S i j := fun i j => P.S_symm.apply i j
  have hLHS : ∑ i, (v i ^ 2 / u i) * (P.S *ᵥ u) i
      = ∑ i, ∑ j, P.S i j * (v i ^ 2 / u i * u j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hkin := P.kin_eq_double_sum v
  -- the per-pair identity: `A i j + A j i = -T i j`
  have hAT : ∀ i j, P.S i j * (v i * v j - v i ^ 2 / u i * u j)
      + P.S j i * (v j * v i - v j ^ 2 / u j * u i)
      = - (P.S i j * ((v i * u j - v j * u i) ^ 2 / (u i * u j))) := by
    intro i j
    rw [hS i j]
    have hui := (hu i).ne'
    have huj := (hu j).ne'
    field_simp
    ring
  -- `∑ᵢⱼ T i j ≤ 0`: the diagonal terms vanish and the off-diagonal ones are nonpositive
  have hT : ∑ i, ∑ j, P.S i j * ((v i * u j - v j * u i) ^ 2 / (u i * u j)) ≤ 0 := by
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    by_cases hij : i = j
    · subst hij; simp
    · have h1 := P.S_offdiag i j hij
      have h2 : 0 ≤ (v i * u j - v j * u i) ^ 2 / (u i * u j) :=
        div_nonneg (sq_nonneg _) (mul_pos (hu i) (hu j)).le
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2
  -- symmetrization: `2 ∑ᵢⱼ A i j = - ∑ᵢⱼ T i j`
  have hsum : ∑ i, ∑ j, P.S i j * (v i * v j - v i ^ 2 / u i * u j)
      = ∑ i, ∑ j, P.S j i * (v j * v i - v j ^ 2 / u j * u i) := Finset.sum_comm
  have h2 : 2 * ∑ i, ∑ j, P.S i j * (v i * v j - v i ^ 2 / u i * u j)
      = - ∑ i, ∑ j, P.S i j * ((v i * u j - v j * u i) ^ 2 / (u i * u j)) := by
    rw [two_mul]
    nth_rewrite 2 [hsum]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact hAT i j
  have hdiff : P.kin v - ∑ i, (v i ^ 2 / u i) * (P.S *ᵥ u) i
      = ∑ i, ∑ j, P.S i j * (v i * v j - v i ^ 2 / u i * u j) := by
    rw [hkin, hLHS, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith

/-- `|v|ᵀ S |v| ≤ vᵀ S v`, since the off-diagonal entries of `S` are nonpositive. -/
theorem kin_abs_le (v : ι → ℝ) : P.kin (fun i => |v i|) ≤ P.kin v := by
  rw [kin_eq_double_sum, kin_eq_double_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  by_cases hij : i = j
  · subst hij
    rw [abs_mul_abs_self]
  · have hS := P.S_offdiag i j hij
    have h1 : v i * v j ≤ |v i| * |v j| := by rw [← abs_mul]; exact le_abs_self _
    exact mul_le_mul_of_nonpos_left h1 hS

/-- `E_h(|v|) ≤ E_h(v)`. -/
theorem energy_abs_le (v : ι → ℝ) : P.energy (fun i => |v i|) ≤ P.energy v := by
  rw [energy_eq, energy_eq]
  have hpot : P.pot (fun i => |v i|) = P.pot v := by
    unfold pot; simp only [sq_abs]
  have h4 : wnorm4p4 P.w (fun i => |v i|) = wnorm4p4 P.w v := by
    unfold wnorm4p4
    simp only [Even.pow_abs (by decide : Even 4)]
  have hk := P.kin_abs_le v
  rw [hpot, h4]
  linarith

/-- `‖ |v| ‖₂² = ‖v‖₂²`. -/
theorem nrm2sq_abs (v : ι → ℝ) : P.nrm2sq (fun i => |v i|) = P.nrm2sq v := by
  rw [nrm2sq_eq_sum, nrm2sq_eq_sum]
  simp only [sq_abs]

/-- A critical point satisfies `-Δ_h v = λ(v) v - n(v)`. -/
theorem negLap_eq_of_critical {v : ι → ℝ} (hg : P.g v = 0) :
    P.negLap v = P.lam v • v - P.nonlin v := by
  have h := P.gradE_eq_lam_smul_add_g v
  rw [hg, add_zero, gradE_def] at h
  exact eq_sub_of_add_eq h

/-- Remark 2.3: a nonnegative critical point of `E_h` on `𝓜` is strictly positive. -/
theorem critical_pos [Nonempty ι] {v : ι → ℝ} (hv : P.nrm2sq v = 1) (hnn : ∀ i, 0 ≤ v i)
    (hg : P.g v = 0) (i : ι) : 0 < v i := by
  have hβ := P.β_pos
  have hwmin := P.wmin_pos
  have hVinf := P.Vinf_nonneg
  have hlam := P.lam_nonneg v
  -- a step size `γ > 0` with `γ (‖V‖_∞ + β / w_min) < 1`
  obtain ⟨γ, hγ, hγK⟩ : ∃ γ : ℝ, 0 < γ ∧ γ * (P.Vinf + P.β / P.wmin) < 1 := by
    refine ⟨1 / (1 + (P.Vinf + P.β / P.wmin)), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  -- `vⱼ² ≤ 1 / w_min` since `‖v‖₂ = 1`
  have hsq : ∀ j, v j ^ 2 ≤ 1 / P.wmin := by
    intro j
    have h1 := P.w_mul_sq_le_nrm2sq v j
    rw [hv] at h1
    have h2 := P.wmin_le j
    rw [le_div_iff₀ hwmin]
    calc v j ^ 2 * P.wmin ≤ v j ^ 2 * P.w j := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = P.w j * v j ^ 2 := by ring
      _ ≤ 1 := h1
  -- the diagonal factors `κⱼ = 1 + γ (λ(v) - Vⱼ - β vⱼ²)` are positive
  have hκ : ∀ j, 0 < 1 + γ * (P.lam v - P.V j - P.β * v j ^ 2) := by
    intro j
    have h1 := P.le_Vinf j
    have h3 : P.β * v j ^ 2 ≤ P.β / P.wmin := by
      calc P.β * v j ^ 2 ≤ P.β * (1 / P.wmin) := mul_le_mul_of_nonneg_left (hsq j) hβ.le
        _ = P.β / P.wmin := by ring
    have h6 : γ * (-(P.Vinf + P.β / P.wmin)) ≤ γ * (P.lam v - P.V j - P.β * v j ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hγ.le
      linarith
    linarith
  -- `G_X v = κ v`, hence `v = G_X⁻¹ (κ v)` with `κ v ≥ 0`, `κ v ≠ 0`
  have key : v = P.resolvent γ (fun j => (1 + γ * (P.lam v - P.V j - P.β * v j ^ 2)) * v j) := by
    apply (P.GX_eq_iff hγ.le _ v).mp
    funext j
    simp only [GX_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, P.negLap_eq_of_critical hg,
      Pi.sub_apply, nonlin_apply]
    ring
  rw [key]
  apply P.resolvent_pos_of_nonneg hγ
  · intro j
    exact mul_nonneg (hκ j).le (hnn j)
  · intro h0
    have hv0 : v = 0 := by
      funext j
      have hj := congrFun h0 j
      simp only [Pi.zero_apply] at hj
      rcases mul_eq_zero.mp hj with h | h
      · exact absurd h (hκ j).ne'
      · exact h
    rw [(P.nrm2sq_eq_zero_iff v).mpr hv0] at hv
    exact zero_ne_one hv

/-- The key inequality used here to prove Remark 2.3:
for a positive critical point `u ∈ 𝓜` and any nonnegative `v ∈ 𝓜`,
`E_h(v) ≥ E_h(u) + (β/4) ∑ᵢ wᵢ (vᵢ² - uᵢ²)²`. -/
theorem energy_ge_of_critical {u v : ι → ℝ} (hu : P.nrm2sq u = 1) (hupos : ∀ i, 0 < u i)
    (hg : P.g u = 0) (hv : P.nrm2sq v = 1) (hvnn : ∀ i, 0 ≤ v i) :
    P.energy u + P.β / 4 * ∑ i, P.w i * (v i ^ 2 - u i ^ 2) ^ 2 ≤ P.energy v := by
  have hpic := P.picone hupos v
  have hneg := P.negLap_eq_of_critical hg
  -- `(S u)ᵢ = wᵢ (λ(u) uᵢ - Vᵢ uᵢ - β uᵢ³)`
  have hSu : ∀ i, (P.S *ᵥ u) i = (P.lam u * u i - (P.V i * u i + P.β * u i ^ 3)) * P.w i := by
    intro i
    have h1 : P.negLap u i = P.lam u * u i - (P.V i * u i + P.β * u i ^ 3) := by
      rw [hneg]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nonlin_apply]
    rw [negLap_apply, div_eq_iff (P.w_pos i).ne'] at h1
    exact h1
  -- the Picone sum is `λ(u) ‖v‖₂² - ⟪V v, v⟫_h - β ∑ᵢ wᵢ uᵢ² vᵢ²`
  have hsum : ∑ i, (v i ^ 2 / u i) * (P.S *ᵥ u) i
      = P.lam u * P.nrm2sq v - P.pot v - P.β * ∑ i, P.w i * (u i ^ 2 * v i ^ 2) := by
    rw [nrm2sq_eq_sum, pot, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hSu i]
    have := (hupos i).ne'
    field_simp
    ring
  rw [hv, mul_one] at hsum
  have hEu := P.lam_eq_energy u
  have hEv := P.energy_eq v
  -- `∑ᵢ wᵢ (vᵢ² - uᵢ²)² = ‖v‖₄⁴ - 2 ∑ᵢ wᵢ uᵢ² vᵢ² + ‖u‖₄⁴`
  have hsq : ∑ i, P.w i * (v i ^ 2 - u i ^ 2) ^ 2
      = wnorm4p4 P.w v - 2 * ∑ i, P.w i * (u i ^ 2 * v i ^ 2) + wnorm4p4 P.w u := by
    unfold wnorm4p4
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsq]
  linarith

/-- Remark 2.3: a positive critical point is a global minimizer of `E_h` on `𝓜`. -/
theorem energy_le_of_critical {u v : ι → ℝ} (hu : P.nrm2sq u = 1) (hupos : ∀ i, 0 < u i)
    (hg : P.g u = 0) (hv : P.nrm2sq v = 1) : P.energy u ≤ P.energy v := by
  have h1 := P.energy_ge_of_critical hu hupos hg (v := fun i => |v i|)
    (by rw [nrm2sq_abs]; exact hv) (fun i => abs_nonneg _)
  beta_reduce at h1
  have h2 := P.energy_abs_le v
  have hβ := P.β_pos
  have h3 : 0 ≤ P.β / 4 * ∑ i, P.w i * (|v i| ^ 2 - u i ^ 2) ^ 2 := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => mul_nonneg (P.w_pos i).le (sq_nonneg _)
  linarith

/-- Remark 2.3, uniqueness: a nonnegative `v ∈ 𝓜` with `E_h(v) ≤ E_h(u)`,
where `u > 0` is a critical point, equals `u`. -/
theorem eq_of_nonneg_le_energy {u v : ι → ℝ} (hu : P.nrm2sq u = 1) (hupos : ∀ i, 0 < u i)
    (hg : P.g u = 0) (hv : P.nrm2sq v = 1) (hvnn : ∀ i, 0 ≤ v i)
    (hE : P.energy v ≤ P.energy u) : v = u := by
  have h1 := P.energy_ge_of_critical hu hupos hg hv hvnn
  have hβ := P.β_pos
  have hterm : ∀ i, 0 ≤ P.w i * (v i ^ 2 - u i ^ 2) ^ 2 :=
    fun i => mul_nonneg (P.w_pos i).le (sq_nonneg _)
  have hsum0 : 0 ≤ ∑ i, P.w i * (v i ^ 2 - u i ^ 2) ^ 2 :=
    Finset.sum_nonneg fun i _ => hterm i
  -- the sum `∑ᵢ wᵢ (vᵢ² - uᵢ²)²` vanishes
  have hsum : ∑ i, P.w i * (v i ^ 2 - u i ^ 2) ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < ∑ i, P.w i * (v i ^ 2 - u i ^ 2) ^ 2 := lt_of_le_of_ne hsum0 (Ne.symm hne)
    have hβ4 : 0 < P.β / 4 := by positivity
    have := mul_pos hβ4 hpos
    linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)] at hsum
  funext i
  have hi := hsum i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hi with h | h
  · exact absurd h (P.w_pos i).ne'
  · have h2 : v i ^ 2 = u i ^ 2 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      linarith
    exact (sq_eq_sq₀ (hvnn i) (hupos i).le).mp h2

/-- Remark 2.3, uniqueness of the nonnegative critical point: two nonnegative critical points on `𝓜`
coincide. -/
theorem eq_of_critical_nonneg [Nonempty ι] {u v : ι → ℝ} (hu : P.nrm2sq u = 1)
    (hunn : ∀ i, 0 ≤ u i) (hgu : P.g u = 0) (hv : P.nrm2sq v = 1) (hvnn : ∀ i, 0 ≤ v i)
    (hgv : P.g v = 0) : v = u := by
  have hupos := P.critical_pos hu hunn hgu
  have hvpos := P.critical_pos hv hvnn hgv
  have hE : P.energy v ≤ P.energy u := P.energy_le_of_critical hv hvpos hgv hu
  exact P.eq_of_nonneg_le_energy hu hupos hgu hv hvnn hE

end Setting

end GPDYS

end
