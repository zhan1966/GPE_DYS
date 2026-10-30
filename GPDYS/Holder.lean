import GPDYS.Lemmas

/-!
# Weighted Hölder inequalities

The Hölder inequalities for the quadrature norms used in Lemma 4.3 of the paper:

* `∑ᵢ wᵢ aᵢ² bᵢ² ≤ ‖a‖₆² ‖b‖₃²` (exponents `3` and `3/2`),
* `‖b‖₃² ≤ ‖b‖₂ ‖b‖₆` (exponents `4/3` and `4`),
* `∑ᵢ wᵢ |uᵢ|³ |cᵢ|³ ≤ ‖u‖₆³ ‖c‖₆³` (Cauchy–Schwarz),

together with elementary facts about `‖·‖₃`, `‖·‖₆` (`GPDYS.wnorm3`, `GPDYS.wnorm6`).
-/

open Finset

noncomputable section

namespace GPDYS

variable {ι : Type*} [Fintype ι]

/-- `‖v‖₆⁶ ≥ 0` for nonnegative weights. -/
theorem wnorm6p6_nonneg' (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ι → ℝ) : 0 ≤ wnorm6p6 w v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (by positivity)

/-- `‖v‖₃³ ≥ 0` for nonnegative weights. -/
theorem wnorm3p3_nonneg' (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ι → ℝ) : 0 ≤ wnorm3p3 w v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (by positivity)

/-- `‖v‖₆ ≥ 0` for nonnegative weights. -/
theorem wnorm6_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ι → ℝ) : 0 ≤ wnorm6 w v :=
  Real.rpow_nonneg (wnorm6p6_nonneg' w hw v) _

/-- `‖v‖₃ ≥ 0` for nonnegative weights. -/
theorem wnorm3_nonneg (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ι → ℝ) : 0 ≤ wnorm3 w v :=
  Real.rpow_nonneg (wnorm3p3_nonneg' w hw v) _

/-- `‖v‖₆⁶ = ∑ᵢ wᵢ vᵢ⁶` for nonnegative weights. -/
theorem wnorm6_pow_six (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ι → ℝ) :
    wnorm6 w v ^ 6 = wnorm6p6 w v := by
  unfold wnorm6
  rw [← Real.rpow_mul_natCast (wnorm6p6_nonneg' w hw v)]
  norm_num

/-- `‖v‖₃³ = ∑ᵢ wᵢ |vᵢ|³` for nonnegative weights. -/
theorem wnorm3_pow_three (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ι → ℝ) :
    wnorm3 w v ^ 3 = wnorm3p3 w v := by
  unfold wnorm3
  rw [← Real.rpow_mul_natCast (wnorm3p3_nonneg' w hw v)]
  norm_num

/-- `‖v²‖₃ = ‖v‖₆²` (componentwise square). -/
theorem wnorm3_sq_eq (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (v : ι → ℝ) :
    wnorm3 w (fun i => v i ^ 2) = wnorm6 w v ^ 2 := by
  have h : wnorm3p3 w (fun i => v i ^ 2) = wnorm6p6 w v := by
    unfold wnorm3p3 wnorm6p6
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    ring
  unfold wnorm3 wnorm6
  rw [h, ← Real.rpow_mul_natCast (wnorm6p6_nonneg' w hw v)]
  norm_num

/-- Hölder with exponents `3` and `3/2`: `∑ᵢ wᵢ aᵢ² bᵢ² ≤ ‖a‖₆² ‖b‖₃²`. -/
theorem holder_six_three (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a b : ι → ℝ) :
    ∑ i, w i * (a i ^ 2 * b i ^ 2) ≤ wnorm6 w a ^ 2 * wnorm3 w b ^ 2 := by
  -- Hölder for the unweighted sum with `fᵢ = wᵢ^{1/3} aᵢ²`, `gᵢ = wᵢ^{2/3} bᵢ²`.
  have hpq : (3:ℝ).HolderConjugate (3/2) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hf0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i ^ ((1:ℝ)/3) * a i ^ 2 :=
    fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (sq_nonneg _)
  have hg0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i ^ ((2:ℝ)/3) * b i ^ 2 :=
    fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (sq_nonneg _)
  have key : ∑ i, (w i ^ ((1:ℝ)/3) * a i ^ 2) * (w i ^ ((2:ℝ)/3) * b i ^ 2)
      ≤ (∑ i, (w i ^ ((1:ℝ)/3) * a i ^ 2) ^ (3:ℝ)) ^ (1/(3:ℝ))
        * (∑ i, (w i ^ ((2:ℝ)/3) * b i ^ 2) ^ ((3:ℝ)/2)) ^ (1/((3:ℝ)/2)) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq hf0 hg0
  -- `fᵢ gᵢ = wᵢ aᵢ² bᵢ²`
  have e1 : ∑ i, (w i ^ ((1:ℝ)/3) * a i ^ 2) * (w i ^ ((2:ℝ)/3) * b i ^ 2)
      = ∑ i, w i * (a i ^ 2 * b i ^ 2) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : w i ^ ((1:ℝ)/3) * w i ^ ((2:ℝ)/3) = w i := by
      rw [← Real.rpow_add' (hw i) (by norm_num)]; norm_num
    calc w i ^ ((1:ℝ)/3) * a i ^ 2 * (w i ^ ((2:ℝ)/3) * b i ^ 2)
        = (w i ^ ((1:ℝ)/3) * w i ^ ((2:ℝ)/3)) * (a i ^ 2 * b i ^ 2) := by ring
      _ = w i * (a i ^ 2 * b i ^ 2) := by rw [h1]
  -- `fᵢ³ = wᵢ aᵢ⁶`
  have e2 : ∑ i, (w i ^ ((1:ℝ)/3) * a i ^ 2) ^ (3:ℝ) = wnorm6p6 w a := by
    unfold wnorm6p6
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (sq_nonneg _), ← Real.rpow_mul (hw i),
      Real.rpow_ofNat, show (1:ℝ)/3 * 3 = 1 by norm_num, Real.rpow_one]
    ring
  -- `gᵢ^{3/2} = wᵢ |bᵢ|³`
  have e3 : ∑ i, (w i ^ ((2:ℝ)/3) * b i ^ 2) ^ ((3:ℝ)/2) = wnorm3p3 w b := by
    unfold wnorm3p3
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (sq_nonneg _), ← Real.rpow_mul (hw i),
      show (2:ℝ)/3 * (3/2) = 1 by norm_num, Real.rpow_one, ← sq_abs (b i), ← Real.rpow_two,
      ← Real.rpow_mul (abs_nonneg _), show (2:ℝ) * (3/2) = 3 by norm_num, Real.rpow_ofNat]
  -- `(‖a‖₆⁶)^{1/3} = ‖a‖₆²` and `(‖b‖₃³)^{2/3} = ‖b‖₃²`
  have e4 : (wnorm6p6 w a) ^ (1/(3:ℝ)) = wnorm6 w a ^ 2 := by
    unfold wnorm6
    rw [← Real.rpow_mul_natCast (wnorm6p6_nonneg' w hw a)]
    norm_num
  have e5 : (wnorm3p3 w b) ^ (1/((3:ℝ)/2)) = wnorm3 w b ^ 2 := by
    unfold wnorm3
    rw [← Real.rpow_mul_natCast (wnorm3p3_nonneg' w hw b)]
    norm_num
  rw [e1, e2, e3, e4, e5] at key
  exact key

/-- Hölder with exponents `4/3` and `4`: `‖b‖₃² ≤ ‖b‖₂ ‖b‖₆`. -/
theorem wnorm3_sq_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (b : ι → ℝ) :
    wnorm3 w b ^ 2 ≤ wnorm2 w b * wnorm6 w b := by
  -- Hölder for the unweighted sum with `fᵢ = wᵢ^{3/4} |bᵢ|^{3/2}`, `gᵢ = wᵢ^{1/4} |bᵢ|^{3/2}`.
  have hpq : ((4:ℝ)/3).HolderConjugate 4 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hf0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i ^ ((3:ℝ)/4) * |b i| ^ ((3:ℝ)/2) :=
    fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hg0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i ^ ((1:ℝ)/4) * |b i| ^ ((3:ℝ)/2) :=
    fun i _ => mul_nonneg (Real.rpow_nonneg (hw i) _) (Real.rpow_nonneg (abs_nonneg _) _)
  have key : ∑ i, (w i ^ ((3:ℝ)/4) * |b i| ^ ((3:ℝ)/2)) * (w i ^ ((1:ℝ)/4) * |b i| ^ ((3:ℝ)/2))
      ≤ (∑ i, (w i ^ ((3:ℝ)/4) * |b i| ^ ((3:ℝ)/2)) ^ ((4:ℝ)/3)) ^ (1/((4:ℝ)/3))
        * (∑ i, (w i ^ ((1:ℝ)/4) * |b i| ^ ((3:ℝ)/2)) ^ (4:ℝ)) ^ (1/(4:ℝ)) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg Finset.univ hpq hf0 hg0
  -- `fᵢ gᵢ = wᵢ |bᵢ|³`
  have e1 : ∑ i, (w i ^ ((3:ℝ)/4) * |b i| ^ ((3:ℝ)/2)) * (w i ^ ((1:ℝ)/4) * |b i| ^ ((3:ℝ)/2))
      = wnorm3p3 w b := by
    unfold wnorm3p3
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : w i ^ ((3:ℝ)/4) * w i ^ ((1:ℝ)/4) = w i := by
      rw [← Real.rpow_add' (hw i) (by norm_num)]; norm_num
    have h2 : |b i| ^ ((3:ℝ)/2) * |b i| ^ ((3:ℝ)/2) = |b i| ^ 3 := by
      rw [← Real.rpow_add' (abs_nonneg _) (by norm_num)]; norm_num
    calc (w i ^ ((3:ℝ)/4) * |b i| ^ ((3:ℝ)/2)) * (w i ^ ((1:ℝ)/4) * |b i| ^ ((3:ℝ)/2))
        = (w i ^ ((3:ℝ)/4) * w i ^ ((1:ℝ)/4)) * (|b i| ^ ((3:ℝ)/2) * |b i| ^ ((3:ℝ)/2)) := by
          ring
      _ = w i * |b i| ^ 3 := by rw [h1, h2]
  -- `fᵢ^{4/3} = wᵢ bᵢ²`
  have e2 : ∑ i, (w i ^ ((3:ℝ)/4) * |b i| ^ ((3:ℝ)/2)) ^ ((4:ℝ)/3) = wnorm2sq w b := by
    unfold wnorm2sq winner
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_mul (hw i), ← Real.rpow_mul (abs_nonneg _),
      show (3:ℝ)/4 * (4/3) = 1 by norm_num, show (3:ℝ)/2 * (4/3) = 2 by norm_num,
      Real.rpow_one, Real.rpow_two, sq_abs]
    ring
  -- `gᵢ⁴ = wᵢ bᵢ⁶`
  have e3 : ∑ i, (w i ^ ((1:ℝ)/4) * |b i| ^ ((3:ℝ)/2)) ^ (4:ℝ) = wnorm6p6 w b := by
    unfold wnorm6p6
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.mul_rpow (Real.rpow_nonneg (hw i) _) (Real.rpow_nonneg (abs_nonneg _) _),
      ← Real.rpow_mul (hw i), ← Real.rpow_mul (abs_nonneg _),
      show (1:ℝ)/4 * 4 = 1 by norm_num, show (3:ℝ)/2 * 4 = 6 by norm_num,
      Real.rpow_one, Real.rpow_ofNat, Even.pow_abs (by decide : Even 6)]
  rw [e1, e2, e3] at key
  -- `key : ‖b‖₃³ ≤ (‖b‖₂²)^{3/4} (‖b‖₆⁶)^{1/4}`; now take the power `2/3`.
  have h2 : 0 ≤ wnorm2sq w b :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (mul_self_nonneg _)
  have h6 := wnorm6p6_nonneg' w hw b
  have e4 : wnorm3 w b ^ 2 = wnorm3p3 w b ^ ((2:ℝ)/3) := by
    unfold wnorm3; rw [← Real.rpow_mul_natCast (wnorm3p3_nonneg' w hw b)]; norm_num
  have e5 : wnorm2 w b = wnorm2sq w b ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow _
  have e6 : (wnorm2sq w b ^ (1/((4:ℝ)/3)) * wnorm6p6 w b ^ (1/(4:ℝ))) ^ ((2:ℝ)/3)
      = wnorm2sq w b ^ ((1:ℝ)/2) * wnorm6p6 w b ^ ((1:ℝ)/6) := by
    rw [Real.mul_rpow (Real.rpow_nonneg h2 _) (Real.rpow_nonneg h6 _), ← Real.rpow_mul h2,
      ← Real.rpow_mul h6]
    norm_num
  rw [e4, e5]
  unfold wnorm6
  rw [← e6]
  exact Real.rpow_le_rpow (wnorm3p3_nonneg' w hw b) key (by norm_num)

/-- Cauchy–Schwarz: `∑ᵢ wᵢ |uᵢ|³ |cᵢ|³ ≤ ‖u‖₆³ ‖c‖₆³`. -/
theorem holder_cubes (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (u c : ι → ℝ) :
    ∑ i, w i * (|u i| ^ 3 * |c i| ^ 3) ≤ wnorm6 w u ^ 3 * wnorm6 w c ^ 3 := by
  -- Cauchy–Schwarz in the form `(∑ rᵢ)² ≤ (∑ fᵢ)(∑ gᵢ)` with `rᵢ² = fᵢ gᵢ`.
  have hcs : (∑ i, w i * (|u i| ^ 3 * |c i| ^ 3)) ^ 2
      ≤ (∑ i, w i * u i ^ 6) * ∑ i, w i * c i ^ 6 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun i _ => mul_nonneg (hw i) (by positivity))
      (fun i _ => mul_nonneg (hw i) (by positivity))
      (fun i _ => by
        have h1 : |u i| ^ 6 = u i ^ 6 := Even.pow_abs (by decide) _
        have h2 : |c i| ^ 6 = c i ^ 6 := Even.pow_abs (by decide) _
        apply le_of_eq
        calc (w i * (|u i| ^ 3 * |c i| ^ 3)) ^ 2 = w i ^ 2 * (|u i| ^ 6 * |c i| ^ 6) := by ring
          _ = (w i * u i ^ 6) * (w i * c i ^ 6) := by rw [h1, h2]; ring)
  have e : (∑ i, w i * u i ^ 6) * ∑ i, w i * c i ^ 6 = (wnorm6 w u ^ 3 * wnorm6 w c ^ 3) ^ 2 := by
    show wnorm6p6 w u * wnorm6p6 w c = _
    rw [← wnorm6_pow_six w hw u, ← wnorm6_pow_six w hw c]; ring
  rw [e] at hcs
  have h0 : 0 ≤ ∑ i, w i * (|u i| ^ 3 * |c i| ^ 3) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (by positivity)
  have h1 : 0 ≤ wnorm6 w u ^ 3 * wnorm6 w c ^ 3 :=
    mul_nonneg (pow_nonneg (wnorm6_nonneg w hw u) 3) (pow_nonneg (wnorm6_nonneg w hw c) 3)
  exact (sq_le_sq₀ h0 h1).mp hcs

/-- Monotonicity of `‖·‖₆` under a componentwise bound `|aᵢ| ≤ |bᵢ|`. -/
theorem wnorm6_le_of_abs_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {a b : ι → ℝ}
    (h : ∀ i, |a i| ≤ |b i|) : wnorm6 w a ≤ wnorm6 w b := by
  unfold wnorm6
  apply Real.rpow_le_rpow (wnorm6p6_nonneg' w hw a) _ (by norm_num)
  unfold wnorm6p6
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  rw [← Even.pow_abs (by decide : Even 6) (a i), ← Even.pow_abs (by decide : Even 6) (b i)]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 6

/-- `|w^{1/6} x|⁶ = w x⁶` for `w ≥ 0` (the integrand of the Minkowski inequality). -/
theorem abs_rpow_sixth_mul_pow_six (w : ℝ) (hw : 0 ≤ w) (x : ℝ) :
    |w ^ ((1:ℝ)/6) * x| ^ (6:ℝ) = w * x ^ 6 := by
  rw [Real.rpow_ofNat, Even.pow_abs (by decide : Even 6), mul_pow,
    ← Real.rpow_mul_natCast hw]
  norm_num

/-- The `‖·‖₆` triangle inequality (Minkowski), used for `‖u + σδ‖₆ ≤ (1-σ)‖u‖₆ + σ‖u⁺‖₆`. -/
theorem wnorm6_add_le (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (a b : ι → ℝ) :
    wnorm6 w (a + b) ≤ wnorm6 w a + wnorm6 w b := by
  -- Minkowski for the unweighted `ℓ⁶` norm with `fᵢ = wᵢ^{1/6} aᵢ`, `gᵢ = wᵢ^{1/6} bᵢ`.
  have e1 : ∑ i, |w i ^ ((1:ℝ)/6) * a i + w i ^ ((1:ℝ)/6) * b i| ^ (6:ℝ)
      = wnorm6p6 w (a + b) := by
    unfold wnorm6p6
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, ← mul_add, abs_rpow_sixth_mul_pow_six (w i) (hw i)]
  have e2 : ∑ i, |w i ^ ((1:ℝ)/6) * a i| ^ (6:ℝ) = wnorm6p6 w a := by
    unfold wnorm6p6
    exact Finset.sum_congr rfl fun i _ => abs_rpow_sixth_mul_pow_six (w i) (hw i) (a i)
  have e3 : ∑ i, |w i ^ ((1:ℝ)/6) * b i| ^ (6:ℝ) = wnorm6p6 w b := by
    unfold wnorm6p6
    exact Finset.sum_congr rfl fun i _ => abs_rpow_sixth_mul_pow_six (w i) (hw i) (b i)
  have key : (∑ i, |w i ^ ((1:ℝ)/6) * a i + w i ^ ((1:ℝ)/6) * b i| ^ (6:ℝ)) ^ (1/(6:ℝ))
      ≤ (∑ i, |w i ^ ((1:ℝ)/6) * a i| ^ (6:ℝ)) ^ (1/(6:ℝ))
        + (∑ i, |w i ^ ((1:ℝ)/6) * b i| ^ (6:ℝ)) ^ (1/(6:ℝ)) :=
    Real.Lp_add_le Finset.univ (fun i => w i ^ ((1:ℝ)/6) * a i) (fun i => w i ^ ((1:ℝ)/6) * b i)
      (by norm_num)
  rw [e1, e2, e3] at key
  exact key

/-- Homogeneity: `‖c • v‖₆ = |c| ‖v‖₆`. -/
theorem wnorm6_smul (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (c : ℝ) (v : ι → ℝ) :
    wnorm6 w (c • v) = |c| * wnorm6 w v := by
  have h : wnorm6p6 w (c • v) = |c| ^ 6 * wnorm6p6 w v := by
    unfold wnorm6p6
    rw [Finset.mul_sum, Even.pow_abs (by decide : Even 6)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  unfold wnorm6
  rw [h, Real.mul_rpow (by positivity) (wnorm6p6_nonneg' w hw v), ← Real.rpow_natCast |c| 6,
    ← Real.rpow_mul (abs_nonneg c)]
  norm_num

end GPDYS

end
