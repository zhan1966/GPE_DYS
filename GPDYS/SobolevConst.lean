import GPDYS.Holder

/-!
# A Sobolev constant always exists on a fixed mesh

The hypothesis `sobolev` of `GPDYS.Setting` (the discrete Sobolev inequality
`‖v‖₆ ≤ C_S ‖v‖_{1,h}`, Lemma 2.2 (iii) of the paper) has a witness on every fixed nonempty mesh:
for
any positive weights `w` and any positive semidefinite `S`, some constant `C_S` works, namely
`C_S = (∑ᵢ wᵢ)^{1/6} / √w_min`. The paper's Lemma 2.2 (iii) is the stronger statement that `C_S`
can be chosen independently of the mesh size, which only matters for the dependence of `γ_max` on
the mesh (Remark 3.3) and not for Theorems 3.4 and 5.1 on a fixed mesh.
-/

open Finset Matrix

noncomputable section

namespace GPDYS

/-- On a fixed nonempty mesh a Sobolev constant exists for positive weights `w`
and positive semidefinite `S`. The proof chooses `(∑ᵢ wᵢ)^{1/6} / √(minᵢ wᵢ)`. -/
theorem exists_sobolev_const {ι : Type*} [Fintype ι] [Nonempty ι] (w : ι → ℝ) (hw : ∀ i, 0 < w i)
    (S : Matrix ι ι ℝ) (hS : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (S *ᵥ v)) :
    ∃ CS : ℝ, 0 < CS ∧ ∀ v : ι → ℝ, wnorm6 w v ≤ CS * Real.sqrt (v ⬝ᵥ (S *ᵥ v) + wnorm2sq w v) := by
  -- `m = minᵢ wᵢ > 0` and `W = ∑ᵢ wᵢ > 0`
  obtain ⟨i0, hi0⟩ := Finite.exists_min w
  set m := w i0 with hm_def
  have hm : 0 < m := hw i0
  set W := ∑ i, w i with hW_def
  have hW : 0 < W := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  refine ⟨W ^ ((1:ℝ)/6) / Real.sqrt m, ?_, ?_⟩
  · exact div_pos (Real.rpow_pos_of_pos hW _) (Real.sqrt_pos.mpr hm)
  · intro v
    set N := wnorm2sq w v with hN_def
    have hN : 0 ≤ N := Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (mul_self_nonneg _)
    -- Step 1: `vᵢ² ≤ N / m` for every `i`
    have h1 : ∀ i, v i ^ 2 ≤ N / m := by
      intro i
      have hwi : 0 < w i := hw i
      have hmi : m ≤ w i := hi0 i
      have hterm : w i * (v i * v i) ≤ N :=
        Finset.single_le_sum (f := fun j => w j * (v j * v j))
          (fun j _ => mul_nonneg (hw j).le (mul_self_nonneg _)) (Finset.mem_univ i)
      calc v i ^ 2 = (w i * (v i * v i)) / w i := (eq_div_iff hwi.ne').mpr (by ring)
        _ ≤ N / w i := by gcongr
        _ ≤ N / m := by gcongr
    -- Step 2: `‖v‖₆⁶ ≤ W (N / m)³`
    have hNm : 0 ≤ N / m := div_nonneg hN hm.le
    have h2 : wnorm6p6 w v ≤ W * (N / m) ^ 3 := by
      calc wnorm6p6 w v = ∑ i, w i * (v i ^ 2) ^ 3 := by
            unfold wnorm6p6
            exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ ∑ i, w i * (N / m) ^ 3 :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg _) (h1 i) 3) (hw i).le
        _ = W * (N / m) ^ 3 := by rw [hW_def, Finset.sum_mul]
    -- Step 3: `‖v‖₆ ≤ W^{1/6} √(N / m)`
    have h3 : wnorm6 w v ≤ W ^ ((1:ℝ)/6) * Real.sqrt (N / m) := by
      calc wnorm6 w v = (wnorm6p6 w v) ^ ((1:ℝ)/6) := rfl
        _ ≤ (W * (N / m) ^ 3) ^ ((1:ℝ)/6) :=
            Real.rpow_le_rpow (wnorm6p6_nonneg' w (fun i => (hw i).le) v) h2 (by norm_num)
        _ = W ^ ((1:ℝ)/6) * ((N / m) ^ 3) ^ ((1:ℝ)/6) := Real.mul_rpow hW.le (pow_nonneg hNm 3)
        _ = W ^ ((1:ℝ)/6) * Real.sqrt (N / m) := by
            congr 1
            rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNm]
            norm_num
    -- Step 4: `√N ≤ √(vᵀ S v + N)`
    have h4 : Real.sqrt N ≤ Real.sqrt (v ⬝ᵥ (S *ᵥ v) + N) :=
      Real.sqrt_le_sqrt (le_add_of_nonneg_left (hS v))
    -- Step 5: conclusion
    calc wnorm6 w v ≤ W ^ ((1:ℝ)/6) * Real.sqrt (N / m) := h3
      _ = W ^ ((1:ℝ)/6) * (Real.sqrt N / Real.sqrt m) := by rw [Real.sqrt_div' _ hm.le]
      _ = (W ^ ((1:ℝ)/6) / Real.sqrt m) * Real.sqrt N := by ring
      _ ≤ (W ^ ((1:ℝ)/6) / Real.sqrt m) * Real.sqrt (v ⬝ᵥ (S *ᵥ v) + N) :=
          mul_le_mul_of_nonneg_left h4
            (div_nonneg (Real.rpow_nonneg hW.le _) (Real.sqrt_nonneg _))

end GPDYS

end
