import GPDYS.Main

/-!
# Uniqueness of the discrete ground state up to sign (Remark 2.3)

The paper's Remark 2.3 states that the minimizer of `E_h` on `𝓜` is unique up to sign. The
argument needs the irreducibility of the stiffness matrix `S` (the connectivity of the mesh), which
is encoded in `GPDYS.Setting` through the entrywise positivity of the resolvent `(M + γS)⁻¹`:

* `S_irreducible`: for every proper nonempty set `A` of indices there are `i ∈ A`, `j ∉ A` with
  `S i j ≠ 0`. Otherwise `M + S` would be block diagonal, and so would its inverse, contradicting
  the positivity of the resolvent.
* `same_sign_of_kin_le`: if `v` has no zero component and `vᵀ S v ≤ |v|ᵀ S |v|`, then all
  components of `v` have the same sign.
* `eq_or_eq_neg_of_energy_le`: a minimizer `v` of `E_h` on `𝓜` equals `u` or `-u`, where `u > 0`
  is a positive critical point (the discrete ground state): `|v|` is a nonnegative minimizer, hence
  `|v| = u`, and `E_h(v) = E_h(|v|)` forces `vᵀ S v = |v|ᵀ S |v|`, so `v` has constant sign.
* `exists_groundState_sign`: Remark 2.3 in full.
-/

open Finset Matrix Filter Topology

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-- The `i`-th component of `(M + γ S) x`. -/
theorem MS_mulVec_apply (γ : ℝ) (x : ι → ℝ) (i : ι) :
    ((P.M + γ • P.S) *ᵥ x) i = P.w i * x i + γ * ∑ j, P.S i j * x j := by
  rw [add_mulVec, smul_mulVec, Pi.add_apply, M_mulVec, Pi.smul_apply, smul_eq_mul, mulVec,
    dotProduct]

/-- Irreducibility of `S` (connectivity of the mesh), derived from the entrywise positivity of the
resolvent: for every proper nonempty subset `A` of the indices there are `i ∈ A` and `j ∉ A` with
`S i j ≠ 0`. -/
theorem S_irreducible (A : Finset ι) (hA : A.Nonempty) (hA' : Aᶜ.Nonempty) :
    ∃ i ∈ A, ∃ j ∉ A, P.S i j ≠ 0 := by
  by_contra hcon
  have hz : ∀ i ∈ A, ∀ j ∉ A, P.S i j = 0 := fun i hi j hj =>
    by_contra fun h => hcon ⟨i, hi, j, hj, h⟩
  have hS : ∀ i j, P.S j i = P.S i j := fun i j => P.S_symm.apply i j
  set b : ι → ℝ := fun i => if i ∈ A then 1 else 0 with hb_def
  have hb : ∀ i, 0 ≤ b i := fun i => by simp only [hb_def]; split_ifs <;> norm_num
  have hb0 : b ≠ 0 := by
    obtain ⟨i0, hi0⟩ := hA
    intro h
    have := congrFun h i0
    simp [hb_def, hi0] at this
  set y := P.resolvent 1 b with hy_def
  have hypos : ∀ i, 0 < y i := P.resolvent_pos_of_nonneg one_pos hb hb0
  have hy : (P.M + (1:ℝ) • P.S) *ᵥ y = P.M *ᵥ b := P.MS_mulVec_resolvent zero_le_one b
  set yB : ι → ℝ := fun i => if i ∈ A then 0 else y i with hyB_def
  have hy' : ∀ i, P.w i * y i + ∑ j, P.S i j * y j = P.w i * b i := by
    intro i
    have := congrFun hy i
    rw [P.MS_mulVec_apply, one_mul, M_mulVec] at this
    exact this
  have hyB : (P.M + (1:ℝ) • P.S) *ᵥ yB = 0 := by
    funext i
    rw [P.MS_mulVec_apply, one_mul, Pi.zero_apply]
    by_cases hi : i ∈ A
    · have h1 : yB i = 0 := by simp [hyB_def, hi]
      have h2 : ∑ j, P.S i j * yB j = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j ∈ A
        · simp [hyB_def, hj]
        · rw [hz i hi j hj, zero_mul]
      rw [h1, h2]; ring
    · have h1 : yB i = y i := by simp [hyB_def, hi]
      have h2 : ∑ j, P.S i j * yB j = ∑ j, P.S i j * y j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j ∈ A
        · rw [← hS i j, hz j hj i hi]; simp
        · simp [hyB_def, hj]
      rw [h1, h2, hy' i]
      simp [hb_def, hi]
  have hyB0 := P.MS_mulVec_eq_zero zero_le_one hyB
  obtain ⟨j0, hj0⟩ := hA'
  rw [Finset.mem_compl] at hj0
  have := congrFun hyB0 j0
  simp [hyB_def, hj0] at this
  exact (hypos j0).ne' this

/-- If `v` has no zero component and `vᵀ S v ≤ |v|ᵀ S |v|`, then all components of `v` have the
same sign. -/
theorem same_sign_of_kin_le {v : ι → ℝ} (hv : ∀ i, v i ≠ 0)
    (hk : P.kin v ≤ P.kin (fun i => |v i|)) : (∀ i, 0 < v i) ∨ (∀ i, v i < 0) := by
  have hk' := P.kin_abs_le v
  have heq : P.kin v = P.kin (fun i => |v i|) := le_antisymm hk hk'
  rw [kin_eq_double_sum, kin_eq_double_sum] at heq
  have hterm : ∀ i j, 0 ≤ P.S i j * (v i * v j) - P.S i j * (|v i| * |v j|) := by
    intro i j
    by_cases hij : i = j
    · subst hij; rw [abs_mul_abs_self]; simp
    · have hS := P.S_offdiag i j hij
      have h1 : v i * v j ≤ |v i| * |v j| := by rw [← abs_mul]; exact le_abs_self _
      have := mul_le_mul_of_nonpos_left h1 hS
      linarith
  have hsum0 : ∑ i, ∑ j, (P.S i j * (v i * v j) - P.S i j * (|v i| * |v j|)) = 0 := by
    simp only [Finset.sum_sub_distrib]
    linarith
  have hall : ∀ i j, P.S i j * (v i * v j) - P.S i j * (|v i| * |v j|) = 0 := by
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => hterm i j)).mp hsum0
    intro i j
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm i j)).mp
      (h1 i (Finset.mem_univ i))
    exact h2 j (Finset.mem_univ j)
  have hpos : ∀ i j, i ≠ j → P.S i j ≠ 0 → 0 < v i * v j := by
    intro i j hij hS
    have h := hall i j
    have h' : v i * v j = |v i| * |v j| := by
      have : P.S i j * (v i * v j - |v i| * |v j|) = 0 := by rw [mul_sub]; exact h
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hS
      · linarith
    rw [h', ← abs_mul]
    exact abs_pos.mpr (mul_ne_zero (hv i) (hv j))
  set A := Finset.univ.filter (fun i => 0 < v i) with hA_def
  by_cases hAu : A = Finset.univ
  · left
    intro i
    have : i ∈ A := hAu ▸ Finset.mem_univ i
    simpa [hA_def] using this
  · by_cases hAe : A = ∅
    · right
      intro i
      have hi : i ∉ A := by rw [hAe]; exact Finset.notMem_empty i
      simp only [hA_def, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
      exact lt_of_le_of_ne hi (hv i)
    · exfalso
      have hA : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hAe
      have hA' : Aᶜ.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hAu ((Finset.compl_eq_empty_iff A).mp h)
      obtain ⟨i, hi, j, hj, hS⟩ := P.S_irreducible A hA hA'
      have hvi : 0 < v i := by simpa [hA_def] using hi
      have hvj : v j < 0 := by
        simp only [hA_def, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
        exact lt_of_le_of_ne hj (hv j)
      have hij : i ≠ j := fun h => by subst h; exact absurd hvi (not_lt.mpr hvj.le)
      have := hpos i j hij hS
      have := mul_neg_of_pos_of_neg hvi hvj
      linarith

/-- Remark 2.3, uniqueness up to sign: if `u > 0` is a critical point of `E_h` on `𝓜` and
`v ∈ 𝓜` satisfies `E_h(v) ≤ E_h(u)`, then `v = u` or `v = -u`. -/
theorem eq_or_eq_neg_of_energy_le {u v : ι → ℝ} (hu : P.nrm2sq u = 1) (hupos : ∀ i, 0 < u i)
    (hg : P.g u = 0) (hv : P.nrm2sq v = 1) (hE : P.energy v ≤ P.energy u) : v = u ∨ v = -u := by
  have ha1 : P.nrm2sq (fun i => |v i|) = 1 := by rw [P.nrm2sq_abs]; exact hv
  have hann : ∀ i, 0 ≤ |v i| := fun i => abs_nonneg _
  have hEa : P.energy (fun i => |v i|) ≤ P.energy v := P.energy_abs_le v
  have hau : (fun i => |v i|) = u :=
    P.eq_of_nonneg_le_energy hu hupos hg ha1 hann (hEa.trans hE)
  have hvne : ∀ i, v i ≠ 0 := by
    intro i
    have : |v i| = u i := congrFun hau i
    exact abs_pos.mp (this ▸ hupos i)
  have hEu : P.energy u ≤ P.energy v := P.energy_le_of_critical hu hupos hg hv
  have hEva : P.energy v = P.energy (fun i => |v i|) := by rw [hau]; exact le_antisymm hE hEu
  have hpot : P.pot (fun i => |v i|) = P.pot v := by
    unfold pot; simp only [sq_abs]
  have h4 : wnorm4p4 P.w (fun i => |v i|) = wnorm4p4 P.w v := by
    unfold wnorm4p4
    simp only [Even.pow_abs (by decide : Even 4)]
  have hkin : P.kin v ≤ P.kin (fun i => |v i|) := by
    have e1 := P.energy_eq v
    have e2 := P.energy_eq (fun i => |v i|)
    rw [hpot, h4] at e2
    linarith
  rcases P.same_sign_of_kin_le hvne hkin with hpos | hneg
  · left
    rw [← hau]
    funext i
    exact (abs_of_pos (hpos i)).symm
  · right
    rw [← hau]
    funext i
    rw [Pi.neg_apply, abs_of_neg (hneg i), neg_neg]

/-- **Remark 2.3** in full: there is a positive `u_GS ∈ 𝓜` which is a critical point of `E_h|_𝓜`,
the global minimizer of `E_h` on `𝓜`, the unique nonnegative critical point, and the minimizer is
unique up to sign: every minimizer of `E_h` on `𝓜` is `u_GS` or `-u_GS`. -/
theorem exists_groundState_sign [Nonempty ι] :
    ∃ uGS : ι → ℝ, (∀ i, 0 < uGS i) ∧ P.nrm2 uGS = 1 ∧ P.g uGS = 0 ∧
      (∀ v, P.nrm2 v = 1 → P.energy uGS ≤ P.energy v) ∧
      (∀ v, P.nrm2 v = 1 → (∀ i, 0 ≤ v i) → P.g v = 0 → v = uGS) ∧
      (∀ v, P.nrm2 v = 1 → P.energy v ≤ P.energy uGS → v = uGS ∨ v = -uGS) := by
  obtain ⟨uGS, h1, h2, h3, h4, h5⟩ := P.exists_groundState
  refine ⟨uGS, h1, h2, h3, h4, h5, fun v hv hE => ?_⟩
  exact P.eq_or_eq_neg_of_energy_le (P.nrm2sq_eq_one_of_nrm2 h2) h1 h3
    (P.nrm2sq_eq_one_of_nrm2 hv) hE

end Setting

end GPDYS

end
