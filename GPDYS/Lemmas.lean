import GPDYS.Basic

/-!
# Basic API for the discrete inner product, the norms, the energy and the gradients

Elementary identities and inequalities for the objects of `GPDYS.Basic`:
bilinearity and symmetry of `⟪·,·⟫_h` and of the kinetic form `⟪u, -Δ_h v⟫_h = uᵀ S v`,
Cauchy–Schwarz inequalities, the pointwise bound (3.1), and the identities
`λ(v) = 2E_h(v) + (β/2)‖v‖₄⁴`, `∇E_h(v) = λ(v) v + g(v)`, `⟪g(v), v⟫_h = 0` of §3.1.
-/

open Finset Matrix

noncomputable section

namespace GPDYS

/-! ### A Cauchy–Schwarz inequality for positive semidefinite symmetric bilinear forms -/

/-- Cauchy–Schwarz for a symmetric positive semidefinite bilinear form on a real vector space. -/
theorem sq_le_of_psd {E : Type*} [AddCommGroup E] [Module ℝ E] (B : E → E → ℝ)
    (hadd : ∀ u v w, B (u + v) w = B u w + B v w)
    (hsmul : ∀ (c : ℝ) (u v : E), B (c • u) v = c * B u v)
    (hsymm : ∀ u v, B u v = B v u) (hpsd : ∀ v, 0 ≤ B v v) (u v : E) :
    (B u v) ^ 2 ≤ B u u * B v v := by
  have hsub : ∀ (t : ℝ), B (u - t • v) (u - t • v)
      = B u u - 2 * t * B u v + t ^ 2 * B v v := by
    intro t
    have h1 : ∀ x y, B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
      intro x y
      have hneg : ∀ a b, B (-a) b = - B a b := by
        intro a b
        have := hsmul (-1) a b
        simpa using this
      have hneg' : ∀ a b, B a (-b) = - B a b := by
        intro a b; rw [hsymm, hneg, hsymm]
      have hadd' : ∀ a b c, B a (b + c) = B a b + B a c := by
        intro a b c; rw [hsymm, hadd, hsymm b, hsymm c]
      simp only [sub_eq_add_neg, hadd, hadd', hneg, hneg']
      ring
    rw [h1]
    have e1 : B u (t • v) = t * B u v := by rw [hsymm, hsmul, hsymm]
    have e2 : B (t • v) u = t * B u v := by rw [hsmul, hsymm]
    have e3 : B (t • v) (t • v) = t * (t * B v v) := by rw [hsmul, hsymm, hsmul, hsymm]
    rw [e1, e2, e3]; ring
  by_cases hv : B v v = 0
  · -- then B u v = 0
    have h : ∀ t : ℝ, 0 ≤ B u u - 2 * t * B u v := by
      intro t; have := hpsd (u - t • v); rw [hsub, hv] at this; linarith
    have huv : B u v = 0 := by
      by_contra hne
      have := h ((B u u + 1) / (2 * B u v))
      have e : 2 * ((B u u + 1) / (2 * B u v)) * B u v = B u u + 1 := by field_simp
      linarith
    rw [huv, hv]; simp
  · have hvpos : 0 < B v v := lt_of_le_of_ne (hpsd v) (Ne.symm hv)
    have := hpsd (u - (B u v / B v v) • v)
    rw [hsub] at this
    have key : 0 ≤ B u u - (B u v) ^ 2 / B v v := by
      have e : B u u - 2 * (B u v / B v v) * B u v + (B u v / B v v) ^ 2 * B v v
          = B u u - (B u v) ^ 2 / B v v := by field_simp; ring
      linarith [e]
    have := mul_le_mul_of_nonneg_right (sub_nonneg.mp key) hvpos.le
    rw [div_mul_cancel₀ _ hv] at this
    linarith

/-- A componentwise positive vector on a nonempty index type is nonzero. -/
theorem ne_zero_of_pos {ι : Type*} [Nonempty ι] {z : ι → ℝ} (hpos : ∀ i, 0 < z i) : z ≠ 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have := hpos i
  rw [h] at this
  simp at this

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-! ### The inner product -/

theorem inner_def (u v : ι → ℝ) : P.inner u v = ∑ i, P.w i * (u i * v i) := rfl

theorem inner_comm (u v : ι → ℝ) : P.inner u v = P.inner v u := by
  unfold inner winner; refine Finset.sum_congr rfl fun i _ => ?_; ring

theorem inner_add_left (u v x : ι → ℝ) : P.inner (u + v) x = P.inner u x + P.inner v x := by
  unfold inner winner; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

theorem inner_add_right (u v x : ι → ℝ) : P.inner x (u + v) = P.inner x u + P.inner x v := by
  rw [inner_comm, inner_add_left, inner_comm P u, inner_comm P v]

theorem inner_smul_left (c : ℝ) (u v : ι → ℝ) : P.inner (c • u) v = c * P.inner u v := by
  unfold inner winner; rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_; simp; ring

theorem inner_smul_right (c : ℝ) (u v : ι → ℝ) : P.inner u (c • v) = c * P.inner u v := by
  rw [inner_comm, inner_smul_left, inner_comm]

theorem inner_neg_left (u v : ι → ℝ) : P.inner (-u) v = - P.inner u v := by
  have := P.inner_smul_left (-1) u v; simpa using this

theorem inner_neg_right (u v : ι → ℝ) : P.inner u (-v) = - P.inner u v := by
  rw [inner_comm, inner_neg_left, inner_comm]

theorem inner_sub_left (u v x : ι → ℝ) : P.inner (u - v) x = P.inner u x - P.inner v x := by
  rw [sub_eq_add_neg, inner_add_left, inner_neg_left, sub_eq_add_neg]

theorem inner_sub_right (u v x : ι → ℝ) : P.inner x (u - v) = P.inner x u - P.inner x v := by
  rw [sub_eq_add_neg, inner_add_right, inner_neg_right, sub_eq_add_neg]

@[simp] theorem inner_zero_left (v : ι → ℝ) : P.inner 0 v = 0 := by
  unfold inner winner; simp

@[simp] theorem inner_zero_right (v : ι → ℝ) : P.inner v 0 = 0 := by
  unfold inner winner; simp

theorem inner_sum_left {κ : Type*} (s : Finset κ) (f : κ → ι → ℝ) (v : ι → ℝ) :
    P.inner (∑ k ∈ s, f k) v = ∑ k ∈ s, P.inner (f k) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, inner_add_left, ih, Finset.sum_insert ha]

/-! ### `‖·‖₂` -/

theorem nrm2sq_def (v : ι → ℝ) : P.nrm2sq v = P.inner v v := rfl

theorem nrm2sq_eq_sum (v : ι → ℝ) : P.nrm2sq v = ∑ i, P.w i * v i ^ 2 := by
  unfold nrm2sq wnorm2sq winner; refine Finset.sum_congr rfl fun i _ => ?_; ring

theorem nrm2sq_nonneg (v : ι → ℝ) : 0 ≤ P.nrm2sq v := by
  rw [nrm2sq_eq_sum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (P.w_pos i).le (sq_nonneg _)

theorem w_mul_sq_le_nrm2sq (v : ι → ℝ) (i : ι) : P.w i * v i ^ 2 ≤ P.nrm2sq v := by
  rw [nrm2sq_eq_sum]
  exact Finset.single_le_sum (fun j _ => mul_nonneg (P.w_pos j).le (sq_nonneg _))
    (Finset.mem_univ i)

theorem nrm2sq_eq_zero_iff (v : ι → ℝ) : P.nrm2sq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have h1 := P.w_mul_sq_le_nrm2sq v i
    rw [h] at h1
    have h2 : 0 ≤ P.w i * v i ^ 2 := mul_nonneg (P.w_pos i).le (sq_nonneg _)
    have h3 : P.w i * v i ^ 2 = 0 := le_antisymm h1 h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (P.w_pos i).ne'
    · simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h4
  · rintro rfl; simp [nrm2sq_eq_sum]

theorem nrm2sq_pos_of_ne_zero {v : ι → ℝ} (hv : v ≠ 0) : 0 < P.nrm2sq v :=
  lt_of_le_of_ne (P.nrm2sq_nonneg v) (fun h => hv ((P.nrm2sq_eq_zero_iff v).mp h.symm))

theorem nrm2_def (v : ι → ℝ) : P.nrm2 v = Real.sqrt (P.nrm2sq v) := rfl

theorem nrm2_nonneg (v : ι → ℝ) : 0 ≤ P.nrm2 v := Real.sqrt_nonneg _

theorem nrm2_sq (v : ι → ℝ) : P.nrm2 v ^ 2 = P.nrm2sq v := by
  rw [nrm2_def, Real.sq_sqrt (P.nrm2sq_nonneg v)]

theorem nrm2_mul_self (v : ι → ℝ) : P.nrm2 v * P.nrm2 v = P.nrm2sq v := by
  rw [← sq, nrm2_sq]

theorem nrm2_pos_of_ne_zero {v : ι → ℝ} (hv : v ≠ 0) : 0 < P.nrm2 v :=
  Real.sqrt_pos.mpr (P.nrm2sq_pos_of_ne_zero hv)

theorem nrm2_eq_zero_iff (v : ι → ℝ) : P.nrm2 v = 0 ↔ v = 0 := by
  rw [nrm2_def, Real.sqrt_eq_zero (P.nrm2sq_nonneg v), nrm2sq_eq_zero_iff]

theorem nrm2sq_eq_one_of_nrm2 {v : ι → ℝ} (h : P.nrm2 v = 1) : P.nrm2sq v = 1 := by
  rw [← nrm2_sq, h]; norm_num

theorem nrm2_eq_one_of_nrm2sq {v : ι → ℝ} (h : P.nrm2sq v = 1) : P.nrm2 v = 1 := by
  rw [nrm2_def, h, Real.sqrt_one]

theorem nrm2_eq_one_iff (v : ι → ℝ) : P.nrm2 v = 1 ↔ P.nrm2sq v = 1 :=
  ⟨P.nrm2sq_eq_one_of_nrm2, P.nrm2_eq_one_of_nrm2sq⟩

theorem nrm2sq_smul (c : ℝ) (v : ι → ℝ) : P.nrm2sq (c • v) = c ^ 2 * P.nrm2sq v := by
  simp only [nrm2sq_def, inner_smul_left, inner_smul_right]; ring

theorem nrm2_smul (c : ℝ) (v : ι → ℝ) : P.nrm2 (c • v) = |c| * P.nrm2 v := by
  rw [nrm2_def, nrm2_def, nrm2sq_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem nrm2sq_add (u v : ι → ℝ) :
    P.nrm2sq (u + v) = P.nrm2sq u + 2 * P.inner u v + P.nrm2sq v := by
  simp only [nrm2sq_def, inner_add_left, inner_add_right, inner_comm P v u]; ring

theorem nrm2sq_sub (u v : ι → ℝ) :
    P.nrm2sq (u - v) = P.nrm2sq u - 2 * P.inner u v + P.nrm2sq v := by
  simp only [nrm2sq_def, inner_sub_left, inner_sub_right, inner_comm P v u]; ring

theorem nrm2sq_neg (v : ι → ℝ) : P.nrm2sq (-v) = P.nrm2sq v := by
  simp only [nrm2sq_def, inner_neg_left, inner_neg_right, neg_neg]

/-- Cauchy–Schwarz: `⟪u, v⟫_h² ≤ ‖u‖₂² ‖v‖₂²`. -/
theorem inner_sq_le (u v : ι → ℝ) : (P.inner u v) ^ 2 ≤ P.nrm2sq u * P.nrm2sq v :=
  sq_le_of_psd P.inner P.inner_add_left P.inner_smul_left P.inner_comm P.nrm2sq_nonneg u v

/-- Cauchy–Schwarz: `⟪u, v⟫_h ≤ ‖u‖₂ ‖v‖₂`. -/
theorem inner_le_nrm2_mul_nrm2 (u v : ι → ℝ) : P.inner u v ≤ P.nrm2 u * P.nrm2 v := by
  have h := P.inner_sq_le u v
  rw [← nrm2_sq, ← nrm2_sq, ← mul_pow] at h
  exact abs_le_of_sq_le_sq' h (mul_nonneg (P.nrm2_nonneg u) (P.nrm2_nonneg v)) |>.2

theorem abs_inner_le_nrm2_mul_nrm2 (u v : ι → ℝ) : |P.inner u v| ≤ P.nrm2 u * P.nrm2 v := by
  have h := P.inner_sq_le u v
  rw [← nrm2_sq, ← nrm2_sq, ← mul_pow] at h
  exact abs_le.mpr (abs_le_of_sq_le_sq' h (mul_nonneg (P.nrm2_nonneg u) (P.nrm2_nonneg v)))

/-- Triangle inequality for `‖·‖₂`. -/
theorem nrm2_add_le (u v : ι → ℝ) : P.nrm2 (u + v) ≤ P.nrm2 u + P.nrm2 v := by
  rw [nrm2_def, Real.sqrt_le_left (add_nonneg (P.nrm2_nonneg u) (P.nrm2_nonneg v)), nrm2sq_add]
  have h := P.inner_le_nrm2_mul_nrm2 u v
  have hu := P.nrm2_sq u
  have hv := P.nrm2_sq v
  nlinarith

theorem nrm2_neg (v : ι → ℝ) : P.nrm2 (-v) = P.nrm2 v := by
  rw [nrm2_def, nrm2_def, nrm2sq_neg]

theorem nrm2_sub_le (u v : ι → ℝ) : P.nrm2 (u - v) ≤ P.nrm2 u + P.nrm2 v := by
  have h := P.nrm2_add_le u (-v)
  rw [← sub_eq_add_neg, nrm2_neg] at h
  exact h

theorem nrm2_le_of_nrm2sq_le {v : ι → ℝ} {c : ℝ} (hc : 0 ≤ c) (h : P.nrm2sq v ≤ c ^ 2) :
    P.nrm2 v ≤ c := by
  rw [nrm2_def]; exact Real.sqrt_le_iff.mpr ⟨hc, h⟩

theorem nrm2_le_nrm2_iff (u v : ι → ℝ) : P.nrm2 u ≤ P.nrm2 v ↔ P.nrm2sq u ≤ P.nrm2sq v := by
  rw [nrm2_def, nrm2_def]
  exact Real.sqrt_le_sqrt_iff (P.nrm2sq_nonneg v)

/-- Monotonicity of `‖·‖₂` on nonnegative vectors. -/
theorem nrm2sq_le_nrm2sq_of_le {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    P.nrm2sq x ≤ P.nrm2sq y := by
  rw [nrm2sq_eq_sum, nrm2sq_eq_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hx i) (hxy i) 2) (P.w_pos i).le

theorem nrm2_le_nrm2_of_le {x y : ι → ℝ} (hx : ∀ i, 0 ≤ x i) (hxy : ∀ i, x i ≤ y i) :
    P.nrm2 x ≤ P.nrm2 y :=
  Real.sqrt_le_sqrt (P.nrm2sq_le_nrm2sq_of_le hx hxy)

/-! ### The kinetic form `uᵀ S v = ⟪u, -Δ_h v⟫_h` -/

theorem dotS_comm (u v : ι → ℝ) : u ⬝ᵥ (P.S *ᵥ v) = v ⬝ᵥ (P.S *ᵥ u) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, P.S_symm.eq, dotProduct_comm]

theorem dotS_add_left (u v x : ι → ℝ) :
    (u + v) ⬝ᵥ (P.S *ᵥ x) = u ⬝ᵥ (P.S *ᵥ x) + v ⬝ᵥ (P.S *ᵥ x) := add_dotProduct _ _ _

theorem dotS_add_right (u v x : ι → ℝ) :
    x ⬝ᵥ (P.S *ᵥ (u + v)) = x ⬝ᵥ (P.S *ᵥ u) + x ⬝ᵥ (P.S *ᵥ v) := by
  rw [mulVec_add, dotProduct_add]

theorem dotS_smul_left (c : ℝ) (u x : ι → ℝ) : (c • u) ⬝ᵥ (P.S *ᵥ x) = c * (u ⬝ᵥ (P.S *ᵥ x)) :=
  smul_dotProduct _ _ _

theorem dotS_smul_right (c : ℝ) (u x : ι → ℝ) : x ⬝ᵥ (P.S *ᵥ (c • u)) = c * (x ⬝ᵥ (P.S *ᵥ u)) := by
  rw [mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem dotS_sub_left (u v x : ι → ℝ) :
    (u - v) ⬝ᵥ (P.S *ᵥ x) = u ⬝ᵥ (P.S *ᵥ x) - v ⬝ᵥ (P.S *ᵥ x) := sub_dotProduct _ _ _

theorem dotS_sub_right (u v x : ι → ℝ) :
    x ⬝ᵥ (P.S *ᵥ (u - v)) = x ⬝ᵥ (P.S *ᵥ u) - x ⬝ᵥ (P.S *ᵥ v) := by
  rw [mulVec_sub, dotProduct_sub]

theorem dotS_neg_left (u x : ι → ℝ) : (-u) ⬝ᵥ (P.S *ᵥ x) = - (u ⬝ᵥ (P.S *ᵥ x)) :=
  neg_dotProduct _ _

theorem dotS_neg_right (u x : ι → ℝ) : x ⬝ᵥ (P.S *ᵥ (-u)) = - (x ⬝ᵥ (P.S *ᵥ u)) := by
  rw [mulVec_neg, dotProduct_neg]

@[simp] theorem dotS_zero_left (x : ι → ℝ) : (0 : ι → ℝ) ⬝ᵥ (P.S *ᵥ x) = 0 := zero_dotProduct _

@[simp] theorem dotS_zero_right (x : ι → ℝ) : x ⬝ᵥ (P.S *ᵥ (0 : ι → ℝ)) = 0 := by
  rw [mulVec_zero, dotProduct_zero]

theorem kin_def (v : ι → ℝ) : P.kin v = v ⬝ᵥ (P.S *ᵥ v) := rfl

theorem kin_nonneg (v : ι → ℝ) : 0 ≤ P.kin v := P.S_psd v

theorem kin_smul (c : ℝ) (v : ι → ℝ) : P.kin (c • v) = c ^ 2 * P.kin v := by
  rw [kin_def, kin_def, dotS_smul_left, dotS_smul_right, ← mul_assoc, sq]

theorem kin_add (u v : ι → ℝ) :
    P.kin (u + v) = P.kin u + 2 * (u ⬝ᵥ (P.S *ᵥ v)) + P.kin v := by
  simp only [kin_def, dotS_add_left, dotS_add_right, P.dotS_comm v u]; ring

theorem kin_sub (u v : ι → ℝ) :
    P.kin (u - v) = P.kin u - 2 * (u ⬝ᵥ (P.S *ᵥ v)) + P.kin v := by
  simp only [kin_def, dotS_sub_left, dotS_sub_right, P.dotS_comm v u]; ring

theorem kin_neg (v : ι → ℝ) : P.kin (-v) = P.kin v := by
  simp only [kin_def, dotS_neg_left, dotS_neg_right, neg_neg]

/-- Cauchy–Schwarz for the kinetic form: `(uᵀ S v)² ≤ (uᵀ S u)(vᵀ S v)`. -/
theorem dotS_sq_le (u v : ι → ℝ) : (u ⬝ᵥ (P.S *ᵥ v)) ^ 2 ≤ P.kin u * P.kin v :=
  sq_le_of_psd (fun u v => u ⬝ᵥ (P.S *ᵥ v)) P.dotS_add_left P.dotS_smul_left P.dotS_comm
    P.S_psd u v

theorem abs_dotS_le (u v : ι → ℝ) :
    |u ⬝ᵥ (P.S *ᵥ v)| ≤ Real.sqrt (P.kin u) * Real.sqrt (P.kin v) := by
  rw [← Real.sqrt_mul (P.kin_nonneg u)]
  apply Real.abs_le_sqrt
  exact P.dotS_sq_le u v

/-! ### The negative discrete Laplacian -/

theorem negLap_apply (v : ι → ℝ) (i : ι) : P.negLap v i = (P.S *ᵥ v) i / P.w i := rfl

theorem inner_negLap (u v : ι → ℝ) : P.inner u (P.negLap v) = u ⬝ᵥ (P.S *ᵥ v) := by
  unfold inner winner negLap dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  have := (P.w_pos i).ne'
  field_simp

theorem inner_negLap_comm (u v : ι → ℝ) :
    P.inner u (P.negLap v) = P.inner (P.negLap u) v := by
  rw [inner_negLap, inner_comm, inner_negLap, dotS_comm]

theorem negLap_inner (u v : ι → ℝ) : P.inner (P.negLap u) v = u ⬝ᵥ (P.S *ᵥ v) := by
  rw [← inner_negLap_comm, inner_negLap]

theorem kin_eq_inner (v : ι → ℝ) : P.kin v = P.inner v (P.negLap v) := by
  rw [inner_negLap, kin_def]

theorem negLap_add (u v : ι → ℝ) : P.negLap (u + v) = P.negLap u + P.negLap v := by
  funext i; simp only [negLap_apply, mulVec_add, Pi.add_apply]; ring

theorem negLap_smul (c : ℝ) (v : ι → ℝ) : P.negLap (c • v) = c • P.negLap v := by
  funext i; simp only [negLap_apply, mulVec_smul, Pi.smul_apply, smul_eq_mul]; ring

theorem negLap_sub (u v : ι → ℝ) : P.negLap (u - v) = P.negLap u - P.negLap v := by
  funext i; simp only [negLap_apply, mulVec_sub, Pi.sub_apply]; ring

theorem negLap_neg (v : ι → ℝ) : P.negLap (-v) = - P.negLap v := by
  funext i; simp only [negLap_apply, mulVec_neg, Pi.neg_apply]; ring

@[simp] theorem negLap_zero : P.negLap 0 = 0 := by
  funext i; simp [negLap_apply]

theorem M_mulVec (v : ι → ℝ) : P.M *ᵥ v = fun i => P.w i * v i := by
  funext i; simp [M, mulVec_diagonal]

theorem M_mulVec_negLap (v : ι → ℝ) : P.M *ᵥ (P.negLap v) = P.S *ᵥ v := by
  rw [M_mulVec]; funext i; simp only [negLap_apply]
  have := (P.w_pos i).ne'
  field_simp

/-! ### Energy, gradients, the eigenvalue functional and the projected gradient -/

theorem pot_nonneg (v : ι → ℝ) : 0 ≤ P.pot v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.w_pos i).le (mul_nonneg (P.V_nonneg i) (sq_nonneg _))

theorem wnorm4p4_nonneg (v : ι → ℝ) : 0 ≤ wnorm4p4 P.w v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.w_pos i).le (by positivity)

theorem wnorm6p6_nonneg (v : ι → ℝ) : 0 ≤ wnorm6p6 P.w v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.w_pos i).le (by positivity)

theorem wnorm3p3_nonneg (v : ι → ℝ) : 0 ≤ wnorm3p3 P.w v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.w_pos i).le (by positivity)

theorem H_nonneg (v : ι → ℝ) : 0 ≤ P.H v := by
  unfold H
  have := P.pot_nonneg v; have := P.wnorm4p4_nonneg v; have := P.β_pos
  positivity

theorem energy_def (v : ι → ℝ) : P.energy v = (1 / 2) * P.kin v + P.H v := rfl

theorem energy_eq (v : ι → ℝ) :
    P.energy v = (1 / 2) * P.kin v + (1 / 2) * P.pot v + P.β / 4 * wnorm4p4 P.w v := by
  rw [energy_def, H]; ring

theorem energy_nonneg (v : ι → ℝ) : 0 ≤ P.energy v := by
  rw [energy_def]; have := P.kin_nonneg v; have := P.H_nonneg v; positivity

theorem kin_le_two_energy (v : ι → ℝ) : P.kin v ≤ 2 * P.energy v := by
  rw [energy_def]; have := P.H_nonneg v; linarith

theorem quarter_wnorm4p4_le_energy (v : ι → ℝ) : P.β / 4 * wnorm4p4 P.w v ≤ P.energy v := by
  rw [energy_eq]; have := P.kin_nonneg v; have := P.pot_nonneg v; linarith

theorem nonlin_apply (v : ι → ℝ) (i : ι) : P.nonlin v i = P.V i * v i + P.β * v i ^ 3 := rfl

theorem inner_nonlin_self (v : ι → ℝ) :
    P.inner (P.nonlin v) v = P.pot v + P.β * wnorm4p4 P.w v := by
  unfold inner winner pot wnorm4p4
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [nonlin_apply]; ring

theorem lam_eq (v : ι → ℝ) : P.lam v = P.kin v + P.pot v + P.β * wnorm4p4 P.w v := by
  unfold lam gradE
  rw [inner_add_left, negLap_inner, inner_nonlin_self, kin_def]; ring

theorem lam_eq_energy (v : ι → ℝ) : P.lam v = 2 * P.energy v + P.β / 2 * wnorm4p4 P.w v := by
  rw [lam_eq, energy_eq]; ring

theorem lam_nonneg (v : ι → ℝ) : 0 ≤ P.lam v := by
  rw [lam_eq]
  have := P.kin_nonneg v; have := P.pot_nonneg v; have := P.wnorm4p4_nonneg v
  have := P.β_pos; positivity

theorem lam_le_four_energy (v : ι → ℝ) : P.lam v ≤ 4 * P.energy v := by
  rw [lam_eq_energy]; have := P.quarter_wnorm4p4_le_energy v; linarith

theorem gradE_def (v : ι → ℝ) : P.gradE v = P.negLap v + P.nonlin v := rfl

theorem gradE_eq_lam_smul_add_g (v : ι → ℝ) : P.gradE v = P.lam v • v + P.g v := by
  unfold g; abel

theorem inner_gradE_self (v : ι → ℝ) : P.inner (P.gradE v) v = P.lam v := rfl

theorem inner_g_self {v : ι → ℝ} (hv : P.nrm2sq v = 1) : P.inner (P.g v) v = 0 := by
  unfold g
  rw [inner_sub_left, inner_smul_left, inner_gradE_self, ← nrm2sq_def, hv]; ring

theorem inner_self_g {v : ι → ℝ} (hv : P.nrm2sq v = 1) : P.inner v (P.g v) = 0 := by
  rw [inner_comm, inner_g_self P hv]

theorem inner_gradE_eq (v d : ι → ℝ) :
    P.inner (P.gradE v) d = P.lam v * P.inner v d + P.inner (P.g v) d := by
  rw [gradE_eq_lam_smul_add_g, inner_add_left, inner_smul_left]

/-- `⟪n(u), d⟫_h` expanded. -/
theorem inner_nonlin (u d : ι → ℝ) :
    P.inner (P.nonlin u) d = ∑ i, P.w i * ((P.V i * u i + P.β * u i ^ 3) * d i) := rfl

/-! ### The metric matrix `G_X` -/

theorem GX_def (γ : ℝ) (v : ι → ℝ) : P.GX γ v = v + γ • P.negLap v := rfl

theorem inner_GX (γ : ℝ) (u v : ι → ℝ) :
    P.inner u (P.GX γ v) = P.inner u v + γ * (u ⬝ᵥ (P.S *ᵥ v)) := by
  rw [GX_def, inner_add_right, inner_smul_right, inner_negLap]

theorem GX_inner (γ : ℝ) (u v : ι → ℝ) :
    P.inner (P.GX γ u) v = P.inner u v + γ * (u ⬝ᵥ (P.S *ᵥ v)) := by
  rw [inner_comm, inner_GX, inner_comm, dotS_comm]

theorem inner_GX_self (γ : ℝ) (v : ι → ℝ) : P.inner v (P.GX γ v) = P.nrmGsq γ v := by
  rw [inner_GX, nrmGsq, nrm2sq_def, kin_def]

theorem GX_add (γ : ℝ) (u v : ι → ℝ) : P.GX γ (u + v) = P.GX γ u + P.GX γ v := by
  simp only [GX_def, negLap_add, smul_add]; abel

theorem GX_sub (γ : ℝ) (u v : ι → ℝ) : P.GX γ (u - v) = P.GX γ u - P.GX γ v := by
  simp only [GX_def, negLap_sub, smul_sub]; abel

theorem GX_smul (γ c : ℝ) (v : ι → ℝ) : P.GX γ (c • v) = c • P.GX γ v := by
  simp only [GX_def, negLap_smul, smul_add, smul_comm γ c]

theorem GX_neg (γ : ℝ) (v : ι → ℝ) : P.GX γ (-v) = - P.GX γ v := by
  simp only [GX_def, negLap_neg, smul_neg]; abel

@[simp] theorem GX_zero (γ : ℝ) : P.GX γ 0 = 0 := by simp [GX_def]

theorem nrmGsq_def (γ : ℝ) (v : ι → ℝ) : P.nrmGsq γ v = P.nrm2sq v + γ * P.kin v := rfl

theorem nrmGsq_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : 0 ≤ P.nrmGsq γ v := by
  rw [nrmGsq_def]; have := P.nrm2sq_nonneg v; have := P.kin_nonneg v; positivity

theorem nrm2sq_le_nrmGsq {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : P.nrm2sq v ≤ P.nrmGsq γ v := by
  rw [nrmGsq_def]; have := P.kin_nonneg v; nlinarith

theorem mul_kin_le_nrmGsq {γ : ℝ} (v : ι → ℝ) : γ * P.kin v ≤ P.nrmGsq γ v := by
  rw [nrmGsq_def]; have := P.nrm2sq_nonneg v; linarith

theorem nrmGsq_eq_zero_iff {γ : ℝ} (hγ : 0 ≤ γ) (v : ι → ℝ) : P.nrmGsq γ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 := P.nrm2sq_le_nrmGsq hγ v
    rw [h] at h1
    exact (P.nrm2sq_eq_zero_iff v).mp (le_antisymm h1 (P.nrm2sq_nonneg v))
  · rintro rfl; simp [nrmGsq_def, kin_def, nrm2sq_eq_sum]

theorem nrmGsq_smul (γ c : ℝ) (v : ι → ℝ) : P.nrmGsq γ (c • v) = c ^ 2 * P.nrmGsq γ v := by
  rw [nrmGsq_def, nrmGsq_def, nrm2sq_smul, kin_smul]; ring

theorem nrmGsq_add (γ : ℝ) (u v : ι → ℝ) :
    P.nrmGsq γ (u + v) = P.nrmGsq γ u + 2 * P.inner u (P.GX γ v) + P.nrmGsq γ v := by
  simp only [nrmGsq_def, nrm2sq_add, kin_add, inner_GX]; ring

/-- Cauchy–Schwarz for the `𝒢`-inner product `⟪u, G_X v⟫_h`. -/
theorem inner_GX_sq_le {γ : ℝ} (hγ : 0 ≤ γ) (u v : ι → ℝ) :
    (P.inner u (P.GX γ v)) ^ 2 ≤ P.nrmGsq γ u * P.nrmGsq γ v := by
  have h := sq_le_of_psd (fun u v => P.inner u (P.GX γ v))
    (fun u v w => by rw [inner_add_left])
    (fun c u v => by rw [inner_smul_left])
    (fun u v => by rw [inner_GX, inner_GX, inner_comm, dotS_comm])
    (fun v => by rw [inner_GX_self]; exact P.nrmGsq_nonneg hγ v) u v
  simpa only [inner_GX_self] using h

/-! ### Normalization -/

theorem normalize_def (z : ι → ℝ) : P.normalize z = (P.nrm2 z)⁻¹ • z := rfl

theorem nrm2_normalize {z : ι → ℝ} (hz : z ≠ 0) : P.nrm2 (P.normalize z) = 1 := by
  rw [normalize_def, nrm2_smul, abs_of_pos (inv_pos.mpr (P.nrm2_pos_of_ne_zero hz)),
    inv_mul_cancel₀ (P.nrm2_pos_of_ne_zero hz).ne']

theorem nrm2sq_normalize {z : ι → ℝ} (hz : z ≠ 0) : P.nrm2sq (P.normalize z) = 1 :=
  P.nrm2sq_eq_one_of_nrm2 (P.nrm2_normalize hz)

theorem nrm2_smul_normalize {z : ι → ℝ} (hz : z ≠ 0) : P.nrm2 z • P.normalize z = z := by
  rw [normalize_def, smul_smul, mul_inv_cancel₀ (P.nrm2_pos_of_ne_zero hz).ne', one_smul]

theorem normalize_eq_self {u : ι → ℝ} (hu : P.nrm2 u = 1) : P.normalize u = u := by
  rw [normalize_def, hu, inv_one, one_smul]

theorem normalize_smul (z : ι → ℝ) {c : ℝ} (hc : 0 < c) :
    P.normalize (c • z) = P.normalize z := by
  rw [normalize_def, normalize_def, nrm2_smul, abs_of_pos hc, smul_smul]
  congr 1
  field_simp

theorem normalize_pos {z : ι → ℝ} (hz : z ≠ 0) (hpos : ∀ i, 0 < z i) (i : ι) :
    0 < P.normalize z i := by
  rw [normalize_def, Pi.smul_apply, smul_eq_mul]
  exact mul_pos (inv_pos.mpr (P.nrm2_pos_of_ne_zero hz)) (hpos i)

theorem normalize_nonneg {z : ι → ℝ} (hpos : ∀ i, 0 ≤ z i) (i : ι) : 0 ≤ P.normalize z i := by
  rw [normalize_def, Pi.smul_apply, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (P.nrm2_nonneg z)) (hpos i)

/-! ### The iteration -/

theorem iter_zero (γ : ℝ) (u0 : ι → ℝ) : P.iter γ u0 0 = u0 := rfl

theorem iter_succ (γ : ℝ) (u0 : ι → ℝ) (k : ℕ) :
    P.iter γ u0 (k + 1) = P.step γ (P.iter γ u0 k) := by
  unfold iter; rw [Function.iterate_succ_apply']

theorem uiter_def (γ : ℝ) (u0 : ι → ℝ) (k : ℕ) :
    P.uiter γ u0 k = P.normalize (P.iter γ u0 k) := rfl

theorem R_def (γ : ℝ) (z : ι → ℝ) : P.R γ z = P.nrm2 z - 1 + γ * P.lam (P.normalize z) := rfl

theorem lyap_def (γ : ℝ) (z : ι → ℝ) :
    P.lyap γ z = P.energy (P.normalize z) + (P.R γ z) ^ 2 / γ := rfl

theorem energy_le_lyap {γ : ℝ} (hγ : 0 < γ) (z : ι → ℝ) :
    P.energy (P.normalize z) ≤ P.lyap γ z := by
  rw [lyap_def]; have : 0 ≤ (P.R γ z) ^ 2 / γ := by positivity
  linarith

end Setting

end GPDYS

end
