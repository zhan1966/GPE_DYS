import GPDYS.Resolvent
import GPDYS.Holder

/-!
# The data constants, the step-size conditions and the energy bounds

Section 3.3 of the paper: elementary properties of `w_min`, `‖V‖_∞`, `Λ_d`, of the level
`E₀` and of the constants `P₀, U₀, B₀, D, B₁, C₀, L₀`; Lemma 3.1 (the step-size conditions
(C1)–(C4) are equivalent to `γ ≤ γ_max`, and `𝓛(z⁰) ≤ E₀`); and Lemma 3.2 (consequences of the
energy bound `E_h(v) ≤ E₀` for `v ∈ 𝓜`).
-/

open Finset

noncomputable section

namespace GPDYS

namespace Setting

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Setting ι)

/-! ### `w_min`, `‖V‖_∞`, `Λ_d` -/

theorem wmin_le (i : ι) : P.wmin ≤ P.w i := Finite.ciInf_le P.w i

theorem wmin_pos [Nonempty ι] : 0 < P.wmin := by
  obtain ⟨i0, hi0⟩ := Finite.exists_min P.w
  exact lt_of_lt_of_le (P.w_pos i0) (le_ciInf hi0)

theorem le_Vinf (i : ι) : P.V i ≤ P.Vinf := Finite.le_ciSup P.V i

theorem Vinf_nonneg [Nonempty ι] : 0 ≤ P.Vinf := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (P.V_nonneg i).trans (P.le_Vinf i)

/-- `Sᵢᵢ ≥ 0`, as the value of the quadratic form of `S` at the `i`th unit vector. -/
theorem S_diag_nonneg (i : ι) : 0 ≤ P.S i i := by
  have h := P.S_psd (Pi.single i 1)
  rw [Matrix.mulVec_single_one, single_one_dotProduct] at h
  exact h

theorem le_Λd (i : ι) : P.S i i / P.w i ≤ P.Λd := Finite.le_ciSup (fun i => P.S i i / P.w i) i

theorem Λd_nonneg [Nonempty ι] : 0 ≤ P.Λd := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (div_nonneg (P.S_diag_nonneg i) (P.w_pos i).le).trans (P.le_Λd i)

/-- `⟪V v, v⟫_h ≤ ‖V‖_∞ ‖v‖₂²`. -/
theorem pot_le (v : ι → ℝ) : P.pot v ≤ P.Vinf * P.nrm2sq v := by
  rw [nrm2sq_eq_sum, Finset.mul_sum]
  unfold pot
  refine Finset.sum_le_sum fun i _ => ?_
  have h := mul_le_mul_of_nonneg_right (P.le_Vinf i)
    (mul_nonneg (P.w_pos i).le (sq_nonneg (v i)))
  linarith

/-- `‖V v‖₂ ≤ ‖V‖_∞ ‖v‖₂`. -/
theorem nrm2_Vmul_le (v : ι → ℝ) :
    P.nrm2 (fun i => P.V i * v i) ≤ P.Vinf * P.nrm2 v := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp [nrm2_def, nrm2sq_eq_sum]
  · apply P.nrm2_le_of_nrm2sq_le (mul_nonneg P.Vinf_nonneg (P.nrm2_nonneg v))
    rw [mul_pow, nrm2_sq, nrm2sq_eq_sum, nrm2sq_eq_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : P.V i ^ 2 ≤ P.Vinf ^ 2 := pow_le_pow_left₀ (P.V_nonneg i) (P.le_Vinf i) 2
    have h2 := mul_le_mul_of_nonneg_right h1 (mul_nonneg (P.w_pos i).le (sq_nonneg (v i)))
    rw [mul_pow]
    linarith

/-! ### The level `E₀` and the constants -/

variable (u0 : ι → ℝ)

theorem energy_le_E0 : P.energy u0 ≤ P.E0 u0 := by
  unfold E0
  have : 0 ≤ (P.lam u0) ^ 2 / max 1 (128 * P.energy u0) :=
    div_nonneg (sq_nonneg _) (le_trans zero_le_one (le_max_left _ _))
  linarith

theorem E0_le : P.E0 u0 ≤ 9 / 8 * P.energy u0 := by
  unfold E0
  have hE := P.energy_nonneg u0
  have hl := P.lam_le_four_energy u0
  have hl0 := P.lam_nonneg u0
  have hmax : 0 < max 1 (128 * P.energy u0) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hsq : (P.lam u0) ^ 2 ≤ (4 * P.energy u0) ^ 2 := pow_le_pow_left₀ hl0 hl 2
  have key : (P.lam u0) ^ 2 / max 1 (128 * P.energy u0) ≤ P.energy u0 / 8 := by
    rw [div_le_iff₀ hmax]
    rcases le_or_gt (128 * P.energy u0) 1 with h | h
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right h.le]
      nlinarith
  linarith

theorem energy_pos_of_ne_zero {v : ι → ℝ} (hv : v ≠ 0) : 0 < P.energy v := by
  have h1 := P.quarter_wnorm4p4_le_energy v
  have h2 : 0 < wnorm4p4 P.w v := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hi' : v i ≠ 0 := hi
    unfold wnorm4p4
    refine Finset.sum_pos' (fun j _ => mul_nonneg (P.w_pos j).le (by positivity)) ?_
    exact ⟨i, Finset.mem_univ i, mul_pos (P.w_pos i) (by positivity)⟩
  have hβ := P.β_pos
  have : 0 < P.β / 4 * wnorm4p4 P.w v := by positivity
  linarith

theorem E0_pos (hu0 : u0 ≠ 0) : 0 < P.E0 u0 :=
  lt_of_lt_of_le (P.energy_pos_of_ne_zero hu0) (P.energy_le_E0 u0)

theorem E0_nonneg : 0 ≤ P.E0 u0 := (P.energy_nonneg u0).trans (P.energy_le_E0 u0)

theorem P0_nonneg : 0 ≤ P.P0 u0 := by
  unfold P0; have := P.E0_nonneg u0; positivity

/-- The Sobolev constant is positive (apply the Sobolev inequality to the constant vector `1`). -/
theorem CS_pos [Nonempty ι] : 0 < P.CS := by
  have h : wnorm6 P.w (fun _ => 1) ≤
      P.CS * Real.sqrt (P.kin (fun _ => 1) + P.nrm2sq (fun _ => 1)) := P.sobolev _
  have hpos : 0 < wnorm6 P.w (fun _ => 1) := by
    unfold wnorm6
    apply Real.rpow_pos_of_pos
    unfold wnorm6p6
    simp only [one_pow, mul_one]
    exact Finset.sum_pos (fun i _ => P.w_pos i) Finset.univ_nonempty
  by_contra hcon
  rw [not_lt] at hcon
  have h2 := mul_nonpos_of_nonpos_of_nonneg hcon
    (Real.sqrt_nonneg (P.kin (fun _ => 1) + P.nrm2sq (fun _ => 1)))
  linarith

theorem P0_pos [Nonempty ι] : 0 < P.P0 u0 := by
  unfold P0; have := P.E0_nonneg u0; have := P.CS_pos; positivity

theorem U0_nonneg [Nonempty ι] : 0 ≤ P.U0 u0 := by
  unfold U0
  have hw := P.wmin_pos
  have hP := P.P0_nonneg u0
  refine le_min (by positivity) (le_min ?_ ?_)
  · exact div_nonneg hP (Real.rpow_nonneg hw.le _)
  · exact mul_nonneg zero_le_two (Real.sqrt_nonneg _)

theorem U0_pos [Nonempty ι] (hu0 : u0 ≠ 0) : 0 < P.U0 u0 := by
  unfold U0
  have hw := P.wmin_pos
  have hP := P.P0_pos u0
  have hE := P.E0_pos u0 hu0
  have hβ := P.β_pos
  refine lt_min (by positivity) (lt_min ?_ ?_)
  · exact div_pos hP (Real.rpow_pos_of_pos hw _)
  · exact mul_pos two_pos (Real.sqrt_pos.mpr (div_pos hE (mul_pos hβ hw)))

theorem U0_le_inv_wmin : P.U0 u0 ≤ 1 / P.wmin := min_le_left _ _

theorem B0_nonneg [Nonempty ι] : 0 ≤ P.B0 u0 := by
  unfold B0
  have h1 := P.Vinf_nonneg
  have h2 : 0 ≤ min ((P.P0 u0) ^ ((3 : ℝ) / 2)) (P.U0 u0) :=
    le_min (Real.rpow_nonneg (P.P0_nonneg u0) _) (P.U0_nonneg u0)
  exact add_nonneg h1 (mul_nonneg P.β_pos.le h2)

theorem E0_le_D [Nonempty ι] : P.E0 u0 ≤ P.D u0 := by
  unfold D; have := P.B0_nonneg u0; linarith

theorem B0_le_D : P.B0 u0 ≤ P.D u0 := by
  unfold D; have := P.E0_nonneg u0; linarith

theorem D_pos [Nonempty ι] (hu0 : u0 ≠ 0) : 0 < P.D u0 :=
  lt_of_lt_of_le (P.E0_pos u0 hu0) (P.E0_le_D u0)

theorem B1_pos [Nonempty ι] (hu0 : u0 ≠ 0) : 0 < P.B1 u0 := by
  unfold B1
  have := P.Vinf_nonneg; have := P.β_pos; have := P.U0_pos u0 hu0
  positivity

theorem C0_pos [Nonempty ι] : 0 < P.C0 u0 := by
  unfold C0; have := P.β_pos; have := P.CS_pos; have := P.P0_pos u0; positivity

theorem L0_pos [Nonempty ι] (hu0 : u0 ≠ 0) : 0 < P.L0 u0 := by
  unfold L0
  have h1 := P.Vinf_nonneg
  have hβ := P.β_pos
  have hU := P.U0_pos u0 hu0
  have hC := P.C0_pos u0
  have h2 : 0 < min (3 * P.β * P.U0 u0) (P.C0 u0 + 2 * (max (P.C0 u0 - 1 / 4) 0) ^ 2) := by
    refine lt_min (by positivity) ?_
    have : 0 ≤ (max (P.C0 u0 - 1 / 4) 0) ^ 2 := sq_nonneg _
    linarith
  linarith

theorem γmax_pos [Nonempty ι] (hu0 : u0 ≠ 0) : 0 < P.γmax u0 := by
  unfold γmax
  have hD := P.D_pos u0 hu0
  have hL := P.L0_pos u0 hu0
  have hB := P.B1_pos u0 hu0
  refine lt_min one_pos (lt_min (by positivity) (lt_min (by positivity) ?_))
  exact div_pos two_pos (by positivity)

/-! ### Lemma 3.1: the step-size conditions -/

/-- The key algebraic identity behind (C4): with `s = √(B₁² + 12 D Λ_d)`,
`4 (γ B₁ + 3 γ² D Λ_d - 1) = (γ (B₁ + s) - 2) (γ (s - B₁) + 2)`. -/
theorem C4_identity {B D Λ γ s : ℝ} (hs : s ^ 2 = B ^ 2 + 12 * D * Λ) :
    4 * (γ * B + 3 * γ ^ 2 * D * Λ - 1) = (γ * (B + s) - 2) * (γ * (s - B) + 2) := by
  linear_combination (-(γ ^ 2)) * hs

/-- Lemma 3.1 (⇒): `γ ≤ γ_max` implies (C1)–(C4). -/
theorem conditions_of_le_γmax [Nonempty ι] (hu0 : u0 ≠ 0) {γ : ℝ} (hγ : 0 < γ)
    (h : γ ≤ P.γmax u0) : P.Conditions u0 γ := by
  unfold γmax at h
  rw [le_min_iff, le_min_iff, le_min_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hD := P.D_pos u0 hu0
  have hL := P.L0_pos u0 hu0
  have hB := P.B1_pos u0 hu0
  have hΛ := P.Λd_nonneg
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at h2; linarith
  · rw [le_div_iff₀ (by positivity)] at h3; linarith
  · have hDΛ : 0 ≤ 12 * P.D u0 * P.Λd := by positivity
    set s := Real.sqrt ((P.B1 u0) ^ 2 + 12 * P.D u0 * P.Λd) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = (P.B1 u0) ^ 2 + 12 * P.D u0 * P.Λd := Real.sq_sqrt (by positivity)
    have hsB : P.B1 u0 ≤ s := by
      rw [hs]; exact Real.le_sqrt_of_sq_le (by linarith)
    rw [le_div_iff₀ (by positivity)] at h4
    have hid := C4_identity (B := P.B1 u0) (D := P.D u0) (Λ := P.Λd) (γ := γ) hs2
    have hpos : 0 ≤ γ * (s - P.B1 u0) + 2 := by nlinarith
    have hprod : (γ * (P.B1 u0 + s) - 2) * (γ * (s - P.B1 u0) + 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hpos
    linarith

/-- Lemma 3.1 (⇐): (C1)–(C4) imply `γ ≤ γ_max`. -/
theorem le_γmax_of_conditions [Nonempty ι] (hu0 : u0 ≠ 0) {γ : ℝ} (hγ : 0 < γ)
    (h : P.Conditions u0 γ) : γ ≤ P.γmax u0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hD := P.D_pos u0 hu0
  have hL := P.L0_pos u0 hu0
  have hB := P.B1_pos u0 hu0
  have hΛ := P.Λd_nonneg
  unfold γmax
  refine le_min h1 (le_min ?_ (le_min ?_ ?_))
  · rw [le_div_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith
  · have hDΛ : 0 ≤ 12 * P.D u0 * P.Λd := by positivity
    set s := Real.sqrt ((P.B1 u0) ^ 2 + 12 * P.D u0 * P.Λd) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = (P.B1 u0) ^ 2 + 12 * P.D u0 * P.Λd := Real.sq_sqrt (by positivity)
    have hsB : P.B1 u0 ≤ s := by
      rw [hs]; exact Real.le_sqrt_of_sq_le (by linarith)
    rw [le_div_iff₀ (by positivity)]
    have hid := C4_identity (B := P.B1 u0) (D := P.D u0) (Λ := P.Λd) (γ := γ) hs2
    have hpos : 0 < γ * (s - P.B1 u0) + 2 := by nlinarith
    by_contra hcon
    rw [not_le] at hcon
    have hprod : 0 < (γ * (P.B1 u0 + s) - 2) * (γ * (s - P.B1 u0) + 2) :=
      mul_pos (by linarith) hpos
    linarith

/-- Under (C1), (C2): `γ ≤ 1 / max{1, 128 E_h(u⁰)}`. -/
theorem le_inv_max_of_conditions [Nonempty ι] {γ : ℝ} (hγ : 0 < γ) (h : P.Conditions u0 γ) :
    γ ≤ 1 / max 1 (128 * P.energy u0) := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hE := P.energy_le_E0 u0
  have hED := P.E0_le_D u0
  rcases le_or_gt (128 * P.energy u0) 1 with hc | hc
  · rw [max_eq_left hc, div_one]; exact h1
  · rw [max_eq_right hc.le, le_div_iff₀ (by linarith)]
    have : γ * P.energy u0 ≤ γ * P.D u0 := mul_le_mul_of_nonneg_left (hE.trans hED) hγ.le
    linarith

/-- Lemma 3.1, last assertion: `𝓛(z⁰) ≤ E₀` for `z⁰ = u⁰ ∈ 𝓜`.
The proof uses `𝓛(z⁰) = E_h(u⁰) + γ λ(u⁰)²`. -/
theorem lyap_init_le_E0 [Nonempty ι] (hn : P.nrm2 u0 = 1) {γ : ℝ} (hγ : 0 < γ)
    (h : P.Conditions u0 γ) : P.lyap γ u0 ≤ P.E0 u0 := by
  have hγm := P.le_inv_max_of_conditions u0 hγ h
  have hγ' := hγ.ne'
  rw [lyap_def, R_def, P.normalize_eq_self hn, hn]
  unfold E0
  have hR : (1 - 1 + γ * P.lam u0) ^ 2 / γ = γ * (P.lam u0) ^ 2 := by
    field_simp; ring
  rw [hR]
  have hmax : 0 < max 1 (128 * P.energy u0) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have : γ * (P.lam u0) ^ 2 ≤ (P.lam u0) ^ 2 / max 1 (128 * P.energy u0) := by
    rw [le_div_iff₀ hmax]
    rw [le_div_iff₀ hmax] at hγm
    have := mul_le_mul_of_nonneg_left hγm (sq_nonneg (P.lam u0))
    linarith
  linarith

/-! ### Lemma 3.2: consequences of the energy bound -/

/-- A vector of norm one forces the index type to be nonempty. -/
theorem nonempty_of_nrm2sq_eq_one {v : ι → ℝ} (hv : P.nrm2sq v = 1) : Nonempty ι := by
  rcases isEmpty_or_nonempty ι with h | h
  · exfalso
    rw [nrm2sq_eq_sum, Finset.univ_eq_empty, Finset.sum_empty] at hv
    exact zero_ne_one hv
  · exact h

section EnergyBound

variable {u0} {v : ι → ℝ} (hv : P.nrm2sq v = 1) (hE : P.energy v ≤ P.E0 u0)
include hv hE

/-- Lemma 3.2 (i): `⟪v, -Δ_h v⟫_h ≤ 2E₀`. -/
theorem kin_le_two_E0 : P.kin v ≤ 2 * P.E0 u0 := by
  have := P.kin_le_two_energy v; linarith

/-- Lemma 3.2 (i): `‖v‖²_{1,h} ≤ 2E₀ + 1`. -/
theorem h1norm_le : P.kin v + P.nrm2sq v ≤ 2 * P.E0 u0 + 1 := by
  have := P.kin_le_two_E0 hv hE; linarith

/-- Lemma 3.2 (i): `‖v‖₆² ≤ P₀`. -/
theorem wnorm6_sq_le_P0 : wnorm6 P.w v ^ 2 ≤ P.P0 u0 := by
  have hs : wnorm6 P.w v ≤ P.CS * Real.sqrt (P.kin v + P.nrm2sq v) := P.sobolev v
  have h1 := P.h1norm_le hv hE
  have hw6 : 0 ≤ wnorm6 P.w v := wnorm6_nonneg P.w (fun i => (P.w_pos i).le) v
  have hkin : 0 ≤ P.kin v + P.nrm2sq v := add_nonneg (P.kin_nonneg v) (P.nrm2sq_nonneg v)
  unfold P0
  calc wnorm6 P.w v ^ 2 ≤ (P.CS * Real.sqrt (P.kin v + P.nrm2sq v)) ^ 2 :=
        pow_le_pow_left₀ hw6 hs 2
    _ = P.CS ^ 2 * (P.kin v + P.nrm2sq v) := by rw [mul_pow, Real.sq_sqrt hkin]
    _ ≤ P.CS ^ 2 * (2 * P.E0 u0 + 1) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

/-- Lemma 3.2 (i): `‖v‖₆⁶ ≤ P₀³`. -/
theorem wnorm6p6_le_P0_cube : wnorm6p6 P.w v ≤ P.P0 u0 ^ 3 := by
  have h := P.wnorm6_sq_le_P0 hv hE
  rw [← wnorm6_pow_six P.w (fun i => (P.w_pos i).le) v]
  calc wnorm6 P.w v ^ 6 = (wnorm6 P.w v ^ 2) ^ 3 := by ring
    _ ≤ P.P0 u0 ^ 3 := pow_le_pow_left₀ (sq_nonneg _) h 3

/-- Lemma 3.2 (ii): `vᵢ² ≤ U₀` for every `i` (i.e. `‖v‖_∞² ≤ U₀`). -/
theorem sq_le_U0 (i : ι) : v i ^ 2 ≤ P.U0 u0 := by
  have : Nonempty ι := ⟨i⟩
  have hw := P.w_pos i
  have hwmin := P.wmin_le i
  have hwmin0 := P.wmin_pos
  have hβ := P.β_pos
  have hP0 := P.P0_nonneg u0
  have hE0 := P.E0_nonneg u0
  -- (1) `vᵢ² ≤ 1 / w_min`
  have h1 : v i ^ 2 ≤ 1 / P.wmin := by
    have h := P.w_mul_sq_le_nrm2sq v i
    rw [hv] at h
    rw [le_div_iff₀ hwmin0]
    have := mul_le_mul_of_nonneg_left hwmin (sq_nonneg (v i))
    linarith
  -- (2) `vᵢ² ≤ P₀ / w_min^{1/3}`
  have h2 : v i ^ 2 ≤ P.P0 u0 / P.wmin ^ ((1 : ℝ) / 3) := by
    have hc : 0 < P.wmin ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hwmin0 _
    have hc3 : (P.wmin ^ ((1 : ℝ) / 3)) ^ 3 = P.wmin := by
      rw [← Real.rpow_mul_natCast hwmin0.le]; norm_num
    have h6 : P.w i * v i ^ 6 ≤ P.P0 u0 ^ 3 := by
      refine le_trans ?_ (P.wnorm6p6_le_P0_cube hv hE)
      unfold wnorm6p6
      exact Finset.single_le_sum
        (fun j _ => mul_nonneg (P.w_pos j).le (Even.pow_nonneg ⟨3, rfl⟩ _)) (Finset.mem_univ i)
    rw [le_div_iff₀ hc]
    refine (pow_le_pow_iff_left₀ (by positivity) hP0 (by norm_num : (3 : ℕ) ≠ 0)).mp ?_
    calc (v i ^ 2 * P.wmin ^ ((1 : ℝ) / 3)) ^ 3
        = (v i ^ 2) ^ 3 * (P.wmin ^ ((1 : ℝ) / 3)) ^ 3 := by ring
      _ = v i ^ 6 * P.wmin := by rw [hc3]; ring
      _ ≤ v i ^ 6 * P.w i := mul_le_mul_of_nonneg_left hwmin (by positivity)
      _ = P.w i * v i ^ 6 := by ring
      _ ≤ P.P0 u0 ^ 3 := h6
  -- (3) `vᵢ² ≤ 2 √(E₀ / (β w_min))`
  have h3 : v i ^ 2 ≤ 2 * Real.sqrt (P.E0 u0 / (P.β * P.wmin)) := by
    have h4 : P.w i * v i ^ 4 ≤ wnorm4p4 P.w v := by
      unfold wnorm4p4
      exact Finset.single_le_sum
        (fun j _ => mul_nonneg (P.w_pos j).le (Even.pow_nonneg ⟨2, rfl⟩ _)) (Finset.mem_univ i)
    have hE' := (P.quarter_wnorm4p4_le_energy v).trans hE
    have h5 : P.β * P.wmin * v i ^ 4 ≤ 4 * P.E0 u0 := by
      have h7 : P.β * P.wmin * v i ^ 4 ≤ P.β * P.w i * v i ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwmin hβ.le) (by positivity)
      have h8 := mul_le_mul_of_nonneg_left h4 hβ.le
      linarith
    have e : (2 : ℝ) * Real.sqrt (P.E0 u0 / (P.β * P.wmin))
        = Real.sqrt (4 * P.E0 u0 / (P.β * P.wmin)) := by
      rw [show (4 : ℝ) * P.E0 u0 / (P.β * P.wmin) = 2 ^ 2 * (P.E0 u0 / (P.β * P.wmin)) by ring,
        Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [e]
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ (by positivity)]
    linarith
  unfold U0
  exact le_min h1 (le_min h2 h3)

/-- Lemma 3.2 (iii): `‖v³‖₂ ≤ min{P₀^{3/2}, U₀}`. -/
theorem nrm2_cube_le : P.nrm2 (fun i => v i ^ 3) ≤ min (P.P0 u0 ^ ((3 : ℝ) / 2)) (P.U0 u0) := by
  have hcube : P.nrm2sq (fun i => v i ^ 3) = wnorm6p6 P.w v := by
    rw [nrm2sq_eq_sum]; unfold wnorm6p6
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hP0 := P.P0_nonneg u0
  refine le_min ?_ ?_
  · apply P.nrm2_le_of_nrm2sq_le (Real.rpow_nonneg hP0 _)
    have e : (P.P0 u0 ^ ((3 : ℝ) / 2)) ^ 2 = P.P0 u0 ^ 3 := by
      rw [← Real.rpow_mul_natCast hP0]; norm_num
    rw [hcube, e]
    exact P.wnorm6p6_le_P0_cube hv hE
  · have := P.nonempty_of_nrm2sq_eq_one hv
    apply P.nrm2_le_of_nrm2sq_le (P.U0_nonneg u0)
    rw [hcube]
    calc wnorm6p6 P.w v = ∑ i, P.w i * v i ^ 2 * (v i ^ 2) ^ 2 := by
          unfold wnorm6p6; refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ ≤ ∑ i, P.w i * v i ^ 2 * P.U0 u0 ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (sq_nonneg _) (P.sq_le_U0 hv hE i) 2)
            (mul_nonneg (P.w_pos i).le (sq_nonneg _))
      _ = P.U0 u0 ^ 2 * P.nrm2sq v := by
          rw [nrm2sq_eq_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_; ring
      _ = P.U0 u0 ^ 2 := by rw [hv, mul_one]

/-- Lemma 3.2 (iii): `‖v‖₄⁴ ≤ min{P₀^{3/2}, U₀}`. -/
theorem wnorm4p4_le_min : wnorm4p4 P.w v ≤ min (P.P0 u0 ^ ((3 : ℝ) / 2)) (P.U0 u0) := by
  have h1 : wnorm4p4 P.w v = P.inner v (fun i => v i ^ 3) := by
    unfold wnorm4p4; rw [inner_def]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have h2 := P.inner_le_nrm2_mul_nrm2 v (fun i => v i ^ 3)
  rw [P.nrm2_eq_one_of_nrm2sq hv, one_mul] at h2
  rw [h1]
  exact h2.trans (P.nrm2_cube_le hv hE)

/-- Lemma 3.2 (iii): `‖n(v)‖₂ ≤ B₀`. -/
theorem nrm2_nonlin_le [Nonempty ι] : P.nrm2 (P.nonlin v) ≤ P.B0 u0 := by
  have hfun : P.nonlin v = (fun i => P.V i * v i) + P.β • (fun i => v i ^ 3) := by
    funext i; simp [nonlin_apply]
  rw [hfun]
  have h1 := P.nrm2_add_le (fun i => P.V i * v i) (P.β • fun i => v i ^ 3)
  have h2 := P.nrm2_Vmul_le v
  rw [P.nrm2_eq_one_of_nrm2sq hv, mul_one] at h2
  have h3 : P.nrm2 (P.β • fun i => v i ^ 3) = P.β * P.nrm2 (fun i => v i ^ 3) := by
    rw [nrm2_smul, abs_of_pos P.β_pos]
  have h4 := P.nrm2_cube_le hv hE
  have hβ := P.β_pos
  unfold B0
  calc P.nrm2 ((fun i => P.V i * v i) + P.β • fun i => v i ^ 3)
      ≤ P.nrm2 (fun i => P.V i * v i) + P.nrm2 (P.β • fun i => v i ^ 3) := h1
    _ ≤ P.Vinf + P.β * min (P.P0 u0 ^ ((3 : ℝ) / 2)) (P.U0 u0) := by
        rw [h3]; exact add_le_add h2 (mul_le_mul_of_nonneg_left h4 hβ.le)

/-- Lemma 3.2 (iii): `⟪n(v), v⟫_h ≤ B₀`. -/
theorem inner_nonlin_self_le [Nonempty ι] : P.inner (P.nonlin v) v ≤ P.B0 u0 := by
  rw [inner_nonlin_self]
  have h1 := P.pot_le v
  rw [hv, mul_one] at h1
  have h2 := P.wnorm4p4_le_min hv hE
  unfold B0
  exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 P.β_pos.le)

/-- Upper bound in Lemma 3.2 (iv): `λ(v) ≤ 2D`; `lam_nonneg` gives the lower bound. -/
theorem lam_le_two_D [Nonempty ι] : P.lam v ≤ 2 * P.D u0 := by
  rw [lam_eq]
  have h1 := P.kin_le_two_E0 hv hE
  have h2 := P.inner_nonlin_self_le hv hE
  rw [inner_nonlin_self] at h2
  have h3 := P.B0_nonneg u0
  unfold D
  linarith

end EnergyBound

end Setting

end GPDYS

end
