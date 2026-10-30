import Mathlib

/-!
# The discrete Gross–Pitaevskii ground state problem and the DYS I scheme

Formalization of

  J. Li, S. Zheng, X. Zhang, *Global convergence of an efficient splitting method for the
  defocusing Gross–Pitaevskii ground state problem*, arXiv:2609.13509.

This file contains the definitions of Sections 2 and 3 of the paper:

* the data of a monotone discretization (`GPDYS.Setting`), using the fixed-mesh properties
  listed in Lemma 2.2 ("What the discretization provides"); mesh-uniformity of the Sobolev
  constant and construction of a mesh satisfying these properties are not formalized;
* the discrete inner product, norms, energy, gradient, eigenvalue functional and projected
  gradient of §3.1;
* the metric matrix `G_X = I - γ Δ_h`, its resolvent, the `X`- and `𝒢`-norms, one step of the
  scheme (DYS I), the radial residual `R` and the Lyapunov function `𝓛` of §3.2;
* the data constants and the step-size threshold `γ_max` of §3.3.

Vectors are functions `ι → ℝ` on a finite index type `ι` (the interior nodes of the mesh).
-/

open Finset Matrix

noncomputable section

namespace GPDYS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Weighted norms (quadrature norms) -/

/-- The weighted (discrete `L²`) inner product `⟪u, v⟫_h = ∑ᵢ wᵢ uᵢ vᵢ`. -/
def winner (w : ι → ℝ) (u v : ι → ℝ) : ℝ := ∑ i, w i * (u i * v i)

/-- `‖v‖₂² = ∑ᵢ wᵢ vᵢ²`. -/
def wnorm2sq (w : ι → ℝ) (v : ι → ℝ) : ℝ := winner w v v

/-- `‖v‖₂ = (∑ᵢ wᵢ vᵢ²)^{1/2}`. -/
def wnorm2 (w : ι → ℝ) (v : ι → ℝ) : ℝ := Real.sqrt (wnorm2sq w v)

/-- `‖v‖₃³ = ∑ᵢ wᵢ |vᵢ|³`. -/
def wnorm3p3 (w : ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, w i * |v i| ^ 3

/-- `‖v‖₄⁴ = ∑ᵢ wᵢ vᵢ⁴`. -/
def wnorm4p4 (w : ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, w i * v i ^ 4

/-- `‖v‖₆⁶ = ∑ᵢ wᵢ vᵢ⁶`. -/
def wnorm6p6 (w : ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, w i * v i ^ 6

/-- `‖v‖₃ = (∑ᵢ wᵢ |vᵢ|³)^{1/3}`. -/
def wnorm3 (w : ι → ℝ) (v : ι → ℝ) : ℝ := (wnorm3p3 w v) ^ ((1 : ℝ) / 3)

/-- `‖v‖₆ = (∑ᵢ wᵢ vᵢ⁶)^{1/6}`. -/
def wnorm6 (w : ι → ℝ) (v : ι → ℝ) : ℝ := (wnorm6p6 w v) ^ ((1 : ℝ) / 6)

/-! ### The setting: what the discretization provides (Lemma 2.2) -/

/-- The data of the discrete ground state problem under Assumption 2.1, recorded through the
fixed-mesh properties of Lemma 2.2. The structure assumes these properties; it does not
construct a finite element mesh or express uniformity of `CS` across a family of meshes:

* `w` are the quadrature weights (the lumped mass matrix is `M = diag w`), all positive;
* `S` is the stiffness matrix: symmetric, positive semidefinite, with nonpositive off-diagonal
  entries, and such that `(M + γ S)⁻¹` has strictly positive entries for every `γ > 0`
  (Lemma 2.2 (ii), a consequence of `M + γ S` being an irreducible Stieltjes matrix);
* `V ≥ 0` is the potential at the nodes and `β > 0` the coupling constant;
* `CS` is the constant of the discrete Sobolev inequality `‖v‖₆ ≤ C_S ‖v‖_{1,h}`
  (Lemma 2.2 (iii)), where `‖v‖²_{1,h} = ⟪v, -Δ_h v⟫_h + ‖v‖₂² = vᵀ S v + ‖v‖₂²`. -/
structure Setting (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- quadrature weights -/
  w : ι → ℝ
  w_pos : ∀ i, 0 < w i
  /-- stiffness matrix -/
  S : Matrix ι ι ℝ
  S_symm : S.IsSymm
  S_psd : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (S *ᵥ v)
  S_offdiag : ∀ i j, i ≠ j → S i j ≤ 0
  /-- `(M + γ S)⁻¹` has strictly positive entries for every `γ > 0` -/
  resolvent_pos : ∀ γ : ℝ, 0 < γ → ∀ i j, 0 < (Matrix.diagonal w + γ • S)⁻¹ i j
  /-- potential -/
  V : ι → ℝ
  V_nonneg : ∀ i, 0 ≤ V i
  /-- coupling constant -/
  β : ℝ
  β_pos : 0 < β
  /-- Sobolev constant -/
  CS : ℝ
  sobolev : ∀ v : ι → ℝ, wnorm6 w v ≤ CS * Real.sqrt (v ⬝ᵥ (S *ᵥ v) + wnorm2sq w v)

namespace Setting

variable (P : Setting ι)

/-! ### Norms, energy and gradients (§2 and §3.1) -/

/-- The lumped mass matrix `M = diag(w)`. -/
def M : Matrix ι ι ℝ := Matrix.diagonal P.w

/-- The discrete inner product `⟪u, v⟫_h = uᵀ M v`. -/
def inner (u v : ι → ℝ) : ℝ := winner P.w u v

/-- `‖v‖₂²`. -/
def nrm2sq (v : ι → ℝ) : ℝ := wnorm2sq P.w v

/-- `‖v‖₂`. -/
def nrm2 (v : ι → ℝ) : ℝ := wnorm2 P.w v

/-- The negative discrete Laplacian `-Δ_h = M⁻¹ S`. -/
def negLap (v : ι → ℝ) : ι → ℝ := fun i => (P.S *ᵥ v) i / P.w i

/-- The kinetic quadratic form `⟪v, -Δ_h v⟫_h = vᵀ S v`. -/
def kin (v : ι → ℝ) : ℝ := v ⬝ᵥ (P.S *ᵥ v)

/-- The potential quadratic form `⟪V v, v⟫_h`. -/
def pot (v : ι → ℝ) : ℝ := ∑ i, P.w i * (P.V i * v i ^ 2)

/-- The explicit part `H(v) = ½ ⟪V v, v⟫_h + (β/4) ‖v‖₄⁴` of the energy. -/
def H (v : ι → ℝ) : ℝ := (1 / 2) * P.pot v + P.β / 4 * wnorm4p4 P.w v

/-- The discrete energy `E_h(v) = ½ ⟪v, -Δ_h v⟫_h + ½ ⟪V v, v⟫_h + (β/4) ‖v‖₄⁴`. -/
def energy (v : ι → ℝ) : ℝ := (1 / 2) * P.kin v + P.H v

/-- The explicit part `n(v) = V v + β v³` of the gradient. -/
def nonlin (v : ι → ℝ) : ι → ℝ := fun i => P.V i * v i + P.β * v i ^ 3

/-- The gradient `∇E_h(v) = -Δ_h v + n(v)` with respect to `⟪·,·⟫_h`. -/
def gradE (v : ι → ℝ) : ι → ℝ := P.negLap v + P.nonlin v

/-- The eigenvalue functional `λ(v) = ⟪∇E_h(v), v⟫_h`. -/
def lam (v : ι → ℝ) : ℝ := P.inner (P.gradE v) v

/-- The projected gradient `g(v) = ∇E_h(v) - λ(v) v`. -/
def g (v : ι → ℝ) : ι → ℝ := P.gradE v - P.lam v • v

/-- The Jacobian of `n`: `n'(v) = V + 3 β diag(v²)`, applied to a vector. -/
def nonlin' (v d : ι → ℝ) : ι → ℝ := fun i => (P.V i + 3 * P.β * v i ^ 2) * d i

/-! ### The metric matrix, the resolvent and the `X`- and `𝒢`-norms (§3.2) -/

/-- The metric matrix `G_X = I - γ Δ_h`, applied to a vector. -/
def GX (γ : ℝ) (v : ι → ℝ) : ι → ℝ := v + γ • P.negLap v

/-- The resolvent `G_X⁻¹ = (M + γ S)⁻¹ M`, applied to a vector. -/
def resolvent (γ : ℝ) (v : ι → ℝ) : ι → ℝ := (P.M + γ • P.S)⁻¹ *ᵥ (P.M *ᵥ v)

/-- The `X`-inner product `⟪v, w⟫_X = ⟪v, G_X⁻¹ w⟫_h`. -/
def innerX (γ : ℝ) (v w : ι → ℝ) : ℝ := P.inner v (P.resolvent γ w)

/-- `‖v‖_X²`. -/
def nrmXsq (γ : ℝ) (v : ι → ℝ) : ℝ := P.innerX γ v v

/-- `‖v‖_𝒢² = ⟪v, G_X v⟫_h = ‖v‖₂² + γ ⟪v, -Δ_h v⟫_h`. -/
def nrmGsq (γ : ℝ) (v : ι → ℝ) : ℝ := P.nrm2sq v + γ * P.kin v

/-! ### One step of the scheme, the residual and the Lyapunov function (§3.2) -/

/-- The normalized vector `u = z / ‖z‖₂` for `z ≠ 0`; at zero this total function is zero. -/
def normalize (z : ι → ℝ) : ι → ℝ := (P.nrm2 z)⁻¹ • z

/-- The intermediate vector `𝐱 = G_X⁻¹ (2u - z - γ n(u))` of (DYS I). -/
def xi (γ : ℝ) (z : ι → ℝ) : ι → ℝ :=
  P.resolvent γ ((2 : ℝ) • P.normalize z - z - γ • P.nonlin (P.normalize z))

/-- One step `z ↦ z⁺ = z + 𝐱 - u` of the scheme (DYS I), (1.6) in the paper. -/
def step (γ : ℝ) (z : ι → ℝ) : ι → ℝ := z + P.xi γ z - P.normalize z

/-- The radial residual `R(z) = ‖z‖₂ - 1 + γ λ(u)`. -/
def R (γ : ℝ) (z : ι → ℝ) : ℝ := P.nrm2 z - 1 + γ * P.lam (P.normalize z)

/-- The Lyapunov function `𝓛(z) = E_h(u) + R(z)² / γ`. -/
def lyap (γ : ℝ) (z : ι → ℝ) : ℝ := P.energy (P.normalize z) + (P.R γ z) ^ 2 / γ

/-- The iteration `z^k`, started from `z⁰ = u⁰`. -/
def iter (γ : ℝ) (u0 : ι → ℝ) (k : ℕ) : ι → ℝ := (P.step γ)^[k] u0

/-- The normalized iterates `u^k = z^k / ‖z^k‖₂`. -/
def uiter (γ : ℝ) (u0 : ι → ℝ) (k : ℕ) : ι → ℝ := P.normalize (P.iter γ u0 k)

/-! ### Data constants and the step-size threshold (§3.3) -/

/-- `w_min = minᵢ wᵢ` when `ι` is nonempty; the empty-index value is zero. -/
def wmin : ℝ := ⨅ i, P.w i

/-- `‖V‖_∞ = maxᵢ Vᵢ` on a nonempty mesh (recall `V ≥ 0`); zero for empty `ι`. -/
def Vinf : ℝ := ⨆ i, P.V i

/-- The stiffness-to-mass ratio `Λ_d = maxᵢ Sᵢᵢ / wᵢ` on a nonempty mesh; zero for empty `ι`. -/
def Λd : ℝ := ⨆ i, P.S i i / P.w i

/-- The energy level `E₀ = E_h(u⁰) + λ(u⁰)² / max{1, 128 E_h(u⁰)}`, (3.9). -/
def E0 (u0 : ι → ℝ) : ℝ := P.energy u0 + (P.lam u0) ^ 2 / max 1 (128 * P.energy u0)

/-- `P₀ = C_S² (2E₀ + 1)`, (3.10). -/
def P0 (u0 : ι → ℝ) : ℝ := P.CS ^ 2 * (2 * P.E0 u0 + 1)

/-- `U₀ = min{1/w_min, P₀/w_min^{1/3}, 2 √(E₀/(β w_min))}`, (3.10). -/
def U0 (u0 : ι → ℝ) : ℝ :=
  min (1 / P.wmin) (min (P.P0 u0 / P.wmin ^ ((1 : ℝ) / 3))
    (2 * Real.sqrt (P.E0 u0 / (P.β * P.wmin))))

/-- `B₀ = ‖V‖_∞ + β min{P₀^{3/2}, U₀}`, (3.11). -/
def B0 (u0 : ι → ℝ) : ℝ := P.Vinf + P.β * min ((P.P0 u0) ^ ((3 : ℝ) / 2)) (P.U0 u0)

/-- `D = E₀ + B₀`, (3.11). -/
def D (u0 : ι → ℝ) : ℝ := P.E0 u0 + P.B0 u0

/-- `B₁ = ‖V‖_∞ + β U₀`, (3.11). -/
def B1 (u0 : ι → ℝ) : ℝ := P.Vinf + P.β * P.U0 u0

/-- `C₀ = 3 β C_S P₀`, (3.12). -/
def C0 (u0 : ι → ℝ) : ℝ := 3 * P.β * P.CS * P.P0 u0

/-- `L₀ = ‖V‖_∞ + min{3 β U₀, C₀ + 2 max{C₀ - 1/4, 0}²}`, (3.12). -/
def L0 (u0 : ι → ℝ) : ℝ :=
  P.Vinf + min (3 * P.β * P.U0 u0) (P.C0 u0 + 2 * (max (P.C0 u0 - 1 / 4) 0) ^ 2)

/-- The step-size threshold
`γ_max = min{1, 1/(128 D), 1/(8 L₀), 2/(B₁ + √(B₁² + 12 D Λ_d))}`, (3.14). -/
def γmax (u0 : ι → ℝ) : ℝ :=
  min 1 (min (1 / (128 * P.D u0)) (min (1 / (8 * P.L0 u0))
    (2 / (P.B1 u0 + Real.sqrt ((P.B1 u0) ^ 2 + 12 * P.D u0 * P.Λd)))))

/-- The four step-size conditions (C1)–(C4) of Lemma 3.1, (3.15).
Positivity of `γ` is supplied separately in the theorems using these conditions. -/
def Conditions (u0 : ι → ℝ) (γ : ℝ) : Prop :=
  γ ≤ 1 ∧ γ * P.D u0 ≤ 1 / 128 ∧ γ * P.L0 u0 ≤ 1 / 8 ∧
    γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1

end Setting

end GPDYS

end
