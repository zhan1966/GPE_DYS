# Catalog of statements in the Lean formalization

Every explicitly named source definition, structure, and theorem, with its compiler docstring and elaborated type. These types include all actual implicit parameters and hypotheses introduced by `include`; `omit` is respected. Definition and structure bodies are also shown from source. Generated auxiliary declarations are not listed.

Regenerate with `python3 tools/catalog.py` after installing Graphviz. The dependency graph follows compiled constant references through helper declarations.


## `GPDYS/Basic.lean` — Sections 2, 3.1–3.3 (definitions and constants)


### `winner`  (def, line 36)

The weighted (discrete `L²`) inner product `⟪u, v⟫_h = ∑ᵢ wᵢ uᵢ vᵢ`.

```lean
def winner (w : ι → ℝ) (u v : ι → ℝ) : ℝ := ∑ i, w i * (u i * v i)
```

*Elaborated type:*
```lean
GPDYS.winner :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `wnorm2sq`  (def, line 39)

`‖v‖₂² = ∑ᵢ wᵢ vᵢ²`.

```lean
def wnorm2sq (w : ι → ℝ) (v : ι → ℝ) : ℝ := winner w v v
```

*Elaborated type:*
```lean
GPDYS.wnorm2sq :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `wnorm2`  (def, line 42)

`‖v‖₂ = (∑ᵢ wᵢ vᵢ²)^{1/2}`.

```lean
def wnorm2 (w : ι → ℝ) (v : ι → ℝ) : ℝ := Real.sqrt (wnorm2sq w v)
```

*Elaborated type:*
```lean
GPDYS.wnorm2 :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `wnorm3p3`  (def, line 45)

`‖v‖₃³ = ∑ᵢ wᵢ |vᵢ|³`.

```lean
def wnorm3p3 (w : ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, w i * |v i| ^ 3
```

*Elaborated type:*
```lean
GPDYS.wnorm3p3 :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `wnorm4p4`  (def, line 48)

`‖v‖₄⁴ = ∑ᵢ wᵢ vᵢ⁴`.

```lean
def wnorm4p4 (w : ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, w i * v i ^ 4
```

*Elaborated type:*
```lean
GPDYS.wnorm4p4 :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `wnorm6p6`  (def, line 51)

`‖v‖₆⁶ = ∑ᵢ wᵢ vᵢ⁶`.

```lean
def wnorm6p6 (w : ι → ℝ) (v : ι → ℝ) : ℝ := ∑ i, w i * v i ^ 6
```

*Elaborated type:*
```lean
GPDYS.wnorm6p6 :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `wnorm3`  (def, line 54)

`‖v‖₃ = (∑ᵢ wᵢ |vᵢ|³)^{1/3}`.

```lean
def wnorm3 (w : ι → ℝ) (v : ι → ℝ) : ℝ := (wnorm3p3 w v) ^ ((1 : ℝ) / 3)
```

*Elaborated type:*
```lean
GPDYS.wnorm3 :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `wnorm6`  (def, line 57)

`‖v‖₆ = (∑ᵢ wᵢ vᵢ⁶)^{1/6}`.

```lean
def wnorm6 (w : ι → ℝ) (v : ι → ℝ) : ℝ := (wnorm6p6 w v) ^ ((1 : ℝ) / 6)
```

*Elaborated type:*
```lean
GPDYS.wnorm6 :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `Setting`  (structure, line 72)

The data of the discrete ground state problem under Assumption 2.1, recorded through the
fixed-mesh properties of Lemma 2.2. The structure assumes these properties; it does not
construct a finite element mesh or express uniformity of `CS` across a family of meshes:

* `w` are the quadrature weights (the lumped mass matrix is `M = diag w`), all positive;
* `S` is the stiffness matrix: symmetric, positive semidefinite, with nonpositive off-diagonal
  entries, and such that `(M + γ S)⁻¹` has strictly positive entries for every `γ > 0`
  (Lemma 2.2 (ii), a consequence of `M + γ S` being an irreducible Stieltjes matrix);
* `V ≥ 0` is the potential at the nodes and `β > 0` the coupling constant;
* `CS` is the constant of the discrete Sobolev inequality `‖v‖₆ ≤ C_S ‖v‖_{1,h}`
  (Lemma 2.2 (iii)), where `‖v‖²_{1,h} = ⟪v, -Δ_h v⟫_h + ‖v‖₂² = vᵀ S v + ‖v‖₂²`.

```lean
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
```

*Elaborated type:*
```lean
GPDYS.Setting :
(ι : Type u_2) → [Fintype ι] → [DecidableEq ι] → Type u_2
```


### `M`  (def, line 100)

The lumped mass matrix `M = diag(w)`.

```lean
def M : Matrix ι ι ℝ := Matrix.diagonal P.w
```

*Elaborated type:*
```lean
GPDYS.Setting.M :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → Matrix ι ι ℝ
```


### `inner`  (def, line 103)

The discrete inner product `⟪u, v⟫_h = uᵀ M v`.

```lean
def inner (u v : ι → ℝ) : ℝ := winner P.w u v
```

*Elaborated type:*
```lean
GPDYS.Setting.inner :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `nrm2sq`  (def, line 106)

`‖v‖₂²`.

```lean
def nrm2sq (v : ι → ℝ) : ℝ := wnorm2sq P.w v
```

*Elaborated type:*
```lean
GPDYS.Setting.nrm2sq :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `nrm2`  (def, line 109)

`‖v‖₂`.

```lean
def nrm2 (v : ι → ℝ) : ℝ := wnorm2 P.w v
```

*Elaborated type:*
```lean
GPDYS.Setting.nrm2 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `negLap`  (def, line 112)

The negative discrete Laplacian `-Δ_h = M⁻¹ S`.

```lean
def negLap (v : ι → ℝ) : ι → ℝ := fun i => (P.S *ᵥ v) i / P.w i
```

*Elaborated type:*
```lean
GPDYS.Setting.negLap :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ι → ℝ
```


### `kin`  (def, line 115)

The kinetic quadratic form `⟪v, -Δ_h v⟫_h = vᵀ S v`.

```lean
def kin (v : ι → ℝ) : ℝ := v ⬝ᵥ (P.S *ᵥ v)
```

*Elaborated type:*
```lean
GPDYS.Setting.kin :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `pot`  (def, line 118)

The potential quadratic form `⟪V v, v⟫_h`.

```lean
def pot (v : ι → ℝ) : ℝ := ∑ i, P.w i * (P.V i * v i ^ 2)
```

*Elaborated type:*
```lean
GPDYS.Setting.pot :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `H`  (def, line 121)

The explicit part `H(v) = ½ ⟪V v, v⟫_h + (β/4) ‖v‖₄⁴` of the energy.

```lean
def H (v : ι → ℝ) : ℝ := (1 / 2) * P.pot v + P.β / 4 * wnorm4p4 P.w v
```

*Elaborated type:*
```lean
GPDYS.Setting.H :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `energy`  (def, line 124)

The discrete energy `E_h(v) = ½ ⟪v, -Δ_h v⟫_h + ½ ⟪V v, v⟫_h + (β/4) ‖v‖₄⁴`.

```lean
def energy (v : ι → ℝ) : ℝ := (1 / 2) * P.kin v + P.H v
```

*Elaborated type:*
```lean
GPDYS.Setting.energy :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `nonlin`  (def, line 127)

The explicit part `n(v) = V v + β v³` of the gradient.

```lean
def nonlin (v : ι → ℝ) : ι → ℝ := fun i => P.V i * v i + P.β * v i ^ 3
```

*Elaborated type:*
```lean
GPDYS.Setting.nonlin :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ι → ℝ
```


### `gradE`  (def, line 130)

The gradient `∇E_h(v) = -Δ_h v + n(v)` with respect to `⟪·,·⟫_h`.

```lean
def gradE (v : ι → ℝ) : ι → ℝ := P.negLap v + P.nonlin v
```

*Elaborated type:*
```lean
GPDYS.Setting.gradE :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ι → ℝ
```


### `lam`  (def, line 133)

The eigenvalue functional `λ(v) = ⟪∇E_h(v), v⟫_h`.

```lean
def lam (v : ι → ℝ) : ℝ := P.inner (P.gradE v) v
```

*Elaborated type:*
```lean
GPDYS.Setting.lam :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `g`  (def, line 136)

The projected gradient `g(v) = ∇E_h(v) - λ(v) v`.

```lean
def g (v : ι → ℝ) : ι → ℝ := P.gradE v - P.lam v • v
```

*Elaborated type:*
```lean
GPDYS.Setting.g :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ι → ℝ
```


### `nonlin'`  (def, line 139)

The Jacobian of `n`: `n'(v) = V + 3 β diag(v²)`, applied to a vector.

```lean
def nonlin' (v d : ι → ℝ) : ι → ℝ := fun i => (P.V i + 3 * P.β * v i ^ 2) * d i
```

*Elaborated type:*
```lean
GPDYS.Setting.nonlin' :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → (ι → ℝ) → ι → ℝ
```


### `GX`  (def, line 144)

The metric matrix `G_X = I - γ Δ_h`, applied to a vector.

```lean
def GX (γ : ℝ) (v : ι → ℝ) : ι → ℝ := v + γ • P.negLap v
```

*Elaborated type:*
```lean
GPDYS.Setting.GX :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ι → ℝ
```


### `resolvent`  (def, line 147)

The resolvent `G_X⁻¹ = (M + γ S)⁻¹ M`, applied to a vector.

```lean
def resolvent (γ : ℝ) (v : ι → ℝ) : ι → ℝ := (P.M + γ • P.S)⁻¹ *ᵥ (P.M *ᵥ v)
```

*Elaborated type:*
```lean
GPDYS.Setting.resolvent :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ι → ℝ
```


### `innerX`  (def, line 150)

The `X`-inner product `⟪v, w⟫_X = ⟪v, G_X⁻¹ w⟫_h`.

```lean
def innerX (γ : ℝ) (v w : ι → ℝ) : ℝ := P.inner v (P.resolvent γ w)
```

*Elaborated type:*
```lean
GPDYS.Setting.innerX :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `nrmXsq`  (def, line 153)

`‖v‖_X²`.

```lean
def nrmXsq (γ : ℝ) (v : ι → ℝ) : ℝ := P.innerX γ v v
```

*Elaborated type:*
```lean
GPDYS.Setting.nrmXsq :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ℝ
```


### `nrmGsq`  (def, line 156)

`‖v‖_𝒢² = ⟪v, G_X v⟫_h = ‖v‖₂² + γ ⟪v, -Δ_h v⟫_h`.

```lean
def nrmGsq (γ : ℝ) (v : ι → ℝ) : ℝ := P.nrm2sq v + γ * P.kin v
```

*Elaborated type:*
```lean
GPDYS.Setting.nrmGsq :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ℝ
```


### `normalize`  (def, line 161)

The normalized vector `u = z / ‖z‖₂` for `z ≠ 0`; at zero this total function is zero.

```lean
def normalize (z : ι → ℝ) : ι → ℝ := (P.nrm2 z)⁻¹ • z
```

*Elaborated type:*
```lean
GPDYS.Setting.normalize :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ι → ℝ
```


### `xi`  (def, line 164)

The intermediate vector `𝐱 = G_X⁻¹ (2u - z - γ n(u))` of (DYS I).

```lean
def xi (γ : ℝ) (z : ι → ℝ) : ι → ℝ :=
  P.resolvent γ ((2 : ℝ) • P.normalize z - z - γ • P.nonlin (P.normalize z))
```

*Elaborated type:*
```lean
GPDYS.Setting.xi :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ι → ℝ
```


### `step`  (def, line 168)

One step `z ↦ z⁺ = z + 𝐱 - u` of the scheme (DYS I), (1.6) in the paper.

```lean
def step (γ : ℝ) (z : ι → ℝ) : ι → ℝ := z + P.xi γ z - P.normalize z
```

*Elaborated type:*
```lean
GPDYS.Setting.step :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ι → ℝ
```


### `R`  (def, line 171)

The radial residual `R(z) = ‖z‖₂ - 1 + γ λ(u)`.

```lean
def R (γ : ℝ) (z : ι → ℝ) : ℝ := P.nrm2 z - 1 + γ * P.lam (P.normalize z)
```

*Elaborated type:*
```lean
GPDYS.Setting.R :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ℝ
```


### `lyap`  (def, line 174)

The Lyapunov function `𝓛(z) = E_h(u) + R(z)² / γ`.

```lean
def lyap (γ : ℝ) (z : ι → ℝ) : ℝ := P.energy (P.normalize z) + (P.R γ z) ^ 2 / γ
```

*Elaborated type:*
```lean
GPDYS.Setting.lyap :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ℝ
```


### `iter`  (def, line 177)

The iteration `z^k`, started from `z⁰ = u⁰`.

```lean
def iter (γ : ℝ) (u0 : ι → ℝ) (k : ℕ) : ι → ℝ := (P.step γ)^[k] u0
```

*Elaborated type:*
```lean
GPDYS.Setting.iter :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ℕ → ι → ℝ
```


### `uiter`  (def, line 180)

The normalized iterates `u^k = z^k / ‖z^k‖₂`.

```lean
def uiter (γ : ℝ) (u0 : ι → ℝ) (k : ℕ) : ι → ℝ := P.normalize (P.iter γ u0 k)
```

*Elaborated type:*
```lean
GPDYS.Setting.uiter :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ℕ → ι → ℝ
```


### `wmin`  (def, line 185)

`w_min = minᵢ wᵢ` when `ι` is nonempty; the empty-index value is zero.

```lean
def wmin : ℝ := ⨅ i, P.w i
```

*Elaborated type:*
```lean
GPDYS.Setting.wmin :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ
```


### `Vinf`  (def, line 188)

`‖V‖_∞ = maxᵢ Vᵢ` on a nonempty mesh (recall `V ≥ 0`); zero for empty `ι`.

```lean
def Vinf : ℝ := ⨆ i, P.V i
```

*Elaborated type:*
```lean
GPDYS.Setting.Vinf :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ
```


### `Λd`  (def, line 191)

The stiffness-to-mass ratio `Λ_d = maxᵢ Sᵢᵢ / wᵢ` on a nonempty mesh; zero for empty `ι`.

```lean
def Λd : ℝ := ⨆ i, P.S i i / P.w i
```

*Elaborated type:*
```lean
GPDYS.Setting.Λd :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ
```


### `E0`  (def, line 194)

The energy level `E₀ = E_h(u⁰) + λ(u⁰)² / max{1, 128 E_h(u⁰)}`, (3.9).

```lean
def E0 (u0 : ι → ℝ) : ℝ := P.energy u0 + (P.lam u0) ^ 2 / max 1 (128 * P.energy u0)
```

*Elaborated type:*
```lean
GPDYS.Setting.E0 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `P0`  (def, line 197)

`P₀ = C_S² (2E₀ + 1)`, (3.10).

```lean
def P0 (u0 : ι → ℝ) : ℝ := P.CS ^ 2 * (2 * P.E0 u0 + 1)
```

*Elaborated type:*
```lean
GPDYS.Setting.P0 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `U0`  (def, line 200)

`U₀ = min{1/w_min, P₀/w_min^{1/3}, 2 √(E₀/(β w_min))}`, (3.10).

```lean
def U0 (u0 : ι → ℝ) : ℝ :=
  min (1 / P.wmin) (min (P.P0 u0 / P.wmin ^ ((1 : ℝ) / 3))
    (2 * Real.sqrt (P.E0 u0 / (P.β * P.wmin))))
```

*Elaborated type:*
```lean
GPDYS.Setting.U0 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `B0`  (def, line 205)

`B₀ = ‖V‖_∞ + β min{P₀^{3/2}, U₀}`, (3.11).

```lean
def B0 (u0 : ι → ℝ) : ℝ := P.Vinf + P.β * min ((P.P0 u0) ^ ((3 : ℝ) / 2)) (P.U0 u0)
```

*Elaborated type:*
```lean
GPDYS.Setting.B0 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `D`  (def, line 208)

`D = E₀ + B₀`, (3.11).

```lean
def D (u0 : ι → ℝ) : ℝ := P.E0 u0 + P.B0 u0
```

*Elaborated type:*
```lean
GPDYS.Setting.D :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `B1`  (def, line 211)

`B₁ = ‖V‖_∞ + β U₀`, (3.11).

```lean
def B1 (u0 : ι → ℝ) : ℝ := P.Vinf + P.β * P.U0 u0
```

*Elaborated type:*
```lean
GPDYS.Setting.B1 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `C0`  (def, line 214)

`C₀ = 3 β C_S P₀`, (3.12).

```lean
def C0 (u0 : ι → ℝ) : ℝ := 3 * P.β * P.CS * P.P0 u0
```

*Elaborated type:*
```lean
GPDYS.Setting.C0 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `L0`  (def, line 217)

`L₀ = ‖V‖_∞ + min{3 β U₀, C₀ + 2 max{C₀ - 1/4, 0}²}`, (3.12).

```lean
def L0 (u0 : ι → ℝ) : ℝ :=
  P.Vinf + min (3 * P.β * P.U0 u0) (P.C0 u0 + 2 * (max (P.C0 u0 - 1 / 4) 0) ^ 2)
```

*Elaborated type:*
```lean
GPDYS.Setting.L0 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `γmax`  (def, line 222)

The step-size threshold
`γ_max = min{1, 1/(128 D), 1/(8 L₀), 2/(B₁ + √(B₁² + 12 D Λ_d))}`, (3.14).

```lean
def γmax (u0 : ι → ℝ) : ℝ :=
  min 1 (min (1 / (128 * P.D u0)) (min (1 / (8 * P.L0 u0))
    (2 / (P.B1 u0 + Real.sqrt ((P.B1 u0) ^ 2 + 12 * P.D u0 * P.Λd)))))
```

*Elaborated type:*
```lean
GPDYS.Setting.γmax :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `Conditions`  (def, line 228)

The four step-size conditions (C1)–(C4) of Lemma 3.1, (3.15).
Positivity of `γ` is supplied separately in the theorems using these conditions.

```lean
def Conditions (u0 : ι → ℝ) (γ : ℝ) : Prop :=
  γ ≤ 1 ∧ γ * P.D u0 ≤ 1 / 128 ∧ γ * P.L0 u0 ≤ 1 / 8 ∧
    γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1
```

*Elaborated type:*
```lean
GPDYS.Setting.Conditions :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ → Prop
```


## `GPDYS/Lemmas.lean` — Section 3.1 (basic identities)


### `sq_le_of_psd`  (theorem, line 21)

Cauchy–Schwarz for a symmetric positive semidefinite bilinear form on a real vector space.

```lean
GPDYS.sq_le_of_psd :
∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _root_.Module ℝ E] (B : E → E → ℝ),
  (∀ (u v w : E), B (u + v) w = B u w + B v w) →
    (∀ (c : ℝ) (u v : E), B (c • u) v = c * B u v) →
      (∀ (u v : E), B u v = B v u) → (∀ (v : E), 0 ≤ B v v) → ∀ (u v : E), B u v ^ 2 ≤ B u u * B v v
```


### `ne_zero_of_pos`  (theorem, line 68)

A componentwise positive vector on a nonempty index type is nonzero.

```lean
GPDYS.ne_zero_of_pos :
∀ {ι : Type u_1} [Nonempty ι] {z : ι → ℝ}, (∀ (i : ι), 0 < z i) → z ≠ 0
```


### `inner_def`  (theorem, line 81)

```lean
GPDYS.Setting.inner_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner u v = ∑ i, P.w i * (u i * v i)
```


### `inner_comm`  (theorem, line 83)

```lean
GPDYS.Setting.inner_comm :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner u v = P.inner v u
```


### `inner_add_left`  (theorem, line 86)

```lean
GPDYS.Setting.inner_add_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v x : ι → ℝ),
  P.inner (u + v) x = P.inner u x + P.inner v x
```


### `inner_add_right`  (theorem, line 90)

```lean
GPDYS.Setting.inner_add_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v x : ι → ℝ),
  P.inner x (u + v) = P.inner x u + P.inner x v
```


### `inner_smul_left`  (theorem, line 93)

```lean
GPDYS.Setting.inner_smul_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (c : ℝ) (u v : ι → ℝ),
  P.inner (c • u) v = c * P.inner u v
```


### `inner_smul_right`  (theorem, line 97)

```lean
GPDYS.Setting.inner_smul_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (c : ℝ) (u v : ι → ℝ),
  P.inner u (c • v) = c * P.inner u v
```


### `inner_neg_left`  (theorem, line 100)

```lean
GPDYS.Setting.inner_neg_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner (-u) v = -P.inner u v
```


### `inner_neg_right`  (theorem, line 103)

```lean
GPDYS.Setting.inner_neg_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner u (-v) = -P.inner u v
```


### `inner_sub_left`  (theorem, line 106)

```lean
GPDYS.Setting.inner_sub_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v x : ι → ℝ),
  P.inner (u - v) x = P.inner u x - P.inner v x
```


### `inner_sub_right`  (theorem, line 109)

```lean
GPDYS.Setting.inner_sub_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v x : ι → ℝ),
  P.inner x (u - v) = P.inner x u - P.inner x v
```


### `inner_zero_left`  (theorem, line 112)

```lean
GPDYS.Setting.inner_zero_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.inner 0 v = 0
```


### `inner_zero_right`  (theorem, line 115)

```lean
GPDYS.Setting.inner_zero_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.inner v 0 = 0
```


### `inner_sum_left`  (theorem, line 118)

```lean
GPDYS.Setting.inner_sum_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {κ : Type u_2} (s : Finset κ)
  (f : κ → ι → ℝ) (v : ι → ℝ), P.inner (∑ k ∈ s, f k) v = ∑ k ∈ s, P.inner (f k) v
```


### `nrm2sq_def`  (theorem, line 127)

```lean
GPDYS.Setting.nrm2sq_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.nrm2sq v = P.inner v v
```


### `nrm2sq_eq_sum`  (theorem, line 129)

```lean
GPDYS.Setting.nrm2sq_eq_sum :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.nrm2sq v = ∑ i, P.w i * v i ^ 2
```


### `nrm2sq_nonneg`  (theorem, line 132)

```lean
GPDYS.Setting.nrm2sq_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ P.nrm2sq v
```


### `w_mul_sq_le_nrm2sq`  (theorem, line 136)

```lean
GPDYS.Setting.w_mul_sq_le_nrm2sq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ) (i : ι),
  P.w i * v i ^ 2 ≤ P.nrm2sq v
```


### `nrm2sq_eq_zero_iff`  (theorem, line 141)

```lean
GPDYS.Setting.nrm2sq_eq_zero_iff :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.nrm2sq v = 0 ↔ v = 0
```


### `nrm2sq_pos_of_ne_zero`  (theorem, line 154)

```lean
GPDYS.Setting.nrm2sq_pos_of_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ}, v ≠ 0 → 0 < P.nrm2sq v
```


### `nrm2_def`  (theorem, line 157)

```lean
GPDYS.Setting.nrm2_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.nrm2 v = √(P.nrm2sq v)
```


### `nrm2_nonneg`  (theorem, line 159)

```lean
GPDYS.Setting.nrm2_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ P.nrm2 v
```


### `nrm2_sq`  (theorem, line 161)

```lean
GPDYS.Setting.nrm2_sq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.nrm2 v ^ 2 = P.nrm2sq v
```


### `nrm2_mul_self`  (theorem, line 164)

```lean
GPDYS.Setting.nrm2_mul_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.nrm2 v * P.nrm2 v = P.nrm2sq v
```


### `nrm2_pos_of_ne_zero`  (theorem, line 167)

```lean
GPDYS.Setting.nrm2_pos_of_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ}, v ≠ 0 → 0 < P.nrm2 v
```


### `nrm2_eq_zero_iff`  (theorem, line 170)

```lean
GPDYS.Setting.nrm2_eq_zero_iff :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.nrm2 v = 0 ↔ v = 0
```


### `nrm2sq_eq_one_of_nrm2`  (theorem, line 173)

```lean
GPDYS.Setting.nrm2sq_eq_one_of_nrm2 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ},
  P.nrm2 v = 1 → P.nrm2sq v = 1
```


### `nrm2_eq_one_of_nrm2sq`  (theorem, line 176)

```lean
GPDYS.Setting.nrm2_eq_one_of_nrm2sq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ},
  P.nrm2sq v = 1 → P.nrm2 v = 1
```


### `nrm2_eq_one_iff`  (theorem, line 179)

```lean
GPDYS.Setting.nrm2_eq_one_iff :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.nrm2 v = 1 ↔ P.nrm2sq v = 1
```


### `nrm2sq_smul`  (theorem, line 182)

```lean
GPDYS.Setting.nrm2sq_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (c : ℝ) (v : ι → ℝ),
  P.nrm2sq (c • v) = c ^ 2 * P.nrm2sq v
```


### `nrm2_smul`  (theorem, line 185)

```lean
GPDYS.Setting.nrm2_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (c : ℝ) (v : ι → ℝ),
  P.nrm2 (c • v) = |c| * P.nrm2 v
```


### `nrm2sq_add`  (theorem, line 188)

```lean
GPDYS.Setting.nrm2sq_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.nrm2sq (u + v) = P.nrm2sq u + 2 * P.inner u v + P.nrm2sq v
```


### `nrm2sq_sub`  (theorem, line 192)

```lean
GPDYS.Setting.nrm2sq_sub :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.nrm2sq (u - v) = P.nrm2sq u - 2 * P.inner u v + P.nrm2sq v
```


### `nrm2sq_neg`  (theorem, line 196)

```lean
GPDYS.Setting.nrm2sq_neg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.nrm2sq (-v) = P.nrm2sq v
```


### `inner_sq_le`  (theorem, line 200)

Cauchy–Schwarz: `⟪u, v⟫_h² ≤ ‖u‖₂² ‖v‖₂²`.

```lean
GPDYS.Setting.inner_sq_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner u v ^ 2 ≤ P.nrm2sq u * P.nrm2sq v
```


### `inner_le_nrm2_mul_nrm2`  (theorem, line 204)

Cauchy–Schwarz: `⟪u, v⟫_h ≤ ‖u‖₂ ‖v‖₂`.

```lean
GPDYS.Setting.inner_le_nrm2_mul_nrm2 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner u v ≤ P.nrm2 u * P.nrm2 v
```


### `abs_inner_le_nrm2_mul_nrm2`  (theorem, line 209)

```lean
GPDYS.Setting.abs_inner_le_nrm2_mul_nrm2 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  |P.inner u v| ≤ P.nrm2 u * P.nrm2 v
```


### `nrm2_add_le`  (theorem, line 215)

Triangle inequality for `‖·‖₂`.

```lean
GPDYS.Setting.nrm2_add_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.nrm2 (u + v) ≤ P.nrm2 u + P.nrm2 v
```


### `nrm2_neg`  (theorem, line 222)

```lean
GPDYS.Setting.nrm2_neg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.nrm2 (-v) = P.nrm2 v
```


### `nrm2_sub_le`  (theorem, line 225)

```lean
GPDYS.Setting.nrm2_sub_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.nrm2 (u - v) ≤ P.nrm2 u + P.nrm2 v
```


### `nrm2_le_of_nrm2sq_le`  (theorem, line 230)

```lean
GPDYS.Setting.nrm2_le_of_nrm2sq_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ} {c : ℝ},
  0 ≤ c → P.nrm2sq v ≤ c ^ 2 → P.nrm2 v ≤ c
```


### `nrm2_le_nrm2_iff`  (theorem, line 234)

```lean
GPDYS.Setting.nrm2_le_nrm2_iff :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.nrm2 u ≤ P.nrm2 v ↔ P.nrm2sq u ≤ P.nrm2sq v
```


### `nrm2sq_le_nrm2sq_of_le`  (theorem, line 239)

Monotonicity of `‖·‖₂` on nonnegative vectors.

```lean
GPDYS.Setting.nrm2sq_le_nrm2sq_of_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {x y : ι → ℝ},
  (∀ (i : ι), 0 ≤ x i) → (∀ (i : ι), x i ≤ y i) → P.nrm2sq x ≤ P.nrm2sq y
```


### `nrm2_le_nrm2_of_le`  (theorem, line 245)

```lean
GPDYS.Setting.nrm2_le_nrm2_of_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {x y : ι → ℝ},
  (∀ (i : ι), 0 ≤ x i) → (∀ (i : ι), x i ≤ y i) → P.nrm2 x ≤ P.nrm2 y
```


### `dotS_comm`  (theorem, line 251)

```lean
GPDYS.Setting.dotS_comm :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  u ⬝ᵥ P.S.mulVec v = v ⬝ᵥ P.S.mulVec u
```


### `dotS_add_left`  (theorem, line 254)

```lean
GPDYS.Setting.dotS_add_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v x : ι → ℝ),
  (u + v) ⬝ᵥ P.S.mulVec x = u ⬝ᵥ P.S.mulVec x + v ⬝ᵥ P.S.mulVec x
```


### `dotS_add_right`  (theorem, line 257)

```lean
GPDYS.Setting.dotS_add_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v x : ι → ℝ),
  x ⬝ᵥ P.S.mulVec (u + v) = x ⬝ᵥ P.S.mulVec u + x ⬝ᵥ P.S.mulVec v
```


### `dotS_smul_left`  (theorem, line 261)

```lean
GPDYS.Setting.dotS_smul_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (c : ℝ) (u x : ι → ℝ),
  c • u ⬝ᵥ P.S.mulVec x = c * u ⬝ᵥ P.S.mulVec x
```


### `dotS_smul_right`  (theorem, line 264)

```lean
GPDYS.Setting.dotS_smul_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (c : ℝ) (u x : ι → ℝ),
  x ⬝ᵥ P.S.mulVec (c • u) = c * x ⬝ᵥ P.S.mulVec u
```


### `dotS_sub_left`  (theorem, line 267)

```lean
GPDYS.Setting.dotS_sub_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v x : ι → ℝ),
  (u - v) ⬝ᵥ P.S.mulVec x = u ⬝ᵥ P.S.mulVec x - v ⬝ᵥ P.S.mulVec x
```


### `dotS_sub_right`  (theorem, line 270)

```lean
GPDYS.Setting.dotS_sub_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v x : ι → ℝ),
  x ⬝ᵥ P.S.mulVec (u - v) = x ⬝ᵥ P.S.mulVec u - x ⬝ᵥ P.S.mulVec v
```


### `dotS_neg_left`  (theorem, line 274)

```lean
GPDYS.Setting.dotS_neg_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u x : ι → ℝ),
  -u ⬝ᵥ P.S.mulVec x = -(u ⬝ᵥ P.S.mulVec x)
```


### `dotS_neg_right`  (theorem, line 277)

```lean
GPDYS.Setting.dotS_neg_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u x : ι → ℝ),
  x ⬝ᵥ P.S.mulVec (-u) = -(x ⬝ᵥ P.S.mulVec u)
```


### `dotS_zero_left`  (theorem, line 280)

```lean
GPDYS.Setting.dotS_zero_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (x : ι → ℝ), 0 ⬝ᵥ P.S.mulVec x = 0
```


### `dotS_zero_right`  (theorem, line 282)

```lean
GPDYS.Setting.dotS_zero_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (x : ι → ℝ), x ⬝ᵥ P.S.mulVec 0 = 0
```


### `kin_def`  (theorem, line 285)

```lean
GPDYS.Setting.kin_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.kin v = v ⬝ᵥ P.S.mulVec v
```


### `kin_nonneg`  (theorem, line 287)

```lean
GPDYS.Setting.kin_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ P.kin v
```


### `kin_smul`  (theorem, line 289)

```lean
GPDYS.Setting.kin_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (c : ℝ) (v : ι → ℝ),
  P.kin (c • v) = c ^ 2 * P.kin v
```


### `kin_add`  (theorem, line 292)

```lean
GPDYS.Setting.kin_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.kin (u + v) = P.kin u + 2 * u ⬝ᵥ P.S.mulVec v + P.kin v
```


### `kin_sub`  (theorem, line 296)

```lean
GPDYS.Setting.kin_sub :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.kin (u - v) = P.kin u - 2 * u ⬝ᵥ P.S.mulVec v + P.kin v
```


### `kin_neg`  (theorem, line 300)

```lean
GPDYS.Setting.kin_neg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.kin (-v) = P.kin v
```


### `dotS_sq_le`  (theorem, line 304)

Cauchy–Schwarz for the kinetic form: `(uᵀ S v)² ≤ (uᵀ S u)(vᵀ S v)`.

```lean
GPDYS.Setting.dotS_sq_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  (u ⬝ᵥ P.S.mulVec v) ^ 2 ≤ P.kin u * P.kin v
```


### `abs_dotS_le`  (theorem, line 308)

```lean
GPDYS.Setting.abs_dotS_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  |u ⬝ᵥ P.S.mulVec v| ≤ √(P.kin u) * √(P.kin v)
```


### `negLap_apply`  (theorem, line 316)

```lean
GPDYS.Setting.negLap_apply :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ) (i : ι),
  P.negLap v i = P.S.mulVec v i / P.w i
```


### `inner_negLap`  (theorem, line 318)

```lean
GPDYS.Setting.inner_negLap :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner u (P.negLap v) = u ⬝ᵥ P.S.mulVec v
```


### `inner_negLap_comm`  (theorem, line 324)

```lean
GPDYS.Setting.inner_negLap_comm :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner u (P.negLap v) = P.inner (P.negLap u) v
```


### `negLap_inner`  (theorem, line 328)

```lean
GPDYS.Setting.negLap_inner :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.inner (P.negLap u) v = u ⬝ᵥ P.S.mulVec v
```


### `kin_eq_inner`  (theorem, line 331)

```lean
GPDYS.Setting.kin_eq_inner :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.kin v = P.inner v (P.negLap v)
```


### `negLap_add`  (theorem, line 334)

```lean
GPDYS.Setting.negLap_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.negLap (u + v) = P.negLap u + P.negLap v
```


### `negLap_smul`  (theorem, line 337)

```lean
GPDYS.Setting.negLap_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (c : ℝ) (v : ι → ℝ),
  P.negLap (c • v) = c • P.negLap v
```


### `negLap_sub`  (theorem, line 340)

```lean
GPDYS.Setting.negLap_sub :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u v : ι → ℝ),
  P.negLap (u - v) = P.negLap u - P.negLap v
```


### `negLap_neg`  (theorem, line 343)

```lean
GPDYS.Setting.negLap_neg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.negLap (-v) = -P.negLap v
```


### `negLap_zero`  (theorem, line 346)

```lean
GPDYS.Setting.negLap_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι), P.negLap 0 = 0
```


### `M_mulVec`  (theorem, line 349)

```lean
GPDYS.Setting.M_mulVec :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.M.mulVec v = fun i => P.w i * v i
```


### `M_mulVec_negLap`  (theorem, line 352)

```lean
GPDYS.Setting.M_mulVec_negLap :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.M.mulVec (P.negLap v) = P.S.mulVec v
```


### `pot_nonneg`  (theorem, line 359)

```lean
GPDYS.Setting.pot_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ P.pot v
```


### `wnorm4p4_nonneg`  (theorem, line 362)

```lean
GPDYS.Setting.wnorm4p4_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ GPDYS.wnorm4p4 P.w v
```


### `wnorm6p6_nonneg`  (theorem, line 365)

```lean
GPDYS.Setting.wnorm6p6_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ GPDYS.wnorm6p6 P.w v
```


### `wnorm3p3_nonneg`  (theorem, line 368)

```lean
GPDYS.Setting.wnorm3p3_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ GPDYS.wnorm3p3 P.w v
```


### `H_nonneg`  (theorem, line 371)

```lean
GPDYS.Setting.H_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ P.H v
```


### `energy_def`  (theorem, line 376)

```lean
GPDYS.Setting.energy_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.energy v = 1 / 2 * P.kin v + P.H v
```


### `energy_eq`  (theorem, line 378)

```lean
GPDYS.Setting.energy_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.energy v = 1 / 2 * P.kin v + 1 / 2 * P.pot v + P.β / 4 * GPDYS.wnorm4p4 P.w v
```


### `energy_nonneg`  (theorem, line 382)

```lean
GPDYS.Setting.energy_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ P.energy v
```


### `kin_le_two_energy`  (theorem, line 385)

```lean
GPDYS.Setting.kin_le_two_energy :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.kin v ≤ 2 * P.energy v
```


### `quarter_wnorm4p4_le_energy`  (theorem, line 388)

```lean
GPDYS.Setting.quarter_wnorm4p4_le_energy :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.β / 4 * GPDYS.wnorm4p4 P.w v ≤ P.energy v
```


### `nonlin_apply`  (theorem, line 391)

```lean
GPDYS.Setting.nonlin_apply :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ) (i : ι),
  P.nonlin v i = P.V i * v i + P.β * v i ^ 3
```


### `inner_nonlin_self`  (theorem, line 393)

```lean
GPDYS.Setting.inner_nonlin_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.inner (P.nonlin v) v = P.pot v + P.β * GPDYS.wnorm4p4 P.w v
```


### `lam_eq`  (theorem, line 400)

```lean
GPDYS.Setting.lam_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.lam v = P.kin v + P.pot v + P.β * GPDYS.wnorm4p4 P.w v
```


### `lam_eq_energy`  (theorem, line 404)

```lean
GPDYS.Setting.lam_eq_energy :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.lam v = 2 * P.energy v + P.β / 2 * GPDYS.wnorm4p4 P.w v
```


### `lam_nonneg`  (theorem, line 407)

```lean
GPDYS.Setting.lam_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), 0 ≤ P.lam v
```


### `lam_le_four_energy`  (theorem, line 412)

```lean
GPDYS.Setting.lam_le_four_energy :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.lam v ≤ 4 * P.energy v
```


### `gradE_def`  (theorem, line 415)

```lean
GPDYS.Setting.gradE_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.gradE v = P.negLap v + P.nonlin v
```


### `gradE_eq_lam_smul_add_g`  (theorem, line 417)

```lean
GPDYS.Setting.gradE_eq_lam_smul_add_g :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.gradE v = P.lam v • v + P.g v
```


### `inner_gradE_self`  (theorem, line 420)

```lean
GPDYS.Setting.inner_gradE_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.inner (P.gradE v) v = P.lam v
```


### `inner_g_self`  (theorem, line 422)

```lean
GPDYS.Setting.inner_g_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ},
  P.nrm2sq v = 1 → P.inner (P.g v) v = 0
```


### `inner_self_g`  (theorem, line 426)

```lean
GPDYS.Setting.inner_self_g :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ},
  P.nrm2sq v = 1 → P.inner v (P.g v) = 0
```


### `inner_gradE_eq`  (theorem, line 429)

```lean
GPDYS.Setting.inner_gradE_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v d : ι → ℝ),
  P.inner (P.gradE v) d = P.lam v * P.inner v d + P.inner (P.g v) d
```


### `inner_nonlin`  (theorem, line 434)

`⟪n(u), d⟫_h` expanded.

```lean
GPDYS.Setting.inner_nonlin :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u d : ι → ℝ),
  P.inner (P.nonlin u) d = ∑ i, P.w i * ((P.V i * u i + P.β * u i ^ 3) * d i)
```


### `GX_def`  (theorem, line 439)

```lean
GPDYS.Setting.GX_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.GX γ v = v + γ • P.negLap v
```


### `inner_GX`  (theorem, line 441)

```lean
GPDYS.Setting.inner_GX :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v : ι → ℝ),
  P.inner u (P.GX γ v) = P.inner u v + γ * u ⬝ᵥ P.S.mulVec v
```


### `GX_inner`  (theorem, line 445)

```lean
GPDYS.Setting.GX_inner :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v : ι → ℝ),
  P.inner (P.GX γ u) v = P.inner u v + γ * u ⬝ᵥ P.S.mulVec v
```


### `inner_GX_self`  (theorem, line 449)

```lean
GPDYS.Setting.inner_GX_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.inner v (P.GX γ v) = P.nrmGsq γ v
```


### `GX_add`  (theorem, line 452)

```lean
GPDYS.Setting.GX_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v : ι → ℝ),
  P.GX γ (u + v) = P.GX γ u + P.GX γ v
```


### `GX_sub`  (theorem, line 455)

```lean
GPDYS.Setting.GX_sub :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v : ι → ℝ),
  P.GX γ (u - v) = P.GX γ u - P.GX γ v
```


### `GX_smul`  (theorem, line 458)

```lean
GPDYS.Setting.GX_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ c : ℝ) (v : ι → ℝ),
  P.GX γ (c • v) = c • P.GX γ v
```


### `GX_neg`  (theorem, line 461)

```lean
GPDYS.Setting.GX_neg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.GX γ (-v) = -P.GX γ v
```


### `GX_zero`  (theorem, line 464)

```lean
GPDYS.Setting.GX_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ), P.GX γ 0 = 0
```


### `nrmGsq_def`  (theorem, line 466)

```lean
GPDYS.Setting.nrmGsq_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.nrmGsq γ v = P.nrm2sq v + γ * P.kin v
```


### `nrmGsq_nonneg`  (theorem, line 468)

```lean
GPDYS.Setting.nrmGsq_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), 0 ≤ P.nrmGsq γ v
```


### `nrm2sq_le_nrmGsq`  (theorem, line 471)

```lean
GPDYS.Setting.nrm2sq_le_nrmGsq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.nrm2sq v ≤ P.nrmGsq γ v
```


### `mul_kin_le_nrmGsq`  (theorem, line 474)

```lean
GPDYS.Setting.mul_kin_le_nrmGsq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ} (v : ι → ℝ),
  γ * P.kin v ≤ P.nrmGsq γ v
```


### `nrmGsq_eq_zero_iff`  (theorem, line 477)

```lean
GPDYS.Setting.nrmGsq_eq_zero_iff :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.nrmGsq γ v = 0 ↔ v = 0
```


### `nrmGsq_smul`  (theorem, line 485)

```lean
GPDYS.Setting.nrmGsq_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ c : ℝ) (v : ι → ℝ),
  P.nrmGsq γ (c • v) = c ^ 2 * P.nrmGsq γ v
```


### `nrmGsq_add`  (theorem, line 488)

```lean
GPDYS.Setting.nrmGsq_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v : ι → ℝ),
  P.nrmGsq γ (u + v) = P.nrmGsq γ u + 2 * P.inner u (P.GX γ v) + P.nrmGsq γ v
```


### `inner_GX_sq_le`  (theorem, line 493)

Cauchy–Schwarz for the `𝒢`-inner product `⟪u, G_X v⟫_h`.

```lean
GPDYS.Setting.inner_GX_sq_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (u v : ι → ℝ), P.inner u (P.GX γ v) ^ 2 ≤ P.nrmGsq γ u * P.nrmGsq γ v
```


### `normalize_def`  (theorem, line 504)

```lean
GPDYS.Setting.normalize_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (z : ι → ℝ),
  P.normalize z = (P.nrm2 z)⁻¹ • z
```


### `nrm2_normalize`  (theorem, line 506)

```lean
GPDYS.Setting.nrm2_normalize :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 (P.normalize z) = 1
```


### `nrm2sq_normalize`  (theorem, line 510)

```lean
GPDYS.Setting.nrm2sq_normalize :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2sq (P.normalize z) = 1
```


### `nrm2_smul_normalize`  (theorem, line 513)

```lean
GPDYS.Setting.nrm2_smul_normalize :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z • P.normalize z = z
```


### `normalize_eq_self`  (theorem, line 516)

```lean
GPDYS.Setting.normalize_eq_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u : ι → ℝ},
  P.nrm2 u = 1 → P.normalize u = u
```


### `normalize_smul`  (theorem, line 519)

```lean
GPDYS.Setting.normalize_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (z : ι → ℝ) {c : ℝ},
  0 < c → P.normalize (c • z) = P.normalize z
```


### `normalize_pos`  (theorem, line 525)

```lean
GPDYS.Setting.normalize_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → (∀ (i : ι), 0 < z i) → ∀ (i : ι), 0 < P.normalize z i
```


### `normalize_nonneg`  (theorem, line 530)

```lean
GPDYS.Setting.normalize_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  (∀ (i : ι), 0 ≤ z i) → ∀ (i : ι), 0 ≤ P.normalize z i
```


### `iter_zero`  (theorem, line 536)

```lean
GPDYS.Setting.iter_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u0 : ι → ℝ),
  P.iter γ u0 0 = u0
```


### `iter_succ`  (theorem, line 538)

```lean
GPDYS.Setting.iter_succ :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u0 : ι → ℝ) (k : ℕ),
  P.iter γ u0 (k + 1) = P.step γ (P.iter γ u0 k)
```


### `uiter_def`  (theorem, line 542)

```lean
GPDYS.Setting.uiter_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u0 : ι → ℝ) (k : ℕ),
  P.uiter γ u0 k = P.normalize (P.iter γ u0 k)
```


### `R_def`  (theorem, line 545)

```lean
GPDYS.Setting.R_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (z : ι → ℝ),
  P.R γ z = P.nrm2 z - 1 + γ * P.lam (P.normalize z)
```


### `lyap_def`  (theorem, line 547)

```lean
GPDYS.Setting.lyap_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (z : ι → ℝ),
  P.lyap γ z = P.energy (P.normalize z) + P.R γ z ^ 2 / γ
```


### `energy_le_lyap`  (theorem, line 550)

```lean
GPDYS.Setting.energy_le_lyap :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 < γ → ∀ (z : ι → ℝ), P.energy (P.normalize z) ≤ P.lyap γ z
```


## `GPDYS/Resolvent.lean` — Section 3.2 (the resolvent and the X-norm)


### `dot_M_mulVec`  (theorem, line 34)

```lean
GPDYS.Setting.dot_M_mulVec :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (x y : ι → ℝ),
  x ⬝ᵥ P.M.mulVec y = P.inner x y
```


### `dot_MS_mulVec`  (theorem, line 38)

```lean
GPDYS.Setting.dot_MS_mulVec :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (x : ι → ℝ),
  x ⬝ᵥ (P.M + γ • P.S).mulVec x = P.nrm2sq x + γ * P.kin x
```


### `MS_mulVec_eq_zero`  (theorem, line 43)

```lean
GPDYS.Setting.MS_mulVec_eq_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ {x : ι → ℝ}, (P.M + γ • P.S).mulVec x = 0 → x = 0
```


### `MS_mulVec_injective`  (theorem, line 51)

```lean
GPDYS.Setting.MS_mulVec_injective :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → Function.Injective fun x => (P.M + γ • P.S).mulVec x
```


### `MS_det_ne_zero`  (theorem, line 58)

```lean
GPDYS.Setting.MS_det_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → (P.M + γ • P.S).det ≠ 0
```


### `MS_isUnit_det`  (theorem, line 63)

```lean
GPDYS.Setting.MS_isUnit_det :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → IsUnit (P.M + γ • P.S).det
```


### `M_mulVec_injective`  (theorem, line 66)

```lean
GPDYS.Setting.M_mulVec_injective :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι),
  Function.Injective fun x => P.M.mulVec x
```


### `resolvent_def`  (theorem, line 75)

```lean
GPDYS.Setting.resolvent_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.resolvent γ v = (P.M + γ • P.S)⁻¹.mulVec (P.M.mulVec v)
```


### `MS_mulVec_resolvent`  (theorem, line 78)

```lean
GPDYS.Setting.MS_mulVec_resolvent :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), (P.M + γ • P.S).mulVec (P.resolvent γ v) = P.M.mulVec v
```


### `M_mulVec_GX`  (theorem, line 82)

```lean
GPDYS.Setting.M_mulVec_GX :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.M.mulVec (P.GX γ v) = (P.M + γ • P.S).mulVec v
```


### `GX_resolvent`  (theorem, line 85)

```lean
GPDYS.Setting.GX_resolvent :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.GX γ (P.resolvent γ v) = v
```


### `resolvent_GX`  (theorem, line 90)

```lean
GPDYS.Setting.resolvent_GX :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.resolvent γ (P.GX γ v) = v
```


### `GX_injective`  (theorem, line 95)

```lean
GPDYS.Setting.GX_injective :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → Function.Injective (P.GX γ)
```


### `GX_eq_iff`  (theorem, line 100)

```lean
GPDYS.Setting.GX_eq_iff :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v x : ι → ℝ), P.GX γ x = v ↔ x = P.resolvent γ v
```


### `resolvent_zero_eq`  (theorem, line 105)

```lean
GPDYS.Setting.resolvent_zero_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ), P.resolvent 0 v = v
```


### `resolvent_add`  (theorem, line 110)

```lean
GPDYS.Setting.resolvent_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v : ι → ℝ),
  P.resolvent γ (u + v) = P.resolvent γ u + P.resolvent γ v
```


### `resolvent_sub`  (theorem, line 114)

```lean
GPDYS.Setting.resolvent_sub :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v : ι → ℝ),
  P.resolvent γ (u - v) = P.resolvent γ u - P.resolvent γ v
```


### `resolvent_smul`  (theorem, line 118)

```lean
GPDYS.Setting.resolvent_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ c : ℝ) (v : ι → ℝ),
  P.resolvent γ (c • v) = c • P.resolvent γ v
```


### `resolvent_neg`  (theorem, line 121)

```lean
GPDYS.Setting.resolvent_neg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.resolvent γ (-v) = -P.resolvent γ v
```


### `resolvent_zero`  (theorem, line 124)

```lean
GPDYS.Setting.resolvent_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ), P.resolvent γ 0 = 0
```


### `nrm2sq_GX`  (theorem, line 130)

`‖y + γ(-Δ_h y)‖₂² = ‖y‖₂² + 2γ ⟪y,-Δ_h y⟫_h + γ² ‖-Δ_h y‖₂²`.

```lean
GPDYS.Setting.nrm2sq_GX :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (y : ι → ℝ),
  P.nrm2sq (P.GX γ y) = P.nrm2sq y + 2 * γ * P.kin y + γ ^ 2 * P.nrm2sq (P.negLap y)
```


### `dotS_negLap_self`  (theorem, line 135)

`⟪y, -Δ_h(-Δ_h y)⟫_h = ‖-Δ_h y‖₂²`.

```lean
GPDYS.Setting.dotS_negLap_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (y : ι → ℝ),
  y ⬝ᵥ P.S.mulVec (P.negLap y) = P.nrm2sq (P.negLap y)
```


### `kin_GX`  (theorem, line 139)

`⟪G_X y, -Δ_h G_X y⟫_h = ⟪y,-Δ_h y⟫_h + 2γ‖-Δ_h y‖₂² + γ² ⟪-Δ_h y, -Δ_h(-Δ_h y)⟫_h`.

```lean
GPDYS.Setting.kin_GX :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (y : ι → ℝ),
  P.kin (P.GX γ y) = P.kin y + 2 * γ * P.nrm2sq (P.negLap y) + γ ^ 2 * P.kin (P.negLap y)
```


### `inner_GX_left_self`  (theorem, line 143)

```lean
GPDYS.Setting.inner_GX_left_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (y : ι → ℝ),
  P.inner (P.GX γ y) y = P.nrm2sq y + γ * P.kin y
```


### `innerX_def`  (theorem, line 149)

```lean
GPDYS.Setting.innerX_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v : ι → ℝ),
  P.innerX γ u v = P.inner u (P.resolvent γ v)
```


### `nrmXsq_def`  (theorem, line 151)

```lean
GPDYS.Setting.nrmXsq_def :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.nrmXsq γ v = P.inner v (P.resolvent γ v)
```


### `nrmXsq_eq`  (theorem, line 154)

`‖v‖_X² = ‖y‖₂² + γ ⟪y,-Δ_h y⟫_h` with `y = G_X⁻¹ v`.

```lean
GPDYS.Setting.nrmXsq_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.nrmXsq γ v = P.nrm2sq (P.resolvent γ v) + γ * P.kin (P.resolvent γ v)
```


### `exists_eq_GX`  (theorem, line 161)

Every vector is `G_X y` for `y = G_X⁻¹ v`.

```lean
GPDYS.Setting.exists_eq_GX :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), ∃ y, P.GX γ y = v
```


### `nrmXsq_GX`  (theorem, line 165)

`‖G_X v‖_X² = ‖v‖_𝒢²`, (3.7).

```lean
GPDYS.Setting.nrmXsq_GX :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.nrmXsq γ (P.GX γ v) = P.nrmGsq γ v
```


### `innerX_GX_right`  (theorem, line 169)

`⟪u, G_X v⟫_X = ⟪u, v⟫_h`.

```lean
GPDYS.Setting.innerX_GX_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (u v : ι → ℝ), P.innerX γ u (P.GX γ v) = P.inner u v
```


### `innerX_comm`  (theorem, line 175)

`h`-self-adjointness of the resolvent: `⟪u, G_X⁻¹ v⟫_h = ⟪G_X⁻¹ u, v⟫_h`.

```lean
GPDYS.Setting.innerX_comm :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (u v : ι → ℝ), P.innerX γ u v = P.innerX γ v u
```


### `innerX_add_left`  (theorem, line 181)

```lean
GPDYS.Setting.innerX_add_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v x : ι → ℝ),
  P.innerX γ (u + v) x = P.innerX γ u x + P.innerX γ v x
```


### `innerX_add_right`  (theorem, line 185)

```lean
GPDYS.Setting.innerX_add_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v x : ι → ℝ),
  P.innerX γ x (u + v) = P.innerX γ x u + P.innerX γ x v
```


### `innerX_smul_left`  (theorem, line 189)

```lean
GPDYS.Setting.innerX_smul_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ c : ℝ) (u x : ι → ℝ),
  P.innerX γ (c • u) x = c * P.innerX γ u x
```


### `innerX_smul_right`  (theorem, line 192)

```lean
GPDYS.Setting.innerX_smul_right :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ c : ℝ) (u x : ι → ℝ),
  P.innerX γ x (c • u) = c * P.innerX γ x u
```


### `innerX_sub_left`  (theorem, line 196)

```lean
GPDYS.Setting.innerX_sub_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u v x : ι → ℝ),
  P.innerX γ (u - v) x = P.innerX γ u x - P.innerX γ v x
```


### `innerX_neg_left`  (theorem, line 200)

```lean
GPDYS.Setting.innerX_neg_left :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (u x : ι → ℝ),
  P.innerX γ (-u) x = -P.innerX γ u x
```


### `nrmXsq_nonneg`  (theorem, line 203)

```lean
GPDYS.Setting.nrmXsq_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), 0 ≤ P.nrmXsq γ v
```


### `nrmXsq_smul`  (theorem, line 208)

```lean
GPDYS.Setting.nrmXsq_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ c : ℝ) (v : ι → ℝ),
  P.nrmXsq γ (c • v) = c ^ 2 * P.nrmXsq γ v
```


### `nrmXsq_neg`  (theorem, line 211)

```lean
GPDYS.Setting.nrmXsq_neg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (v : ι → ℝ),
  P.nrmXsq γ (-v) = P.nrmXsq γ v
```


### `innerX_sq_le`  (theorem, line 215)

Cauchy–Schwarz in `X`: `⟪u, v⟫_X² ≤ ‖u‖_X² ‖v‖_X²`.

```lean
GPDYS.Setting.innerX_sq_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (u v : ι → ℝ), P.innerX γ u v ^ 2 ≤ P.nrmXsq γ u * P.nrmXsq γ v
```


### `sqrt_nrmXsq_add_le`  (theorem, line 221)

Triangle inequality for `‖·‖_X`.

```lean
GPDYS.Setting.sqrt_nrmXsq_add_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (u v : ι → ℝ), √(P.nrmXsq γ (u + v)) ≤ √(P.nrmXsq γ u) + √(P.nrmXsq γ v)
```


### `nrmXsq_le_nrm2sq`  (theorem, line 241)

`‖v‖_X² ≤ ‖v‖₂²`, (3.5).

```lean
GPDYS.Setting.nrmXsq_le_nrm2sq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.nrmXsq γ v ≤ P.nrm2sq v
```


### `nrmXsq_pos`  (theorem, line 249)

`‖v‖_X > 0` for `v ≠ 0`, (3.5).

```lean
GPDYS.Setting.nrmXsq_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ {v : ι → ℝ}, v ≠ 0 → 0 < P.nrmXsq γ v
```


### `nrm2sq_resolvent_le_nrmXsq`  (theorem, line 258)

`‖G_X⁻¹ v‖₂² ≤ ‖v‖_X²`, (3.5).

```lean
GPDYS.Setting.nrm2sq_resolvent_le_nrmXsq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.nrm2sq (P.resolvent γ v) ≤ P.nrmXsq γ v
```


### `nrm2sq_sub_nrmXsq_le`  (theorem, line 265)

Upper bound in (3.6): `‖v‖₂² - ‖v‖_X² ≤ γ ⟪v, -Δ_h v⟫_h`.
The lower bound is `nrmXsq_le_nrm2sq`.

```lean
GPDYS.Setting.nrm2sq_sub_nrmXsq_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.nrm2sq v - P.nrmXsq γ v ≤ γ * P.kin v
```


### `nrmXsq_le_nrmGsq`  (theorem, line 276)

`‖v‖_X² ≤ ‖v‖_𝒢²`.

```lean
GPDYS.Setting.nrmXsq_le_nrmGsq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (v : ι → ℝ), P.nrmXsq γ v ≤ P.nrmGsq γ v
```


### `nrm2sq_contraction`  (theorem, line 282)

For `-1 ≤ a ≤ 0`, the operator `a I + (1 - a) G_X⁻¹` is a contraction in `‖·‖₂`.

```lean
GPDYS.Setting.nrm2sq_contraction :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ a : ℝ},
  0 ≤ γ → -1 ≤ a → a ≤ 0 → ∀ (u : ι → ℝ), P.nrm2sq (a • u + (1 - a) • P.resolvent γ u) ≤ P.nrm2sq u
```


### `nrm2sq_negLap_le`  (theorem, line 302)

`‖-Δ_h y‖₂² ≤ μ ⟪y,-Δ_h y⟫_h` if `⟪·,-Δ_h ·⟫_h ≤ μ ‖·‖₂²`.

```lean
GPDYS.Setting.nrm2sq_negLap_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {μ : ℝ},
  0 ≤ μ → (∀ (x : ι → ℝ), P.kin x ≤ μ * P.nrm2sq x) → ∀ (y : ι → ℝ), P.nrm2sq (P.negLap y) ≤ μ * P.kin y
```


### `nrm2sq_le_mul_nrmXsq`  (theorem, line 321)

`‖v‖₂² ≤ (1 + γ μ) ‖v‖_X²` if `⟪·,-Δ_h ·⟫_h ≤ μ ‖·‖₂²`, (5.3).

```lean
GPDYS.Setting.nrm2sq_le_mul_nrmXsq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ μ : ℝ},
  0 ≤ γ → 0 ≤ μ → (∀ (x : ι → ℝ), P.kin x ≤ μ * P.nrm2sq x) → ∀ (v : ι → ℝ), P.nrm2sq v ≤ (1 + γ * μ) * P.nrmXsq γ v
```


### `resolvent_apply`  (theorem, line 336)

```lean
GPDYS.Setting.resolvent_apply :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (b : ι → ℝ) (i : ι),
  P.resolvent γ b i = ∑ j, (P.M + γ • P.S)⁻¹ i j * (P.w j * b j)
```


### `resolvent_pos_of_nonneg`  (theorem, line 341)

A positive matrix maps a nonnegative nonzero vector to a positive vector.

```lean
GPDYS.Setting.resolvent_pos_of_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 < γ → ∀ {b : ι → ℝ}, (∀ (i : ι), 0 ≤ b i) → b ≠ 0 → ∀ (i : ι), 0 < P.resolvent γ b i
```


### `resolvent_nonneg_of_nonneg`  (theorem, line 354)

```lean
GPDYS.Setting.resolvent_nonneg_of_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ {b : ι → ℝ}, (∀ (i : ι), 0 ≤ b i) → ∀ (i : ι), 0 ≤ P.resolvent γ b i
```


## `GPDYS/Holder.lean` — Hölder inequalities used in Lemma 4.3


### `wnorm6p6_nonneg'`  (theorem, line 24)

`‖v‖₆⁶ ≥ 0` for nonnegative weights.

```lean
GPDYS.wnorm6p6_nonneg' :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ), (∀ (i : ι), 0 ≤ w i) → ∀ (v : ι → ℝ), 0 ≤ GPDYS.wnorm6p6 w v
```


### `wnorm3p3_nonneg'`  (theorem, line 28)

`‖v‖₃³ ≥ 0` for nonnegative weights.

```lean
GPDYS.wnorm3p3_nonneg' :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ), (∀ (i : ι), 0 ≤ w i) → ∀ (v : ι → ℝ), 0 ≤ GPDYS.wnorm3p3 w v
```


### `wnorm6_nonneg`  (theorem, line 32)

`‖v‖₆ ≥ 0` for nonnegative weights.

```lean
GPDYS.wnorm6_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ), (∀ (i : ι), 0 ≤ w i) → ∀ (v : ι → ℝ), 0 ≤ GPDYS.wnorm6 w v
```


### `wnorm3_nonneg`  (theorem, line 36)

`‖v‖₃ ≥ 0` for nonnegative weights.

```lean
GPDYS.wnorm3_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ), (∀ (i : ι), 0 ≤ w i) → ∀ (v : ι → ℝ), 0 ≤ GPDYS.wnorm3 w v
```


### `wnorm6_pow_six`  (theorem, line 40)

`‖v‖₆⁶ = ∑ᵢ wᵢ vᵢ⁶` for nonnegative weights.

```lean
GPDYS.wnorm6_pow_six :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) → ∀ (v : ι → ℝ), GPDYS.wnorm6 w v ^ 6 = GPDYS.wnorm6p6 w v
```


### `wnorm3_pow_three`  (theorem, line 47)

`‖v‖₃³ = ∑ᵢ wᵢ |vᵢ|³` for nonnegative weights.

```lean
GPDYS.wnorm3_pow_three :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) → ∀ (v : ι → ℝ), GPDYS.wnorm3 w v ^ 3 = GPDYS.wnorm3p3 w v
```


### `wnorm3_sq_eq`  (theorem, line 54)

`‖v²‖₃ = ‖v‖₆²` (componentwise square).

```lean
GPDYS.wnorm3_sq_eq :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) → ∀ (v : ι → ℝ), (GPDYS.wnorm3 w fun i => v i ^ 2) = GPDYS.wnorm6 w v ^ 2
```


### `holder_six_three`  (theorem, line 66)

Hölder with exponents `3` and `3/2`: `∑ᵢ wᵢ aᵢ² bᵢ² ≤ ‖a‖₆² ‖b‖₃²`.

```lean
GPDYS.holder_six_three :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) → ∀ (a b : ι → ℝ), ∑ i, w i * (a i ^ 2 * b i ^ 2) ≤ GPDYS.wnorm6 w a ^ 2 * GPDYS.wnorm3 w b ^ 2
```


### `wnorm3_sq_le`  (theorem, line 115)

Hölder with exponents `4/3` and `4`: `‖b‖₃² ≤ ‖b‖₂ ‖b‖₆`.

```lean
GPDYS.wnorm3_sq_le :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) → ∀ (b : ι → ℝ), GPDYS.wnorm3 w b ^ 2 ≤ GPDYS.wnorm2 w b * GPDYS.wnorm6 w b
```


### `holder_cubes`  (theorem, line 177)

Cauchy–Schwarz: `∑ᵢ wᵢ |uᵢ|³ |cᵢ|³ ≤ ‖u‖₆³ ‖c‖₆³`.

```lean
GPDYS.holder_cubes :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) →
    ∀ (u c : ι → ℝ), ∑ i, w i * (|u i| ^ 3 * |c i| ^ 3) ≤ GPDYS.wnorm6 w u ^ 3 * GPDYS.wnorm6 w c ^ 3
```


### `wnorm6_le_of_abs_le`  (theorem, line 202)

Monotonicity of `‖·‖₆` under a componentwise bound `|aᵢ| ≤ |bᵢ|`.

```lean
GPDYS.wnorm6_le_of_abs_le :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) → ∀ {a b : ι → ℝ}, (∀ (i : ι), |a i| ≤ |b i|) → GPDYS.wnorm6 w a ≤ GPDYS.wnorm6 w b
```


### `abs_rpow_sixth_mul_pow_six`  (theorem, line 214)

`|w^{1/6} x|⁶ = w x⁶` for `w ≥ 0` (the integrand of the Minkowski inequality).

```lean
GPDYS.abs_rpow_sixth_mul_pow_six :
∀ (w : ℝ), 0 ≤ w → ∀ (x : ℝ), |w ^ (1 / 6) * x| ^ 6 = w * x ^ 6
```


### `wnorm6_add_le`  (theorem, line 221)

The `‖·‖₆` triangle inequality (Minkowski), used for `‖u + σδ‖₆ ≤ (1-σ)‖u‖₆ + σ‖u⁺‖₆`.

```lean
GPDYS.wnorm6_add_le :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) → ∀ (a b : ι → ℝ), GPDYS.wnorm6 w (a + b) ≤ GPDYS.wnorm6 w a + GPDYS.wnorm6 w b
```


### `wnorm6_smul`  (theorem, line 244)

Homogeneity: `‖c • v‖₆ = |c| ‖v‖₆`.

```lean
GPDYS.wnorm6_smul :
∀ {ι : Type u_1} [inst : Fintype ι] (w : ι → ℝ),
  (∀ (i : ι), 0 ≤ w i) → ∀ (c : ℝ) (v : ι → ℝ), GPDYS.wnorm6 w (c • v) = |c| * GPDYS.wnorm6 w v
```


## `GPDYS/SobolevConst.lean` — a Sobolev constant exists on every fixed nonempty mesh


### `exists_sobolev_const`  (theorem, line 23)

On a fixed nonempty mesh a Sobolev constant exists for positive weights `w`
and positive semidefinite `S`. The proof chooses `(∑ᵢ wᵢ)^{1/6} / √(minᵢ wᵢ)`.

```lean
GPDYS.exists_sobolev_const :
∀ {ι : Type u_1} [inst : Fintype ι] [Nonempty ι] (w : ι → ℝ),
  (∀ (i : ι), 0 < w i) →
    ∀ (S : Matrix ι ι ℝ),
      (∀ (v : ι → ℝ), 0 ≤ v ⬝ᵥ S.mulVec v) →
        ∃ CS, 0 < CS ∧ ∀ (v : ι → ℝ), GPDYS.wnorm6 w v ≤ CS * √(v ⬝ᵥ S.mulVec v + GPDYS.wnorm2sq w v)
```


## `GPDYS/Constants.lean` — Section 3.3: Lemma 3.1 and Lemma 3.2


### `wmin_le`  (theorem, line 25)

```lean
GPDYS.Setting.wmin_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (i : ι), P.wmin ≤ P.w i
```


### `wmin_pos`  (theorem, line 27)

```lean
GPDYS.Setting.wmin_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι], 0 < P.wmin
```


### `le_Vinf`  (theorem, line 31)

```lean
GPDYS.Setting.le_Vinf :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (i : ι), P.V i ≤ P.Vinf
```


### `Vinf_nonneg`  (theorem, line 33)

```lean
GPDYS.Setting.Vinf_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι], 0 ≤ P.Vinf
```


### `S_diag_nonneg`  (theorem, line 38)

`Sᵢᵢ ≥ 0`, as the value of the quadratic form of `S` at the `i`th unit vector.

```lean
GPDYS.Setting.S_diag_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (i : ι), 0 ≤ P.S i i
```


### `le_Λd`  (theorem, line 43)

```lean
GPDYS.Setting.le_Λd :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (i : ι), P.S i i / P.w i ≤ P.Λd
```


### `Λd_nonneg`  (theorem, line 45)

```lean
GPDYS.Setting.Λd_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι], 0 ≤ P.Λd
```


### `pot_le`  (theorem, line 50)

`⟪V v, v⟫_h ≤ ‖V‖_∞ ‖v‖₂²`.

```lean
GPDYS.Setting.pot_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.pot v ≤ P.Vinf * P.nrm2sq v
```


### `nrm2_Vmul_le`  (theorem, line 59)

`‖V v‖₂ ≤ ‖V‖_∞ ‖v‖₂`.

```lean
GPDYS.Setting.nrm2_Vmul_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  (P.nrm2 fun i => P.V i * v i) ≤ P.Vinf * P.nrm2 v
```


### `energy_le_E0`  (theorem, line 75)

```lean
GPDYS.Setting.energy_le_E0 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ), P.energy u0 ≤ P.E0 u0
```


### `E0_le`  (theorem, line 81)

```lean
GPDYS.Setting.E0_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ),
  P.E0 u0 ≤ 9 / 8 * P.energy u0
```


### `energy_pos_of_ne_zero`  (theorem, line 97)

```lean
GPDYS.Setting.energy_pos_of_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ}, v ≠ 0 → 0 < P.energy v
```


### `E0_pos`  (theorem, line 109)

```lean
GPDYS.Setting.E0_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ), u0 ≠ 0 → 0 < P.E0 u0
```


### `E0_nonneg`  (theorem, line 112)

```lean
GPDYS.Setting.E0_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ), 0 ≤ P.E0 u0
```


### `P0_nonneg`  (theorem, line 114)

```lean
GPDYS.Setting.P0_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ), 0 ≤ P.P0 u0
```


### `CS_pos`  (theorem, line 118)

The Sobolev constant is positive (apply the Sobolev inequality to the constant vector `1`).

```lean
GPDYS.Setting.CS_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι], 0 < P.CS
```


### `P0_pos`  (theorem, line 133)

```lean
GPDYS.Setting.P0_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  0 < P.P0 u0
```


### `U0_nonneg`  (theorem, line 136)

```lean
GPDYS.Setting.U0_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  0 ≤ P.U0 u0
```


### `U0_pos`  (theorem, line 144)

```lean
GPDYS.Setting.U0_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  u0 ≠ 0 → 0 < P.U0 u0
```


### `U0_le_inv_wmin`  (theorem, line 154)

```lean
GPDYS.Setting.U0_le_inv_wmin :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ), P.U0 u0 ≤ 1 / P.wmin
```


### `B0_nonneg`  (theorem, line 156)

```lean
GPDYS.Setting.B0_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  0 ≤ P.B0 u0
```


### `E0_le_D`  (theorem, line 163)

```lean
GPDYS.Setting.E0_le_D :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  P.E0 u0 ≤ P.D u0
```


### `B0_le_D`  (theorem, line 166)

```lean
GPDYS.Setting.B0_le_D :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ), P.B0 u0 ≤ P.D u0
```


### `D_pos`  (theorem, line 169)

```lean
GPDYS.Setting.D_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  u0 ≠ 0 → 0 < P.D u0
```


### `B1_pos`  (theorem, line 172)

```lean
GPDYS.Setting.B1_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  u0 ≠ 0 → 0 < P.B1 u0
```


### `C0_pos`  (theorem, line 177)

```lean
GPDYS.Setting.C0_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  0 < P.C0 u0
```


### `L0_pos`  (theorem, line 180)

```lean
GPDYS.Setting.L0_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  u0 ≠ 0 → 0 < P.L0 u0
```


### `γmax_pos`  (theorem, line 192)

```lean
GPDYS.Setting.γmax_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  u0 ≠ 0 → 0 < P.γmax u0
```


### `C4_identity`  (theorem, line 204)

The key algebraic identity behind (C4): with `s = √(B₁² + 12 D Λ_d)`,
`4 (γ B₁ + 3 γ² D Λ_d - 1) = (γ (B₁ + s) - 2) (γ (s - B₁) + 2)`.

```lean
GPDYS.Setting.C4_identity :
∀ {B D Λ γ s : ℝ},
  s ^ 2 = B ^ 2 + 12 * D * Λ → 4 * (γ * B + 3 * γ ^ 2 * D * Λ - 1) = (γ * (B + s) - 2) * (γ * (s - B) + 2)
```


### `conditions_of_le_γmax`  (theorem, line 209)

Lemma 3.1 (⇒): `γ ≤ γ_max` implies (C1)–(C4).

```lean
GPDYS.Setting.conditions_of_le_γmax :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  u0 ≠ 0 → ∀ {γ : ℝ}, 0 < γ → γ ≤ P.γmax u0 → P.Conditions u0 γ
```


### `le_γmax_of_conditions`  (theorem, line 235)

Lemma 3.1 (⇐): (C1)–(C4) imply `γ ≤ γ_max`.

```lean
GPDYS.Setting.le_γmax_of_conditions :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  u0 ≠ 0 → ∀ {γ : ℝ}, 0 < γ → P.Conditions u0 γ → γ ≤ P.γmax u0
```


### `le_inv_max_of_conditions`  (theorem, line 262)

Under (C1), (C2): `γ ≤ 1 / max{1, 128 E_h(u⁰)}`.

```lean
GPDYS.Setting.le_inv_max_of_conditions :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι] {γ : ℝ},
  0 < γ → P.Conditions u0 γ → γ ≤ 1 / max 1 (128 * P.energy u0)
```


### `lyap_init_le_E0`  (theorem, line 275)

Lemma 3.1, last assertion: `𝓛(z⁰) ≤ E₀` for `z⁰ = u⁰ ∈ 𝓜`.
The proof uses `𝓛(z⁰) = E_h(u⁰) + γ λ(u⁰)²`.

```lean
GPDYS.Setting.lyap_init_le_E0 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u0 : ι → ℝ) [Nonempty ι],
  P.nrm2 u0 = 1 → ∀ {γ : ℝ}, 0 < γ → P.Conditions u0 γ → P.lyap γ u0 ≤ P.E0 u0
```


### `nonempty_of_nrm2sq_eq_one`  (theorem, line 295)

A vector of norm one forces the index type to be nonempty.

```lean
GPDYS.Setting.nonempty_of_nrm2sq_eq_one :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ},
  P.nrm2sq v = 1 → Nonempty ι
```


### `kin_le_two_E0`  (theorem, line 308)

Lemma 3.2 (i): `⟪v, -Δ_h v⟫_h ≤ 2E₀`.

```lean
GPDYS.Setting.kin_le_two_E0 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → P.kin v ≤ 2 * P.E0 u0
```


### `h1norm_le`  (theorem, line 312)

Lemma 3.2 (i): `‖v‖²_{1,h} ≤ 2E₀ + 1`.

```lean
GPDYS.Setting.h1norm_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → P.kin v + P.nrm2sq v ≤ 2 * P.E0 u0 + 1
```


### `wnorm6_sq_le_P0`  (theorem, line 316)

Lemma 3.2 (i): `‖v‖₆² ≤ P₀`.

```lean
GPDYS.Setting.wnorm6_sq_le_P0 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → GPDYS.wnorm6 P.w v ^ 2 ≤ P.P0 u0
```


### `wnorm6p6_le_P0_cube`  (theorem, line 328)

Lemma 3.2 (i): `‖v‖₆⁶ ≤ P₀³`.

```lean
GPDYS.Setting.wnorm6p6_le_P0_cube :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → GPDYS.wnorm6p6 P.w v ≤ P.P0 u0 ^ 3
```


### `sq_le_U0`  (theorem, line 335)

Lemma 3.2 (ii): `vᵢ² ≤ U₀` for every `i` (i.e. `‖v‖_∞² ≤ U₀`).

```lean
GPDYS.Setting.sq_le_U0 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → ∀ (i : ι), v i ^ 2 ≤ P.U0 u0
```


### `nrm2_cube_le`  (theorem, line 392)

Lemma 3.2 (iii): `‖v³‖₂ ≤ min{P₀^{3/2}, U₀}`.

```lean
GPDYS.Setting.nrm2_cube_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → (P.nrm2 fun i => v i ^ 3) ≤ min (P.P0 u0 ^ (3 / 2)) (P.U0 u0)
```


### `wnorm4p4_le_min`  (theorem, line 419)

Lemma 3.2 (iii): `‖v‖₄⁴ ≤ min{P₀^{3/2}, U₀}`.

```lean
GPDYS.Setting.wnorm4p4_le_min :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → GPDYS.wnorm4p4 P.w v ≤ min (P.P0 u0 ^ (3 / 2)) (P.U0 u0)
```


### `nrm2_nonlin_le`  (theorem, line 428)

Lemma 3.2 (iii): `‖n(v)‖₂ ≤ B₀`.

```lean
GPDYS.Setting.nrm2_nonlin_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → ∀ [Nonempty ι], P.nrm2 (P.nonlin v) ≤ P.B0 u0
```


### `inner_nonlin_self_le`  (theorem, line 446)

Lemma 3.2 (iii): `⟪n(v), v⟫_h ≤ B₀`.

```lean
GPDYS.Setting.inner_nonlin_self_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → ∀ [Nonempty ι], P.inner (P.nonlin v) v ≤ P.B0 u0
```


### `lam_le_two_D`  (theorem, line 455)

Upper bound in Lemma 3.2 (iv): `λ(v) ≤ 2D`; `lam_nonneg` gives the lower bound.

```lean
GPDYS.Setting.lam_le_two_D :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 v : ι → ℝ},
  P.nrm2sq v = 1 → P.energy v ≤ P.E0 u0 → ∀ [Nonempty ι], P.lam v ≤ 2 * P.D u0
```


## `GPDYS/Step.lean` — Section 4.1: Lemma 4.1 and Lemma 4.2


### `delta`  (def, line 27)

The change of direction `δ = u⁺ - u` of one step.

```lean
def delta (γ : ℝ) (z : ι → ℝ) : ι → ℝ := P.normalize (P.step γ z) - P.normalize z
```

*Elaborated type:*
```lean
GPDYS.Setting.delta :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ι → ℝ
```


### `taylorT`  (def, line 31)

The Taylor remainder `𝒯(u, d) = H(u + d) - H(u) - ⟪n(u), d⟫_h` of the explicit part of the
energy, (4.2).

```lean
def taylorT (u d : ι → ℝ) : ℝ := P.H (u + d) - P.H u - P.inner (P.nonlin u) d
```

*Elaborated type:*
```lean
GPDYS.Setting.taylorT :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `inner_sub_self_eq`  (theorem, line 36)

`⟪u, u⁺ - u⟫_h = -½ ‖u⁺ - u‖₂²` for unit vectors `u, u⁺`.

```lean
GPDYS.Setting.inner_sub_self_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u up : ι → ℝ},
  P.nrm2sq u = 1 → P.nrm2sq up = 1 → P.inner u (up - u) = -(1 / 2) * P.nrm2sq (up - u)
```


### `nrm2sq_sub_eq`  (theorem, line 41)

`‖u⁺ - u‖₂² = 2 (1 - ⟪u, u⁺⟫_h)` for unit vectors `u, u⁺`.

```lean
GPDYS.Setting.nrm2sq_sub_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u up : ι → ℝ},
  P.nrm2sq u = 1 → P.nrm2sq up = 1 → P.nrm2sq (up - u) = 2 * (1 - P.inner u up)
```


### `nrm2sq_delta_eq`  (theorem, line 46)

`‖δ‖₂² = 2 (1 - ⟪u, z⁺⟫_h / ‖z⁺‖₂)`, the second form in (4.1).

```lean
GPDYS.Setting.nrm2sq_delta_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ} {z : ι → ℝ},
  z ≠ 0 → P.step γ z ≠ 0 → P.nrm2sq (P.delta γ z) = 2 * (1 - P.inner (P.normalize z) (P.step γ z) / P.nrm2 (P.step γ z))
```


### `taylorT_eq`  (theorem, line 57)

The explicit polynomial form of the remainder:
`𝒯(u, d) = ½ ∑ᵢ wᵢ Vᵢ dᵢ² + (β/2) ∑ᵢ wᵢ dᵢ² (3uᵢ² + 2uᵢdᵢ + ½dᵢ²)`.

```lean
GPDYS.Setting.taylorT_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u d : ι → ℝ),
  P.taylorT u d =
    1 / 2 * ∑ i, P.w i * (P.V i * d i ^ 2) +
      P.β / 2 * ∑ i, P.w i * (d i ^ 2 * (3 * u i ^ 2 + 2 * u i * d i + d i ^ 2 / 2))
```


### `taylorE`  (theorem, line 67)

The Taylor expansion (4.3):
`E_h(u + d) - E_h(u) = ⟪∇E_h(u), d⟫_h + ½ ⟪d, -Δ_h d⟫_h + 𝒯(u, d)`.

```lean
GPDYS.Setting.taylorE :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (u d : ι → ℝ),
  P.energy (u + d) - P.energy u = P.inner (P.gradE u) d + 1 / 2 * P.kin d + P.taylorT u d
```


### `GX_eq_nrm2_smul`  (theorem, line 77)

`G_X z = ‖z‖₂ u + ‖z‖₂ γ (-Δ_h u)` for `z ≠ 0` and `u = z/‖z‖₂`.

```lean
GPDYS.Setting.GX_eq_nrm2_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) {z : ι → ℝ},
  z ≠ 0 → P.GX γ z = P.nrm2 z • P.normalize z + (P.nrm2 z * γ) • P.negLap (P.normalize z)
```


### `GX_step_aux`  (theorem, line 84)

The first identity of (4.4) with `z = c • u` substituted: for any scalar `c` and vector `u`,
`G_X (c u + G_X⁻¹(2u - c u - γ n(u)) - u) = u - γ n(u) - γ (1 - c) (-Δ_h u)`.

```lean
GPDYS.Setting.GX_step_aux :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ →
    ∀ (c : ℝ) (u : ι → ℝ),
      P.GX γ (c • u + P.resolvent γ (2 • u - c • u - γ • P.nonlin u) - u) =
        u - γ • P.nonlin u - (γ * (1 - c)) • P.negLap u
```


### `GX_step`  (theorem, line 98)

Lemma 4.1, (4.4) first identity: `G_X z⁺ = u - γ n(u) - γ(1 - ‖z‖₂)(-Δ_h u)`.

```lean
GPDYS.Setting.GX_step :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ →
    ∀ {z : ι → ℝ},
      z ≠ 0 →
        P.GX γ (P.step γ z) =
          P.normalize z - γ • P.nonlin (P.normalize z) - (γ * (1 - P.nrm2 z)) • P.negLap (P.normalize z)
```


### `GX_step_sub_eq`  (theorem, line 105)

(4.7): `G_X (z⁺ - z) = (1 - ‖z‖₂) u - γ ∇E_h(u)`.

```lean
GPDYS.Setting.GX_step_sub_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ {z : ι → ℝ}, z ≠ 0 → P.GX γ (P.step γ z - z) = (1 - P.nrm2 z) • P.normalize z - γ • P.gradE (P.normalize z)
```


### `GX_step_sub`  (theorem, line 112)

Lemma 4.1, (4.4) second identity: `G_X (z⁺ - z) = -(R u + γ g(u))`.

```lean
GPDYS.Setting.GX_step_sub :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ {z : ι → ℝ}, z ≠ 0 → P.GX γ (P.step γ z - z) = -(P.R γ z • P.normalize z + γ • P.g (P.normalize z))
```


### `step_sub_decomp`  (theorem, line 119)

(4.8): `z⁺ - z = ‖z⁺‖₂ δ + (‖z⁺‖₂ - ‖z‖₂) u`.

```lean
GPDYS.Setting.step_sub_decomp :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ →
    ∀ {z : ι → ℝ},
      z ≠ 0 →
        P.step γ z ≠ 0 →
          P.step γ z - z = P.nrm2 (P.step γ z) • P.delta γ z + (P.nrm2 (P.step γ z) - P.nrm2 z) • P.normalize z
```


### `GX_delta`  (theorem, line 129)

Lemma 4.1, (4.5): `‖z⁺‖₂ G_X δ = (1 - ‖z⁺‖₂) u - γ ∇E_h(u) - γ(‖z⁺‖₂ - ‖z‖₂)(-Δ_h u)`.

```lean
GPDYS.Setting.GX_delta :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ →
    ∀ {z : ι → ℝ},
      z ≠ 0 →
        P.step γ z ≠ 0 →
          P.nrm2 (P.step γ z) • P.GX γ (P.delta γ z) =
            (1 - P.nrm2 (P.step γ z)) • P.normalize z - γ • P.gradE (P.normalize z) -
              (γ * (P.nrm2 (P.step γ z) - P.nrm2 z)) • P.negLap (P.normalize z)
```


### `radial_identity`  (theorem, line 138)

Lemma 4.1, (4.6): `(1 + γ⟪u,-Δ_h u⟫_h)(‖z⁺‖₂ - ‖z‖₂) = -R - ‖z⁺‖₂ (γ⟪-Δ_h u, δ⟫_h - ½‖δ‖₂²)`.

```lean
GPDYS.Setting.radial_identity :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ →
    ∀ {z : ι → ℝ},
      z ≠ 0 →
        P.step γ z ≠ 0 →
          (1 + γ * P.kin (P.normalize z)) * (P.nrm2 (P.step γ z) - P.nrm2 z) =
            -P.R γ z -
              P.nrm2 (P.step γ z) * (γ * P.normalize z ⬝ᵥ P.S.mulVec (P.delta γ z) - 1 / 2 * P.nrm2sq (P.delta γ z))
```


### `energy_identity`  (theorem, line 167)

Lemma 4.2, (4.9): the energy identity
`γ(E_h(u) - E_h(u⁺)) = ((‖z⁺‖₂+1)/2)‖δ‖₂² + γ(‖z⁺‖₂ - ½)⟪δ,-Δ_h δ⟫_h
  + γ(‖z⁺‖₂ - ‖z‖₂)⟪-Δ_h u, δ⟫_h - γ 𝒯(u, δ)`.

```lean
GPDYS.Setting.energy_identity :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ →
    ∀ {z : ι → ℝ},
      z ≠ 0 →
        P.step γ z ≠ 0 →
          γ * (P.energy (P.normalize z) - P.energy (P.normalize (P.step γ z))) =
            (P.nrm2 (P.step γ z) + 1) / 2 * P.nrm2sq (P.delta γ z) +
                  γ * (P.nrm2 (P.step γ z) - 1 / 2) * P.kin (P.delta γ z) +
                γ * (P.nrm2 (P.step γ z) - P.nrm2 z) * P.normalize z ⬝ᵥ P.S.mulVec (P.delta γ z) -
              γ * P.taylorT (P.normalize z) (P.delta γ z)
```


### `residual_identity`  (theorem, line 195)

Lemma 4.2, (4.10): the residual identity
`R⁺ = -½‖δ‖₂² - γ(‖z⁺‖₂ - ‖z‖₂)⟪-Δ_h u, u⁺⟫_h - γ(‖z⁺‖₂ - 1)⟪-Δ_h δ, u⁺⟫_h
  + γ⟪n(u⁺) - n(u), u⁺⟫_h`.

```lean
GPDYS.Setting.residual_identity :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ →
    ∀ {z : ι → ℝ},
      z ≠ 0 →
        P.step γ z ≠ 0 →
          P.R γ (P.step γ z) =
            -(1 / 2) * P.nrm2sq (P.delta γ z) -
                  γ * (P.nrm2 (P.step γ z) - P.nrm2 z) * P.normalize z ⬝ᵥ P.S.mulVec (P.normalize (P.step γ z)) -
                γ * (P.nrm2 (P.step γ z) - 1) * P.delta γ z ⬝ᵥ P.S.mulVec (P.normalize (P.step γ z)) +
              γ * P.inner (P.nonlin (P.normalize (P.step γ z)) - P.nonlin (P.normalize z)) (P.normalize (P.step γ z))
```


## `GPDYS/Nonlinear.lean` — Section 4.2: Lemma 4.3


### `sobolev_quadratic_bound_aux`  (theorem, line 31)

The elementary inequality behind (4.13), for `0 ≤ x ≤ y` and an arbitrary real `C₀`
(no sign condition on `C₀` is needed):
`C₀ x y ≤ (C₀ + 2 max{C₀ - 1/4, 0}²) x² + (y² - x²)/8`.

```lean
GPDYS.Setting.sobolev_quadratic_bound_aux :
∀ (C0 : ℝ) {x y : ℝ}, 0 ≤ x → x ≤ y → C0 * x * y ≤ (C0 + 2 * max (C0 - 1 / 4) 0 ^ 2) * x ^ 2 + (y ^ 2 - x ^ 2) / 8
```


### `taylorT_le_pointwise`  (theorem, line 52)

The Taylor-remainder consequence of the pointwise Jacobian bound (4.12):
`𝒯(u, δ) ≤ ½ (‖V‖_∞ + 3β U₀) ‖δ‖₂²`.

```lean
GPDYS.Setting.taylorT_le_pointwise :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 u up : ι → ℝ},
  P.nrm2sq u = 1 →
    P.nrm2sq up = 1 →
      P.energy u ≤ P.E0 u0 →
        P.energy up ≤ P.E0 u0 →
          ∀ [Nonempty ι], P.taylorT u (up - u) ≤ 1 / 2 * (P.Vinf + 3 * P.β * P.U0 u0) * P.nrm2sq (up - u)
```


### `taylorT_le_sobolev`  (theorem, line 98)

The Taylor-remainder consequence of the first Jacobian bound in (4.13):
`𝒯(u, δ) ≤ ½ (‖V‖_∞ ‖δ‖₂² + C₀ ‖δ‖₂ ‖δ‖_{1,h})`, with `‖δ‖_{1,h} = √(⟪δ,-Δ_h δ⟫_h + ‖δ‖₂²)`.

```lean
GPDYS.Setting.taylorT_le_sobolev :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 u up : ι → ℝ},
  P.nrm2sq u = 1 →
    P.nrm2sq up = 1 →
      P.energy u ≤ P.E0 u0 →
        P.energy up ≤ P.E0 u0 →
          ∀ [Nonempty ι],
            P.taylorT u (up - u) ≤
              1 / 2 * (P.Vinf * P.nrm2sq (up - u) + P.C0 u0 * P.nrm2 (up - u) * √(P.kin (up - u) + P.nrm2sq (up - u)))
```


### `taylorT_le`  (theorem, line 166)

Lemma 4.3, first inequality (4.11): `γ 𝒯(u, δ) ≤ (1/16) ‖δ‖_𝒢²` under (C3).

```lean
GPDYS.Setting.taylorT_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 u up : ι → ℝ},
  P.nrm2sq u = 1 →
    P.nrm2sq up = 1 →
      P.energy u ≤ P.E0 u0 →
        P.energy up ≤ P.E0 u0 →
          ∀ [Nonempty ι] {γ : ℝ}, 0 ≤ γ → γ * P.L0 u0 ≤ 1 / 8 → γ * P.taylorT u (up - u) ≤ 1 / 16 * P.nrmGsq γ (up - u)
```


### `nrm2_mixed_cube_le`  (theorem, line 213)

The mixed cubes: `‖a b²‖₂ ≤ min{P₀^{3/2}, U₀}` for unit vectors `a, b` of energy at most `E₀`
(here applied to the pairs `(u, u⁺)`, `(u⁺, u)` and `(u⁺, u⁺)`).

```lean
GPDYS.Setting.nrm2_mixed_cube_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 u up : ι → ℝ},
  P.nrm2sq u = 1 →
    P.nrm2sq up = 1 →
      P.energy u ≤ P.E0 u0 →
        P.energy up ≤ P.E0 u0 → ∀ [Nonempty ι], (P.nrm2 fun i => u i * up i ^ 2) ≤ min (P.P0 u0 ^ (3 / 2)) (P.U0 u0)
```


### `abs_inner_nonlin_sub_le`  (theorem, line 263)

Lemma 4.3, second inequality (4.11): `|⟪n(u⁺) - n(u), u⁺⟫_h| ≤ 3 B₀ ‖δ‖₂`.

```lean
GPDYS.Setting.abs_inner_nonlin_sub_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 u up : ι → ℝ},
  P.nrm2sq u = 1 →
    P.nrm2sq up = 1 →
      P.energy u ≤ P.E0 u0 →
        P.energy up ≤ P.E0 u0 → ∀ [Nonempty ι], |P.inner (P.nonlin up - P.nonlin u) up| ≤ 3 * P.B0 u0 * P.nrm2 (up - u)
```


### `sobolev_quadratic_bound`  (theorem, line 323)

The elementary inequality behind (4.13): for `0 ≤ x ≤ y`,
`C₀ x y ≤ (C₀ + 2 max{C₀ - 1/4, 0}²) x² + (y² - x²)/8`.

```lean
GPDYS.Setting.sobolev_quadratic_bound :
∀ (C0 : ℝ),
  0 ≤ C0 → ∀ {x y : ℝ}, 0 ≤ x → x ≤ y → C0 * x * y ≤ (C0 + 2 * max (C0 - 1 / 4) 0 ^ 2) * x ^ 2 + (y ^ 2 - x ^ 2) / 8
```


## `GPDYS/Positivity.lean` — Section 4.3: Lemma 4.4


### `nonlin_le_B1_mul`  (theorem, line 23)

Componentwise bound on the explicit part: `nᵢ(u) ≤ B₁ uᵢ` for `u > 0` with `E_h(u) ≤ E₀`.

```lean
GPDYS.Setting.nonlin_le_B1_mul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 u : ι → ℝ},
  P.nrm2sq u = 1 → P.energy u ≤ P.E0 u0 → (∀ (i : ι), 0 < u i) → ∀ (i : ι), P.nonlin u i ≤ P.B1 u0 * u i
```


### `negLap_le_Λd_mul`  (theorem, line 40)

Componentwise bound on the Laplacian: `(-Δ_h u)ᵢ ≤ Λ_d uᵢ` for `u > 0`.

```lean
GPDYS.Setting.negLap_le_Λd_mul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u : ι → ℝ},
  (∀ (i : ι), 0 < u i) → ∀ (i : ι), P.negLap u i ≤ P.Λd * u i
```


### `nonlin_nonneg`  (theorem, line 63)

`n(u) ≥ 0` for `u ≥ 0`.

```lean
GPDYS.Setting.nonlin_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u : ι → ℝ},
  (∀ (i : ι), 0 ≤ u i) → ∀ (i : ι), 0 ≤ P.nonlin u i
```


### `step_eq`  (theorem, line 69)

(4.16): `z⁺ = (‖z‖₂ - 1) u + (2 - ‖z‖₂) G_X⁻¹ u - γ G_X⁻¹ n(u)`.

```lean
GPDYS.Setting.step_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ} {z : ι → ℝ},
  z ≠ 0 →
    P.step γ z =
      (P.nrm2 z - 1) • P.normalize z + (2 - P.nrm2 z) • P.resolvent γ (P.normalize z) -
        γ • P.resolvent γ (P.nonlin (P.normalize z))
```


### `GX_step_nonneg`  (theorem, line 99)

`G_X z⁺ ≥ 0` componentwise, by (C4).

```lean
GPDYS.Setting.GX_step_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → ∀ (i : ι), 0 ≤ P.GX γ (P.step γ z) i
```


### `GX_step_ne_zero`  (theorem, line 126)

`G_X z⁺ ≠ 0`, by (C2).

```lean
GPDYS.Setting.GX_step_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → P.GX γ (P.step γ z) ≠ 0
```


### `step_pos`  (theorem, line 155)

Lemma 4.4: `z⁺ > 0` componentwise.

```lean
GPDYS.Setting.step_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → ∀ (i : ι), 0 < P.step γ z i
```


### `step_ne_zero`  (theorem, line 160)

```lean
GPDYS.Setting.step_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 → 1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → P.step γ z ≠ 0
```


### `nrm2_step_le_one`  (theorem, line 164)

Lemma 4.4: `‖z⁺‖₂ ≤ 1`.

```lean
GPDYS.Setting.nrm2_step_le_one :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → P.nrm2 (P.step γ z) ≤ 1
```


### `one_sub_inner_step_eq`  (theorem, line 187)

`1 - ⟪u, z⁺⟫_h = (2 - ‖z‖₂)(1 - ‖u‖_X²) + γ ⟪G_X⁻¹ u, n(u)⟫_h`.

```lean
GPDYS.Setting.one_sub_inner_step_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    1 - P.inner (P.normalize z) (P.step γ z) =
                      (2 - P.nrm2 z) * (1 - P.nrmXsq γ (P.normalize z)) +
                        γ * P.inner (P.resolvent γ (P.normalize z)) (P.nonlin (P.normalize z))
```


### `one_sub_inner_step_nonneg`  (theorem, line 202)

Lemma 4.4: `0 ≤ 1 - ⟪u, z⁺⟫_h`.

```lean
GPDYS.Setting.one_sub_inner_step_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → 0 ≤ 1 - P.inner (P.normalize z) (P.step γ z)
```


### `one_sub_inner_step_le`  (theorem, line 220)

Lemma 4.4: `1 - ⟪u, z⁺⟫_h ≤ 3γD`.

```lean
GPDYS.Setting.one_sub_inner_step_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → 1 - P.inner (P.normalize z) (P.step γ z) ≤ 3 * γ * P.D u0
```


### `inner_step_le_nrm2`  (theorem, line 266)

Lemma 4.4: `⟪u, z⁺⟫_h ≤ ‖z⁺‖₂`.

```lean
GPDYS.Setting.inner_step_le_nrm2 :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 → P.inner (P.normalize z) (P.step γ z) ≤ P.nrm2 (P.step γ z)
```


### `nrm2_step_ge`  (theorem, line 271)

Lemma 4.4: `1 - 3γD ≤ ‖z⁺‖₂`.

```lean
GPDYS.Setting.nrm2_step_ge :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → 1 - 3 * γ * P.D u0 ≤ P.nrm2 (P.step γ z)
```


### `nrm2sq_delta_le_two_mul`  (theorem, line 277)

Lemma 4.4: `‖δ‖₂² ≤ 2 (1 - ⟪u, z⁺⟫_h)`.

```lean
GPDYS.Setting.nrm2sq_delta_le_two_mul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 → P.nrm2sq (P.delta γ z) ≤ 2 * (1 - P.inner (P.normalize z) (P.step γ z))
```


### `nrm2sq_delta_le`  (theorem, line 293)

Lemma 4.4: `‖δ‖₂² ≤ 6γD`.

```lean
GPDYS.Setting.nrm2sq_delta_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → P.nrm2sq (P.delta γ z) ≤ 6 * γ * P.D u0
```


### `abs_R_le`  (theorem, line 299)

Lemma 4.4: `|R| ≤ 3γD`.

```lean
GPDYS.Setting.abs_R_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → |P.R γ z| ≤ 3 * γ * P.D u0
```


## `GPDYS/Descent.lean` — Section 4.4: Lemma 4.5 and Lemma 4.6


### `C1`  (def, line 29)

The crude constant `C₁ = ‖V‖_∞ + 3β/w_min`.

```lean
def C1 : ℝ := P.Vinf + 3 * P.β / P.wmin
```

*Elaborated type:*
```lean
GPDYS.Setting.C1 :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ
```


### `taylorT_le_crude`  (theorem, line 33)

The crude pointwise bound on the Taylor remainder for arbitrary unit vectors:
`𝒯(u, u⁺ - u) ≤ ½ C₁ ‖u⁺ - u‖₂²`, using only `vᵢ² ≤ 1/w_min` for `‖v‖₂ = 1`.

```lean
GPDYS.Setting.taylorT_le_crude :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u up : ι → ℝ},
  P.nrm2sq u = 1 → P.nrm2sq up = 1 → P.taylorT u (up - u) ≤ 1 / 2 * P.C1 * P.nrm2sq (up - u)
```


### `mul_abs_dotS_le`  (theorem, line 91)

`γ |xᵀ S y| ≤ √(γ xᵀ S x) √(γ yᵀ S y)` for `γ ≥ 0`.

```lean
GPDYS.Setting.mul_abs_dotS_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (x y : ι → ℝ), γ * |x ⬝ᵥ P.S.mulVec y| ≤ √(γ * P.kin x) * √(γ * P.kin y)
```


### `inner_GX_symm`  (theorem, line 102)

Symmetry of the `𝒢`-inner product: `⟪x, G_X y⟫_h = ⟪G_X x, y⟫_h`.

```lean
GPDYS.Setting.inner_GX_symm :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (x y : ι → ℝ),
  P.inner x (P.GX γ y) = P.inner (P.GX γ x) y
```


### `inner_GX_perp`  (theorem, line 107)

`d - (⟪u, G_X d⟫_h / ‖u‖_𝒢²) u` is `𝒢`-orthogonal to `u`.

```lean
GPDYS.Setting.inner_GX_perp :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) {u : ι → ℝ},
  P.nrmGsq γ u ≠ 0 → ∀ (d : ι → ℝ), P.inner u (P.GX γ (d - (P.inner u (P.GX γ d) / P.nrmGsq γ u) • u)) = 0
```


### `perp_inner_GX`  (theorem, line 112)

```lean
GPDYS.Setting.perp_inner_GX :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) {u : ι → ℝ},
  P.nrmGsq γ u ≠ 0 → ∀ (d : ι → ℝ), P.inner (d - (P.inner u (P.GX γ d) / P.nrmGsq γ u) • u) (P.GX γ u) = 0
```


### `nrmGsq_eq_perp_add`  (theorem, line 117)

Pythagoras for the `𝒢`-orthogonal decomposition of `d` along `u`.

```lean
GPDYS.Setting.nrmGsq_eq_perp_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) {u : ι → ℝ},
  P.nrmGsq γ u ≠ 0 →
    ∀ (d : ι → ℝ),
      P.nrmGsq γ d =
        P.nrmGsq γ (d - (P.inner u (P.GX γ d) / P.nrmGsq γ u) • u) +
          (P.inner u (P.GX γ d) / P.nrmGsq γ u) ^ 2 * P.nrmGsq γ u
```


### `nrmXsq_sub_eq`  (theorem, line 126)

Expansion of `‖a - b‖_X²`.

```lean
GPDYS.Setting.nrmXsq_sub_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ (a b : ι → ℝ), P.nrmXsq γ (a - b) = P.nrmXsq γ a - 2 * P.innerX γ a b + P.nrmXsq γ b
```


### `nrmGsq_sub`  (theorem, line 134)

Expansion of `‖a - b‖_𝒢²`.

```lean
GPDYS.Setting.nrmGsq_sub :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (a b : ι → ℝ),
  P.nrmGsq γ (a - b) = P.nrmGsq γ a - 2 * P.inner a (P.GX γ b) + P.nrmGsq γ b
```


### `abs_dotS_u_delta_le`  (theorem, line 151)

(4.19), first line: `γ|⟪-Δ_h u, δ⟫_h| ≤ √(2γD) ‖δ‖_𝒢`.

```lean
GPDYS.Setting.abs_dotS_u_delta_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    γ * |P.normalize z ⬝ᵥ P.S.mulVec (P.delta γ z)| ≤ √(2 * γ * P.D u0) * √(P.nrmGsq γ (P.delta γ z))
```


### `half_nrm2sq_delta_le`  (theorem, line 169)

`½‖δ‖₂² ≤ √(3γD/2) ‖δ‖_𝒢`, from `‖δ‖₂² ≤ 6γD` and `‖δ‖₂ ≤ ‖δ‖_𝒢`.

```lean
GPDYS.Setting.half_nrm2sq_delta_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 → 1 / 2 * P.nrm2sq (P.delta γ z) ≤ √(3 / 2) * √(γ * P.D u0) * √(P.nrmGsq γ (P.delta γ z))
```


### `abs_nrm2_step_sub_le`  (theorem, line 189)

(4.21): `|‖z⁺‖₂ - ‖z‖₂| ≤ |R| + (8/3) √(γD) ‖δ‖_𝒢`.

```lean
GPDYS.Setting.abs_nrm2_step_sub_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    |P.nrm2 (P.step γ z) - P.nrm2 z| ≤ |P.R γ z| + 8 / 3 * √(γ * P.D u0) * √(P.nrmGsq γ (P.delta γ z))
```


### `energy_step_le_of_small`  (theorem, line 248)

Auxiliary used here for Lemma 4.7: if `γ(28D + 2C₁) ≤ 1` then
`E_h(u⁺) ≤ E_h(u) + 2D R²`.

```lean
GPDYS.Setting.energy_step_le_of_small :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    γ * (28 * P.D u0 + 2 * P.C1) ≤ 1 →
                      P.energy (P.normalize (P.step γ z)) ≤ P.energy (P.normalize z) + 2 * P.D u0 * P.R γ z ^ 2
```


### `energy_drop`  (theorem, line 350)

(4.22): the energy drop `γ(E_h(u) - E_h(u⁺)) ≥ (7/16 - 10γD)‖δ‖_𝒢² - (1/5)R²`.

```lean
GPDYS.Setting.energy_drop :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.L0 u0 ≤ 1 / 8 →
        γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
          ∀ {z : ι → ℝ},
            z ≠ 0 →
              (∀ (i : ι), 0 < P.normalize z i) →
                P.energy (P.normalize z) ≤ P.E0 u0 →
                  1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                    P.nrm2 z ≤ 1 →
                      P.energy (P.normalize (P.step γ z)) ≤ P.E0 u0 →
                        γ * (P.energy (P.normalize z) - P.energy (P.normalize (P.step γ z))) ≥
                          (7 / 16 - 10 * γ * P.D u0) * P.nrmGsq γ (P.delta γ z) - 1 / 5 * P.R γ z ^ 2
```


### `residual_sq_le`  (theorem, line 422)

(4.23): the residual bound `(R⁺)² ≤ 8γ²D² R² + (128/25) γD ‖δ‖_𝒢²`.

```lean
GPDYS.Setting.residual_sq_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.L0 u0 ≤ 1 / 8 →
        γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
          ∀ {z : ι → ℝ},
            z ≠ 0 →
              (∀ (i : ι), 0 < P.normalize z i) →
                P.energy (P.normalize z) ≤ P.E0 u0 →
                  1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                    P.nrm2 z ≤ 1 →
                      P.energy (P.normalize (P.step γ z)) ≤ P.E0 u0 →
                        P.R γ (P.step γ z) ^ 2 ≤
                          8 * γ ^ 2 * P.D u0 ^ 2 * P.R γ z ^ 2 + 128 / 25 * γ * P.D u0 * P.nrmGsq γ (P.delta γ z)
```


### `conditional_descent`  (theorem, line 557)

Lemma 4.5, (4.17): `γ(𝓛(z) - 𝓛(z⁺)) ≥ (5/16)‖δ‖_𝒢² + (3/4)R²`.

```lean
GPDYS.Setting.conditional_descent :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.L0 u0 ≤ 1 / 8 →
        γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
          ∀ {z : ι → ℝ},
            z ≠ 0 →
              (∀ (i : ι), 0 < P.normalize z i) →
                P.energy (P.normalize z) ≤ P.E0 u0 →
                  1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                    P.nrm2 z ≤ 1 →
                      P.energy (P.normalize (P.step γ z)) ≤ P.E0 u0 →
                        γ * (P.lyap γ z - P.lyap γ (P.step γ z)) ≥
                          5 / 16 * P.nrmGsq γ (P.delta γ z) + 3 / 4 * P.R γ z ^ 2
```


### `descent_equality_case`  (theorem, line 582)

Lemma 4.5, equality case: if `δ = 0` and `R = 0` then `g(u) = 0` and `z⁺ = z`.
(For `γ = 0` one has `z⁺ = u` and `δ = 0` for every `z`, so `γ > 0` is needed for `g(u) = 0`.)

```lean
GPDYS.Setting.descent_equality_case :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 < γ →
    ∀ {z : ι → ℝ}, z ≠ 0 → P.step γ z ≠ 0 → P.delta γ z = 0 → P.R γ z = 0 → P.g (P.normalize z) = 0 ∧ P.step γ z = z
```


### `step_eq_self_of_R_g`  (theorem, line 607)

Conversely, if `R = 0` and `g(u) = 0` then `z⁺ = z` (used in the barrier argument).

```lean
GPDYS.Setting.step_eq_self_of_R_g :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {γ : ℝ},
  0 ≤ γ → ∀ {z : ι → ℝ}, z ≠ 0 → P.R γ z = 0 → P.g (P.normalize z) = 0 → P.step γ z = z
```


### `nrmGsq_mul_nrm2_sub`  (theorem, line 624)

The radial identity in the form `‖u‖_𝒢² (‖z⁺‖₂ - ‖z‖₂) = -R - ‖z⁺‖₂ ⟪u, G_X δ⟫_h`.

```lean
GPDYS.Setting.nrmGsq_mul_nrm2_sub :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    P.nrmGsq γ (P.normalize z) * (P.nrm2 (P.step γ z) - P.nrm2 z) =
                      -P.R γ z - P.nrm2 (P.step γ z) * P.inner (P.normalize z) (P.GX γ (P.delta γ z))
```


### `step_sub_eq_perp`  (theorem, line 638)

The decomposition `z⁺ - z = ‖z⁺‖₂ δ⊥ - (R/‖u‖_𝒢²) u`, where
`δ⊥ = δ - (⟪u, G_X δ⟫_h/‖u‖_𝒢²) u` is the `𝒢`-orthogonal part of `δ`.

```lean
GPDYS.Setting.step_sub_eq_perp :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    P.step γ z - z =
                      P.nrm2 (P.step γ z) •
                          (P.delta γ z -
                            (P.inner (P.normalize z) (P.GX γ (P.delta γ z)) / P.nrmGsq γ (P.normalize z)) •
                              P.normalize z) -
                        (P.R γ z / P.nrmGsq γ (P.normalize z)) • P.normalize z
```


### `gradX_sq_le`  (theorem, line 657)

Lemma 4.6, first bound of (4.24): `γ²‖g(u)‖_X² ≤ (5/4)‖δ‖_𝒢² + 10γD R²`.

```lean
GPDYS.Setting.gradX_sq_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    γ ^ 2 * P.nrmXsq γ (P.g (P.normalize z)) ≤
                      5 / 4 * P.nrmGsq γ (P.delta γ z) + 10 * γ * P.D u0 * P.R γ z ^ 2
```


### `nrmGsq_step_sub_le`  (theorem, line 743)

Lemma 4.6, second bound of (4.24): `‖z⁺ - z‖_𝒢² ≤ ‖δ‖_𝒢² + R²`.

```lean
GPDYS.Setting.nrmGsq_step_sub_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ} {γ : ℝ},
  0 < γ →
    γ * P.D u0 ≤ 1 / 128 →
      γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
        ∀ {z : ι → ℝ},
          z ≠ 0 →
            (∀ (i : ι), 0 < P.normalize z i) →
              P.energy (P.normalize z) ≤ P.E0 u0 →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 → P.nrmGsq γ (P.step γ z - z) ≤ P.nrmGsq γ (P.delta γ z) + P.R γ z ^ 2
```


## `GPDYS/Barrier.lean` — Section 4.5: Lemma 4.7 (energy barrier)


### `zcont`  (def, line 34)

The continuation `z_θ = (1 - θ(1 - ‖z‖₂)) u`, (4.27).

```lean
def zcont (z : ι → ℝ) (θ : ℝ) : ι → ℝ := (1 - θ * (1 - P.nrm2 z)) • P.normalize z
```

*Elaborated type:*
```lean
GPDYS.Setting.zcont :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ → ι → ℝ
```


### `stepcont`  (def, line 37)

One step of size `θγ` from `z_θ`, (4.29).

```lean
def stepcont (γ : ℝ) (z : ι → ℝ) (θ : ℝ) : ι → ℝ := P.step (θ * γ) (P.zcont z θ)
```

*Elaborated type:*
```lean
GPDYS.Setting.stepcont :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ℝ → ι → ℝ
```


### `φcont`  (def, line 40)

`φ(θ) = E_h(u_θ⁺)`.

```lean
def φcont (γ : ℝ) (z : ι → ℝ) (θ : ℝ) : ℝ := P.energy (P.normalize (P.stepcont γ z θ))
```

*Elaborated type:*
```lean
GPDYS.Setting.φcont :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ → (ι → ℝ) → ℝ → ℝ
```


### `nrm2_zcont`  (theorem, line 51)

`‖z_θ‖₂ = 1 - θ(1 - ‖z‖₂)` for `θ ∈ [0,1]`, (4.28).

```lean
GPDYS.Setting.nrm2_zcont :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → P.nrm2 (P.zcont z θ) = 1 - θ * (1 - P.nrm2 z)
```


### `zcont_coeff_pos`  (theorem, line 59)

`1 - θ(1 - ‖z‖₂) > 0` for `θ ∈ [0,1]` and `z ≠ 0`.

```lean
GPDYS.Setting.zcont_coeff_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ {θ : ℝ}, θ ≤ 1 → 0 < 1 - θ * (1 - P.nrm2 z)
```


### `zcont_ne_zero`  (theorem, line 64)

```lean
GPDYS.Setting.zcont_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → P.zcont z θ ≠ 0
```


### `normalize_zcont`  (theorem, line 73)

The normalized vector of `z_θ` is `u`.

```lean
GPDYS.Setting.normalize_zcont :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → P.normalize (P.zcont z θ) = P.normalize z
```


### `zcont_one`  (theorem, line 79)

`z_1 = z`.

```lean
GPDYS.Setting.zcont_one :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → P.zcont z 1 = z
```


### `stepcont_zero`  (theorem, line 83)

`z_0⁺ = u` (a step of size `0` from `u` returns `u`).

```lean
GPDYS.Setting.stepcont_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ (γ : ℝ), P.stepcont γ z 0 = P.normalize z
```


### `stepcont_one`  (theorem, line 91)

`z_1⁺ = z⁺`.

```lean
GPDYS.Setting.stepcont_one :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ (γ : ℝ), P.stepcont γ z 1 = P.step γ z
```


### `R_zcont`  (theorem, line 95)

The residual scales: `R_{θγ}(z_θ) = θ R(z)`, (4.30).

```lean
GPDYS.Setting.R_zcont :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ (γ : ℝ) {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → P.R (θ * γ) (P.zcont z θ) = θ * P.R γ z
```


### `lyap_zcont`  (theorem, line 101)

The Lyapunov function of the scaled input: `𝓛_{θγ}(z_θ) = E_h(u) + θ R²/γ`, (4.30).

```lean
GPDYS.Setting.lyap_zcont :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 →
    P.nrm2 z ≤ 1 →
      ∀ {γ : ℝ},
        0 < γ → ∀ {θ : ℝ}, 0 < θ → θ ≤ 1 → P.lyap (θ * γ) (P.zcont z θ) = P.energy (P.normalize z) + θ * P.R γ z ^ 2 / γ
```


### `stepcont_eq`  (theorem, line 111)

Explicit form of `z_θ⁺` on `[0,1]`:
`z_θ⁺ = z_θ - u + G_{θγ}⁻¹ (2u - z_θ - θγ n(u))`.

```lean
GPDYS.Setting.stepcont_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 →
    P.nrm2 z ≤ 1 →
      ∀ (γ : ℝ) {θ : ℝ},
        0 ≤ θ →
          θ ≤ 1 →
            P.stepcont γ z θ =
              P.zcont z θ - P.normalize z +
                P.resolvent (θ * γ) (2 • P.normalize z - P.zcont z θ - (θ * γ) • P.nonlin (P.normalize z))
```


### `continuousOn_inv_MS`  (theorem, line 120)

Continuity of the resolvent in the step size: `θ ↦ (M + θγS)⁻¹` is continuous on `[0,1]`
(for `γ ≥ 0`), since `det (M + θγ S) ≠ 0` there.

```lean
GPDYS.Setting.continuousOn_inv_MS :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ {γ : ℝ}, 0 ≤ γ → ContinuousOn (fun θ => (P.M + (θ * γ) • P.S)⁻¹) (Set.Icc 0 1)
```


### `stepcont_continuousOn`  (theorem, line 135)

`θ ↦ z_θ⁺` is continuous on `[0,1]`.

```lean
GPDYS.Setting.stepcont_continuousOn :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → P.nrm2 z ≤ 1 → ∀ {γ : ℝ}, 0 ≤ γ → ContinuousOn (P.stepcont γ z) (Set.Icc 0 1)
```


### `energy_continuous`  (theorem, line 157)

The energy `E_h` is a continuous function on `ι → ℝ`.

```lean
GPDYS.Setting.energy_continuous :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι), Continuous P.energy
```


### `g_continuous`  (theorem, line 162)

The projected gradient `g` is a continuous function on `ι → ℝ`.

```lean
GPDYS.Setting.g_continuous :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι), Continuous P.g
```


### `nrm2_continuous`  (theorem, line 167)

`‖·‖₂` is continuous.

```lean
GPDYS.Setting.nrm2_continuous :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι), Continuous P.nrm2
```


### `normalize_continuousAt`  (theorem, line 172)

`normalize` is continuous at every nonzero vector.

```lean
GPDYS.Setting.normalize_continuousAt :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {z : ι → ℝ},
  z ≠ 0 → ContinuousAt P.normalize z
```


### `zcont_hyp`  (theorem, line 192)

Conditions used in Lemma 4.7: for `θ ∈ (0,1]`, (C2)–(C4) hold for `θγ`,
and `1 - 3θγD ≤ ‖z_θ‖₂ ≤ 1`. Positivity and the energy bound are proved separately.

```lean
GPDYS.Setting.zcont_hyp :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 →
                        P.lyap γ z ≤ P.E0 u0 →
                          ∀ {θ : ℝ},
                            0 < θ →
                              θ ≤ 1 →
                                θ * γ * P.D u0 ≤ 1 / 128 ∧
                                  θ * γ * P.L0 u0 ≤ 1 / 8 ∧
                                    θ * γ * P.B1 u0 + 3 * (θ * γ) ^ 2 * P.D u0 * P.Λd ≤ 1 ∧
                                      1 - 3 * (θ * γ) * P.D u0 ≤ P.nrm2 (P.zcont z θ) ∧ P.nrm2 (P.zcont z θ) ≤ 1
```


### `energy_normalize_le`  (theorem, line 221)

`E_h(u) ≤ E₀`.

```lean
GPDYS.Setting.energy_normalize_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 → P.lyap γ z ≤ P.E0 u0 → P.energy (P.normalize z) ≤ P.E0 u0
```


### `stepcont_ne_zero`  (theorem, line 225)

`z_θ⁺ ≠ 0` for every `θ ∈ [0,1]`.

```lean
GPDYS.Setting.stepcont_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 → P.lyap γ z ≤ P.E0 u0 → ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → P.stepcont γ z θ ≠ 0
```


### `φcont_continuousOn`  (theorem, line 241)

Lemma 4.7: `φ` is continuous on `[0,1]`.

```lean
GPDYS.Setting.φcont_continuousOn :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 → P.lyap γ z ≤ P.E0 u0 → ContinuousOn (P.φcont γ z) (Set.Icc 0 1)
```


### `φcont_zero_le`  (theorem, line 250)

`φ(0) ≤ E₀`, using the identity `φ(0) = E_h(u)`.

```lean
GPDYS.Setting.φcont_zero_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → P.lyap γ z ≤ P.E0 u0 → P.φcont γ z 0 ≤ P.E0 u0
```


### `C1_pos`  (theorem, line 256)

`C₁ > 0`.

```lean
GPDYS.Setting.C1_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → P.lyap γ z ≤ P.E0 u0 → 0 < P.C1
```


### `φcont_le_of_small`  (theorem, line 262)

For small `θ`, `φ(θ) ≤ E₀`: the threshold `θ₁ = min{1, 1/(γ(28D + 2C₁))} > 0` works.

```lean
GPDYS.Setting.φcont_le_of_small :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 →
                        P.lyap γ z ≤ P.E0 u0 →
                          ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ min 1 (1 / (γ * (28 * P.D u0 + 2 * P.C1))) → P.φcont γ z θ ≤ P.E0 u0
```


### `φcont_le_of_le`  (theorem, line 298)

If `φ(θ) ≤ E₀` for some `θ ∈ (0,1]`, then
`φ(θ) ≤ E_h(u) + θ R²/(4γ) - (5/(16 θγ)) ‖δ_θ‖_𝒢²`, by the conditional descent.

```lean
GPDYS.Setting.φcont_le_of_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 →
                        P.lyap γ z ≤ P.E0 u0 →
                          ∀ {θ : ℝ},
                            0 < θ →
                              θ ≤ 1 →
                                P.φcont γ z θ ≤ P.E0 u0 →
                                  P.φcont γ z θ ≤
                                    P.energy (P.normalize z) + θ * P.R γ z ^ 2 / (4 * γ) -
                                      5 / (16 * (θ * γ)) * P.nrmGsq (θ * γ) (P.delta (θ * γ) (P.zcont z θ))
```


### `φcont_lt_of_le`  (theorem, line 331)

Strict version: if `φ(θ) ≤ E₀` for some `θ ∈ (0,1]` and not (`R = 0` and `g(u) = 0`),
then `φ(θ) < E₀`.

```lean
GPDYS.Setting.φcont_lt_of_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 →
                        P.lyap γ z ≤ P.E0 u0 →
                          ∀ {θ : ℝ},
                            0 < θ →
                              θ ≤ 1 →
                                P.φcont γ z θ ≤ P.E0 u0 →
                                  ¬(P.R γ z = 0 ∧ P.g (P.normalize z) = 0) → P.φcont γ z θ < P.E0 u0
```


### `φcont_eq_of_R_g`  (theorem, line 366)

If `R = 0` and `g(u) = 0`, then `φ(θ) = E_h(u)` for every `θ ∈ [0,1]`.
The proof first uses `step_eq_self_of_R_g` to show `z_θ⁺ = z_θ`.

```lean
GPDYS.Setting.φcont_eq_of_R_g :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 →
                        P.lyap γ z ≤ P.E0 u0 →
                          P.R γ z = 0 →
                            P.g (P.normalize z) = 0 →
                              ∀ {θ : ℝ}, 0 ≤ θ → θ ≤ 1 → P.φcont γ z θ = P.energy (P.normalize z)
```


### `energy_barrier`  (theorem, line 378)

Lemma 4.7 (energy barrier): `E_h(u⁺) ≤ E₀`.

```lean
GPDYS.Setting.energy_barrier :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ * P.D u0 ≤ 1 / 128 →
          γ * P.L0 u0 ≤ 1 / 8 →
            γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1 →
              ∀ {z : ι → ℝ},
                z ≠ 0 →
                  (∀ (i : ι), 0 < P.normalize z i) →
                    1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                      P.nrm2 z ≤ 1 → P.lyap γ z ≤ P.E0 u0 → P.energy (P.normalize (P.step γ z)) ≤ P.E0 u0
```


## `GPDYS/OneStep.lean` — Section 4.5: Proposition 4.8


### `onestep_conditions`  (theorem, line 31)

The step-size conditions (C2)–(C4), unpacked.

```lean
GPDYS.Setting.onestep_conditions :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ → γ ≤ P.γmax u0 → γ * P.D u0 ≤ 1 / 128 ∧ γ * P.L0 u0 ≤ 1 / 8 ∧ γ * P.B1 u0 + 3 * γ ^ 2 * P.D u0 * P.Λd ≤ 1
```


### `onestep_energy_le`  (theorem, line 39)

`E_h(u) ≤ E₀`.

```lean
GPDYS.Setting.onestep_energy_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u0 : ι → ℝ} {γ : ℝ},
  0 < γ → ∀ {z : ι → ℝ}, P.lyap γ z ≤ P.E0 u0 → P.energy (P.normalize z) ≤ P.E0 u0
```


### `onestep_pos`  (theorem, line 43)

Proposition 4.8: positivity of `z⁺`.

```lean
GPDYS.Setting.onestep_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ ≤ P.γmax u0 →
          ∀ {z : ι → ℝ},
            z ≠ 0 →
              (∀ (i : ι), 0 < P.normalize z i) →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z → P.nrm2 z ≤ 1 → P.lyap γ z ≤ P.E0 u0 → ∀ (i : ι), 0 < P.step γ z i
```


### `onestep_radial`  (theorem, line 48)

Proposition 4.8: the radial interval for `z⁺`.

```lean
GPDYS.Setting.onestep_radial :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ ≤ P.γmax u0 →
          ∀ {z : ι → ℝ},
            z ≠ 0 →
              (∀ (i : ι), 0 < P.normalize z i) →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    P.lyap γ z ≤ P.E0 u0 → 1 - 3 * γ * P.D u0 ≤ P.nrm2 (P.step γ z) ∧ P.nrm2 (P.step γ z) ≤ 1
```


### `onestep_energy`  (theorem, line 54)

Proposition 4.8: `E_h(u⁺) ≤ E₀`, by the energy barrier.

```lean
GPDYS.Setting.onestep_energy :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ ≤ P.γmax u0 →
          ∀ {z : ι → ℝ},
            z ≠ 0 →
              (∀ (i : ι), 0 < P.normalize z i) →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 → P.lyap γ z ≤ P.E0 u0 → P.energy (P.normalize (P.step γ z)) ≤ P.E0 u0
```


### `onestep_drop`  (theorem, line 60)

Proposition 4.8, (4.31) first inequality:
`𝓛(z) - 𝓛(z⁺) ≥ ¼ γ ‖g(u)‖_X² + R²/(2γ)`.

```lean
GPDYS.Setting.onestep_drop :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ ≤ P.γmax u0 →
          ∀ {z : ι → ℝ},
            z ≠ 0 →
              (∀ (i : ι), 0 < P.normalize z i) →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    P.lyap γ z ≤ P.E0 u0 →
                      P.lyap γ z - P.lyap γ (P.step γ z) ≥
                        1 / 4 * γ * P.nrmXsq γ (P.g (P.normalize z)) + P.R γ z ^ 2 / (2 * γ)
```


### `onestep_drop'`  (theorem, line 86)

Proposition 4.8, (4.31) second inequality: `𝓛(z) - 𝓛(z⁺) ≥ (5/(16γ)) ‖z⁺ - z‖_𝒢²`.

```lean
GPDYS.Setting.onestep_drop' :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  u0 ≠ 0 →
    ∀ {γ : ℝ},
      0 < γ →
        γ ≤ P.γmax u0 →
          ∀ {z : ι → ℝ},
            z ≠ 0 →
              (∀ (i : ι), 0 < P.normalize z i) →
                1 - 3 * γ * P.D u0 ≤ P.nrm2 z →
                  P.nrm2 z ≤ 1 →
                    P.lyap γ z ≤ P.E0 u0 →
                      P.lyap γ z - P.lyap γ (P.step γ z) ≥ 5 / (16 * γ) * P.nrmGsq γ (P.step γ z - z)
```


## `GPDYS/GroundState.lean` — Remark 2.3 / Appendix A (the discrete ground state)


### `kin_eq_double_sum`  (theorem, line 34)

`vᵀ S v` written as a double sum.

```lean
GPDYS.Setting.kin_eq_double_sum :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.kin v = ∑ i, ∑ j, P.S i j * (v i * v j)
```


### `picone`  (theorem, line 45)

The discrete Picone inequality used here to prove Remark 2.3.
For `u > 0` componentwise and any `v`,
`∑ᵢ (vᵢ²/uᵢ) (S u)ᵢ ≤ vᵀ S v`.

```lean
GPDYS.Setting.picone :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u : ι → ℝ},
  (∀ (i : ι), 0 < u i) → ∀ (v : ι → ℝ), ∑ i, v i ^ 2 / u i * P.S.mulVec u i ≤ P.kin v
```


### `kin_abs_le`  (theorem, line 96)

`|v|ᵀ S |v| ≤ vᵀ S v`, since the off-diagonal entries of `S` are nonpositive.

```lean
GPDYS.Setting.kin_abs_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  (P.kin fun i => |v i|) ≤ P.kin v
```


### `energy_abs_le`  (theorem, line 107)

`E_h(|v|) ≤ E_h(v)`.

```lean
GPDYS.Setting.energy_abs_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  (P.energy fun i => |v i|) ≤ P.energy v
```


### `nrm2sq_abs`  (theorem, line 119)

`‖ |v| ‖₂² = ‖v‖₂²`.

```lean
GPDYS.Setting.nrm2sq_abs :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  (P.nrm2sq fun i => |v i|) = P.nrm2sq v
```


### `negLap_eq_of_critical`  (theorem, line 124)

A critical point satisfies `-Δ_h v = λ(v) v - n(v)`.

```lean
GPDYS.Setting.negLap_eq_of_critical :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ},
  P.g v = 0 → P.negLap v = P.lam v • v - P.nonlin v
```


### `critical_pos`  (theorem, line 131)

Remark 2.3: a nonnegative critical point of `E_h` on `𝓜` is strictly positive.

```lean
GPDYS.Setting.critical_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {v : ι → ℝ},
  P.nrm2sq v = 1 → (∀ (i : ι), 0 ≤ v i) → P.g v = 0 → ∀ (i : ι), 0 < v i
```


### `energy_ge_of_critical`  (theorem, line 188)

The key inequality used here to prove Remark 2.3:
for a positive critical point `u ∈ 𝓜` and any nonnegative `v ∈ 𝓜`,
`E_h(v) ≥ E_h(u) + (β/4) ∑ᵢ wᵢ (vᵢ² - uᵢ²)²`.

```lean
GPDYS.Setting.energy_ge_of_critical :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u v : ι → ℝ},
  P.nrm2sq u = 1 →
    (∀ (i : ι), 0 < u i) →
      P.g u = 0 →
        P.nrm2sq v = 1 → (∀ (i : ι), 0 ≤ v i) → P.energy u + P.β / 4 * ∑ i, P.w i * (v i ^ 2 - u i ^ 2) ^ 2 ≤ P.energy v
```


### `energy_le_of_critical`  (theorem, line 225)

Remark 2.3: a positive critical point is a global minimizer of `E_h` on `𝓜`.

```lean
GPDYS.Setting.energy_le_of_critical :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u v : ι → ℝ},
  P.nrm2sq u = 1 → (∀ (i : ι), 0 < u i) → P.g u = 0 → P.nrm2sq v = 1 → P.energy u ≤ P.energy v
```


### `eq_of_nonneg_le_energy`  (theorem, line 239)

Remark 2.3, uniqueness: a nonnegative `v ∈ 𝓜` with `E_h(v) ≤ E_h(u)`,
where `u > 0` is a critical point, equals `u`.

```lean
GPDYS.Setting.eq_of_nonneg_le_energy :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u v : ι → ℝ},
  P.nrm2sq u = 1 →
    (∀ (i : ι), 0 < u i) → P.g u = 0 → P.nrm2sq v = 1 → (∀ (i : ι), 0 ≤ v i) → P.energy v ≤ P.energy u → v = u
```


### `eq_of_critical_nonneg`  (theorem, line 267)

Remark 2.3, uniqueness of the nonnegative critical point: two nonnegative critical points on `𝓜`
coincide.

```lean
GPDYS.Setting.eq_of_critical_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u v : ι → ℝ},
  P.nrm2sq u = 1 → (∀ (i : ι), 0 ≤ u i) → P.g u = 0 → P.nrm2sq v = 1 → (∀ (i : ι), 0 ≤ v i) → P.g v = 0 → v = u
```


## `GPDYS/Main.lean` — Section 5: Theorem 3.4


### `tendsto_zero_of_sq_tendsto_zero`  (theorem, line 20)

If `f ^ 2 → 0` then `f → 0`.

```lean
GPDYS.tendsto_zero_of_sq_tendsto_zero :
∀ {α : Type u_1} {l : Filter α} {f : α → ℝ}, Filter.Tendsto (fun x => f x ^ 2) l (nhds 0) → Filter.Tendsto f l (nhds 0)
```


### `tendsto_zero_of_const_mul_tendsto_zero`  (theorem, line 30)

If `c * f → 0` with `c ≠ 0` then `f → 0`.

```lean
GPDYS.tendsto_zero_of_const_mul_tendsto_zero :
∀ {α : Type u_1} {l : Filter α} {f : α → ℝ} {c : ℝ},
  c ≠ 0 → Filter.Tendsto (fun x => c * f x) l (nhds 0) → Filter.Tendsto f l (nhds 0)
```


### `nrm2sq_continuous`  (theorem, line 42)

`‖·‖₂²` is continuous.

```lean
GPDYS.Setting.nrm2sq_continuous :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι), Continuous P.nrm2sq
```


### `kin_eq_sum_sum`  (theorem, line 49)

`vᵀ S v` as a double sum.

```lean
GPDYS.Setting.kin_eq_sum_sum :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (v : ι → ℝ),
  P.kin v = ∑ i, ∑ j, P.S i j * (v i * v j)
```


### `exists_kin_bound`  (theorem, line 54)

A Rayleigh-quotient bound for the discrete Laplacian: there is `μ ≥ 0` with
`⟪v, -Δ_h v⟫_h ≤ μ ‖v‖₂²` for all `v` (in the paper, `μ_max` is the largest eigenvalue).

```lean
GPDYS.Setting.exists_kin_bound :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  ∃ μ, 0 ≤ μ ∧ ∀ (v : ι → ℝ), P.kin v ≤ μ * P.nrm2sq v
```


### `sphere_isCompact`  (theorem, line 90)

The sphere `𝓜` is compact.

```lean
GPDYS.Setting.sphere_isCompact :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  IsCompact {v | P.nrm2sq v = 1}
```


### `invariant`  (theorem, line 119)

Theorem 3.4, the invariant (5.1): for every `k`,
`u^k > 0`, `1 - 3γD ≤ ‖z^k‖₂ ≤ 1` and `𝓛^k ≤ E₀`.

```lean
GPDYS.Setting.invariant :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ},
        0 < γ →
          γ ≤ P.γmax u0 →
            ∀ (k : ℕ),
              (∀ (i : ι), 0 < P.uiter γ u0 k i) ∧
                1 - 3 * γ * P.D u0 ≤ P.nrm2 (P.iter γ u0 k) ∧
                  P.nrm2 (P.iter γ u0 k) ≤ 1 ∧ P.lyap γ (P.iter γ u0 k) ≤ P.E0 u0
```


### `iter_ne_zero`  (theorem, line 153)

```lean
GPDYS.Setting.iter_ne_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) → P.nrm2 u0 = 1 → ∀ {γ : ℝ}, 0 < γ → γ ≤ P.γmax u0 → ∀ (k : ℕ), P.iter γ u0 k ≠ 0
```


### `drop`  (theorem, line 162)

Theorem 3.4, the drop (5.2): `𝓛^k - 𝓛^{k+1} ≥ ¼γ‖g(u^k)‖_X² + (R^k)²/(2γ)`.

```lean
GPDYS.Setting.drop :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ},
        0 < γ →
          γ ≤ P.γmax u0 →
            ∀ (k : ℕ),
              P.lyap γ (P.iter γ u0 k) - P.lyap γ (P.iter γ u0 (k + 1)) ≥
                1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k)) + P.R γ (P.iter γ u0 k) ^ 2 / (2 * γ)
```


### `sum_drop_le`  (theorem, line 173)

Theorem 3.4: every finite partial sum
`∑_{k < m} (¼γ‖g^k‖_X² + (R^k)²/(2γ))` is at most `𝓛⁰`.

```lean
GPDYS.Setting.sum_drop_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ},
        0 < γ →
          γ ≤ P.γmax u0 →
            ∀ (m : ℕ),
              ∑ k ∈ Finset.range m,
                  (1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k)) + P.R γ (P.iter γ u0 k) ^ 2 / (2 * γ)) ≤
                P.lyap γ u0
```


### `drop_summable`  (theorem, line 190)

The descent terms `¼γ‖g^k‖_X² + (R^k)²/(2γ)` are summable.

```lean
GPDYS.Setting.drop_summable :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ},
        0 < γ →
          γ ≤ P.γmax u0 →
            Summable fun k => 1 / 4 * γ * P.nrmXsq γ (P.g (P.uiter γ u0 k)) + P.R γ (P.iter γ u0 k) ^ 2 / (2 * γ)
```


### `nrmXsq_g_tendsto_zero`  (theorem, line 200)

`‖g(u^k)‖_X² → 0`.

```lean
GPDYS.Setting.nrmXsq_g_tendsto_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ},
        0 < γ → γ ≤ P.γmax u0 → Filter.Tendsto (fun k => P.nrmXsq γ (P.g (P.uiter γ u0 k))) Filter.atTop (nhds 0)
```


### `R_tendsto_zero`  (theorem, line 212)

`R^k → 0`.

```lean
GPDYS.Setting.R_tendsto_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ}, 0 < γ → γ ≤ P.γmax u0 → Filter.Tendsto (fun k => P.R γ (P.iter γ u0 k)) Filter.atTop (nhds 0)
```


### `g_tendsto_zero`  (theorem, line 224)

Theorem 3.4: `g(u^k) → 0`.

```lean
GPDYS.Setting.g_tendsto_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ}, 0 < γ → γ ≤ P.γmax u0 → Filter.Tendsto (fun k => P.g (P.uiter γ u0 k)) Filter.atTop (nhds 0)
```


### `accumulation_point_critical`  (theorem, line 248)

Theorem 3.4: every accumulation point of `(u^k)`
is a nonnegative critical point of `E_h` on `𝓜`.

```lean
GPDYS.Setting.accumulation_point_critical :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ},
        0 < γ →
          γ ≤ P.γmax u0 →
            ∀ {ns : ℕ → ℕ},
              Filter.Tendsto ns Filter.atTop Filter.atTop →
                ∀ {ustar : ι → ℝ},
                  Filter.Tendsto (fun j => P.uiter γ u0 (ns j)) Filter.atTop (nhds ustar) →
                    P.nrm2sq ustar = 1 ∧ (∀ (i : ι), 0 ≤ ustar i) ∧ P.g ustar = 0
```


### `uiter_mem_sphere`  (theorem, line 274)

The normalized iterates lie on the sphere `𝓜`.

```lean
GPDYS.Setting.uiter_mem_sphere :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 → ∀ {γ : ℝ}, 0 < γ → γ ≤ P.γmax u0 → ∀ (k : ℕ), P.uiter γ u0 k ∈ {v | P.nrm2sq v = 1}
```


### `exists_accumulation_point`  (theorem, line 279)

Existence of an accumulation point.

```lean
GPDYS.Setting.exists_accumulation_point :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ},
        0 < γ →
          γ ≤ P.γmax u0 →
            ∃ ustar ns, StrictMono ns ∧ Filter.Tendsto (fun j => P.uiter γ u0 (ns j)) Filter.atTop (nhds ustar)
```


### `main_theorem`  (theorem, line 292)

**Theorem 3.4** (global convergence to the discrete ground state). Under
Assumption 2.1 (through Lemma 2.2), for a positive normalized initial vector `u⁰` and a step
size `0 < γ ≤ γ_max`, the iterates `u^k = z^k/‖z^k‖₂` of (DYS I) are positive for every `k`,
and converge to the discrete ground state `u_GS`, the unique positive global minimizer of `E_h`
on `𝓜`, which is also the unique nonnegative critical point of `E_h|_𝓜`; moreover
`E_h(u^k) → E_h(u_GS) = min_𝓜 E_h`.

```lean
GPDYS.Setting.main_theorem :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {u0 : ι → ℝ},
  (∀ (i : ι), 0 < u0 i) →
    P.nrm2 u0 = 1 →
      ∀ {γ : ℝ},
        0 < γ →
          γ ≤ P.γmax u0 →
            (∀ (k : ℕ) (i : ι), 0 < P.uiter γ u0 k i) ∧
              ∃ uGS,
                (∀ (i : ι), 0 < uGS i) ∧
                  P.nrm2 uGS = 1 ∧
                    P.g uGS = 0 ∧
                      (∀ (v : ι → ℝ), P.nrm2 v = 1 → P.energy uGS ≤ P.energy v) ∧
                        (∀ (v : ι → ℝ), P.nrm2 v = 1 → (∀ (i : ι), 0 ≤ v i) → P.energy v ≤ P.energy uGS → v = uGS) ∧
                          (∀ (v : ι → ℝ), P.nrm2 v = 1 → (∀ (i : ι), 0 ≤ v i) → P.g v = 0 → v = uGS) ∧
                            Filter.Tendsto (P.uiter γ u0) Filter.atTop (nhds uGS) ∧
                              Filter.Tendsto (fun k => P.energy (P.uiter γ u0 k)) Filter.atTop (nhds (P.energy uGS))
```


### `exists_groundState`  (theorem, line 338)

**Corollary** (the discrete ground state, Remark 2.3). There is a positive `u_GS ∈ 𝓜` which
is a critical point of `E_h|_𝓜`, the global minimizer of `E_h` on `𝓜`, and the unique
nonnegative critical point. It is obtained from Theorem 3.4 as the limit of the iteration
started from the normalized constant vector with the step size `γ_max`.

```lean
GPDYS.Setting.exists_groundState :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  ∃ uGS,
    (∀ (i : ι), 0 < uGS i) ∧
      P.nrm2 uGS = 1 ∧
        P.g uGS = 0 ∧
          (∀ (v : ι → ℝ), P.nrm2 v = 1 → P.energy uGS ≤ P.energy v) ∧
            ∀ (v : ι → ℝ), P.nrm2 v = 1 → (∀ (i : ι), 0 ≤ v i) → P.g v = 0 → v = uGS
```


## `GPDYS/Rate.lean` — Section 5: Theorem 5.1


### `mGS`  (def, line 32)

`m_GS = minᵢ pᵢ` on a nonempty mesh; the empty-index value is zero.

```lean
def mGS {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ := ⨅ i, p i
```

*Elaborated type:*
```lean
GPDYS.mGS :
{ι : Type u_1} → [Fintype ι] → (ι → ℝ) → ℝ
```


### `η`  (def, line 35)

The rate `η = min{γν/(4(1+γμ)), 1/2}`, (5.5).

```lean
def η (γ μ ν : ℝ) : ℝ := min (γ * ν / (4 * (1 + γ * μ))) (1 / 2)
```

*Elaborated type:*
```lean
GPDYS.η :
ℝ → ℝ → ℝ → ℝ
```


### `hess`  (def, line 42)

The operator `ℋ = -Δ_h + n'(p) - λ(p) I` of (5.4), applied to `w`.

```lean
def hess (p w : ι → ℝ) : ι → ℝ := P.negLap w + P.nonlin' p w - P.lam p • w
```

*Elaborated type:*
```lean
GPDYS.Setting.hess :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → (ι → ℝ) → ι → ℝ
```


### `hessForm`  (def, line 45)

The quadratic form `⟪w, ℋ w⟫_h`.

```lean
def hessForm (p w : ι → ℝ) : ℝ := P.inner w (P.hess p w)
```

*Elaborated type:*
```lean
GPDYS.Setting.hessForm :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → (ι → ℝ) → ℝ
```


### `nu`  (def, line 51)

The infimum of `⟪w, ℋ w⟫_h` over unit tangent vectors.
For a positive critical point and `2 ≤ Fintype.card ι`, `exists_unit_tangent` and
`bddBelow_nu_set` justify the infimum used in the rate theorem. Attainment as a minimum
is proved by `nu_attained` in `Spectral.lean`. The empty-set value is zero.

```lean
def nu (p : ι → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ w : ι → ℝ, P.nrm2sq w = 1 ∧ P.inner p w = 0 ∧ x = P.hessForm p w}
```

*Elaborated type:*
```lean
GPDYS.Setting.nu :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → ℝ
```


### `hessForm_eq`  (theorem, line 56)

```lean
GPDYS.Setting.hessForm_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p w : ι → ℝ),
  P.hessForm p w = P.kin w + P.pot w + 3 * P.β * ∑ i, P.w i * (p i ^ 2 * w i ^ 2) - P.lam p * P.nrm2sq w
```


### `rayleigh_of_critical`  (theorem, line 71)

The Rayleigh bound of a positive critical point (via the discrete Picone inequality):
`⟪w, A_p w⟫_h ≥ λ(p) ‖w‖₂²` for every `w`, where `A_p = -Δ_h + V + β diag(p²)`.

```lean
GPDYS.Setting.rayleigh_of_critical :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p : ι → ℝ},
  P.nrm2sq p = 1 →
    (∀ (i : ι), 0 < p i) →
      P.g p = 0 → ∀ (w : ι → ℝ), P.lam p * P.nrm2sq w ≤ P.kin w + P.pot w + P.β * ∑ i, P.w i * (p i ^ 2 * w i ^ 2)
```


### `mGS_le`  (theorem, line 99)

```lean
GPDYS.Setting.mGS_le :
∀ {ι : Type u_1} [inst : Fintype ι] (p : ι → ℝ) (i : ι), GPDYS.mGS p ≤ p i
```


### `mGS_pos`  (theorem, line 102)

```lean
GPDYS.Setting.mGS_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [Nonempty ι] {p : ι → ℝ}, (∀ (i : ι), 0 < p i) → 0 < GPDYS.mGS p
```


### `hessForm_ge`  (theorem, line 107)

Theorem 5.1: `⟪w, ℋ w⟫_h ≥ 2β m_GS² ‖w‖₂²` for every `w`.

```lean
GPDYS.Setting.hessForm_ge :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p : ι → ℝ},
  P.nrm2sq p = 1 →
    (∀ (i : ι), 0 < p i) → P.g p = 0 → ∀ (w : ι → ℝ), 2 * P.β * GPDYS.mGS p ^ 2 * P.nrm2sq w ≤ P.hessForm p w
```


### `exists_unit_tangent`  (theorem, line 127)

For `N ≥ 2` there is a unit vector orthogonal to `p`.

```lean
GPDYS.Setting.exists_unit_tangent :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι),
  2 ≤ Fintype.card ι → ∀ {p : ι → ℝ}, (∀ (i : ι), 0 < p i) → ∃ w, P.nrm2sq w = 1 ∧ P.inner p w = 0
```


### `nu_ge`  (theorem, line 151)

Theorem 5.1: `ν ≥ 2β m_GS²`.

```lean
GPDYS.Setting.nu_ge :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι),
  2 ≤ Fintype.card ι →
    ∀ {p : ι → ℝ}, P.nrm2sq p = 1 → (∀ (i : ι), 0 < p i) → P.g p = 0 → 2 * P.β * GPDYS.mGS p ^ 2 ≤ P.nu p
```


### `nu_pos`  (theorem, line 162)

`ν > 0`.

```lean
GPDYS.Setting.nu_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι),
  2 ≤ Fintype.card ι → ∀ {p : ι → ℝ}, P.nrm2sq p = 1 → (∀ (i : ι), 0 < p i) → P.g p = 0 → 0 < P.nu p
```


### `nonlin'_add`  (theorem, line 170)

`n'(p)` is linear in its second argument.

```lean
GPDYS.Setting.nonlin'_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p u v : ι → ℝ),
  P.nonlin' p (u + v) = P.nonlin' p u + P.nonlin' p v
```


### `nonlin'_smul`  (theorem, line 173)

```lean
GPDYS.Setting.nonlin'_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p : ι → ℝ) (c : ℝ) (v : ι → ℝ),
  P.nonlin' p (c • v) = c • P.nonlin' p v
```


### `inner_nonlin'_comm`  (theorem, line 178)

`n'(p)` is a diagonal operator, hence `h`-self-adjoint.

```lean
GPDYS.Setting.inner_nonlin'_comm :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p x y : ι → ℝ),
  P.inner x (P.nonlin' p y) = P.inner (P.nonlin' p x) y
```


### `hess_add`  (theorem, line 184)

`ℋ` is linear.

```lean
GPDYS.Setting.hess_add :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p u v : ι → ℝ),
  P.hess p (u + v) = P.hess p u + P.hess p v
```


### `hess_smul`  (theorem, line 189)

```lean
GPDYS.Setting.hess_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p : ι → ℝ) (c : ℝ) (v : ι → ℝ),
  P.hess p (c • v) = c • P.hess p v
```


### `hess_zero`  (theorem, line 193)

```lean
GPDYS.Setting.hess_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p : ι → ℝ), P.hess p 0 = 0
```


### `inner_hess_comm`  (theorem, line 198)

`ℋ` is `h`-self-adjoint: `⟪x, ℋ y⟫_h = ⟪ℋ x, y⟫_h`.

```lean
GPDYS.Setting.inner_hess_comm :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p x y : ι → ℝ),
  P.inner x (P.hess p y) = P.inner (P.hess p x) y
```


### `hessForm_smul`  (theorem, line 204)

Homogeneity of the Hessian form.

```lean
GPDYS.Setting.hessForm_smul :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p : ι → ℝ) (c : ℝ) (w : ι → ℝ),
  P.hessForm p (c • w) = c ^ 2 * P.hessForm p w
```


### `hessForm_zero`  (theorem, line 209)

```lean
GPDYS.Setting.hessForm_zero :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p : ι → ℝ), P.hessForm p 0 = 0
```


### `bddBelow_nu_set`  (theorem, line 213)

The set defining `ν` is bounded below by `2β m_GS²`.

```lean
GPDYS.Setting.bddBelow_nu_set :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p : ι → ℝ},
  P.nrm2sq p = 1 →
    (∀ (i : ι), 0 < p i) → P.g p = 0 → BddBelow {x | ∃ w, P.nrm2sq w = 1 ∧ P.inner p w = 0 ∧ x = P.hessForm p w}
```


### `hessForm_ge_nu`  (theorem, line 223)

`⟪w, ℋ w⟫_h ≥ ν ‖w‖₂²` for every tangent vector `w` (`⟪p, w⟫_h = 0`).

```lean
GPDYS.Setting.hessForm_ge_nu :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p : ι → ℝ},
  P.nrm2sq p = 1 →
    (∀ (i : ι), 0 < p i) → P.g p = 0 → ∀ {w : ι → ℝ}, P.inner p w = 0 → P.nu p * P.nrm2sq w ≤ P.hessForm p w
```


### `energy_sub_eq`  (theorem, line 248)

Exact energy expansion used here to prove Theorem 5.1, for `u, p ∈ 𝓜` with `p` critical
and `h = u - p`:
`E_h(u) - E_h(p) = ½⟪h, ℋ h⟫_h + β ∑ wᵢ pᵢ hᵢ³ + (β/4) ∑ wᵢ hᵢ⁴`.

```lean
GPDYS.Setting.energy_sub_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p u : ι → ℝ},
  P.nrm2sq p = 1 →
    P.g p = 0 →
      P.nrm2sq u = 1 →
        P.energy u - P.energy p =
          1 / 2 * P.hessForm p (u - p) + P.β * ∑ i, P.w i * (p i * (u i - p i) ^ 3) +
            P.β / 4 * ∑ i, P.w i * (u i - p i) ^ 4
```


### `rho`  (def, line 274)

The vector `ρ = β(3 p h² + h³)`.

```lean
def rho (p h : ι → ℝ) : ι → ℝ := fun i => P.β * (3 * p i * h i ^ 2 + h i ^ 3)
```

*Elaborated type:*
```lean
GPDYS.Setting.rho :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → (ι → ℝ) → (ι → ℝ) → ι → ℝ
```


### `gradE_eq_of_critical`  (theorem, line 277)

`∇E_h(u) = λ(p) u + ℋ h + ρ` for `h = u - p`, `p` critical.

```lean
GPDYS.Setting.gradE_eq_of_critical :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p u : ι → ℝ},
  P.g p = 0 → P.gradE u = P.lam p • u + P.hess p (u - p) + P.rho p (u - p)
```


### `inner_g_sub_eq`  (theorem, line 291)

Exact expansion used here to prove Theorem 5.1: `⟪g(u), h⟫_h`,
using `⟪u, h⟫_h = ½‖h‖₂²`:
`⟪g(u), h⟫_h = ⟪h, ℋ h⟫_h + ⟪ρ, h⟫_h - ½‖h‖₂² ⟪ℋ h + ρ, u⟫_h`.

```lean
GPDYS.Setting.inner_g_sub_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p u : ι → ℝ},
  P.nrm2sq p = 1 →
    P.g p = 0 →
      P.nrm2sq u = 1 →
        P.inner (P.g u) (u - p) =
          P.hessForm p (u - p) + P.inner (P.rho p (u - p)) (u - p) -
            1 / 2 * P.nrm2sq (u - p) * P.inner (P.hess p (u - p) + P.rho p (u - p)) u
```


### `hess_self`  (theorem, line 319)

`ℋ p = 2β p³` for a critical point `p`.

```lean
GPDYS.Setting.hess_self :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p : ι → ℝ},
  P.g p = 0 → P.hess p p = (2 * P.β) • fun i => p i ^ 3
```


### `hessForm_decomp`  (theorem, line 327)

Decomposition of the Hessian form along `h = (h - c p) + c p`.

```lean
GPDYS.Setting.hessForm_decomp :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p h : ι → ℝ) (c : ℝ),
  P.hessForm p h = P.hessForm p (h - c • p) + 2 * c * P.inner (h - c • p) (P.hess p p) + c ^ 2 * P.inner p (P.hess p p)
```


### `hessForm_sub_ge_aux`  (theorem, line 339)

The elementary inequality behind `hessForm_sub_ge`.

```lean
GPDYS.Setting.hessForm_sub_ge_aux :
∀ {ν β N3 R HT X Y c : ℝ},
  c = -(1 / 2) * R ^ 2 →
    ν * (R ^ 2 - c ^ 2) ≤ HT →
      0 ≤ Y → |X| ≤ R * (2 * β * N3) → ν * R ^ 2 - ν / 4 * (R ^ 2) ^ 2 - 2 * β * N3 * R ^ 3 ≤ HT + 2 * c * X + c ^ 2 * Y
```


### `hessForm_sub_ge`  (theorem, line 353)

The tangential lower bound: `⟪h, ℋ h⟫_h ≥ ν‖h‖₂² - (ν/4)‖h‖₂⁴ - 2β‖p³‖₂ ‖h‖₂³`
for `h = u - p` with `u, p ∈ 𝓜`.

```lean
GPDYS.Setting.hessForm_sub_ge :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {p u : ι → ℝ},
  P.nrm2sq p = 1 →
    (∀ (i : ι), 0 < p i) →
      P.g p = 0 →
        P.nrm2sq u = 1 →
          P.nu p * P.nrm2sq (u - p) - P.nu p / 4 * P.nrm2sq (u - p) ^ 2 -
              (2 * P.β * P.nrm2 fun i => p i ^ 3) * P.nrm2 (u - p) ^ 3 ≤
            P.hessForm p (u - p)
```


### `exists_sq_bound`  (theorem, line 398)

The pointwise bound `vᵢ² ≤ K ‖v‖₂²` with `K = 1/w_min`.

```lean
GPDYS.Setting.exists_sq_bound :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  ∃ K, 0 < K ∧ ∀ (v : ι → ℝ) (i : ι), v i ^ 2 ≤ K * P.nrm2sq v
```


### `abs_mul_le_of_unit`  (theorem, line 409)

`|pᵢ hᵢ| ≤ K ‖h‖₂` for a unit vector `p`.

```lean
GPDYS.Setting.abs_mul_le_of_unit :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {K : ℝ},
  0 ≤ K →
    (∀ (v : ι → ℝ) (i : ι), v i ^ 2 ≤ K * P.nrm2sq v) →
      ∀ {p : ι → ℝ}, P.nrm2sq p = 1 → ∀ (h : ι → ℝ) (i : ι), |p i * h i| ≤ K * P.nrm2 h
```


### `abs_sum_cube_le`  (theorem, line 421)

`|∑ᵢ wᵢ pᵢ hᵢ³| ≤ K ‖h‖₂³` for a unit vector `p`.

```lean
GPDYS.Setting.abs_sum_cube_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {K : ℝ},
  0 ≤ K →
    (∀ (v : ι → ℝ) (i : ι), v i ^ 2 ≤ K * P.nrm2sq v) →
      ∀ {p : ι → ℝ}, P.nrm2sq p = 1 → ∀ (h : ι → ℝ), |∑ i, P.w i * (p i * h i ^ 3)| ≤ K * P.nrm2 h ^ 3
```


### `sum_pow_four_le`  (theorem, line 439)

`∑ᵢ wᵢ hᵢ⁴ ≤ K ‖h‖₂⁴`.

```lean
GPDYS.Setting.sum_pow_four_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {K : ℝ},
  (∀ (v : ι → ℝ) (i : ι), v i ^ 2 ≤ K * P.nrm2sq v) → ∀ (h : ι → ℝ), ∑ i, P.w i * h i ^ 4 ≤ K * P.nrm2sq h ^ 2
```


### `local_quadratic_growth`  (theorem, line 451)

Theorem 5.1, local quadratic growth deduced after (5.8): there is `r > 0` such that
`(ν/4)‖u - p‖₂² ≤ E_h(u) - E_h(p)` for every `u ∈ 𝓜` with `‖u - p‖₂ ≤ r`.

```lean
GPDYS.Setting.local_quadratic_growth :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {p : ι → ℝ},
      P.nrm2sq p = 1 →
        (∀ (i : ι), 0 < p i) →
          P.g p = 0 →
            ∃ r,
              0 < r ∧
                ∀ (u : ι → ℝ),
                  P.nrm2sq u = 1 → P.nrm2 (u - p) ≤ r → P.nu p / 4 * P.nrm2sq (u - p) ≤ P.energy u - P.energy p
```


### `nrm2_negLap_le`  (theorem, line 487)

`‖-Δ_h v‖₂ ≤ μ ‖v‖₂` under the Rayleigh bound `⟪·,-Δ_h ·⟫_h ≤ μ ‖·‖₂²`.

```lean
GPDYS.Setting.nrm2_negLap_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {μ : ℝ},
  0 ≤ μ → (∀ (x : ι → ℝ), P.kin x ≤ μ * P.nrm2sq x) → ∀ (v : ι → ℝ), P.nrm2 (P.negLap v) ≤ μ * P.nrm2 v
```


### `nrm2_nonlin'_le`  (theorem, line 496)

`‖n'(p) v‖₂ ≤ (‖V‖_∞ + 3βK) ‖v‖₂` if `pᵢ² ≤ K`.

```lean
GPDYS.Setting.nrm2_nonlin'_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {K : ℝ},
  0 ≤ K →
    ∀ {p : ι → ℝ}, (∀ (i : ι), p i ^ 2 ≤ K) → ∀ (v : ι → ℝ), P.nrm2 (P.nonlin' p v) ≤ (P.Vinf + 3 * P.β * K) * P.nrm2 v
```


### `nrm2_hess_le`  (theorem, line 516)

The operator bound `‖ℋ v‖₂ ≤ (μ + ‖V‖_∞ + 3βK + λ(p)) ‖v‖₂`.

```lean
GPDYS.Setting.nrm2_hess_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {μ K : ℝ},
  0 ≤ μ →
    (∀ (x : ι → ℝ), P.kin x ≤ μ * P.nrm2sq x) →
      0 ≤ K →
        ∀ {p : ι → ℝ},
          (∀ (i : ι), p i ^ 2 ≤ K) →
            ∀ (v : ι → ℝ), P.nrm2 (P.hess p v) ≤ (μ + P.Vinf + 3 * P.β * K + P.lam p) * P.nrm2 v
```


### `nrm2_rho_le`  (theorem, line 529)

`‖ρ‖₂ ≤ βK(3‖h‖₂² + ‖h‖₂³)` for a unit vector `p`.

```lean
GPDYS.Setting.nrm2_rho_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {K : ℝ},
  0 ≤ K →
    (∀ (v : ι → ℝ) (i : ι), v i ^ 2 ≤ K * P.nrm2sq v) →
      ∀ {p : ι → ℝ}, P.nrm2sq p = 1 → ∀ (h : ι → ℝ), P.nrm2 (P.rho p h) ≤ P.β * K * (3 * P.nrm2 h ^ 2 + P.nrm2 h ^ 3)
```


### `inner_rho_eq`  (theorem, line 569)

`⟪ρ, h⟫_h = β (3 ∑ᵢ wᵢ pᵢ hᵢ³ + ∑ᵢ wᵢ hᵢ⁴)`.

```lean
GPDYS.Setting.inner_rho_eq :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p h : ι → ℝ),
  P.inner (P.rho p h) h = P.β * (3 * ∑ i, P.w i * (p i * h i ^ 3) + ∑ i, P.w i * h i ^ 4)
```


### `local_PL`  (theorem, line 579)

Theorem 5.1, local Polyak–Łojasiewicz inequality deduced after (5.8): there is `r > 0` such that
`E_h(u) - E_h(p) ≤ (1/ν)‖g(u)‖₂²` for every `u ∈ 𝓜` with `‖u - p‖₂ ≤ r`.

```lean
GPDYS.Setting.local_PL :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {p : ι → ℝ},
      P.nrm2sq p = 1 →
        (∀ (i : ι), 0 < p i) →
          P.g p = 0 →
            ∃ r,
              0 < r ∧
                ∀ (u : ι → ℝ),
                  P.nrm2sq u = 1 → P.nrm2 (u - p) ≤ r → P.energy u - P.energy p ≤ 1 / P.nu p * P.nrm2sq (P.g u)
```


### `eventually_close`  (theorem, line 667)

The iterates are eventually within any distance `r > 0` of `p`.

```lean
GPDYS.Setting.eventually_close :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {u0 : ι → ℝ},
      (∀ (i : ι), 0 < u0 i) →
        P.nrm2 u0 = 1 →
          ∀ {γ : ℝ},
            0 < γ →
              γ ≤ P.γmax u0 →
                ∀ {μ : ℝ},
                  0 ≤ μ →
                    (∀ (v : ι → ℝ), P.kin v ≤ μ * P.nrm2sq v) →
                      ∀ {p : ι → ℝ},
                        P.nrm2sq p = 1 →
                          (∀ (i : ι), 0 < p i) →
                            P.g p = 0 →
                              Filter.Tendsto (P.uiter γ u0) Filter.atTop (nhds p) →
                                ∀ {r : ℝ}, 0 < r → ∃ K, ∀ (k : ℕ), K ≤ k → P.nrm2 (P.uiter γ u0 k - p) ≤ r
```


### `η_pos`  (theorem, line 681)

`0 < η`; the upper bound is `η_lt_one`.

```lean
GPDYS.Setting.η_pos :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {u0 : ι → ℝ},
      (∀ (i : ι), 0 < u0 i) →
        P.nrm2 u0 = 1 →
          ∀ {γ : ℝ},
            0 < γ →
              γ ≤ P.γmax u0 →
                ∀ {μ : ℝ},
                  0 ≤ μ →
                    (∀ (v : ι → ℝ), P.kin v ≤ μ * P.nrm2sq v) →
                      ∀ {p : ι → ℝ},
                        P.nrm2sq p = 1 →
                          (∀ (i : ι), 0 < p i) →
                            P.g p = 0 → Filter.Tendsto (P.uiter γ u0) Filter.atTop (nhds p) → 0 < GPDYS.η γ μ (P.nu p)
```


### `η_lt_one`  (theorem, line 687)

```lean
GPDYS.Setting.η_lt_one :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {u0 : ι → ℝ},
      (∀ (i : ι), 0 < u0 i) →
        P.nrm2 u0 = 1 →
          ∀ {γ : ℝ},
            0 < γ →
              γ ≤ P.γmax u0 →
                ∀ {μ : ℝ},
                  0 ≤ μ →
                    (∀ (v : ι → ℝ), P.kin v ≤ μ * P.nrm2sq v) →
                      ∀ {p : ι → ℝ},
                        P.nrm2sq p = 1 →
                          (∀ (i : ι), 0 < p i) →
                            P.g p = 0 → Filter.Tendsto (P.uiter γ u0) Filter.atTop (nhds p) → GPDYS.η γ μ (P.nu p) < 1
```


### `rate_step`  (theorem, line 693)

Theorem 5.1, first inequality of (5.6): there is `K` such that for `k ≥ K`,
`𝓛^{k+1} - E_GS ≤ (1 - η)(𝓛^k - E_GS)`.

```lean
GPDYS.Setting.rate_step :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {u0 : ι → ℝ},
      (∀ (i : ι), 0 < u0 i) →
        P.nrm2 u0 = 1 →
          ∀ {γ : ℝ},
            0 < γ →
              γ ≤ P.γmax u0 →
                ∀ {μ : ℝ},
                  0 ≤ μ →
                    (∀ (v : ι → ℝ), P.kin v ≤ μ * P.nrm2sq v) →
                      ∀ {p : ι → ℝ},
                        P.nrm2sq p = 1 →
                          (∀ (i : ι), 0 < p i) →
                            P.g p = 0 →
                              Filter.Tendsto (P.uiter γ u0) Filter.atTop (nhds p) →
                                ∃ K,
                                  ∀ (k : ℕ),
                                    K ≤ k →
                                      P.lyap γ (P.iter γ u0 (k + 1)) - P.energy p ≤
                                        (1 - GPDYS.η γ μ (P.nu p)) * (P.lyap γ (P.iter γ u0 k) - P.energy p)
```


### `rate_theorem`  (theorem, line 749)

**Theorem 5.1**, conditional form: assume the section hypotheses, including
convergence of the iterates to the positive normalized critical point `p`, and a Rayleigh
bound `μ ≥ 0`. Then there is an index `K` such that for every `k ≥ K`,
`𝓛^{k+1} - E_GS ≤ (1-η)(𝓛^k - E_GS)` and
`E_h(u^k) - E_GS + (R^k)²/γ + (ν/4)‖u^k - u_GS‖₂² ≤ 2(1-η)^{k-K}(𝓛^K - E_GS)`.

```lean
GPDYS.Setting.rate_theorem :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {u0 : ι → ℝ},
      (∀ (i : ι), 0 < u0 i) →
        P.nrm2 u0 = 1 →
          ∀ {γ : ℝ},
            0 < γ →
              γ ≤ P.γmax u0 →
                ∀ {μ : ℝ},
                  0 ≤ μ →
                    (∀ (v : ι → ℝ), P.kin v ≤ μ * P.nrm2sq v) →
                      ∀ {p : ι → ℝ},
                        P.nrm2sq p = 1 →
                          (∀ (i : ι), 0 < p i) →
                            P.g p = 0 →
                              Filter.Tendsto (P.uiter γ u0) Filter.atTop (nhds p) →
                                ∃ K,
                                  ∀ (k : ℕ),
                                    K ≤ k →
                                      P.lyap γ (P.iter γ u0 (k + 1)) - P.energy p ≤
                                          (1 - GPDYS.η γ μ (P.nu p)) * (P.lyap γ (P.iter γ u0 k) - P.energy p) ∧
                                        P.energy (P.uiter γ u0 k) - P.energy p + P.R γ (P.iter γ u0 k) ^ 2 / γ +
                                            P.nu p / 4 * P.nrm2sq (P.uiter γ u0 k - p) ≤
                                          2 * (1 - GPDYS.η γ μ (P.nu p)) ^ (k - K) *
                                            (P.lyap γ (P.iter γ u0 K) - P.energy p)
```


### `rate_theorem'`  (theorem, line 798)

**Theorem 5.1**, self-contained form: under the hypotheses of Theorem 3.4, `N ≥ 2`, and
any Rayleigh bound `μ` for `-Δ_h`, the iterates converge to the discrete ground state `u_GS`,
the constant `ν` satisfies `ν ≥ 2β m_GS² > 0`, `0 < η < 1`, and the geometric decay (5.6) holds
from some index `K` on.

```lean
GPDYS.Setting.rate_theorem' :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {u0 : ι → ℝ},
      (∀ (i : ι), 0 < u0 i) →
        P.nrm2 u0 = 1 →
          ∀ {γ : ℝ},
            0 < γ →
              γ ≤ P.γmax u0 →
                ∀ {μ : ℝ},
                  0 ≤ μ →
                    (∀ (v : ι → ℝ), P.kin v ≤ μ * P.nrm2sq v) →
                      ∃ uGS,
                        (∀ (i : ι), 0 < uGS i) ∧
                          P.nrm2 uGS = 1 ∧
                            P.g uGS = 0 ∧
                              Filter.Tendsto (P.uiter γ u0) Filter.atTop (nhds uGS) ∧
                                2 * P.β * GPDYS.mGS uGS ^ 2 ≤ P.nu uGS ∧
                                  0 < P.nu uGS ∧
                                    0 < GPDYS.η γ μ (P.nu uGS) ∧
                                      GPDYS.η γ μ (P.nu uGS) < 1 ∧
                                        ∃ K,
                                          ∀ (k : ℕ),
                                            K ≤ k →
                                              P.lyap γ (P.iter γ u0 (k + 1)) - P.energy uGS ≤
                                                  (1 - GPDYS.η γ μ (P.nu uGS)) *
                                                    (P.lyap γ (P.iter γ u0 k) - P.energy uGS) ∧
                                                P.energy (P.uiter γ u0 k) - P.energy uGS +
                                                      P.R γ (P.iter γ u0 k) ^ 2 / γ +
                                                    P.nu uGS / 4 * P.nrm2sq (P.uiter γ u0 k - uGS) ≤
                                                  2 * (1 - GPDYS.η γ μ (P.nu uGS)) ^ (k - K) *
                                                    (P.lyap γ (P.iter γ u0 K) - P.energy uGS)
```


## `GPDYS/Spectral.lean` — μ_max as the largest eigenvalue of -Δ_h; Theorem 5.1 with μ = μ_max; ν attained


### `eq_zero_of_forall_two_mul_add_sq_mul_le`  (theorem, line 27)

If `2 t c + t² d ≤ 0` for every real `t`, then `c = 0`
(the first variation of a quadratic with a maximum at `t = 0` vanishes).

```lean
GPDYS.eq_zero_of_forall_two_mul_add_sq_mul_le :
∀ {c d : ℝ}, (∀ (t : ℝ), 2 * t * c + t ^ 2 * d ≤ 0) → c = 0
```


### `μmax`  (def, line 49)

On a nonempty mesh, `μ_max = max {⟪v, -Δ_h v⟫_h : v ∈ 𝓜}` is the largest eigenvalue
of `-Δ_h`. The empty-set value is zero.

```lean
def μmax : ℝ := sSup {x : ℝ | ∃ v : ι → ℝ, P.nrm2sq v = 1 ∧ x = P.kin v}
```

*Elaborated type:*
```lean
GPDYS.Setting.μmax :
{ι : Type u_1} → [inst : Fintype ι] → [inst_1 : DecidableEq ι] → GPDYS.Setting ι → ℝ
```


### `kin_continuous`  (theorem, line 52)

The kinetic form is continuous.

```lean
GPDYS.Setting.kin_continuous :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι), Continuous P.kin
```


### `exists_kin_max`  (theorem, line 57)

The Rayleigh quotient attains its maximum on the sphere.

```lean
GPDYS.Setting.exists_kin_max :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  ∃ v, P.nrm2sq v = 1 ∧ ∀ (w : ι → ℝ), P.nrm2sq w = 1 → P.kin w ≤ P.kin v
```


### `μmax_eq_kin_of_max`  (theorem, line 67)

If `vm ∈ 𝓜` maximizes the Rayleigh quotient on `𝓜`, then `μ_max = ⟪vm, -Δ_h vm⟫_h`.

```lean
GPDYS.Setting.μmax_eq_kin_of_max :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {vm : ι → ℝ},
  P.nrm2sq vm = 1 → (∀ (w : ι → ℝ), P.nrm2sq w = 1 → P.kin w ≤ P.kin vm) → P.μmax = P.kin vm
```


### `μmax_attained`  (theorem, line 76)

`μ_max` is attained: `μ_max = ⟪v, -Δ_h v⟫_h` for some `v ∈ 𝓜`.

```lean
GPDYS.Setting.μmax_attained :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  ∃ v, P.nrm2sq v = 1 ∧ P.kin v = P.μmax
```


### `kin_le_μmax`  (theorem, line 81)

The Rayleigh bound `⟪v, -Δ_h v⟫_h ≤ μ_max ‖v‖₂²` for every `v`.

```lean
GPDYS.Setting.kin_le_μmax :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] (v : ι → ℝ),
  P.kin v ≤ P.μmax * P.nrm2sq v
```


### `μmax_nonneg`  (theorem, line 97)

```lean
GPDYS.Setting.μmax_nonneg :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι], 0 ≤ P.μmax
```


### `μmax_isEigenvalue`  (theorem, line 105)

`μ_max` is an eigenvalue of `-Δ_h`: `-Δ_h v = μ_max v` for a maximizer `v ∈ 𝓜` of the
Rayleigh quotient.

```lean
GPDYS.Setting.μmax_isEigenvalue :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  ∃ v, P.nrm2sq v = 1 ∧ P.negLap v = P.μmax • v
```


### `eigenvalue_le_μmax`  (theorem, line 129)

Every eigenvalue of `-Δ_h` is at most `μ_max`.

```lean
GPDYS.Setting.eigenvalue_le_μmax :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι] {v : ι → ℝ},
  v ≠ 0 → ∀ {l : ℝ}, P.negLap v = l • v → l ≤ P.μmax
```


### `rate_theorem_μmax`  (theorem, line 138)

**Theorem 5.1** with `μ = μ_max`, the largest eigenvalue of `-Δ_h`, exactly as in the paper:
the iterates converge to the discrete ground state `u_GS`, `ν ≥ 2β m_GS² > 0`, the rate
`η = min{γν/(4(1+γμ_max)), 1/2}` satisfies `0 < η < 1`, and (5.6) holds from some index `K` on.

```lean
GPDYS.Setting.rate_theorem_μmax :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  2 ≤ Fintype.card ι →
    ∀ {u0 : ι → ℝ},
      (∀ (i : ι), 0 < u0 i) →
        P.nrm2 u0 = 1 →
          ∀ {γ : ℝ},
            0 < γ →
              γ ≤ P.γmax u0 →
                ∃ uGS,
                  (∀ (i : ι), 0 < uGS i) ∧
                    P.nrm2 uGS = 1 ∧
                      P.g uGS = 0 ∧
                        Filter.Tendsto (P.uiter γ u0) Filter.atTop (nhds uGS) ∧
                          2 * P.β * GPDYS.mGS uGS ^ 2 ≤ P.nu uGS ∧
                            0 < P.nu uGS ∧
                              0 < GPDYS.η γ P.μmax (P.nu uGS) ∧
                                GPDYS.η γ P.μmax (P.nu uGS) < 1 ∧
                                  ∃ K,
                                    ∀ (k : ℕ),
                                      K ≤ k →
                                        P.lyap γ (P.iter γ u0 (k + 1)) - P.energy uGS ≤
                                            (1 - GPDYS.η γ P.μmax (P.nu uGS)) *
                                              (P.lyap γ (P.iter γ u0 k) - P.energy uGS) ∧
                                          P.energy (P.uiter γ u0 k) - P.energy uGS + P.R γ (P.iter γ u0 k) ^ 2 / γ +
                                              P.nu uGS / 4 * P.nrm2sq (P.uiter γ u0 k - uGS) ≤
                                            2 * (1 - GPDYS.η γ P.μmax (P.nu uGS)) ^ (k - K) *
                                              (P.lyap γ (P.iter γ u0 K) - P.energy uGS)
```


### `hessForm_continuous`  (theorem, line 154)

The Hessian form `w ↦ ⟪w, ℋ w⟫_h` is continuous.

```lean
GPDYS.Setting.hessForm_continuous :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p : ι → ℝ),
  Continuous (P.hessForm p)
```


### `inner_continuous`  (theorem, line 159)

`w ↦ ⟪p, w⟫_h` is continuous.

```lean
GPDYS.Setting.inner_continuous :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (p : ι → ℝ),
  Continuous fun w => P.inner p w
```


### `nu_attained`  (theorem, line 165)

`ν` is attained: it is the minimum of `⟪w, ℋ w⟫_h` over the unit tangent vectors `w ∈ 𝓜`,
`⟪p, w⟫_h = 0`, as in the paper.

```lean
GPDYS.Setting.nu_attained :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι),
  2 ≤ Fintype.card ι →
    ∀ {p : ι → ℝ},
      P.nrm2sq p = 1 →
        (∀ (i : ι), 0 < p i) → P.g p = 0 → ∃ w, P.nrm2sq w = 1 ∧ P.inner p w = 0 ∧ P.hessForm p w = P.nu p
```


## `GPDYS/Sign.lean` — Remark 2.3: uniqueness of the minimizer up to sign (irreducibility from the positive resolvent)


### `MS_mulVec_apply`  (theorem, line 32)

The `i`-th component of `(M + γ S) x`.

```lean
GPDYS.Setting.MS_mulVec_apply :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (γ : ℝ) (x : ι → ℝ) (i : ι),
  (P.M + γ • P.S).mulVec x i = P.w i * x i + γ * ∑ j, P.S i j * x j
```


### `S_irreducible`  (theorem, line 40)

Irreducibility of `S` (connectivity of the mesh), derived from the entrywise positivity of the
resolvent: for every proper nonempty subset `A` of the indices there are `i ∈ A` and `j ∉ A` with
`S i j ≠ 0`.

```lean
GPDYS.Setting.S_irreducible :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) (A : Finset ι),
  A.Nonempty → Aᶜ.Nonempty → ∃ i ∈ A, ∃ j ∉ A, P.S i j ≠ 0
```


### `same_sign_of_kin_le`  (theorem, line 90)

If `v` has no zero component and `vᵀ S v ≤ |v|ᵀ S |v|`, then all components of `v` have the
same sign.

```lean
GPDYS.Setting.same_sign_of_kin_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {v : ι → ℝ},
  (∀ (i : ι), v i ≠ 0) → (P.kin v ≤ P.kin fun i => |v i|) → (∀ (i : ι), 0 < v i) ∨ ∀ (i : ι), v i < 0
```


### `eq_or_eq_neg_of_energy_le`  (theorem, line 153)

Remark 2.3, uniqueness up to sign: if `u > 0` is a critical point of `E_h` on `𝓜` and
`v ∈ 𝓜` satisfies `E_h(v) ≤ E_h(u)`, then `v = u` or `v = -u`.

```lean
GPDYS.Setting.eq_or_eq_neg_of_energy_le :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) {u v : ι → ℝ},
  P.nrm2sq u = 1 → (∀ (i : ι), 0 < u i) → P.g u = 0 → P.nrm2sq v = 1 → P.energy v ≤ P.energy u → v = u ∨ v = -u
```


### `exists_groundState_sign`  (theorem, line 189)

**Remark 2.3** in full: there is a positive `u_GS ∈ 𝓜` which is a critical point of `E_h|_𝓜`,
the global minimizer of `E_h` on `𝓜`, the unique nonnegative critical point, and the minimizer is
unique up to sign: every minimizer of `E_h` on `𝓜` is `u_GS` or `-u_GS`.

```lean
GPDYS.Setting.exists_groundState_sign :
∀ {ι : Type u_1} [inst : Fintype ι] [inst_1 : DecidableEq ι] (P : GPDYS.Setting ι) [Nonempty ι],
  ∃ uGS,
    (∀ (i : ι), 0 < uGS i) ∧
      P.nrm2 uGS = 1 ∧
        P.g uGS = 0 ∧
          (∀ (v : ι → ℝ), P.nrm2 v = 1 → P.energy uGS ≤ P.energy v) ∧
            (∀ (v : ι → ℝ), P.nrm2 v = 1 → (∀ (i : ι), 0 ≤ v i) → P.g v = 0 → v = uGS) ∧
              ∀ (v : ι → ℝ), P.nrm2 v = 1 → P.energy v ≤ P.energy uGS → v = uGS ∨ v = -uGS
```
