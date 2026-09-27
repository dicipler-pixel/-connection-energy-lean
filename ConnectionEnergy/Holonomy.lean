/-
Non-normality is connection energy (Jeromie Beasley, 17 September 2026, DOI
10.5281/zenodo.22804072): the connection and holonomy statements.

* The induced edge transport `Uᵢⱼ(X) = Aᵢⱼ X Aᵢⱼ†` ignores the central sign (`U` of `−A` is `U`
  of `A`), and `Aⱼᵢ = −Aᵢⱼ†` gives `Uⱼᵢ = Uᵢⱼ⁻¹`: `U` is a connection on `End(E)`.
* Parallel transport along a walk composes: if `Dᵥ = Aᵥᵥ' Dᵥ' Aᵥᵥ'†` along every step, then the
  start equals `W D_end W†` with `W` the product of the edge matrices.
* Around a loop a parallel section is fixed by the holonomy, `W D W† = D`, which for unitary `W`
  is exactly `[D, W] = 0`.
* The scalar specialisation (`r = 1`): a unit-modulus link transports a scalar to itself, so each
  edge term reduces to `|dᵢ − dⱼ|²`, the weighted Dirichlet energy.
-/
import ConnectionEnergy.Basic

namespace ConnectionEnergy

open Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The induced edge transport on `End(E)`: `U_A(X) = A X A†`. -/
def edgeTransport (A X : Matrix m m ℂ) : Matrix m m ℂ := A * X * Aᴴ

/-- **The central sign cancels.** `U_{−A} = U_A`. -/
theorem transport_neg (A X : Matrix m m ℂ) : edgeTransport (-A) X = edgeTransport A X := by
  simp [edgeTransport, conjTranspose_neg]

/-- **`Uⱼᵢ = Uᵢⱼ⁻¹`.** With `Aⱼᵢ = −Aᵢⱼ†` and `Aᵢⱼ` unitary, transporting along the edge and
back is the identity, in both orders. -/
theorem transport_inverse (A X : Matrix m m ℂ) (h1 : A * Aᴴ = 1) (h2 : Aᴴ * A = 1) :
    edgeTransport (-Aᴴ) (edgeTransport A X) = X ∧ edgeTransport A (edgeTransport (-Aᴴ) X) = X := by
  constructor
  · rw [transport_neg]
    unfold edgeTransport
    rw [conjTranspose_conjTranspose]
    calc Aᴴ * (A * X * Aᴴ) * A = (Aᴴ * A) * X * (Aᴴ * A) := by noncomm_ring
      _ = X := by rw [h2, one_mul, mul_one]
  · rw [transport_neg]
    unfold edgeTransport
    rw [conjTranspose_conjTranspose]
    calc A * (Aᴴ * X * A) * Aᴴ = (A * Aᴴ) * X * (A * Aᴴ) := by noncomm_ring
      _ = X := by rw [h1, one_mul, mul_one]

/-- The end of a walk: each step is a pair (edge matrix, next obstruction block). -/
def walkEnd : Matrix m m ℂ → List (Matrix m m ℂ × Matrix m m ℂ) → Matrix m m ℂ
  | D, [] => D
  | _, (_, D') :: rest => walkEnd D' rest

/-- The walk is parallel when each block is the transport of the next. -/
def Parallel : Matrix m m ℂ → List (Matrix m m ℂ × Matrix m m ℂ) → Prop
  | _, [] => True
  | D, (A, D') :: rest => D = A * D' * Aᴴ ∧ Parallel D' rest

/-- **Parallel transport composes.** Along a parallel walk, `D_start = W D_end W†` with `W` the
ordered product of the edge matrices. -/
theorem parallel_along : ∀ (D : Matrix m m ℂ) (path : List (Matrix m m ℂ × Matrix m m ℂ)),
    Parallel D path → D = (path.map Prod.fst).prod * walkEnd D path * ((path.map Prod.fst).prod)ᴴ
  | D, [], _ => by simp [walkEnd]
  | D, (A, D') :: rest, h => by
    obtain ⟨hstep, hrest⟩ := h
    have ih := parallel_along D' rest hrest
    simp only [List.map_cons, List.prod_cons, walkEnd, conjTranspose_mul]
    rw [hstep]
    conv_lhs => rw [ih]
    simp only [Matrix.mul_assoc]

/-- For unitary `W`, being fixed by `Ad W` is the same as commuting with `W`. -/
theorem ad_fixed_iff_commute (W X : Matrix m m ℂ) (h1 : W * Wᴴ = 1) (h2 : Wᴴ * W = 1) :
    W * X * Wᴴ = X ↔ X * W = W * X := by
  constructor
  · intro h
    calc X * W = (W * X * Wᴴ) * W := by rw [h]
      _ = W * X * (Wᴴ * W) := by noncomm_ring
      _ = W * X := by rw [h2, mul_one]
  · intro h
    calc W * X * Wᴴ = X * W * Wᴴ := by rw [h]
      _ = X * (W * Wᴴ) := by noncomm_ring
      _ = X := by rw [h1, mul_one]

/-- **Holonomy.** Around a parallel loop (the walk returns to its starting block), the base
block is fixed by the holonomy: `W D W† = D`, and for unitary `W` this is `[D, W] = 0`. -/
theorem parallel_loop_commutes (D : Matrix m m ℂ) (path : List (Matrix m m ℂ × Matrix m m ℂ))
    (hpar : Parallel D path) (hloop : walkEnd D path = D)
    (h1 : (path.map Prod.fst).prod * ((path.map Prod.fst).prod)ᴴ = 1)
    (h2 : ((path.map Prod.fst).prod)ᴴ * (path.map Prod.fst).prod = 1) :
    D * (path.map Prod.fst).prod = (path.map Prod.fst).prod * D := by
  have h := parallel_along D path hpar
  rw [hloop] at h
  exact (ad_fixed_iff_commute _ D h1 h2).mp h.symm

/-- **The scalar specialisation.** For `r = 1` a unit-modulus link transports a scalar to
itself, so the edge term `dᵢ − a dⱼ ā` is `dᵢ − dⱼ`: the weighted Dirichlet energy. -/
theorem scalar_dirichlet (a di dj : ℂ) (ha : a * (starRingEnd ℂ) a = 1) :
    di - a * dj * (starRingEnd ℂ) a = di - dj := by
  rw [mul_comm a dj, mul_assoc, ha, mul_one]

end ConnectionEnergy
