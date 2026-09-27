/-
Non-normality is connection energy (Jeromie Beasley, DOI 10.5281/zenodo.22804072).

A finite graph `G` on vertices `V`, blocks of size `m`. The operator is a `V × V` block matrix
`H = D + A`: `D = diag(Dᵢ)` with Hermitian blocks, and `A` anti-Hermitian (`A† = −A`),
supported on edges, with a unitary block `Aᵢⱼ` on every edge. Proved here:

* `[H, H†] = −2 [D, A]` and `[D, A]ᵢⱼ = Dᵢ Aᵢⱼ − Aᵢⱼ Dⱼ = (Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†) Aᵢⱼ`;
* the energy identity: the Frobenius self-commutator energy equals four times the sum, over
  ordered adjacent pairs, of `‖Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†‖²`, and the two orientations of an edge give
  equal terms. Hence `⅛ ‖[H, H†]‖² = Σ_{edges} ‖Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†‖²`, equation (1) of the note;
* normality: `H` is normal exactly when `Dᵢ = Aᵢⱼ Dⱼ Aᵢⱼ†` on every edge, equation (2) —
  `D` is parallel for the induced connection on `End(E)`.
-/
import Mathlib

namespace ConnectionEnergy

open Matrix

variable {V m : Type*} [Fintype V] [DecidableEq V] [Fintype m] [DecidableEq m]

/-- Frobenius norm squared, `‖Y‖² = Re Tr(Y Y†)`. -/
noncomputable def frob (Y : Matrix m m ℂ) : ℝ := (trace (Y * Yᴴ)).re

/-- The Frobenius norm squared is the sum of the squared moduli of the entries. -/
theorem frob_eq_sum (Y : Matrix m m ℂ) : frob Y = ∑ a, ∑ b, Complex.normSq (Y a b) := by
  unfold frob
  simp only [trace, diag_apply, mul_apply, conjTranspose_apply, RCLike.star_def,
    Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]

/-- Block energy of a block matrix: the sum of the Frobenius energies of its blocks, i.e. the
Frobenius norm squared of the full matrix. -/
noncomputable def energy (X : Matrix V V (Matrix m m ℂ)) : ℝ := ∑ i, ∑ j, frob (X i j)

theorem frob_mul_unitary (X U : Matrix m m ℂ) (hU : U * Uᴴ = 1) : frob (X * U) = frob X := by
  unfold frob
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU, Matrix.one_mul]

theorem frob_unitary_conj (X U : Matrix m m ℂ) (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) :
    frob (Uᴴ * X * U) = frob X := by
  rw [frob_mul_unitary _ _ hU]
  unfold frob
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, trace_mul_comm Uᴴ,
    Matrix.mul_assoc, Matrix.mul_assoc, hU, Matrix.mul_one]

theorem frob_neg (Y : Matrix m m ℂ) : frob (-Y) = frob Y := by
  unfold frob
  rw [conjTranspose_neg, neg_mul_neg]

theorem frob_neg_double (Y : Matrix m m ℂ) : frob (-(Y + Y)) = 4 * frob Y := by
  unfold frob
  have h : -(Y + Y) * (-(Y + Y))ᴴ = Y * Yᴴ + Y * Yᴴ + (Y * Yᴴ + Y * Yᴴ) := by
    rw [conjTranspose_neg, conjTranspose_add]
    noncomm_ring
  rw [h]
  simp only [trace_add, Complex.add_re]
  ring

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The hypotheses of the note. -/
structure Transport (D : V → Matrix m m ℂ) (A : Matrix V V (Matrix m m ℂ)) : Prop where
  herm : ∀ i, (D i)ᴴ = D i
  anti : Aᴴ = -A
  unitary : ∀ i j, G.Adj i j → A i j * (A i j)ᴴ = 1 ∧ (A i j)ᴴ * A i j = 1
  support : ∀ i j, ¬ G.Adj i j → A i j = 0

variable {G}

/-- `H† = D − A`. -/
theorem conjTranspose_H {D : V → Matrix m m ℂ} {A : Matrix V V (Matrix m m ℂ)}
    (h : Transport G D A) : (diagonal D + A)ᴴ = diagonal D - A := by
  rw [conjTranspose_add, diagonal_conjTranspose, h.anti, sub_eq_add_neg]
  congr 2
  funext i
  exact h.herm i

/-- **`[H, H†] = −2 [D, A]`.** -/
theorem self_commutator {D : V → Matrix m m ℂ} {A : Matrix V V (Matrix m m ℂ)}
    (h : Transport G D A) :
    (diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A) =
      -((diagonal D * A - A * diagonal D) + (diagonal D * A - A * diagonal D)) := by
  rw [conjTranspose_H h]
  noncomm_ring

/-- The blocks of `[D, A]`. -/
theorem commutator_block (D : V → Matrix m m ℂ) (A : Matrix V V (Matrix m m ℂ)) (i j : V) :
    (diagonal D * A - A * diagonal D) i j = D i * A i j - A i j * D j := by
  rw [Matrix.sub_apply, diagonal_mul, mul_diagonal]

/-- On an edge, `[D, A]ᵢⱼ = (Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†) Aᵢⱼ`. -/
theorem edge_factor {D : V → Matrix m m ℂ} {A : Matrix V V (Matrix m m ℂ)}
    (h : Transport G D A) {i j : V} (hij : G.Adj i j) :
    D i * A i j - A i j * D j = (D i - A i j * D j * (A i j)ᴴ) * A i j := by
  rw [Matrix.sub_mul, Matrix.mul_assoc (A i j * D j), (h.unitary i j hij).2, Matrix.mul_one]

/-- Each edge term of the energy. -/
theorem edge_energy {D : V → Matrix m m ℂ} {A : Matrix V V (Matrix m m ℂ)}
    (h : Transport G D A) (i j : V) :
    frob (D i * A i j - A i j * D j) =
      if G.Adj i j then frob (D i - A i j * D j * (A i j)ᴴ) else 0 := by
  split_ifs with hij
  · rw [edge_factor h hij, frob_mul_unitary _ _ (h.unitary i j hij).1]
  · rw [h.support i j hij, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    simp [frob]

/-- **The energy identity.** `‖[H, H†]‖² = 4 Σ_{i ~ j} ‖Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†‖²` over ordered
adjacent pairs. -/
theorem energy_identity {D : V → Matrix m m ℂ} {A : Matrix V V (Matrix m m ℂ)}
    (h : Transport G D A) :
    energy ((diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)) =
      4 * ∑ i, ∑ j, if G.Adj i j then frob (D i - A i j * D j * (A i j)ᴴ) else 0 := by
  rw [self_commutator h]
  unfold energy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.neg_apply, Matrix.add_apply, commutator_block, frob_neg_double, edge_energy h]

/-- **The two orientations of an edge give the same term.** -/
theorem orientation_symm {D : V → Matrix m m ℂ} {A : Matrix V V (Matrix m m ℂ)}
    (h : Transport G D A) {i j : V} (hij : G.Adj i j) :
    frob (D j - A j i * D i * (A j i)ᴴ) = frob (D i - A i j * D j * (A i j)ᴴ) := by
  obtain ⟨hU1, hU2⟩ := h.unitary i j hij
  have hji : A j i = -(A i j)ᴴ := by
    have e := congrFun (congrFun h.anti i) j
    rw [conjTranspose_apply, Matrix.neg_apply, star_eq_conjTranspose] at e
    rw [← conjTranspose_conjTranspose (A j i), e, conjTranspose_neg]
  rw [hji, conjTranspose_neg, conjTranspose_conjTranspose]
  have e : (A i j)ᴴ * (A i j * D j * (A i j)ᴴ) * A i j = D j := by
    simp only [← Matrix.mul_assoc]
    rw [hU2, Matrix.one_mul, Matrix.mul_assoc, hU2, Matrix.mul_one]
  have key : D j - -(A i j)ᴴ * D i * -A i j =
      -((A i j)ᴴ * (D i - A i j * D j * (A i j)ᴴ) * A i j) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, e]
    noncomm_ring
  rw [key, frob_neg, frob_unitary_conj _ _ hU1 hU2]

theorem double_eq_zero_iff (X : Matrix V V (Matrix m m ℂ)) : X + X = 0 ↔ X = 0 := by
  constructor
  · intro hc
    ext i j a b
    have := congrFun (congrFun (congrFun (congrFun hc i) j) a) b
    simp only [Matrix.add_apply, Matrix.zero_apply] at this
    exact add_self_eq_zero.mp this
  · intro hc
    rw [hc, add_zero]

/-- **Normality (equation (2)).** `H` is normal exactly when `D` is parallel along every edge:
`Dᵢ = Aᵢⱼ Dⱼ Aᵢⱼ†`. -/
theorem normal_iff_parallel {D : V → Matrix m m ℂ} {A : Matrix V V (Matrix m m ℂ)}
    (h : Transport G D A) :
    (diagonal D + A) * (diagonal D + A)ᴴ = (diagonal D + A)ᴴ * (diagonal D + A) ↔
      ∀ i j, G.Adj i j → D i = A i j * D j * (A i j)ᴴ := by
  rw [← sub_eq_zero, self_commutator h, neg_eq_zero, double_eq_zero_iff]
  constructor
  · intro hc i j hij
    have hb := congrFun (congrFun hc i) j
    rw [commutator_block, Matrix.zero_apply, edge_factor h hij] at hb
    have := congrArg (· * (A i j)ᴴ) hb
    simp only [Matrix.zero_mul, Matrix.mul_assoc, (h.unitary i j hij).1, Matrix.mul_one] at this
    rw [sub_eq_zero.mp this, Matrix.mul_assoc]
  · intro hp
    ext1 i j
    rw [commutator_block, Matrix.zero_apply]
    by_cases hij : G.Adj i j
    · rw [edge_factor h hij, ← hp i j hij, sub_self, Matrix.zero_mul]
    · rw [h.support i j hij, Matrix.mul_zero, Matrix.zero_mul, sub_zero]

end ConnectionEnergy
