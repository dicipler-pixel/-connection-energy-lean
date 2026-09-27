<div align="center">

# Non-Normality Is Connection Energy — Lean proofs

**The note's identity and its normality criterion, checked by the Lean kernel on every push.**

[![Lean proof check](https://github.com/dicipler-pixel/-connection-energy-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/-connection-energy-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-14-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.22803572-blue)](https://doi.org/10.5281/zenodo.22803572)

Jeromie Beasley

</div>

---

## The idea in one line

Put Hermitian blocks `Dᵢ` on the vertices of a graph and unitary transports `Aᵢⱼ` on its edges,
with `A† = −A`. The operator `H = D + A` fails to be normal by exactly the amount `D` fails to
be parallel under the induced transport `X ↦ Aᵢⱼ X Aᵢⱼ†`:

```
⅛ ‖[H, H†]‖²  =  Σ over edges ‖Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†‖²
```

## What is proved

| Note | Result | Theorem |
| :--- | :--- | :--- |
| Setup | `H† = D − A` from Hermitian `D` and anti-Hermitian `A` | `conjTranspose_H` |
| Step 1 | `[H, H†] = −2 [D, A]` | `self_commutator` |
| Step 2 | `[D, A]ᵢⱼ = Dᵢ Aᵢⱼ − Aᵢⱼ Dⱼ = (Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†) Aᵢⱼ` on every edge | `commutator_block`, `edge_factor` |
| Step 3 | Unitary invariance of the Frobenius norm | `frob_mul_unitary`, `frob_unitary_conj` |
| (1) | `‖[H, H†]‖² = 4 Σ_{i∼j} ‖Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†‖²` over ordered adjacent pairs | `energy_identity` |
| (1) | The two orientations of an edge give the same term, so the ordered sum is twice the edge sum and `⅛ ‖[H, H†]‖² = Σ_edges ‖Dᵢ − Aᵢⱼ Dⱼ Aᵢⱼ†‖²` | `orientation_symm` |
| (2) | `H` is normal exactly when `Dᵢ = Aᵢⱼ Dⱼ Aᵢⱼ†` on every edge | `normal_iff_parallel` |
| — | The Frobenius energy is the sum of squared moduli of the entries | `frob_eq_sum` |

The file is [`ConnectionEnergy/Basic.lean`](ConnectionEnergy/Basic.lean). What is not proved is
in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*Non-Normality Is Connection Energy*, Jeromie Beasley. DOI
[10.5281/zenodo.22803572](https://doi.org/10.5281/zenodo.22803572).

## Citation, licence and AI use

Citation metadata is in [`CITATION.cff`](CITATION.cff). The Lean code is released under the [MIT License](LICENSE) and the written text under [CC BY 4.0](LICENSE-CC-BY-4.0.md); see [`LICENSING.md`](LICENSING.md). How AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
