# The Baker–Campbell–Hausdorff formula

Articles and a Lean 4 formalization of the Baker–Campbell–Hausdorff (BCH)
formula: for `X`, `Y` in a real or complex Banach algebra with
`‖X‖ + ‖Y‖ < log 2`, `log(e^X e^Y)` is the sum of the homogeneous Lie
polynomials `Z_n(X, Y)`, and formally `log(e^X e^Y)` lies in the completed free
Lie algebra on `X`, `Y`.

| Path | Contents |
| --- | --- |
| [`docs/combined/`](docs/combined/) | the combined article *The Baker–Campbell–Hausdorff Formula: A Unified Treatment with Complete Proofs, All-Order Expansions, and Analytic Qualifications* (`bch_combined.pdf`), which consolidates the three papers below and applies the corrections of three independent referee reviews; exact coefficient tables through degree 12, Zassenhaus tree polynomials, and the code that regenerates and rechecks them |
| [`docs/paper-1/`](docs/paper-1/), [`docs/paper-2/`](docs/paper-2/), [`docs/paper-3/`](docs/paper-3/) | three independent treatments of the mathematics on the English Wikipedia page "Baker–Campbell–Hausdorff formula" (revision 1368909113), each with its own exact verifier and data |
| [`Lean/`](Lean/) | the Lean library `BCH`: the formula itself as one capstone theorem in its formal and analytic forms (`BCH.bch_formula_formal`, `BCH.bch_formula`), with Campbell's identity, Duhamel's formula, the Bernoulli coefficients, Dynkin–Specht–Wever and Dynkin's formula, convergence and uniqueness of the BCH series, closed forms of `Z_1`–`Z_6`, Lie–Trotter and Strang splitting with explicit errors, and the trace identity. There is no `sorry`; `#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound`. Appendix D of the combined article maps its statements to the article. |

The Lean library is part of the ProveIt root workspace (`lake build BCH`,
built one target at a time; see [`Lean/README.md`](Lean/README.md)). It is not
imported by `ProveIt.lean`. On 4 October 2026 it was built there from the
Mathlib cache (Lean 4.32.0, Mathlib `81a5d257`): all 30 modules, with no
errors, warnings or `sorry`, and `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound` for both `BCH.bch_formula` and
`BCH.bch_formula_formal`.

## Provenance

Merged into ProveIt on 4 October 2026, with its history, from the repository
[VladimirReshetnikov/BCH](https://github.com/VladimirReshetnikov/BCH) at
`55bca2e` (17 September 2026); its `lean/` directory is `Lean/` here. The
articles were prepared with AI assistance on 16 September 2026 and the
formalization on 17 September 2026.
