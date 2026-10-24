# Combined integer-variable reductions

Seven completed literal sum-of-squares equations are supplied: two quartics in 37 integers, a sextic in 30, an octic in 26, and degree 10/12/16 forms in 25/24/23 integers. Spaces in these counts are purely prose conventions: each packet contains the full ordered list of integer unknowns.

Read PROOF.md for the mathematical theorem and dependency boundary. BINDING.json binds all six fixed integer coefficients to actual compressed payloads. Every fixed numeral is independent of whether ZFC is consistent. MF is already shifted and must not be shifted again.

## Reproduction

- `python check.py` uses Python's standard library only. It authenticates every retained source and all six actual fixed integer payloads, then independently replays 630 signed modular literal/compact-formula cases, 10,000 nearest-square witnesses and 35,301 signed guard triples.
- `python -O check.py` performs the same checks; no acceptance condition relies on an assert statement.
- `python build.py` regenerates all seven JSON packets using SymPy 1.14 or compatible. This newly authored generator reads upstream JSON through a restricted parser, performs exact algebra and degree checking, and never imports upstream code. `python -O build.py` is also supported.

The inherited coefficient generator is retained as source evidence only; neither component entrypoint executes it. Complete native/compiler semantics are inherited mathematical theorems. No new end-to-end Lean/Rocq or object-language ZFC certificate is claimed. Finite checks do not replace universal proofs or decide consistency.

The direct 37-variable quartic is smaller as a literal expression; the affine 37-variable quartic is the parent for exact projections. All higher-degree packets use the same complete six-numeral binding. The two sign-merging transformations preserve existence, while each displayed monic coordinate projection is a bijection of integer zero sets.
