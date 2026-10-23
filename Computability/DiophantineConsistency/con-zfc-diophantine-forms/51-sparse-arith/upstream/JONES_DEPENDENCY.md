# The inherited Jones ratio theorem: exact source and proof status

The nine-variable construction invokes the two explicitly proved theorems
`Jones1982.Nine.ratio_sound` and `Jones1982.Nine.ratio_complete` in the pinned
ProveIt file

    Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean

Both theorem declarations and their full `by` proofs are included here at
`JONES_RATIO_LEAN/Diophantine/Paper1982/NineRatio.lean`. They are not axiom
declarations. Their non-Mathlib local import closure consists of 20 Lean
files, all included under `JONES_RATIO_LEAN/Diophantine/`. The closure map is
`JONES_RATIO_LEAN/CLOSURE.json`; exact hashes and repository paths are in
`../provenance/JONES_SOURCES.json`.

## What the inherited theorem says

The free values `R,N,b,g,G` are nonnegative integers. Assume
`R,N >= 8`, `0 < b <= R`, and `b <= N`. The auxiliary values `h,s,w,i,j`
are positive integers, while `phi` is nonnegative. With the literal
definitions in `NineRatio.lean`, write the following four conditions:

1. `(P^2-1)K^2+1` is a square.
2. `D F I` is a square.
3. `J F` divides `Q F + J(H-C)`.
4. `K^2 G - 4(C-KY)^2 G - 8gK^2 > 0`.

The soundness theorem assumes `G > 0` and these four conditions. It proves
`N^2 | binomial(2R,R)`, that `b` is a power of two, and `8g < G`.

The completeness theorem assumes `N^2 | binomial(2R,R)`, that `b` is a
power of two, and `32g < G`. It constructs auxiliary values with the
required positive/nonnegative domains satisfying the same four conditions.
The constants 8 and 32 on the two sides are deliberately different.

The literal definition of the source-code bound `G` and the hypotheses
needed to apply both directions are discharged in `../nine/PROOF.md`.
The new packed successor word appears only in the source square; the
ratio theorem still receives the actual unknown `g`.

## Where the underlying ratio and Pell arguments are proved

`NineRatio.lean` proves the combined four-condition statement from:

- `Diophantine/Paper1982/Ratio.lean`: `lemma_2_25` and
  `exists_B25core`, including the quantitative central-binomial/Pell ratio
  estimates used to stack the ceiling for `g`.
- `Diophantine/Paper1982/ProductPell.lean`: `lemma_2_27`, which supplies the
  product-of-Pell-squares representation and congruence.

These files likewise contain theorem proofs. Their local dependencies
through the 1976, 1978, 1982, and 1984 developments and the common Pell
files are part of the included closure. A source scan of the complete
20-file closure found no `axiom`, `sorry`, `admit`, or `unsafe` tokens.
The snapshot was also authenticated against the pinned Git blob identifiers.

## What has and has not been checked for this release

The inherited source snapshot records ordinary theorem statements and
full Lean proof scripts, rather than an assumed ratio-theorem interface.
This release has checked the source dependency closure, exact file hashes,
and correspondence of the theorem hypotheses with the new mathematical
argument. **It has not rerun Lean's kernel on the snapshot.** Absence of
placeholder tokens is a source audit, not a substitute for kernel checking.

The upstream build metadata is preserved under
`JONES_RATIO_LEAN/upstream_build_metadata/`: Lean version `v4.32.0` and
Mathlib commit `81a5d257c8e410db227a6665ed08f64fea08e997` are pinned there.
Mathlib itself is an external standard-library dependency and is not copied
into this archive. The upstream lakefile describes the original complete
ProveIt project; it is retained as provenance, not represented as a standalone
build configuration for this source snapshot.

The new sparse-source construction and its composition with this inherited
ratio theorem remain ordinary mathematical proofs. No new end-to-end
formal proof from the exact released polynomial to Con(ZFC) is claimed.
