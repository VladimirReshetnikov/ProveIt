# Exploratory selector-position mask classes

For the fixed *symbolic* low mask `lowNat`, the source proves two
finite-index facts in an arbitrary `IΣ₁` model. Put `ρ=Exp.exp 67`.

* If the standard natural index `j<943` and `j≠1`, the mask digit at `j` is
  `ρ−2`.
* If the standard natural index `j<8807` is absent from the finite support
  and `j≠1063`, the mask digit at `j` is `ρ−1`.

The second fact applies in particular to index 1 once its support exclusion
and inequality are supplied. The proof uses the exact symbolic finite
support and the model `dig_ofDigits` interface; it does not itself bind that
mask to retained bytes or prove a selector digit bound. A separate client must
combine these facts with the previous per-position `NoCarry` theorem, with
explicit `0<k`, `k<8807*N` and `k%8807=(j:V)`, and handle position `k=0`
separately using the origin theorem.

Single-side exploratory session 40324 exited 0 without warnings; the two
exact named reports are `[propext, Classical.choice, Quot.sound]`. Source,
object, command and observed output are recorded in `observation.txt`. The
scratch author overlay is not a guarded paired build or independent artifact
audit. This result does not construct a word, prove fractional rotation or a
clean carry, instantiate the 943-row decoder, establish machine correctness,
or yield an internal iPRA proof.

Before the successful source, session 55495 failed because the
`ArithmeticMaskConstants` namespace was not opened. Sessions 77879, 32304
and 70344 failed on natural-one casts; session 62664 failed on recursion depth
when a direct fixed-index `change` expanded the large constant. The final
proof states the absent-index lemma generically and simplifies the cast of 1
in the hypothesis. The retained attempt 01 is a reconstruction of the initial
source from the recorded edits; attempt 05 is the immediately preceding
source reconstructed by removing the final cast simplification. None of the
failed sessions establishes its failed theorem.
