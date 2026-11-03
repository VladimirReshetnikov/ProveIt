# Trace75 first/main index alignment

`Trace75IndexAlignment.graph_first_main_alignment` proves, in any IΣ₁
model with β≥31, `MC<β`, `MF<2β`, and a positive trace75 zero, that there
is a positive first Pell index `n` satisfying the exact first ordinate
equation, `n<rankNat`, and `2*n=rankNat+1`; the same result also states
the main ordinate equation at `rankNat`. The first Pell parameter is the
actual unscaled `XY²`, and `K0` is arbitrary.

The proof compares the first and main Pell bases to establish `n<rankNat`,
then combines the q⁴ congruence with `rankNat+1<q⁴` and the remainder
decomposition. It does not assert a power identity, machine halt or an
iPRA equivalence.

Accepted `run-indexalignment-v2.py`, `observations/indexalignment-attempt02/`:
Lean exit 0, no warning/error; object
`/tmp/trace75-indexalignment-w8cm68g2/Trace75IndexAlignment.olean`, SHA-256
`b1ebde37ca118b5262b4c4b5c023feb9192622c40e42ee173169b4936caa7a49`.
The retained attempt 01 failed on the ordering of additions in one strict
inequality and reported `sorryAx`; the accepted attempt uses a commutativity
normalization and reports only `propext`, `Classical.choice`, `Quot.sound`.
Selected direct imports are pinned; inherited transitive/package ancestry
and external graph/file binding are not established by this check.
