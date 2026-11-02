# Fractional rotation and the clean-column predecessor

This is an external finite calculation, not a model theorem, a counterexample
to the equation's correctness, or an iPRA derivation. It identifies a gap in a
proposed sufficient condition and supplies a weaker finite bound that may be
useful in repairing the carry argument.

Let `L = 8807`, `ρ = 2^67`, and let `E` be the 986-position support reconstructed
from the pinned recipe, binding and table. Give digits the upper caps zero
outside `E` or at position 1, three at position 1063, and one at the remaining
positions. These caps are hypotheses here; deriving them from the actual graph
in each arithmetic model is a separate obligation. For a cyclic left shift by
`67q + r` bits, `0 ≤ r < 67`, the output digit at `t` is

```
(a[(t−q) mod L] * 2^r) mod ρ
  + floor(a[(t−q−1) mod L] / 2^(67−r)).
```

The shifted pieces occupy disjoint bit ranges. Each predecessor bound computed
by the checker maximizes the two terms independently over the stated caps;
therefore it remains an upper bound even if graph constraints correlate the
digits. This is a calculation for a single standard-length cyclic word. It
does not prove the corresponding transport for an arbitrary model word, in
particular one of nonstandard length.

## A concrete obstruction to the stronger bound

Set digits 2195 and 3296 to one and all others to zero. These two positions are
Boolean anchors and this word satisfies the stated digit caps. Rotating the
entire 590069-bit integer left by `67*2198 + 1 = 147267` bits gives digits
`0, 2, 2, 0` at positions `4392, 4393, 5494, 5495` respectively. Thus target
4393 has nonzero temporal contribution; target 5495 is clean, but its
predecessor has temporal contribution 2. The support and Boolean-anchor caps
alone cannot establish a target with zero temporal contribution and predecessor
contribution at most one. This word is not claimed to satisfy the graph's
other constraints or to be a solution of the Diophantine equation.

## A weaker finite bound

For every `q < 8807` and `r < 67`, the checker establishes using independent
digit maxima that **at least one** of 4393 and 5495 is identically zero under
the caps and its predecessor is at most `ρ/2`. It checks all 590069 `(q,r)`
cases. The bound is sharp for this criterion: at `(q,r) = (2198,66)`, target
5495 is the only universally clean target and its predecessor can equal
`ρ/2`.

This suggests an alternative carry-reset proof if the actual all-model
fractional rotation can be connected to these caps and the non-temporal
predecessor contribution plus incoming carry can be bounded strictly below
`ρ/2`. For example, the existing finite recipe bound
`M = 29613572795083482608` satisfies `4M < ρ`, hence `ρ/2 + 2M < ρ`;
an all-model proof of the needed `2M` bound has **not** been supplied here.
Nor does this finite computation prove a global carry bound, decode a machine,
or establish the compact44 iPRA endpoint.

## Reproduction and input scope

From the repository root run:

```
python3 -I -S Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-fractional-clean-column/check.py
python3 -O -I -S Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-fractional-clean-column/check.py
```

Both commands exited 0 and reported `PASS_COMPACT44_FRACTIONAL_CLEAN_FINITE`,
590069 cases, the counterexample and the sharp bound. The script uses explicit
checks even under `-O`, hashes the pinned recipe, binding and 943-row JSON both
before and after, derives the support from those inputs, and checks the concrete
counterexample by rotating the full integer separately from the local formula.
File hashing is not continuous. The [independent support audit](../../../reviews/compact44-support-defect-independent-audit/README.md)
also checks the support and actual MC bytes; the present calculation does not
bind the retained MC to the model-level graph port.
