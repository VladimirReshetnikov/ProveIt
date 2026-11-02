# Independent finite fractional-rotation audit

This reviews `research/ordinary12-ipra-bridge/compact44-fractional-clean-column`
as committed in `fc8fd3b3c9`. It establishes only a finite statement under the
specified per-digit caps. It does not derive those caps from the Diophantine
graph, prove a nonstandard-length or all-model rotation result, establish a
carry bound, or prove an iPRA endpoint.

The checker reruns the pinned independent support audit from commit
`aabfd87212`, then independently uses its explicit 986-position interval
formula. The support audit itself pins and checks the recipe, binding,
943-row table, retained MC and beta bytes. The fractional calculation assumes
digit cap 0 outside the support and at position 1, cap 3 at position 1063,
and cap 1 at all other support positions. No claim is made that every legal
capped word satisfies the remaining graph constraints.

For a cyclic left shift of `67q+r` bits, output position `t` draws its low
part from source `t−q` and its upper `r` bits from source `t−q−1`, with
indices modulo 8807. The two pieces occupy disjoint bit ranges, so their sum
is the rotated digit without a carry. For independent caps `a,b∈{0,1,3}`,
the maximum low part is 0, `2^r`, or `3·2^r` respectively, except that for
`a=3, r=66` the maximum low part is `2^66`; the maximum upper part is
`floor(b/2^(67−r))`. The source positions are distinct. The script also
exhaustively checks the same rotation formula for all 4096 words, 12 shifts,
and 3 digits of a separate 12-bit cyclic machine.

For each block shift `q`, this checker classifies the six relevant source caps
(the three successive source positions for each candidate target) into 24
signatures. It then checks all 67 fractional shifts for each signature,
weighted by the number of block shifts with that signature: exactly 590069
cases. For each case, one of the two candidate targets is universally zero
and its predecessor's independent-digit maximum is at most `2^66`. This
independent maximum remains an upper bound if extra constraints correlate the
source digits; the conclusion is conditional on the stated caps.

The explicit legal word with ones at anchor positions 2195 and 3296, zero
elsewhere, rotated left by `67·2198+1=147267` bits, has digits `[0,2,2,0]`
at positions `[4392,4393,5494,5495]`. Thus no universally valid predecessor
bound of 1 follows from these caps alone. At shift `67·2198+66`, the same
word yields `[0,2^66,2^66,0]` at those positions: the sole universally clean
target 5495 has predecessor `2^66`, so the half-radix bound is attained.
The witnesses are finite capped words, not asserted graph solutions.

From the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-fractional-clean-independent-audit/audit.py
python3 -O -I -S Computability/DiophantineConsistency/reviews/compact44-fractional-clean-independent-audit/audit.py
```

Both actual commands exited 0 and reported
`PASS_INDEPENDENT_FRACTIONAL_CLEAN_FINITE`; the pinned author's normal and
optimized checker each exited 0 within both runs. The independent checker
uses explicit checks in both modes, hashes its pinned inputs again afterward,
and has a 20-second parent-audit and 60-second per-author-check timeout.
File rehashing provides point-in-time drift detection, not continuous
protection. The independent checker calls the author checker only after its own
signature and witness tests; its mathematical conclusion does not depend on
using the author's digit-maximization routine.
