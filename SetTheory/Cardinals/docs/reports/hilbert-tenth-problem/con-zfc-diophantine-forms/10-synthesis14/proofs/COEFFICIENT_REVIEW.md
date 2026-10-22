# Independent review of the projected-cross coefficient compiler

Date: 22 October 2026. Outcome: **no mathematical or implementation defect
found in the reviewed change**. This is a mathematical/source review, not a
Lean/Rocq verification. The unchanged native compiler and K215 calibration
remain inherited dependencies.

## Reviewed artifacts

All four files are under `research/coefficient_audit/` in the research tree.

| File | SHA-256 at review |
|---|---|
| projected_cross_compiler.py | edfe868ca8696f15d8a8fe4da7b7344dc9c9c9d979739972742db2bf5678974a |
| projected_cross_section.tex | 71e2f86205d958ddf8d2f179bbd1cbbe1ff432de536cd7b8258ca7fb3983ea45 |
| projected_cross_constants.json | d978486cee5f11b1523d10281a941a2a55d04f70e97f0c840ecabb74cebacc4d |
| cross_count_verified.json | 8d419f3f842c5f934bfe71b46f6f06d0726f5bcbc3d0c5ead451d408871f6d2c |

I also read the literal inherited `blank_helical.local_valid` implementation,
the package06 fixed-blank proof, the complete75 modified-mask proof, and the
complete76 compiler proof. The repository pin is
`3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

## Local language, reconstruction and markers

The inherited predicate reads exactly its center, left, right, following,
and the horizontal-boundary bit of the predecessor. In particular the
predecessor's vertical bit is NOT read at the current cell. Thus the projection
to `(prior_H,left,center,right,following)` is exact. The six native payloads
include the derived `center_H` bit, and the selector clauses force it to
match the selected center; it is not a free extra local datum.

The four proposed overlap equalities reconstruct all five recorded values
from the cyclic center word, even when offsets coincide. Pullback to the
plane therefore restores precisely the original local predicate. No
coprimality or divisibility assumption on the temporal stride was introduced.

The new Start has an initialized Q, adjacent L/R, and following headless1,
as required by the exact first K215 transition. Conversely a global Q has
that cross: the phase adjacency forces L/R, and their blank/headless
initial payloads exclude spurious incoming heads. The omitted corner data
of the old Start are forced by neighboring local predicates in the global
tableau. The forbidden tile is locally allowed at its V center, but its
prior_H=1 forces a predecessor H whose vertical-bit propagation contradicts
the current V. Its exclusion therefore removes no valid global tableau.
The zero temporal shift is still excluded at Start (its prior_H differs
from its center_H, and its following symbol differs from its center).

## Exact census

The fiber reduction is correct, including its boundary cases. Ordinary
interior centers have 438 predecessor representatives for the sole allowed
bit value0; initialization centers have just H and bit value1; boundary
centers allow439 representatives and both bit values. Accordingly the
respective factors are division by438, identity, and multiplication by2/439.
The13 supplied category counts sum to **87,923,161**, including Start and
the excluded tile. No assumption of global extendibility is used in the
count. I independently recomputed the sum and the scalar layout arithmetic.

## Native slots, clauses, overlap and synchronization

The six slot intervals are disjoint and the shifts3a and a implement the
two vertical and two horizontal equality tests with the stated direction.
The heterogeneous slot sizes2 and a do not change the Boolean clause
argument: selector totals lie in[0,k]<A-1, so the low mask A-2 permits only
totals0 or1. Each higher parity bit then forces its native payload or
anchor bit to match the selected tile. Horizontal center/left matching
propagates occupancy from the marked origin through the entire cyclic word.

The actual-dimension interval audit covers every possible native position,
including the entire selector interval, not a selector sample. Its source
incidences agree with the displayed coefficients. All nonanchors lie below
M, and the only native support pair with difference18M is(9M,27M).
The optional upper dummy spill stays below M. The clean-band separation,
the absence of a wrapped anchor pair, and the carry bounds therefore leave
the inherited whole-cell synchronization proof intact.

## Population and carry checks

There are4a+4 payload positions and4 anchors. The mask has3a+2 overlap
targets and2 anchor targets. Thus

    pc(mu)=ell+j_max-1,
    m=2pc(mu)+3a+4=2ell+11a+18+2p.

The base MC mask removes exactly m bits, and the extra dummy subtraction
removes one further bit. The native high mask has m bits before its low
bit2 is added. Consequently their populations are d-m-1 and m+1 and sum
to d; MC is2 mod4 and the native high mask is4 mod8. The exported high
port correctly includes the required B-1 shift.

The stated bound on the sum of clause coefficients is conservative and
valid (each selector has11 monomials). The computed b bound implies the
full inherited raw coefficient mass bound and the mu bound, including
the four-valued dummy and its possible unaligned spill. Since T2-T1 is
2 mod4, paired clause terms cancel modulo5. With a=3 mod4, the four
remaining terms give2DC-DR=3 mod5, so no conditional coefficient correction
or extra dummy is required.

## Exact dimensions and limits

Independent arithmetic reproduces ell27, padding43,960,012, m87,924,925,
one dummy, and all displayed support/band endpoints. The least admissible
powers are b=5^13 and L=5^15, hence

    d=5^28=37,252,902,984,619,140,625.

The binary length of B-1 is exactly d, a factor5^39 below the old5^67.
The proof correctly distinguishes that statement from expanding the
coefficient integers. No huge coefficient, accepting K215 run, or complete
Pell witness was materialized. The review did not repeat the full inherited
census enumeration or routine small compiler fixtures; the exact structural
arguments and the new dimension arithmetic were the review targets.

## Packaging addendum

The review hashes above identify the research artifacts at review time. They
are preserved as historical review evidence, not presented as the hashes of
the final packaged copies. After the review, the coefficient script gained
optional finite marked-tableau checks; their results were added to the
receipt. Packaging also resolves relative CLI paths from the archive root,
creates an output directory when needed, and adds the TeX alias label
`sec:coefficients`. The coefficient formulas and mathematical construction
are unchanged. Final packaged copies at this handoff are:

| Packaged file | SHA-256 |
|---|---|
| code/projected_cross_compiler.py | 678840453e45826c8f1238e26c3b44c502113cc7dcea5d9b629a7c945f332972 |
| sections/projected_cross_section.tex | f23df54d078f1ac74055e11f1566ff39fbbefe04baf8649bd48ee5580f11fc57 |
| coefficients/projected_cross_constants.json | 65933e7b405e1215a038048ea6c55708cc920d2a995b214af8d99194a7bb0965 |
| coefficients/cross_count_verified.json | 8d419f3f842c5f934bfe71b46f6f06d0726f5bcbc3d0c5ead451d408871f6d2c |
