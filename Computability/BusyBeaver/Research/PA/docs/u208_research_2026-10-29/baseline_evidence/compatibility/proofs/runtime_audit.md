# Independent audit of the universal runtime rules and new folds

## Scope and result

I inspected the full `native_symbolic.py` and `source_ops.py` under the Rotated
U211 archive's `checks/native56/`, and the calling checks in `check_runtime.py`.
I found no substantive soundness defect in their acceleration, list induction,
or complete-tape matching rules. The rules support an ordinary inductive proof
of the reported primitive simulations; they are not merely bounded tests of
small register values.

The inspected candidates are exactly:

| Candidate | Native-table SHA-256 |
| --- | --- |
| U210 | `262032bf4237bd9c30e16ab7a3c2c4c50015a00c722ddf523e93cec0dbc51a37` |
| U209 | `4564c4876f9b18725bfb3505ec1f50d1ebce572502f2c6381ad673ecfdc3c3e1` |

I independently reran the four symbolic one-block lemmas on **both** tables,
checked the two-cell fold paths described below, and checked every arithmetic
source-address target against an independently constructed ordinal control-flow
graph. The root investigation performs the complete 5,084-case runtime replay;
this review should not be described as a second independent implementation of
that full replay.

## Why the symbolic step rules are sound

### Complete tape representation

A state contains a control label, two outward-oriented tape words, and a reading
direction. The cut lies between the two words: direction +1 reads the nearest
right cell, while direction -1 reads the nearest left cell. A step continuing in
the same direction transfers the written cell to the opposite word; a direction
reversal preserves the cut and changes the reading side. This accurately models
one ordinary TM move, including the direction-reversal cases.

Run lengths are affine vectors with thirteen slots: constant, extra gap, nine
primary values, first spare value, and the remaining spare-list width. All length
coefficients are required to be nonnegative. A literal step that consumes one
cell requires constant coefficient at least one. Thus an unknown run that may be
empty is never incorrectly treated as nonempty. Positive decrement cases use
1+n; zero cases substitute zero, covering every natural value.

The finite zero words adjacent to either infinite zero exterior may be absorbed.
Adjacent equal-bit runs may be joined. Both are exact tape-word identities.

### Unary acceleration

The sole unary acceleration applies when the actual table row returns to its
own state and moves in the current scan direction. Traversing a constant-bit run
of length n then writes the row's output bit n times, advances n cells, and
returns to the same control state. Induction on n proves the rule for every
natural n, including zero. The rule does not infer a loop from examples or assume
that an arbitrary run is nonempty.

### Finite-list acceleration

The block families are B(v)=0 1^(v+1) and C(v)=1 0 1^v. On each candidate, the
checker rederives these four one-block contracts from literal rows and unary
acceleration:

| State and direction | Block effect | Duration |
| --- | --- | --- |
| 64, right | B(v) to B(v) | v+2 |
| 0, right | B(v) to C(v) | v+2 |
| 40, left | reverse B(v) to reverse B(v) | v+2 |
| 97, left | reverse C(v) to reverse B(v) | v+2 |

Each proof starts with distinct opaque left and right exterior sentinels. Reading
either sentinel is rejected. The final state and direction equal the initial
ones, and the target includes the untouched sentinels. Consequently the contracts
compose by induction on an arbitrary finite list of blocks, including an empty
list. Slot 12 denotes the sum of the traversed block widths; it is not an assumed
number of blocks. Each B or C block has the same width v+2, so this total width is
preserved by every listed transformation.

The list normalization C(A)1 = 1B(A) is exact. For an empty A it is immediate.
For A=v::A', use C(A')1=1B(A') and C(v)1=1B(v), followed by associativity of word
concatenation. Reversing this identity gives 1 reverse(C(A)) = reverse(B(A))1.
The source code checks the empty/single-block algebra and uses this fixed
structural-induction lemma in normalization. The induction principle and word
identities are mathematical premises of the small checker, reviewed here; it
does not export their proofs to a separate formal kernel.

### Endpoint and timing checks

For a nonhalt primitive, success requires equality of the complete normalized
state: native state 84, direction, origin marker, encoded source address, padding
and gap, header, all nine primary blocks, the first spare block, the entire
remaining finite spare list, any specified appended block, and both zero
exteriors. No tape window or numerical-register projection substitutes for that
equality. Head motion is checked separately against the specified address carry.

The duration must have nonnegative coefficients and strictly positive constant,
so every instantiated macro takes a finite positive number of literal steps.
Encountering the halt label during a nonhalt contract fails, rather than being
silently accepted. For the actual CH primitive, reaching the halt label is the
correct endpoint; its final tape need not be prescribed.

These facts give the usual finite-macro simulation theorem. Every source step
has a finite positive literal implementation, nonhalt steps cannot hide an early
halt, and the halt step reaches the literal halt label. Induction on source
histories supplies both halting implications once the source-address interface
and startup frame have been established.

## Source-address arithmetic versus ordinal control flow

I independently checked the interface that can otherwise be obscured by tape
normalization. For a variable-depth source tree, `inc(pc)` may be a longer
zero-extended representation of the next leaf rather than its shortest leaf
address. The printed strings need not be identical. Their infinite zero-padded
bit streams must decode to the same leaf.

For each candidate I formed the interval of leaf ordinals belonging to every
tree prefix. An increment's expected target is the next leaf ordinal. A backward
CC target is the beginning of the selected prefix interval; a CB or zero-CD
target is its end, all with the specified wrap convention. I compared these
independent targets with the first leaf prefix of each `source_ops` result padded
by zeros. Every case agreed:

| Candidate | Source leaves | Nonhalt branch cases checked | Halt cases | Maximum path |
| --- | ---: | ---: | ---: | ---: |
| U210 | 3,909 | 5,083 | 1 | 41 |
| U209 | 3,909 | 5,083 | 1 | 41 |

Every CB/CC/CD escape used enough occurrences of its required path bit, so no
out-of-tree fallback was used. The physical-register map is a permutation of
0 through 8. This check ties the engine's whole-tape targets to the ordinary
source CFG; it is separate from proving that the reassociations preserve the old
CFG, which the construction's independent comparison audit handles.

## U210: deletion of native state 218

The difference from `prefold211.native.tm` consists exactly of deletion of the
two 218 rows and redirection of these three rows:

    (158,0), (163,0), (211,0): 0 R 218  becomes  0 R 157.

Thus each redirected entry writes a zero immediately to the left of the new
head. With the current head at 0, the only assumed cells are tape[-1]=0 and
tape[0]=b. All exterior cells are arbitrary.

| Current bit b | Original 218 step | Replacement path from 157 | Duration |
| --- | --- | --- | ---: |
| 0 | 0 R 90 | 157 -> 67 -> 151 -> 90 | 3 |
| 1 | 1 R 86 | 157 -> 148 -> 186 -> 86 | 3 |

I checked each path against the final U210 literal table with reads outside
{-1,0} forbidden. Each preserves both cells and ends with head +1, exactly as the
one-step original transition. Existing unrelated entries into 157 retain their
original rows and behavior. This is a guarded finite-path equivalence, with the
guard supplied by the preceding write rather than an unproved global invariant.

## U209: predecessor-bit reuse of native state 216

In `prefold210.native.tm`, native 180 has rows 0R152 and 1R211. Its only incoming
rows are (132,1) and (199,1), both 1R180. Native 216 has rows 0R90 and 1R211, and
its only incoming row is (214,0), namely 0R216. These disjoint predecessor bits
allow one shared state to retain the branch choice on the tape.

The final 216 keeps its 1 row and changes its 0 row to 0L211; incoming 180 edges
are redirected to 216 and state 180 is deleted. I independently verified all
four two-cell paths on the final U209 table:

| Predecessor bit | Current bit | Matching old state | Final path | Steps | Exit |
| ---: | ---: | ---: | --- | ---: | --- |
| 0 | 0 | 216 | 216 -> 211 -> 157 -> 67 -> 151 -> 90 | 5 | head +1, state 90 |
| 0 | 1 | 216 | 216 -> 211 | 1 | head +1, state 211 |
| 1 | 0 | 180 | 216 -> 211 -> 184 -> 152 | 3 | head +1, state 152 |
| 1 | 1 | 180 | 216 -> 211 | 1 | head +1, state 211 |

All paths read only cells -1 and 0 and preserve both. They therefore hold over
arbitrary exterior tape. The earlier 218-to-157 helper behavior remains valid on
U209. These bounded replacements give finite stuttering simulations in both
directions from the blank start and from aligned reachable entries. The U209
reassociation and the separate 171-entry repair require their own construction
comparison; the local fold proof does not replace those obligations.

## Reporting boundary

The full primitive replay establishes universal contracts over arbitrary natural
primary values, arbitrary nonnegative extra gap, and arbitrary nonempty finite
spare lists. Its 4,000-iteration limit bounds symbolic proof search, not concrete
register sizes or runtime. A case that does not close raises an error.

Together with exact startup and the preserved source CFG, successful contracts
support a PA-formalizable ordinary simulation proof. The arithmetic/source
calibration remains the separate inherited dependency reviewed in
`work/theory_audit.md`. The fixed K215 formal theorem is not a formal certificate
for these changed tables, and a finite blank trace is not a nonhalting proof.
