# Source invariants, finite blocks, and unused workspace: proof audit

## Status and attribution

This note audits an ordinary mathematical certificate method for the frozen
`Prog254.v` program and the inherited context246 register macros. It does not
claim a new sub246 machine or a new Lean/Rocq endpoint. A modified binary table
still needs its own successful full case check, preservation or reproving of
all invoked register macros, and a verified blank initialization into an
admissible source root.

The four unreachable leaves and two impossible positive CD guards are already
present in earlier beyond252 research. They are not discoveries of this
work. The finite inductive certificates here provide another checked route
to those exclusions and to per-site register facts used by the new symbolic
oracles.

## 1. Sound finite source invariants

For a cutoff K, use the atoms `{0},...,{K-1},{n:n>=K}`. A nonzero bit mask
denotes the union of selected atoms. The source invariant assigns nine masks
to each admitted source leaf. Missing leaves have no admitted register
vector. The physical permutation is the inherited one; source facts are
computed in logical order `(N,T,W,A,D,H,X,Y,L)`.

Increment shifts singleton atoms upward and keeps the tail in the tail.
Positive decrement maps `{i}` to `{i-1}` and the tail to
`{K-1} union {n:n>=K}`. A zero CD branch first intersects its tested mask with
`{0}`; a positive branch intersects with the positive atoms. Other fields
are unchanged. Join is componentwise union. Each transfer overapproximates
every concrete source transition on the represented vectors.

The checker verifies initial inclusion and closure under **every admitted
branch**, independently of the worklist's stopping rule. Induction on source
execution therefore proves membership in the invariant at every visited
leaf. The frozen parser validates the source hash, consumes all declaration
tokens, checks the rooted tree, and enumerates all 6,460 leaves. The finite
source graph also satisfies the following representation check: extending
each computed successor PC with zeros reaches a leaf with the same PC after
trailing zeros are removed. No nonzero PC suffix is ignored.

The three-atom invariant has 6,456 admitted leaves and 8,384 nonhalting
source transfers. Initial inclusion and closure were checked both for the
six-arbitrary-field root class and for all nine fields arbitrary. It carries
5,518 exact-zero facts. The constant-domain runs K=4,8,16, seeded by the exact
context246 root `(3,0,0,0,3,0,0,0,0)`, all carry 5,551 exact-zero facts and
exactly the same leaf/guard exclusions. Thus 33 zero facts are added relative
to the broader root certificate. Seeding the original three-atom domain
with this same exact root gives the same zero/dead/guard facts: the added
zeros come from the initial-state restriction, not the larger cutoff.

The K=4 root-leaf masks are `(30,31,31,1,31,31,1,1,31)`. Consequently, the
same checked invariant can also be initialized with **any N>0 and A=X=Y=0**,
with all other fields arbitrary: their atom masks are already included at
the first leaf. This is a source-execution fact. To obtain the inherited
consistency calibration, the independent dirty-root requirements on the
formula/cache/stack fields must also hold.

None of the larger cutoffs supplied additional impossible branches. This is
a limitation of these tested certificates, not a lower bound on Turing
machine size or a proof that relational invariants cannot improve matters.

## 2. The binary/source frame relation

A dispatcher frame has state96, a single left marker at head-1, a finite PC
followed by zeros, a header at distance d>=40, and a register file encoding
nine primary naturals followed by a nonempty finite spare suffix. Each block
is `B(v)=0 1^(v+1)`. Everything outside this specified finite support is zero.
The head coordinate, d, and spare values may vary between related frames.
Removing trailing zero symbols from the finite PC does not change its
zero-extended tape representation.

The source state records the PC and nine primary values. Spares and absolute
tape coordinates are absent from the source state. The relation can therefore
forget how many extra spares have been appended and how much extra zero
separator space has been created, provided the complete endpoint is again a
frame with d>=40 and a nonempty spare suffix.

All uses of the register-file box depend on the inherited universal macro
contracts. They apply to arbitrary primary naturals and arbitrary nonempty
spare suffixes. A modified table must preserve the protected literal rows
used by those proofs, or supply a replacement universal proof. Passing the
dispatcher checker alone does not establish that prerequisite.

## 3. Finite source blocks preserve the halting equivalence

Suppose that for each admitted source control and guard, a binary checker
proves one of the following statements for every related frame:

1. At source CH, the binary machine halts after a finite positive number of
   binary transitions.
2. At every other source instruction, the binary machine makes a finite
   positive number of transitions, does not halt in that prefix, and reaches
   a related frame for the source state after k source instructions, where
   k>=1. The certified source prefix does not execute CH.

Then the binary and source computations have equivalent halting behavior.
If the source halts, every nonhalting block consumes at least one of its
finitely many remaining instructions, and a block cannot skip over CH.
Eventually the source control is CH and the checked binary halt applies.
If the source never halts, the blocks concatenate indefinitely. Every block
has positive binary length, so their endpoints occur at unbounded binary
times. No block contains a halt. Determinism then rules out a binary halt.

This proof does not require the binary machine to pass through the immediate
source successor frame. It does require an explicit positive source-step
count for every permitted endpoint and positive binary progress. A bounded
symbolic rewrite sequence gives a finite binary sequence because all scan
lengths are finite naturals and every invoked macro has a universal finite
termination proof. The implementations require at least one literal binary
transition and explicitly reject an unexpected visit to the halting label.

This is an ordinary inductive argument formalizable within ZFC. It does not
appeal to external consistency, soundness, or standardness of an ambient
model. The inherited source/Con(ZFC) calibration is still a separate theorem
to compose with it; see the context246 audit for its formalization status.

## 4. Audited quiet-block implementation

The quiet-block checker includes the immediate successor and successive
CB/CC or globally certified-zero CD successors. It stops before CI, an
undecided CD, or CH, and also stops on repeated source control or at 64 source
instructions. In the frozen program, the computed closures have at most five
instructions. There are 2,050 cases with extra endpoints and 10,563 total
endpoints for the 8,385 admitted guarded cases. The arbitrary-root and
exact-root certificates give identical endpoint sets.

Quiet instructions preserve all primary registers. The first instruction's
register effect is retained at every endpoint. If delta is 1 for a positive
first decrement and 0 otherwise, and e is the accumulated number of full PC
overflows, the strict frame target uses d'=d+delta+e and head'=head-e. Each
overflow is computed from the full-width PC operation before trimming
trailing zeros. All endpoint comparisons use the affine checker's `canon`,
which merges trailing PC zeros into the zero gap. The exported JSON retains
the full and normalized PC, overflow count, distance change, and positive
source-step count.

The strict block oracle permits a zero CD test of a register proved zero
before the first register effect. It also permits such tests after the
expected single effect when the checked successor invariant proves the
register zero. Its marked state then retains that first effect. These extra
zero tests restore the complete file and preserve all zero facts; a second
nonzero register effect is refused in this strict block layer.

## 5. Audited workspace-offset implementation

The workspace box instead carries an integer offset vector Delta of length
nine. Its primary registers are exactly the initial vector plus Delta.
Initially Delta is zero. Marking retains Delta. CI adds one to its selected
coordinate and appends one spare; positive CD subtracts one and moves the
header right by one; zero CD preserves both primary values and the whole
file. The number of appended spares is forgotten, but initial nonemptiness
and the finite sequence of macro contracts prove final nonemptiness.

For a K=4 initial mask and a current offset, the checker computes the least
possible shifted value L and the greatest U, using an unbounded upper end
when the mask contains the tail. It first requires L>=0. CD takes the zero
macro only if U=0 and the positive macro only if L>0. If both outcomes remain
possible, neither macro is licensed. In particular, shifting the tail
`{n:n>=4}` by -4 yields `{n:n>=0}`, not a proof of zero. These bounds establish
the chosen guard for every represented initial value, not only for tested
register examples.

At a complete state96 endpoint, the parser requires exactly the left marker,
a finite constant PC prefix, one affine zero gap with coefficient one and
nonnegative constant, one header symbol, and a plain register-file box. The
PC length plus the gap constant must be at least40. The endpoint's nine
offsets must exactly equal the source effect. Arbitrary extra gap and spare
append counts are permitted. Marked files, wrong net effects, stray tape
symbols, a short gap, and uncertified PC endpoints are rejected.

The combined quiet/workspace wrapper supplies only PCs from the certified
source closure. The workspace engine independently validates that subset
and the exact immediate source target; it also validates CH/non-CH metadata.
Because quiet endpoints share the same primary effect, relaxing gap and
spares composes directly with the block theorem above.

A finite-block extension may include CI and universally decidable CD
instructions if it records **each endpoint's own** net offsets and never
crosses CH. The same theorem proves this extension. The subsequently audited
arithmetic implementation and its independent replay are described below.

## 6. Verification and remaining scope

The original 8,385 admitted guarded cases pass the general quiet checker,
the exact-root quiet checker, the workspace checker, and the combined
quiet/workspace checker. All baseline replays use the immediate source
endpoint, and their minimum literal binary length is13. The existing six
excluded guard cases are listed explicitly in the verification JSON.

`check_workspace_affine.py` additionally passes 555 offset/guard controls,
14 endpoint controls, and seven metadata/early-halt controls. The controls
include increment/decrement detours returning to zero net offset, the change
from positive to zero CD after decrementing an exact one, uncertainty of a
shifted unbounded tail, PC trailing-zero normalization, insufficient gap,
wrong marker/header/box/effect, uncertified PC, wrong CH tag, and an early halt
even when artificial outgoing rows are supplied at label254.

These checks substantiate the sufficient certificate method. They do not
certify any search candidate merely because its finite sampled runs look
correct, do not establish untested macro modifications, and do not replace
blank-start verification or the inherited logical calibration. Negative
results from a finite candidate family should be described as such.

## 7. Arithmetic source blocks: subsequent audit

`arithmetic_blocks.py` starts with the initial source-guarded K=4 masks and
zero offsets. At each source instruction it uses the current offset vector
to infer CD only when that branch holds for all represented initial values.
CI and a proved-positive CD update the appropriate physical offset; a zero
CD, CB, or CC changes only the PC. The source tree determines the next leaf,
and its zero-extended representation is checked. An endpoint is emitted
only after a source instruction has executed. The process stops before CH
or an undecided CD, on a repeated (leaf,offset) pair, or at its finite cap.

Induction on this generation establishes a deterministic source prefix for
every represented initial register vector. Crucially, there is no new
restriction on the initial vectors at a later CD: a branch must already be
universal for the original masks plus the exact offsets. If not, the block
stops before that test. Every emitted endpoint therefore has a sound
positive source-step count and an exact nine-coordinate net effect.

`arithmetic_affine.py` retains the audited workspace macro semantics and
complete-frame parser. Its accepted key is the **pair** (normalized PC, full
nine-coordinate offset vector), together with that key's positive source
step count. Matching only the PC would be insufficient once arithmetic
source instructions may be contracted. The original immediate source target
and CH/non-CH metadata are still validated, and unexpected binary halting is
still rejected.

The full arithmetic baseline replay passes all 8,385 admitted guard cases,
again using the immediate endpoint with minimum literal length13. Generation
produces 17,643 endpoints, with extra endpoints in 4,856 cases and a maximum
length of13 instructions. The 8,384 nonhalting source cases terminate their
closures at 8,383 undecided CD tests and once immediately before CH. The
remaining admitted case is CH itself. No closure reaches the cap32 or a
repeated pair, so merely raising this cap cannot extend these closures.

`check_arithmetic_blocks.py` independently walks the frozen source tree and
implements PC increment by integer arithmetic and stripping by matching-bit
indices; it does not call the generator's `source_step`, `lookup`,
`full_inc`, or `full_strip`. It checks 33,536 representative integer
executions totaling 70,572 source transitions, comparing every endpoint's
PC and exact offsets. It also checks 4,313 CD guards directly on every
selected finite atom and the lower endpoint/unboundedness of the tail.
Eleven mutation controls check effect-sensitive endpoint matching, gap
conditions, finite-cap validation, CH tags, premature binary halting, and
rejection of a fabricated zero-source-step descriptor. All pass.

Representative traces here are corroboration of the implementation. The
all-input proof is the initial-mask/offset induction and universal guard
argument. This extension remains a sufficient certificate method; a modified
machine must still pass its own full check and the separate macro and blank
initialization obligations.
