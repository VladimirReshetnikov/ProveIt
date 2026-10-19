# Independent runtime validation method

This directory contains a newly written mathematical checker. It executes only Python standard-library code and the self-authored helper `independent_runtime.py`. Downloaded Python, Lean, JSON and machine files were inspected as data; no downloaded Python was imported or executed. No repository file was changed.

## Contract

For every one of the 6,460 source instruction leaves, and both branches of each decrement, the checker starts at old-label dispatcher 96 with head zero and marker one at -1. The instruction path is followed by zeros to header position 64+n, n an arbitrary natural number. The file is a header one followed by nine primary unary blocks and a nonempty finite spare suffix. A value v is encoded by block B(v)=0 followed by v+1 ones. All other tape cells are zero.

The head-zero coordinate is without loss of generality: translating every tape coordinate and the head by any integer preserves each literal transition, hence every derived finite segment. The result therefore lifts to arbitrary runtime head positions. Likewise, the full decoded leaf is a tape representative of any clean pointer that decodes there: omitted pointer bits and any ignored suffix bits are zero, so extending/truncating those zero suffixes while keeping the header coordinate does not change the tape. The whole-program composition and clean-pointer premise remain separate obligations.

Every primary value is an independent natural parameter. At a zero decrement its selected value is exactly zero; at a positive decrement it is 1 plus an arbitrary natural. The first spare value is independent and arbitrary. The remainder is an arbitrary finite list of natural values, including the empty list. There is no maximum register, gap, spare count, spare value, or actual execution time.

The required target includes the entire tape, the exact updated pointer, unchanged/unary-updated primary registers, the spare suffix, head displacement and dispatcher. Increment appends a value-one spare in the baseline contract. Positive decrement adds one gap cell. Pointer overflow moves the head left one and adds one relative gap cell. Halt cases execute a literal transition to the sole external state 254.

Input guards require a complete prefix-free 6,460-leaf binary source tree, permitted operations and arguments, path lengths at most 64, and the same ordered leaf operations as the pinned source. The table must be total on its working states and have exactly external target 254. Matching ordered operations does not itself prove register-program equivalence; that is a separate obligation.

## Sound elementary rules

1. A literal transition is permitted only when the current affine run has constant lower bound at least one. It performs precisely the supplied write, move and next-state action. No branch is chosen from an unknown zero-or-positive run.
2. If a literal table row stays in the same state and moves in the current scan direction, the checker traverses an entire run of length L. This is valid by induction on every natural L, including zero. The resulting tape run, displacement and elapsed-time expression are retained.
3. Four block-crossing schemas are rederived on the candidate's actual table, with an arbitrary natural block value and opaque left/right contexts. Each preserves its entry state and scan direction, crosses exactly v+2 cells, and changes a B block either to B or to C(v)=1,0,1^v as appropriate. No opaque context may be read in the derivation.
4. Once such a one-block schema has closed, structural induction on a finite list permits crossing the opaque remaining spare suffix. The empty-list case is reflexive. The cons case is the one-block schema followed by the induction hypothesis. Its elapsed time and displacement use the actual list width, sum(v+2). The width variable is not an extra restriction on the list.

Affine vector positions are: constant 0, gap 1, logical-register parameters 2 through 10, first-spare value 11, and remaining-spare-list width 12. The generic block proof temporarily uses position 2 for its arbitrary value. All run coefficients must be nonnegative; equality is coefficient-wise, hence valid for every natural assignment. Negative coefficients are allowed only in accumulated displacement, not run lengths.

## Word normalization

Normalization merges adjacent equal-bit runs and drops empty runs. A finite zero run adjacent to the infinite zero exterior is absorbed. The only nontrivial block-list identity is

C(A) followed by 1 = 1 followed by B(A).

It follows by induction on A. For the empty list both sides are the single bit 1. For a cons v::A, use the induction hypothesis to replace C(A)1 by 1B(A), then the one-block identity C(v)1=1B(v). The one-block identity is immediate from C(v)=101^v and B(v)=01^(v+1). Reversing the equation gives 1 reverse(C(A))=reverse(B(A))1. Both rewrite directions reduce a C-list to a B-list, so they terminate. They are word equalities, not machine-execution assumptions.

## Bounds and confidence

The 4,000-step bound applies only to proof construction using these symbolic rules. Failure to close within the bound is reported as NOT_PROVED, never as a universal counterexample. Successful elapsed-time expressions have a positive constant term, so the represented concrete segment has positive duration for all admitted parameters.

This is an independently written executable ordinary mathematical argument. It is not a Lean theorem or a proof-assistant kernel verification, and it does not finish the 245-state formal endpoint. It also does not prove source equivalence, blank initialization or a ZFC consistency interpretation for a new candidate. Those must be supplied separately.

## Additional implementation checks

The sparse numerical simulator was cross-checked against a separate dense-tape replay for two failing instruction traces. For 131 selected guarded baseline cases with varying registers, gaps and spare lists, the symbolic duration formula and full-tape endpoint agree with numerical simulation. These finite cross-checks test the implementation; they are not premises for the universal inductions.

The obvious reassociation has a stronger parametric rejection: with all primary registers zero and path 111010010010000000, for every n and every nonempty spare suffix, it returns after 658+8n steps with a one at cell13 and zero at cell16, rather than the required zero at13 and one at16. Every other tape cell is identical. This rejects its intended instruction implementation; it does not establish that this frame occurs on the blank run or a consistency-theoretic separation.
