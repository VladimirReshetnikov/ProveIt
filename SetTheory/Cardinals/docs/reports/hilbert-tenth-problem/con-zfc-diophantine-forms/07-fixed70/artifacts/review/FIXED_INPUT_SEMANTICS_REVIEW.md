# Independent review: fixed input, helical semantics, and ZFC calibration

Review scope: the specialization of the modified half-binomial compiler underlying
`FIXED_RAW_UNIVERSAL_75_PROOF.md`, and the exact K215 consistency calibration.
Repository snapshot: `cdd582bec13f908df3711fa9e05d1ddac368a5db`.

This note is an ordinary mathematical review. It is not a new Lean or Rocq
kernel certificate. The final emitted circuit and normalized machine must also
be checked against their literal definitions; those checks are separate from
the interfaces reviewed here.

## 1. Input conventions

The historical 75-operation source has an ordinary input `x`. Its helical
tableau uses marker distance `y=2x`, an initialization run of `y+1` headless
`I` tiles, and one final `Q` tile carrying the initial head. Thus its unary
tape has `y+2` ones in total.

For the fixed instance used here these quantities are:

| Layer | Fixed value |
|---|---:|
| Ordinary historical input | `x=1` |
| End marker distance from Start | `y=2` |
| Number of headless `I` tiles | `3` |
| Number of initial unary ones, including `Q` | `4` |

Let the inner radix be `R0=2^b`, the outer radix be `B=2^d`, and define the
fixed positive integer `W0=R0*B^2=2^(b+2d)`. `R0` is a compiler radix; it is
distinct from the supplied packed Pell index, called `Ridx` below.

The normalized machine may erase its unary input and simulate K215 on blank
tape. The fixed-instance proof only needs equivalence on the four-one input.
It does not need a parity checker or any assumption about how the normalized
machine behaves on unused odd marker distances. In particular such an
input-erasing machine should not be described as recognizing the historical
set `S_even` unless an additional parity test is actually supplied.

## 2. Correct fixed-input specialization

In the unprojected 75 source, replace the variable `W` by `W0`, set
`C=Z+W0` as a polynomial definition, delete the four input-Pell equations
and their five auxiliary coordinates, and replace the width equation
`C+alpha+2d*x=q` by `C+alpha=q`. `Z` and `alpha` remain positive.

These changes are sound. The preliminary kernel argument never needs
the `2d*x` bound except in the input adapter, which has been deleted.
It still has `q>=B>=16` and `0<Z<C<q`.

For precision, the original 75 bootstrap is the shifted one, not the old
77/76 strict-bound argument. Set

```
J=(q-1)/(B-1),
Sprime=(Z-1)+q*F,
TC=MC*J+1, TF=MF*J-1, Tprime=TC+q*TF.
```

The source equation is exactly

```
Ridx=(q^2-Sprime)*(q^2-1)+Tprime.
```

The modified compiler has `0<MC,MF<B-1`, `MC=2 mod4`, and `MF=4 mod8`.
The repunit equation and positivity imply
`0<TC<q`, `3<=TF<q-2`, and `3q+1<=Tprime<q^2-1`.
If `Sprime>q^2`, the packed equation would make `Ridx<0`; hence
`Sprime<=q^2`. Since `F,Z>0`, also `Sprime>=q`. It follows that
`3q+1<=Ridx<q^4`, precisely the preliminary range required by the
half-binomial kernel.

The boundary `Sprime=q^2`, equivalently `Z=1,F=q`, must not be discarded
at this stage. The kernel first recovers `q=B^N`, `X=2^Ridx`, and the
population threshold `popcount(Ridx)>=3dN+2`. The inverse-packing bound
then excludes that boundary, because there `Ridx=Tprime` has population
only `dN+2`. It simultaneously recovers

```
(Z-1) AND (MC*J+1)=0,
F AND (MF*J-1)=0,
F<q.
```

The first mask inserts the Start selector at the origin: `Z-1` has zero
unit bit, so adding one creates exactly that bit without a carry. End's
selector remains absent at every cell of `Z`. The constant `W0` inserts
exactly End's missing bit at cell 2. Since `W0<C<q=B^N`, one has `2<N`.
Thus this insertion does not wrap and the two marker locations are distinct.

The modified compiler's native types, field bound, clean-band argument,
anchor synchronization, and occupancy propagation therefore apply with no
change. The new upper dummy bit and its possible spill during an unaligned
rotation must be treated by the modified75 proof, not by the earlier claim
that every rotated radix digit is either zero or a single power of two.

For completeness, use the historical padded genuine tableau at marker
distance 2 and its five-adic dummy selection. All remaining equations and
kernel witnesses are unchanged. The weaker width slack is simply
`alpha=q-C>0`, positive since the genuine cell bounds give
`C<=(B-2)J<q`. No input-Pell witnesses are needed.

This argument proves equivalence for the fixed unprojected system. Further
elimination of positive witnesses, normalization of Pell roots, or product
finalizers requires its own positive-zero equivalence; one must not infer
those transformations from this specialization alone.

## 3. Required literal normalized machine

The supplied machine specification must be a total finite transition function
with a distinguished absorbing halt. The start convention is a head at
coordinate zero, with four ones at coordinates `-3,-2,-1,0`, blank elsewhere.

The first transition must write the special origin flag and stay at coordinate
zero, entering a distinct nonhalting state. In the notation of the inherited
marker windows:

```
delta(q0,1)=(q1,2,stay), q0!=q1, q0 and q1 nonhalting.
```

An explicit input-erasing prefix can scan left, clearing all remaining unary
ones, then scan right to the flagged origin. It must preserve the origin flag
and enter the blank K215 simulator there. A one-sided simulator can fold the
original tape: physical cell `-j` stores virtual cells `j` and `-j-1` on two
tracks. Finite control records which track is active. A move across virtual
cells 0 and -1 changes tracks while staying on physical cell zero; all other
moves map to the appropriate left or right physical motion. The invariant is
that the physical head never visits a positive coordinate.

The final artifact must specify every state, alphabet symbol, and transition,
including unused malformed-input cases. It is insufficient to write only
"choose a machine recognizing the desired set." No halting decision is needed
to construct this finite table or its local-window predicate.

The dense K215 table's actual conventions are: states 0 through 214 working,
halt 215, start 0, blank symbol 0, symbols 0 and 1, two-way infinite tape,
head initially at zero, and rows `state read write direction next` with
left/right moves only. Initialization is already included in these 215 states.

## 4. Required radius-one rules

The finite tile alphabet must include exactly one vertical boundary tile `V`
and one horizontal boundary tile `H`; neither has tape, phase, or head payload.
`V` has vertical bit 1 and horizontal bit 0, and is propagated vertically.
Adjacent vertical boundaries are forbidden. Horizontal boundary bits propagate
only between horizontally adjacent non-`V` cells. Adjacent horizontal boundary
rows inside a strip are forbidden. There is no intersection tile.

An interior tile has one tape symbol and either no head or one machine state.
An initialization phase is present exactly when the tile directly above it is
`H`. The fixed phase edges are

```
L->L or I; I->I or Q; Q->R; R->R.
```

The first interior column next to a vertical boundary must have phase `L`;
the last must have phase `R`. The payloads are fixed: `L,R` are blank and
headless, `I` is symbol 1 and headless, `Q` is symbol 1 with head `q0`.
Every finite initialization strip is consequently exactly
`L^a I^u Q R^b`, with `a,b,u>=1` and exactly one head. All other interior
rows have no phases.

When both current and next rows are interior, apply the exact deterministic
three-neighbor update. The symbol is written only by the old center head.
Incoming heads can come only from the left head moving right, the center
head staying, or the right head moving left; two or more incoming heads are
forbidden. A vertical-boundary neighbor is treated as blank and headless.
Explicitly forbid a head moving through either adjacent vertical boundary.
On the last interior row, detected by `H` directly below, every head must be
the absorbing halt. No computation step crosses an `H` row.

The no-escape clause is necessary. Without it an initialized head could
disappear through a side boundary and a headless last row would pass a merely
universal "every head is halted" test.

## 5. Exact window alphabet and absence of spurious helical acceptance

Enumerate as lifted symbols precisely the 3-by-3 tile windows satisfying the
local predicate at their center. Do not enumerate all tile windows without
the local test. For center/right/next lifted windows impose the exact six-tile
horizontal overlap and six-tile vertical overlap. The two overlaps imply
that every block equals the centered window of the plane reconstructed from
its center tiles. Thus membership in the window alphabet recovers every
original local test.

For a cyclic word of length `N` and temporal stride `h`, pull back using

```
(column,time) -> -column-h*time (mod N).
```

This gives a valid plane periodic in each coordinate, without assuming
`h|N`, that `h` is the strip width, or that the period lattice is rectangular.

The fixed Start window is centered on the last `I` and has middle row
`I,I,Q`; its next row is `1,1,(flag,q1)` because the first transition stays.
The fixed End window is centered on the first `I`, with middle row `L,I,I`
and next row `blank,1,1`. Their top rows are `H,H,H`.

Every proper initialization `I` run of length at least two has exactly one
of each marker. A run of length one has neither. On the finite cyclic
residues, scanning left from Start to the first `I` and right from End to
the last `I` gives inverse maps. These scans terminate before `N` steps
because the adjacent phase on the far side is `L` or `Q`; an all-`I` cycle
has no marker. A run cannot touch a vertical boundary at an `I`, since the
first and last interior phases must be `L` and `R`. Therefore unique End
implies unique Start on cyclic residues themselves; aliases in the covering
plane cannot merge distinct markers.

With Start at residue zero and End at residue 2, `N>2` makes their same-run
leftward displacement exactly two. Hence `u-1=2`, so `u=3` and the initial
tape has exactly four ones.

Horizontal periodicity forces a vertical boundary on each side of Start's
initialization strip: otherwise the periodic phase row would contain a
directed cycle through `Q`, which the phase graph does not allow. Choose
the nearest pair. The top `H` row is uniform within that strip, and vertical
periodicity supplies a next `H` row. Between them lies a finite rectangle.
Induction using initialization, exact transitions, and no escape proves that
each interior row has exactly one genuine head and is the next configuration
of the normalized machine. Its final head is halted. Consequently a decoded
accepting helical cycle gives a finite genuine halting run, even when its
stride and length are noncanonical.

Conversely, a finite halting run admits independent width and height padding.
For a base strip of width `w` and time height `Htime`, extend by

```
T(z,t)=G[z mod w, (t+floor(z/w)) mod Htime].
```

The uniform `V` tile and absence of horizontal-boundary propagation across it
make every helical seam valid. This plane has periods `(w,-1)` and
`(0,Htime)`. Its cyclic length is `N=w*Htime` and stride `h=w`, with one
Start and one End. Width and height may be chosen as independently large
powers of five, as required by the modified75 dummy-selection proof.

## 6. Consistency calibration and formal verification boundary

The pinned Lean theorem is

```
KEndpoint215.blank_halts_iff_zfc_refutation :
  BlankHalts machine215 <-> BProv ZFCax_s [] Form.fBot.
```

The proof factors through the numerical calculus `C222(1)`, then ZF finite
refutability, then ZFC finite refutability using the constructible model.
The negated endpoint follows by propositional logic. The repository's
ordinary proof describes these arguments as formalizable in ZFC.

All new steps here concern explicitly finite transition tables, finite local
alphabets, integer arithmetic and Pell recurrences, and finite computations.
Their mathematical proofs can likewise be formalized in ZFC. This supplies
the intended *provability of the equivalence*, without claiming a derivation
of consistency itself.

The retained endpoint is an external proof-assistant theorem. The repository
explicitly does not provide an internal PA proof or a derivation encoded in
ZFC's own proof syntax. This review does not change that boundary and does
not claim a fresh kernel check of the Diophantine endpoint.

Freshly recomputed identity checks in this review:

```
k215.tm:
fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090

sites215.json:
17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba
```

Both agree with the pinned release records.

## 7. Primary repository sources inspected

All paths below are relative to the pinned ProveIt root.

- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md`
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_77_PROOF.md`
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_78_PROOF.md`
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md`
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_84_PROOF.md`
- `Computability/HilbertTenthProblem/Papers/1980/FIXED_RAW_UNIVERSAL_88_PROOF.md`
- `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_CYCLIC_MARKER_BIJECTION.md`
- `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_HELICAL_UNARY_TABLEAU.md`
- `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_THREE_CELL_PERIOD_LIFT.md`
- `Computability/HilbertTenthProblem/Papers/1980/EXPLORATION_MARKED_PERIODIC_TM_PADDING.md`
- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md`
- `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_factored_first_norm.md`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KCode222.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean`
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean`
- `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md`
- `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md`
