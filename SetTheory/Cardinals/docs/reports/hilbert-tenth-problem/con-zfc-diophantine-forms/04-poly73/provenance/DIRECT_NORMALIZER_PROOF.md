# Direct K215 normalization and two-sided helical padding

Snapshot: `cdd582bec13f908df3711fa9e05d1ddac368a5db`.

This is a new ordinary mathematical proof, accompanied by executable finite
checks. It is not a new Lean or Rocq theorem. The underlying K215 equivalence
and native Diophantine compiler are inherited, explicitly identified results.

## 1. Literal normalized machine

Let `K` be the dense K215 table, with working states 0,...,214, halt 215,
and tape alphabet {0,1}. Its exact canonical SHA256 is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
The normalizer `N` has states 0,...,219, halt 219, and alphabet {0,1,2}.
States 0,1,2,3 initialize; state q+4 simulates K's state q.

Write a transition as (next state, written symbol, movement). The six
initialization exceptions are

| State | Read | Next | Write | Move |
|---|---|---|---|---|
| 0 | 1 | 1 | 2 | stay |
| 1 | 2 | 2 | 2 | left |
| 2 | 1 | 2 | 0 | left |
| 2 | 0 | 3 | 0 | right |
| 3 | 0 | 3 | 0 | right |
| 3 | 2 | 4 | 0 | stay |

Each K transition `(q,a) -> (q',b,d)` becomes
`(q+4,a) -> (q'+4,b,d)`. Every other transition is the identity stay
transition. In particular halt 219 is absorbing. The construction has
219 working states, 220 total states, three tape symbols and 660 rows.
It makes no claim to improve the 215-state binary Busy Beaver machine:
the extra states and symbol serve only the fixed Diophantine compiler.

For each u>=1, initialize ones at coordinates -u,...,0, state 0 and head 0.
The first step writes the required origin flag 2 and stays in the distinct
nonhalting state 1. The machine then erases the u ones to the left, reaches
the blank at -u-1, and returns right across zero cells to flag 2. Its last
initialization step erases that flag and enters state 4 at coordinate 0.
There are exactly 2u+4 initialization transitions, and the entire tape is
now blank. Symbol 2 never recurs. Induction on subsequent transitions
identifies the complete future with the literal K run under q -> q+4.

Consequently, for every y>=1, N accepts y+2 initial unary ones if and only
if K halts on its blank tape. At y=2 there are four initial ones, u=3,
and initialization takes ten transitions. This all-or-empty input language
also satisfies the parent compiler's S_even normalization: it is unchanged
by restricting to even y.

## 2. Why a folded one-sided simulation is unnecessary

The inherited helical local predicate itself does not constrain the head
to nonpositive coordinates. It constrains heads to remain between the two
vertical boundary columns. Its initial phase graph is

    L -> L or I; I -> I or Q; Q -> R; R -> R.

With L and R forced at the boundary-adjacent interior columns, this gives
`L^a I^u Q R^b` for arbitrary a,b,u>=1. Only the original completeness
witness fixed b=2 by using a one-sided machine. We retain the exact local
predicate and permit b to be chosen after the finite two-sided run.

The literal predicate is `local_valid` in
`Papers/verification/explore_helical_unary_tableau.py`. Its initialization
checks are the phase graph and boundary tests above; it contains neither a
right-margin length test nor a tape-coordinate sign test. The stationary
first-step markers are from Section 1 of
`Papers/1980/FIXED_RAW_UNIVERSAL_81_PROOF.md`, retained by the 77, 76 and
75 constructions.

## 3. Completeness with two independently chosen blank margins

Suppose N has an accepting run of T transitions on the unary input above.
Let e and f be the least and greatest head coordinates visited, including
the entire initialization. Choose

    a >= max(2, 1-u-e),     b >= max(2, f+1).

The base tableau has width h=a+u+b+2, a vertical boundary in column 0,
and interior row `L^a I^u Q R^b`. The Q column is a+u+1. Therefore every
visited head column lies between 2 and h-2. No transition crosses a
vertical boundary. The distinguished Start window is centered on the
last I, in column x_S=a+u; End is centered on the first I, in column a+1.
Their distance is u-1=y. Both complete three-by-three marker windows
lie away from the vertical boundary, including the fixed y=2 case.

For every sufficiently large width h, the same condition can be met:
fix a permitted b and set a=h-u-b-2. Thus h can be any sufficiently large
power of 5. Choose the time height H to be any sufficiently large power
of 5, with H>=max(25,T+2). Put a horizontal boundary at time 0, the
initial row at time 1, the actual finite run above it, and repeat the
absorbing halt through time H-1. Width and height can be increased
independently. In particular N_cells=h*H can exceed every fixed compiler
bound such as 25d, and all modulus-padding obligations used by the
five-adic dummy argument remain available.

Let this finite array be G. Its helical extension is

    T_plane(z,t) = G[z mod h, (t+floor(z/h)) mod H].

The uniform vertical boundary has no payload and the local rules do not
propagate a horizontal boundary across it. Hence the seam is valid even
though adjacent strips have time origins differing by one. The extension
has periods (h,-1) and (0,H). With N_cells=hH, assign a base entry (r,s)
the cyclic index

    i = -(r-x_S)-h(s-1) mod N_cells.

Reduction modulo h determines r, and then reduction modulo H determines
s, so this is a bijection. Reading the actual three-by-three windows
gives the exact lifted overlaps at offsets 0,-1,-h. Start has index 0;
End has index y. Each occurs exactly once, since the fundamental strip
has one initialization row and one proper I-run. The change from the
old formula x_S=h-4 is only the replacement x_S=a+u.

The proof uses no bound on the halting time or space as a function of
input. The finite accepting run is assumed in the completeness implication;
its extrema merely choose existential tableau margins.

## 4. Soundness is unchanged

From any valid periodic lifted word with the distinguished markers,
pull back to the plane using index -z-ht modulo N_cells. The Start marker
contains an initialized Q. The phase graph has no directed cycle through
Q, so horizontal periodicity forces a vertical boundary on either side.
Their vertical propagation defines a finite strip. Horizontal-boundary
propagation inside that strip and vertical periodicity give a finite next
boundary in time. Exact local transitions, the unique initial head, and
the no-escape rule reconstruct one actual finite N run, and the last
interior row has the halted head. This argument never required that N be
one-sided or that its right blank margin have length two.

The unchanged marker-bijection argument identifies the Start and End in
the same initialization run, whose I-length is y+1. Our N accepts any
such unary input exactly if K halts. Thus the inherited fixed-input
compiler theorem applies with precisely the same arithmetic layout and
mask formulas, after the two-margin completeness proof above.

## 5. Internal ZFC scope

The source K215 exposition supplies the ordinary, ZFC-formalizable theorem

    Halt(K215,blank) <-> ZFC has a finite syntactic refutation.

The external Lean theorem is
`KEndpoint215.blank_halts_iff_zfc_refutation`; its semantic calibration
passes through `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. It must not be
described as a derivation already encoded in ZFC proof syntax. The new
normalizer proof and helical-padding proof use only explicitly finite
objects, integer arithmetic, and induction; ZFC proves each construction
and its two implications. Composing these ordinary proofs with the
inherited arithmetical/Pell compiler proof yields the asserted ZFC
equivalence. No appeal to the soundness or consistency of ZFC is needed
to prove that equivalence. No new formal kernel check of the composed
Diophantine theorem is claimed.

## 6. Executable evidence

`normalize_k215_direct.py` authenticates the canonical source table,
emits all 660 normalized rows, and compares every inherited transition.
Its saved receipt verifies six input-erasure lengths, including the
four-one input, and 120,000 paired literal steps. These finite checks
corroborate the uniform proof above. The observed prefix does not prove
unconditional nonhalting. The independent compiler helper tests a
two-sided accepting toy tableau that actually visits a positive tape
coordinate, along with its helical seams and marker distance.
