# Closed K215 coefficient recipe

This note specifies the fixed numerals used by the ordinary polynomial. It uses
the exact complete76 compiler layout and the complete75 half-binomial mask
correction at ProveIt commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db`. The executable specification is
`k215_constants.py`. No universal-machine index, proof number, unknown halting
time, or unspecified implementation choice is a coefficient.

The normalized machine JSON is a literal finite transition table. Its first
transition on symbol 1 writes 2, stays in place, and enters a new nonhalting
state. After erasing the initial unary word it simulates the exact pinned K215
machine. The direct normalizer permits a two-sided tape. The original one-sided
normalizer is an alternative using the same compiler.

## 1. The finite window set is completely specified

Order the original tiles as follows:

1. Vertical boundary V, then horizontal boundary H.
2. Every unphased interior pair (tape symbol, optional head state), in the
   supplied alphabet/state order, with absent head first.
3. Four initial-row tiles L, I, Q, R, with respective payloads blank/headless,
   1/headless, 1/initial-head, blank/headless.

Let `a` be this finite alphabet size. The complete local predicate is printed in
`local_valid`; it inspects center, left, right, predecessor-time and
successor-time entries of a 3-by-3 window. It enforces vertical boundary
propagation, horizontal boundary propagation inside each vertical strip,
nonadjacent boundaries, the phase graph
`L -> L or I`, `I -> I or Q`, `Q -> R`, `R -> R`, exact initialization,
the literal machine update, no boundary crossing, and a halted head just below
the upper horizontal boundary. Overlap will enforce these clauses at every
cell, so no additional neighbor-center predicate is omitted.

The distinguished Start window is centered at the final I, immediately left
of Q. Its three rows, from earlier to later time, are

    H             H             H
    I             I             Q(1,q0)
    (1,none)      (1,none)       (2,q1).

The End window is centered at the first I:

    H             H             H
    L             I             I
    (0,none)      (1,none)       (1,none).

The ordered allowed-window list is Start, End, followed by every other
accepted tuple in `{0,...,a-1}^9` in lexicographic order. This is a finite
bounded enumeration. Denote its length by `k`, and its entries by `w_i`.
The rule is independent of the duration or tape extent of any computation.

At fixed ordinary input `x=1`, the End displacement is `y=2`; the initialized
I-run has length `u=y+1=3`, and the complete initial tape word has four ones,
including the Q cell. The normalizer erases this word and starts K215 blank.

## 2. Exact arithmetic recipe

Everything below is a definition of a fixed positive integer or a finite
polynomial in a formal radix `R`. All loops are bounded by the preceding
explicit finite objects.

Put `A=2^max(2,bit_length(k+1))`. For `r,c=0,1,2` and `s=0,...,a-1`, define

    p(r,c,s)=k+3a+(2-r)3a+(2-c)a+s.

Enumerate the triples `(r,c,s)` lexicographically, starting with index `j=1`.
Initialize selector coefficients `c_i=1`, `i<k`, and `mu=A-2`.
At each triple set `c_p=A^j`, add `A^j` to `mu`, and add `A^j` to `c_i`
exactly when the corresponding window entry `w_i[3r+c]` equals `s`.
For `j=1+9a,...,9a+4`, reserve four anchor coefficients `A^j`, add each to
`mu` and to every selector coefficient.

Put `m=2 popcount(mu)+12a+2`. Append zero-expression clauses: while
`m+1<k+9a+5`, add the next unused power of A to `mu` and increase `m` by 2.
Use `m+1-k-9a-4` dummy positions, consecutively beginning at `k+12a`.
Let E0 contain selectors, all copy positions, and these dummies. Set

    M0=max(E0)+3a+1,
    anchors=(M0,3M0,9M0,27M0),
    E=E0 union anchors.

Assign the four reserved coefficients to the corresponding anchors. Put

    emax=max(E),
    H=emax+24M0+3a+1,
    T1=H+2emax+a+1,
    T2=T1+2emax+1,
    g=T2+emax+1.

Let L be the least power of 5 at least `g+emax+1`. The center polynomial is

    DC(R)=R^(3a)+R^(H+a)+R^(8M0)+R^(24M0)
          + sum_e c_e*(R^(T1-e)+R^(T2-e)),

with an additional monomial `R^g` precisely if
`2DC(2)-2^H=0 modulo 5`. That choice makes `2DC(2)-2^H` nonzero modulo 5.
Let `DR(R)=R^H`.

The unmodified verification mask polynomial is

    MF0(R)=mu*(R^T1+R^T2)
           + sum_(r<2,c<3,s<a) R^p(r,c,s)
           + sum_(r<3,c<2,s<a) R^(H+p(r,c,s))
           + R^(9M0)+R^(27M0).

Set `K=|E|`, `mass=(K+2)*(2 sum_e c_e+6)`, and choose `b` to be the least
power of 5 such that

    2^b >= max(4*mass+8,2*mu+4,16).

The code computes it by applying `next_five_power` to the bit length of one
less than the target. Put `R=2^b`, `d=bL`, `B=2^d`, and let `e_*` be the
first dummy position. The final modified constants are

    MC=B-1-sum_(e in E,e != 1) R^e-2R^e_*,
    MF_native=MF0(R)+4,
    MF_source=MF_native+B-1,
    Kconstant=DC(R)+B*DR(R),
    W0=2^(b+2d)=R*B^2.

The source port named `MF` is `MF_source`, not `MF_native`. Confusing these
two conventions changes the polynomial and invalidates the compiler theorem.
The other source ports are `Bm1=B-1`, `inner_bits=b`, and
`twice_cell_bits=2d`. The final affine input guard also uses the fixed
integer `input_unit_constant=1-3W0`.

## 3. Two-sided padding is sufficient

The original helical construction fixes a two-cell right blank margin by
first normalizing to a one-sided tape. This is unnecessary for a fixed
two-sided machine. If the actual halting run has extreme visited tape
coordinates `ell` and `r`, choose the left blank margin `a_left` and right
blank margin `a_right` after this finite run is given. Both can be arbitrarily
large, with the head and every visited cell strictly between the vertical
boundaries. Choose the desired total width to be any sufficiently large
power of 5, increasing either blank margin to achieve it. Independently
choose the time height to be any sufficiently large power of 5, padding by
the absorbing halt configuration.

Let the initial Q column be `xQ=a_left+u+1`, with `u=3`; Start is at
`xS=xQ-1`. Use the same helical extension

    T(x,t)=G[x modulo width,(t+floor(x/width)) modulo height]

and cyclic index `-(x-xS)-width*(t-1)` modulo `width*height`. Vertical
boundary cells have a time-independent payload, so every seam remains
valid. The unique End is exactly two cyclic positions left of Start.
No bound on the actual halting time or tape extent is assumed or computed.

For soundness the no-escape rule already recovers a genuine finite run
between the selected boundaries, whether its head visits only negative
coordinates or both signs. Thus the change does not weaken any local rule,
native mask, synchronization argument, or five-adic dummy control.

## 4. What was actually computed

The delivered manifest records the literal machine size, tile-alphabet
size, exact Start/End words, exact number `a^9` of candidate window tuples,
the exact allowed-window count, and the exact layout scalars. The giant
window list, sparse polynomial arrays and expanded coefficients were not
evaluated. The remaining coefficients are exact finite-sum definitions,
not claims of feasible decimal materialization.

The default program only emits this manifest. `--compile-sparse PATH`
evaluates the complete window enumeration and sparse layout; `--materialize
PATH` additionally emits all coefficients in hexadecimal. Both commands
are effective finite algorithms with enormous resource requirements and
are not part of the delivered validation run.

The safe `--self-test` run checks a two-sided 126-cell accepting helical
tableau, unique markers at displacement 2, and both exact overlaps.
Separately, five small compiler fixtures are actually materialized and
verified for mask ranges, low bits, mask population, and the five-adic unit.
The smallest fixture has `d=9765625`, which already illustrates why materializing the actual program
coefficients is not a reasonable deliverable requirement. These checks
corroborate the finite transcription; they do not certify a K215 halting
run or replace the mathematical compiler proof.

## Sources

- `Papers/1980/FIXED_RAW_UNIVERSAL_75_PROOF.md`
- `Papers/1980/FIXED_RAW_UNIVERSAL_76_PROOF.md`
- `Papers/1980/EXPLORATION_CYCLIC_MARKER_BIJECTION.md`
- `Papers/verification/explore_helical_unary_tableau.py`
- `Papers/verification/explore_fixed_raw_universal_76.py`
- `Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md`
- `Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.py`

All paths are relative to `Computability/HilbertTenthProblem` at the pinned
commit above. The new two-sided padding observation is stated and justified
here; it is not misattributed to a pre-existing machine-checked theorem.

A separate authenticated source audit extracts only the two pinned compiler
function definitions and compares 25 sparse layout attributes on four finite
fixtures, including both branches of the optional high-monomial correction.
No upstream module top-level, historical builder or test suite executes.
The exact comparison passes; the audit script and receipt are supplied.

## 5. Exact window count without enumerating the window list

For the direct normalizer, the literal table has 220 total states and 3 tape
symbols. Thus `a=2+3*(220+1)+4=669`. The four window corners are completely
unconstrained by `local_valid`, so every valid cross has exactly `a^4`
extensions. The predecessor-time tile is seen only through its H bit: one
choice is H and the other `a-1` choices have H bit zero.

For left and right neighbors, count how many tiles send each possible new
head into the center. Let `L_q,R_q` be these counts, with `q=none` for no
incoming head, after deleting a forbidden vertical-boundary tile when the
center would cross it. Let `U(s,q)` count the allowed successor tiles with
payload `(s,q)`; this includes the separate initial-phase copies when they
share that payload. If the center sends no staying head into itself, its
next-payload contribution is exactly

    L_none*R_none*U(s,none)
    +R_none*sum_q L_q*U(s,q)
    +L_none*sum_q R_q*U(s,q),

where both sums exclude `none`. If the center stays with new head q0, the
contribution is instead `L_none*R_none*U(s,q0)`. Two incoming heads are
excluded in both formulas. The phased rows restrict their right neighbor
by the six phase pairs; the compiler code enumerates this four-element
case separately. The two boundary-center contributions are
`a^2(a-1)` and `2a^2(a-2)`.

This exact finite counting argument, implemented in `count_allowed_windows`,
gives

    boundary crosses  =     896017122,
    unphased crosses  =  235501665872,
    phased crosses    =         11505,
    all valid crosses =  236397694499,
    a^4               =  200310848721,
    k                 = 47353022820782362885779.

The count uses the literal normalized K215 transition table, but no simulated
halting event. An independent test enumerates all 209952 weighted cross
assignments for a smaller 18-tile machine, including both left and right
moves, and exactly reproduces the counting formula.

## 6. Exact large scalar values

Write `A=2^t`. Then `t=76`. The initial mask has
`popcount(mu0)=t-1+9a+4`, hence

    m0=2t+30a+8,
    p=max(0,ceil((k+9a+4-m0)/2)),
    m=m0+2p,
    dummy_count=m-k-9a-3.

Here `p=23676511410391181435787` and `dummy_count=1`, so
`M0=k+15a+1=k+10036`. The geometry formulas simplify to

    H=51M0+3a+1,
    T1=105M0+4a+2,
    T2=159M0+4a+3,
    g=186M0+4a+4,
    L=least power of 5 at least 213M0+4a+5.

Thus `L=5^36`. The modified mask is
`mu=A-2+sum_(j=1)^J A^j`, with `J=9a+4+p`, so its exact bit length is
`tJ+1=1799414867189729789577713`. The stronger radix target is dominated
by `2mu+4`: a separate bound gives bit length at most 458130 for
`4(K+2)(2 sum c_e+6)+8`. To obtain that bound use

    sum c_e < (k+2)*A^(9a+5)

and then bound the integer leading coefficient by its bit length. Therefore
the exact chosen radix exponent is the least power of 5 at least `tJ+2`:

    b=5^35,
    d=bL=5^71,
    B=2^(5^71),
    W0=2^(5^35+2*5^71).

These values are evaluated and checked; only their enormous base-two
expansions are omitted. The sparse MC/MF/DC formulas above remain exact.
The generic closed scalar formulas were additionally compared against all
five materialized small compiler fixtures, including the padding and both
optional high-term cases.
