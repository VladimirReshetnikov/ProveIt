# Independent review of the fixed K215 machine and coefficient recipe

Reviewed on 2026-10-22 against ProveIt commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.

## Conclusion and scope

I found no correction needed in the folded machine, its initialization,
the Start/End windows, the exact window count, or the conservative fixed
coefficient parameters in the reviewed files. There is one necessary
wording distinction: this normalized machine ignores its unary input. It
accepts every positive input if K215 halts, and accepts none otherwise. It
is not literally a machine rejecting all odd inputs for the set S_even.
The compiler uses only input 2x, so at the required x=1 this makes no
difference: the marker distance is 2, the initial unary length is 4, and
acceptance is precisely blank-tape halting of K215.

This review reads the implementation and supplies mathematical invariants;
it is not a new Lean/Rocq formalization. It does not enumerate the full
window alphabet, expand the enormous coefficients, or evaluate a full
Pell witness. Those operations are not needed to define the fixed
integers or to prove the parameter inequalities. The inherited H10
compiler/Pell theorems remain ordinary mathematical proofs with finite
and symbolic checks, whereas the K215 endpoint has the separately stated
proof-assistant verification boundary.

The source files reviewed are coefficients/fixed_machine.py,
normalized_machine.json, coefficient_recipe.py,
coefficient_specification.json, the raw81/raw76/helical notes, and the
pinned repository's raw78 compiler/proof and modified75 compiler/proof.

Reviewed output hashes:

* normalized_machine.json:
  `2e4250b623edee16dd9857e02a726fdd8f9aeb3920f63c5adc1e4190a261d6ed`.
* machine_receipt.json:
  `3c5b6e47e89254f604c4815921d8850d2b925b5997e3f43716ce43cfbdaed449`.
* coefficient_specification.json:
  `a1fd73c6eda98ac3f6edbefe159006cd43e90d3d06bee80e6df3897a98856ed0`.

## 1. Literal K215 endpoint and folded simulation

The native table is the 215-state, 430-row table with SHA256
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
Its nonworking halt label is 254; its initial state is 0. The emitted
canonicalization map carries these to dense labels 215 and 0 and maps all
430 transitions, including written symbol and direction. The dense table
hash is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
This is the accepted dense K215 endpoint already audited separately.

For physical location n<=0 the pair of track bits encodes original cells

    side 0: original location -n;
    side 1: original location n-1.

The unique marked physical location n=0 therefore stores original cells
0 and -1. Plain symbol 0 encodes (0,0). The other ordinary pairs use
symbols 3,4,5; marked pairs use symbols 6,7,8,9.

If an original transition stays on the same side of the cut between -1
and 0, its physical displacement is minus its original displacement on
side 0 and its original displacement on side 1. At the cut, either
side-0/left or side-1/right changes side and makes physical displacement
zero. This is exactly the branch in Machine.__init__. Only the selected
track bit is written, so the other original cell represented at the same
physical location is preserved. The marked status is preserved. This
proves the complete step correspondence by induction, for every finite
native run; no execution-time or tape-space bound is assumed.

For every nonhalting native target the folded state retains the native
target and side. A native target 254 becomes the unique accepting HALT
state, after the prescribed write and movement. HALT then stays in place
forever. All otherwise missing transitions enter the absorbing TRAP
state, which never accepts. No valid folded run encounters a nonpaired
symbol. Consequently normalized simulation halts iff native K215 halts.

## 2. Initialization is exactly blank-tape simulation

Let the normalized input have ell>=1 ones at locations
-(ell-1),...,0, with initial head Q0 at 0 and blanks elsewhere.

The Q0 step writes flag 2 and stays at 0 in Q1. The Q1 step moves left
into ERASE. ERASE crosses and clears the ell-1 remaining ones, reaches
the first blank at -ell, and changes to RETURN while moving right.
RETURN crosses those ell-1 cleared cells, reaches the flag at 0, changes
it to marked blank pair 6, and enters sim(native state 0, side 0) without
moving. This takes exactly

    1 + 1 + (ell-1) + 1 + (ell-1) + 1 = 2ell+2

transitions. The resulting tape is the folded blank tape, with the
unique origin mark at 0. No positive physical coordinate is visited.
Thus every such unary input is erased before the exact blank K215 run.

For the fixed polynomial's x=1, the compiler's input distance is 2x=2;
the raw81 phase row has I-run length 3 and total unary length 4.

## 3. Fixed STAY windows and the helical relation

The tile alphabet has one V tile, one H tile, 10(436+1)=4370 ordinary
symbol/head tiles, and four initialization phase tiles, hence a=4376.
The phase graph has exactly LL,LI,II,IQ,QR,RR. With the boundary rules it
forces each initialized strip to have row L^a0 I^u Q R^b0 with a0,u,b0>=1.

The Start window is centered on the last I, immediately left of Q. Its
next-time row is headless 1, headless 1, flagged 2/Q1. The End window is
centered on the first I, with L,I,I in its initialization row and the
same three headless symbols on the next-time row. These windows are
valid for all u>=2, including u=2 when the centers are adjacent. The
stationary first transition is exactly what ensures that the Start's
next-time center remains headless. Their centers are u-1 cells apart.
Neither window occurs for u=1.

The code's local_valid predicate is the five-cell cross formulation of
the helical proof: vertical V propagation and separation; horizontal H
propagation only across non-V edges; H separation in time; canonical
initial phase payloads; no phases after initialization; a halted head
before the next H row; exact radius-one transition; no escape into V.
Its window alphabet contains all and only 3-by-3 windows over the finite
tile alphabet satisfying that cross predicate. Unchecked corners are
intentional: the exact horizontal and vertical overlap relation checks
the same local condition at every center in the reconstructed plane.

An initialized strip contains exactly one head. The exact update and
no-escape clauses preserve that fact at every row. Thus permitting
headless cells on the final row does not permit a headless fake run:
there is still one head, and the final-row clause forces it to be HALT.
The TRAP state cannot pass this condition.

The periodic-plane soundness argument in raw81 also applies after the
marker center moves from Q to the last I. A positive-distance End cannot
belong to another strip: that destination strip has at least two I's,
and walking left into it would first cross its Start, contradicting
Start's uniqueness. Intervening one-I strips are harmless. This handles
arbitrary cyclic N,h; h need not divide N in soundness. Completeness can
choose arbitrarily large width and height after a finite halting run is
given, as needed for the inherited powers-of-five padding.

The marker order is correct for raw76 and modified75: Start is selector
0 and End is selector 1. Raw81/raw78 historical prose has the opposite
order; the switch is made by raw77/raw76 and must be stated when citing
the historical chain.

## 4. Independent exact window census

I independently reproduced the count from an aggregate census of the
emitted 4360 transition rows, without importing fixed_machine or running
its verify/count_windows functions. The mathematical census is distinct
from the nested-loop count implementation.

Let nL,nR,nS count ordinary head tiles whose transition moves left,
right, or stays. The emitted table gives

    nL=1722, nR=862, nS=1776.

No transition targets Q0. The up-tile multiplicity for a headless symbol
is u(0)=3, u(1)=2, and u(s)=1 for the other eight symbols. Every reachable
headed up payload has multiplicity 1. The weights of moving transitions
by written symbol are

    ML=sum_left u(written)=2206,
    MR=sum_right u(written)=1348.

For a nonterminal row define

    l0=a-1-nR=3513, r0=a-1-nL=2653.

These count potential left/right neighbors sending no head into the
center. A center head moving left excludes the left V and reduces l0 by
one; a right-moving center analogously reduces r0 by one.

The boundary-center contribution is

    a^2(a-1)+2a^2(a-2)=251297261248.

There are 20 ordinary final-row center payloads (10 headless and 10
HALT), each giving a(a-1)^2 crosses. The three permissible headless
phase-center contributions sum to 6a-4. Thus final-row crosses total

    20a(a-1)^2+6a-4=1675187526252.

For ordinary nonterminal centers, summing over all headless/staying/
left-moving/right-moving centers gives, before the a-1 choices of down
tile,

    O=(13+nS)l0*r0+10(nR*r0+l0*nL)
      +ML(l0-1)r0+nL(nR*r0+(l0-1)nL)
      +MR*l0(r0-1)+nR(nR(r0-1)+l0*nL).

The resulting contribution is (a-1)O=312404288109375. The four phase
centers have a unique H down tile; their nonterminal contribution is
17l0+6nR-11=64882. Hence

    cross_count=314330772961757,
    k=cross_count*a^4=115264654755851622862362693632.

The factor a^4 is exact because the local predicate never inspects the
four corners. The special Start and End are distinct valid windows and
are merely moved to the front of the enumeration; neither is added or
removed. This independently agrees with the saved count.

## 5. Clause radix, padding and native support

Let ell=100 and A=2^ell. Then A>k+1 and A>=4. These are precisely the
raw78 proof's requirements; its chosen minimum power of two is not an
upper bound. The new choice additionally has A=1 modulo 5.

Put J0=9a+4 and let p be the least nonnegative integer such that, with

    J=J0+p, mu=A-2+sum_(j=1)^J A^j,
    m=2ell+2J+12a,

one has m+1>=k+9a+5. Since A is a power of two,
popcount(mu)=ell-1+J, so the displayed m is exactly
2popcount(mu)+12a+2. This is the padded mask-population formula of raw76.
The code's closed-form ceiling computes exactly this p. The native
position count K=m+1 therefore leaves at least one dummy position. Here
k and a are divisible by four, so the threshold is reached exactly and
there is precisely one dummy.

Selectors occupy [0,k-1]. The reversed payload formula is a bijection
onto [k+3a,k+12a-1]. The dummy is e*=k+12a. Put M=e*+1+3a, and anchors
M,3M,9M,27M. All these positions are distinct. E=27M is their maximum,
and e*+1<E. This is exactly the raw76 support with the modified75 extra
permitted bit at the existing dummy.

The clause weights have 14 terms per selector (one constant, nine
payload powers, four anchor powers), one power per payload or anchor,
and zero at the dummy. Each base-A clause digit is at most k+1<A, so
there is no clause carry. The occupancy mask A-2 forces zero or one
selector; the other mask-1 clauses then force the copies and anchors to
be precisely those of the selected window, or all zero.

## 6. Conservative radix bound is sufficient

Write n=k+9a+4 for the number of nonzero coefficient positions and
S=sum c_e. Every nonzero c_e<=14A^J, hence S<=14nA^J. Also
mu<A^(J+1). The code sets

    G=128(K+2)n+16,
    b=least power of 5 >= ell(J+2)+bit_length(G),
    R=2^b.

Consequently R>G*A^(J+2). In particular it strictly exceeds all three
modified75 requirements

    4(K+2)(2S+6)+8, 2mu+4, 16.

For the first, the target is at most
112(K+2)nA^J+24(K+2)+8, already below G*A^J; the factor A^2 supplies
still more room. For the second, A>=4 and J>=1 give
2A^(J+1)+4<=A^(J+2). Thus using a conservative fixed upper bound instead
of numerically forming S or mu is valid.

Set H=E+24M+3a+1, T1=H+2E+a+1, T2=T1+2E+1, g=T2+E+1, and take L as
the least power of five at least g+E+1. Then L>g+E. This supplies every
raw76/modified75 separation inequality. Actual parameters have
b=L=5^45 and d=bL=5^90. These are fixed integers; their enormous size
does not introduce exponentiation of a Diophantine variable.

## 7. Native geometry, masks and synchronization

The four low DC shifts have exactly their intended effects: 3a copies
bottom two payload rows onto top two; H+a and DR=R^H compare adjacent
payload columns; 8M and 24M map anchors M and 3M to 9M and 27M. The
gaps before the payload block, before anchors, and before H exclude other
native support at tested locations. The first clause-convolution band
starts above H+E+a, and T2-T1=2E+1 exceeds all support differences. At
T1 or T2 only matching convolution exponents contribute.

The expanded possible support under an unaligned binary rotation is
E_support union {e*+1}, still contained in [0,E]. It cannot hit both T1
and T2 modulo L: their separation is 2E+1 and the complementary circular
separation exceeds E. The difference 18M occurs exactly once between
native support elements, as 27M-9M. With L>2E it has no wrapped
alternative. These are the clean-band and anchor uniqueness properties
used in the synchronization proof. The modified75 spill case is also
covered: the extra high dummy bit can supply an odd residue at only one
within-cell position, so it cannot populate both anchors.

All old tested MF positions are disjoint; their bit population is m.
The old MC clears one bit at each of K-1 positions, since selector 1 is
excluded, and therefore has population d-m. Subtracting 2R^e* clears
the previously permitted binary bit 1 at the dummy with no borrow;
adding 4 to MF sets one previously zero low bit. Thus the new populations
are d-m-1 and m+1, summing to d. The support is strictly below the top
of the B-cell, so 0<MC,MF_native<B-1. MC is even and MF_native=4 modulo
8. The source coefficient is MF_native+B-1, as required by modified75;
the native-mask bound must not be applied to that shifted source value.

## 8. Exact optional-high-term exclusion

Because b is a power of five, R=2 modulo 5. Since ell is divisible by
four, A=1 modulo 5. All selector coefficients are therefore 14 modulo
5 and all payload and anchor coefficients are 1 modulo 5.

The selector interval has length k divisible by four; the payload
interval has length 9a divisible by four. Each interval contributes
zero to sum_e c_e*2^(-e) modulo 5. Here M=1 modulo 4, so the anchor
exponents M,3M,9M,27M have residues 1,3,1,3, whose reciprocal powers
of 2 also sum to zero modulo 5. Hence the entire convolution contribution
to DC is zero modulo 5, independently of T1,T2.

H=51M+3a+1 is 0 modulo 4. All four low DC shifts 3a,H+a,8M,24M are
therefore 0 modulo 4. They contribute DC=4 modulo 5, while DR=1 modulo
5. Thus 2DC-DR=2 modulo 5. The optional high correction is exactly zero;
its omission is proved from finite integer congruences, not assumed.

## 9. Boundaries of the claim

The reviewed algorithm is a complete finite definition of the fixed
coefficients, with finite loops bounded by the explicit machine/window
data. It uses no halting oracle or proof search to select a coefficient.
The algebraic inequalities above establish admissibility for the
inherited compiler theorem even though the full coefficients are never
materialized. That is sufficient for an ordinary explicit Diophantine
construction using integer coefficients defined by fixed finite sums.

The repository's formal K215 theorem and the ordinary H10 mathematical
proof should retain separate status in the final report. No file in
this review upgrades the H10 compiler or the new 16/15-variable
specialization to a newly machine-checked theorem in Lean or Rocq.
