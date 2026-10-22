# A 5,268-tile blank-K215 compiler with B = 2^(5^17)

This note proves a further coefficient reduction for the fixed-input
Diophantine constructions in ProveIt. It is an ordinary mathematical
argument, not a new Lean/Rocq formalization. The machine and source review
are pinned to `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

## 1. Imported interface and exact scope

Use the complete T4 adapter in
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/11-t4/bridge/BRIDGE_AUDIT.md`.
That adapter supplies the native/Pell compiler for a cyclic word of marked
four-cell tiles with three copy constraints, using four fixed integer ports

    beta=B-1, K=DC+B*DR, MC, MFsrc=MF_native+B-1.

Its proof supplies ordinary soundness and completeness, including arbitrary
cyclic temporal strides, unaligned-bit synchronization, positive canonical
slack, and Boolean-dummy adjustment of the actual packed Pell index. The
new construction preserves that interface. The full native/Pell results,
and the exact blank-K215/refutation theorem, remain substantive imported
mathematical dependencies. Finite checks do not replace those proofs.

The literal K215 table is included as `k215.tm` with SHA-256
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
All 430 transitions, including the movement and write on entry to halt,
are retained. State215 is made absorbing only after it is entered.

## 2. A restricted four-cell language

Keep the 439 T4 cell codes. Ordinary headless bits are0,1. An ordinary head
in state q reading bit b has code2(q+1)+b for0<=q<=215. The remaining codes
are L=434,Q=435,R=436,V=437,H=438. Initial phases L,Q,R have blank payloads,
with only Q carrying the state0 head. V,H are payloadless boundaries.

Let `Base(l,c,r,n)` be the literal T4 predicate of package11. In particular,
it has at most one head in(l,c,r), propagates V vertically, propagates H
horizontally except through V, uses the initial phase edges LL,LQ,QR,RR,
updates the binary machine deterministically, and permits a head just
before H only when its state is215.

Restrict Base by the following additional conditions.

1. Both horizontal edges(l,c),(c,r) belong to the relation E:
   - E(V,b) iff b is0,L,or H;
   - E(a,V) iff a is0,R,or H;
   - with neither endpoint V, an H endpoint requires both endpoints H;
   - with neither endpoint a boundary, a phase endpoint requires one of
     LL,LQ,QR,RR;
   - two ordinary symbols are allowed.
2. If c is ordinary and l=V, then r is headless. If c is ordinary and r=V,
   then l is headless.
3. If n=H, every head among l,c,r has state215.

Call the resulting predicate `Good`. It is exactly `valid` in
`../compiler/pruned_t4_check.py`. The code independently transcribes Base and then
applies the displayed restrictions; it imports no upstream program.

Put Start=(L,Q,R,1), and Forbidden=(V,H,V,Q). Both satisfy Good. The first
uses the actual first K215 action(0,0)->(1,right,93). Forbidden cannot occur
in a globally overlapping plane: its two V neighbors propagate vertically,
so its following Q would be adjacent to V, contradicting the phase endpoint
rule. In particular its following Q would have to be L from the left and
R from the right.

Order the alphabet with Start first, Forbidden second, and all remaining
Good quadruples lexicographically. Forbidding selector1 therefore loses
no globally valid plane.

## 3. Halting equivalence and seam proof

For tiles w_i in a cyclic group Z/NZ impose

    w_i.r = w_(i-1).c,
    w_i.c = w_(i-1).l,
    w_i.n = w_(i-h).c.

With a_i=w_i.c, these equations identify
w_i=(a_(i+1),a_i,a_(i-1),a_(i-h)). Pullback along(x,t)->-x-ht therefore
gives the actual neighborhoods of a globally valid plane, even when some
cyclic offsets coincide. No divisibility or coprimality assumption on h,N
is used. A marked Start excludes h=0 moduloN.

**Soundness.** Good implies Base. Hence the existing T4 finite-strip
argument extracts an initialized finite halting computation from any
marked cyclic Good word. The extra restrictions cannot create a spurious
computation.

**Completeness.** Suppose blank K215 halts after finitely many steps.
Choose a finite tape interval containing every visited head position and
at least two unvisited positions between each end of that visited range
and its vertical boundary. Those margin positions remain blank and
headless for the entire run. Add arbitrarily many absorbing halt rows.
As in package11, construct a rectangle G with a V boundary column, an H
top row, an initial L^u Q R^v row, and the run followed by halt padding.

Extend it helically by

    T(x,t)=G(x mod W, (t+floor(x/W)) mod Ht).

Every horizontal edge avoiding V lies at one time within one copy of G.
It is therefore H/H, one of the four phase edges, or ordinary/ordinary.
An edge crossing V sees a first or last interior cell. At any time that
cell is blank0, the appropriate phaseL orR, or H, exactly as required by
E. This statement holds independently on the two sides of the seam;
the one-row helical time offset causes no problem.

An ordinary center adjacent to V is the first blank margin position. Its
other horizontal neighbor is the second unvisited margin position and is
headless. This proves restriction2, including seam neighborhoods.

If an interior center is followed by H, its current row is the last
absorbing-halt row of G. Every head in its own strip is in state215.
A horizontal neighbor across V is in the permanent margin, so it adds no
working head from another time. Thus restriction3 holds. Centers H,V do
not produce an exceptional n=H case.

The inherited at-most-one-head filter holds for the same margin reason.
Consequently every four-cell neighborhood of this helix is Good. The
canonical cyclic word has one Start and no Forbidden tile. Extra margins
and halt padding let W,Ht be chosen independently as arbitrarily large
powers of5, without changing any restriction.

This proves that marked cyclic Good-word existence is equivalent to blank
K215 halting. In particular the new language need not equal all old T4
planes: the construction only needs the stated halting equivalence.

## 4. Exact alphabet cardinality

There are433 headed codes and six headless codes. The exact census is:

| Center | Multiplicity | Good tuples per center | Contribution |
|---|---:|---:|---:|
| ordinary headless0 |1|1754|1754|
| ordinary headless1 |1|1744|1744|
| working head |430|4|1720|
| halted head |2|8|16|
| L |1|6|6|
| Q |1|1|1|
| R |1|6|6|
| V |1|9|9|
| H |1|12|12|
| total |439| |5268|

For ordinary0 followed by an ordinary cell, both non-V neighbors contribute
4+2*432*2=1732 choices; a V neighbor permits only a headless other neighbor,
adding five choices, for1737. If its successor is H, replace432 by the two
halted-head symbols, giving12+5=17. Thus its count is1754. For ordinary1,
no V neighbor is allowed, so the counts are1732+12=1744.

A working center has two ordinary headless choices on each side and only
its deterministic ordinary successor, giving4. A halt center has the same
four contexts and may have ordinary or H successor, giving8. L has four
ordinary-successor contexts and two H-successor contexts; R has the same
count. Q has only the L,Q,R context and its forced successor1. A V center
has three allowed left and three allowed right codes and successor V.
An H center has two possibilities on each side and three following phases.

The independent checker exhausts all46,980 horizontal triples surviving
the head filter. Its exhaustively justified output list contains every
possible successor: V for a V center, L/Q/R for H, and H plus the unique
deterministic ordinary update otherwise. It reproduces the inherited
37075 count before pruning and5268 afterward. The ordered literal list is
`pruned_t4_windows.json`, SHA-256
`6b53241de552096888a80c4d1947d061c32c1efac1f014ffedccfd06f5a6ea47`.

## 5. Complete coefficient recipe

The following definitions denote four specific integers. No coefficient
depends on whether K215 halts. Every sum has a fixed finite bound.

Put

    a=439, k=5268, ell=13, A=2^13,
    rho=2^78125, B=rho^9765625=2^(5^17).

For u=0,...,438 define

    e_l(u)=8780+u, e_c(u)=8341+u,
    e_r(u)=7902+u, e_n(u)=7024+u.

Let E be the disjoint union of selectors0,...,5267, those four copy
intervals, dummies10536,10537, and anchors11855,35565,106695,320085.
It has7030 members. Put

    mu=A-2+sum(A^j,j=1..2843).

For the ordered tile w_i=(l_i,c_i,r_i,n_i) define

    v_i=1+A^(1+l_i)+A^(440+c_i)+A^(879+r_i)+A^(1318+n_i)
        +sum(A^(1756+t),t=1..4).

The four copy coefficients are A^(1+u), A^(440+u), A^(879+u), A^(1318+u),
respectively. The anchor3^(t-1)*11855 has coefficientA^(1756+t), for1<=t<=4.
Both dummy coefficients are0.

Define

    DC=rho^1317+rho^606362+rho^94840+rho^284520
       +sum(v_e*(rho^(1246533-e)+rho^(1886707-e)),e in E),

    DR=rho^605923,

    MF0=mu*(rho^1246533+rho^1886707)
        +sum(rho^(8341+u),u=0..438)
        +sum(rho^(614703+u)+rho^(614264+u),u=0..438)
        +rho^106695+rho^320085,

    MC=B-1-sum(rho^e,e in E except1)-2*rho^10536,
    MF_native=MF0+4.

The four polynomial ports are

    beta=B-1, K=DC+B*DR, MC, MFsrc=MF_native+B-1.

The extra upper binary dummy bit is present only at the first dummy10536.
The second dummy10537 has only its ordinary low bit. Never apply the
factor2 correction to both dummies. The shifted source port is MFsrc;
it must not be replaced by MF_native.

These definitions, all scalar geometry, and exact tile binding are also
in `../compiler/pruned_t4_constants.json`.

## 6. Native layout proof and finite audit

This is the same four-copy/three-overlap construction as package11, with

    p=1083, jmax=2843, m=7029, nd=2,
    M=11855, Emax=320085, Hc=605923,
    T1=1246533, T2=1886707, bmin=36975,
    b=78125=5^7, Lcell=9765625=5^10, d=5^17.

All payload copies use the inherited exponent grid
e(r,c,u)=k+3a+(2-r)3a+(2-c)a+u at(1,0),(1,1),(1,2),(2,1).
Their geometry is independent of tile contents. The new finite audit
checks all7030 native positions, all1319 copy/anchor targets, and both
clause bands at the actual scalar values, without expanding final integers.

At each copy target the only surviving sources are exactly its prescribed
pair; at the two anchor targets they are exactly the old anchor pairs.
Clause terms start above all copy/anchor tests, and the bare shifts cannot
hit a clause target. The two clause bands have separation640174, greater
than2Emax and congruent2 modulo4. Their opposite circular separation also
exceeds Emax. The actual support has exactly one pair at anchor difference
18M, namely(9M,27M), and no wrapped extra pair.

The all-rotation proof is unchanged. Write a bit rotation exponent as
bt+epsilon with0<=epsilon<b. If1<=epsilon<=b-2, all possible low radix
digits are even. Ifepsilon=b-1, only the upper bit of the first dummy can
produce an odd spill, at dummy_start+1. The second dummy low bit there
rotates to the even value rho/2 and creates no second odd spill. Thus two
odd anchor tests forceepsilon=0. The unique anchor difference then forces
the radix rotation to align to a full native cell. The separated clause
bands guarantee an uncontaminated clause test before this conclusion.

The population and carry identities are explicit:

    pc(mu)=13-1+2843=2855,
    pc(MF_native)=2*2855+3*439+2+1=7030,
    pc(MC)=d-7030.

Thus populations sum to d. The literal supports also give
0<MC,MF_native<B-1, MC=2 modulo4, MF_native=4 modulo8. If
S=sum(v_e), the selector/copy census gives

    S<=9(k+4a+4)A^(4a+4).

The standard requirement
rho>max(4(npos+2)(2S+6)+8,2mu+4,16)
follows from b>=36975. The checker verifies this again with the actual
manageable integers mu and S, whose bit lengths are36960 and22893.
It finds the first carry bound has22909 bits, well below b=78125.

Because rho=2 modulo5 and the clause gap is2 modulo4, all paired clause
terms cancel modulo5. The four bare monomials give DC=3 modulo5;
DR=3 modulo5. Hence2DC-DR=3 modulo5, as required for actual-index tuning.

The native coefficient construction therefore supplies exactly the same
compiler contract as package11. In particular one marked tile propagates
occupancy around the cyclic spatial word, and the three copy groups give
precisely the overlaps of Section3. The upper dummy bit, all unaligned
rotations, canonical positive slack and the source-mask shift are paid.

## 7. Canonical witness freedoms and signed-domain transfer

Width W and height Ht remain independently arbitrarily large powers of5.
Take Ht>=25 and N=W*Ht>25d, as in the original adapter. Then N,d are odd.
Use the first dummy's low bit for the same Boolean subset adjustment. Its
coefficient remains a unit modulo dN because2DC-DR=3 modulo5. The actual
packed index can therefore satisfy R=dW modulo dN, with every no-wrap and
size condition used by the inherited proof.

The origin test is unchanged: only selector0 has the native unit bit,
there is exactly one canonical Start, the temporal stride is nonzero,
and dummies occur at strictly higher exponents. Thus the canonical
positive-solution construction, including its Pell-rank choices, works
without alteration. All native mask parity lemmas carry over because
MC mod4, MF_native mod8, and d being a power of5 are unchanged.

In particular, any signed-domain arithmetic proof relying on the original
contract's canonical odd rank, odd strong multiplier, square-scale witness,
or odd auxiliary root may reuse those lemmas. This note does not infer
those arithmetic properties from the tile census: it preserves the full
hypotheses of the original witness construction. Algebraic transformations
must continue to use the entire new quartet together.

The relevant parity calculation can also be made explicit. Write
q=B^N=2^t, t=dN, and J=(q-1)/(B-1). Then q=0 modulo4 and J=1 modulo4.
The canonical packed word C has its Start-selector bit at the origin and
no second binary bit there, hence C=1 modulo4. Neither dummy touches these
two bits. Using G=q(q-F)-C and
R=G(q^2-1)+(MC+q*MFsrc)J gives

    R=C+MC=3 modulo4.

Both R and t are odd. The canonical power extraction X=2^R therefore gives
w=X/q=2^(R-t), an integer square; its exponent is positive and even. This
is a restriction on the chosen complete witness, not on all old solutions.

Let A0=a+2 and Delta=A0^2-1. Since Y=sq^3 is even, a=Y(X+1) and A0 are
even and Delta is odd. With c=psi_A0(R), the Pell recurrence shows c odd.
Choose the normalized strong index

    m=cR, f=chi_A0(m), i=psi_A0(m)/c^2.

In the coefficient of sqrt(Delta) of
(chi_A0(R)+c*sqrt(Delta))^c, the first term has a factor c^2 and all later
odd terms have at least a factor c^3. Thus i is integral. Both m and c
are odd; the same Pell recurrence makes psi_A0(m) odd, so i is positive
and odd. For the ordinary strong convention use i_ordinary=Delta*i, also
positive and odd. Finally rho_aux=Delta*psi_A0(m) is odd and the canonical
auxiliary choice y=psi_rho_aux(R) is odd. The inherited odd-index quotient
identities, with R=3 modulo4, complete V and T as in package14's
`proofs/signed_domain_proof.md`, without changing any packed-word data.

## 8. Logical calibration and verification boundary

The pinned ordinary K215 proof at
`Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md`
explicitly concludes that ZFC proves blank halting iff not Con(ZFC).
Its finite blank initialization, quantified register simulation and
dominated-calculus calibration are not hypotheses of consistency.

The inspected Lean endpoint has literal type

    BlankHalts machine215 <-> BProv ZFCax_s [] Form.fBot.

The Rocq endpoint is

    Dense.halts dense_tm Dense.c0 <-> StandardZFC |-TC bottom.

These are finitary-refutation statements, not existence of an externally
well-founded model. The shared Lean endpoint's ZF/ZFC transport uses the
constructible substructure of an arbitrary model and first-order
soundness/completeness. It assumes neither a transitive model nor an
omega-model. An ordinary internal-ZFC proof is justified by the imported
ordinary mathematical arguments and these finite arithmetic constructions;
external kernel checking by itself is not being presented as an encoded
derivation in ZFC's syntax. The repository's internal-PA endpoint remains
a separate open formalization task.

Taking negations of solution existence iff finite ZFC refutation proves
the requested unsolvability iff Con(ZFC). No assumption of consistency is
needed for the equivalence, and no proof of either side is supplied.

The finite audit verifies the literal machine, old/new local counts,
actual support geometry, exact finite mass bounds, population identities,
the mod5 unit and32 padded control helices with2096 local windows. The
controls are deliberately modified halting machines, not claimed K215
accepting computations. The complete unbounded correctness argument is
Sections3 and6 together with the imported native/Pell theorem. It has not
been newly formalized in a proof assistant.
