# A pruned T4 alphabet and compact synchronization anchors

## Result and scope

This note defines one complete replacement coefficient tuple for the fixed
blank-input K215 arithmetic interface. It combines the 11-t4 four-cell
compiler with two further reductions:

1. retain only 5,252 local tiles, using globally necessary adjacency
   conditions and blank margins that can be imposed on every finite halt;
2. replace the four synchronization anchors at M,3M,9M,27M by
   M,2M,3M,7M.

The resulting base is **B=2^(5^16)**. The previously smallest T4 base is
2^(5^18). Thus the exact binary length of beta=B-1 decreases by a factor
25, from 3,814,697,265,625 to 152,587,890,625 bits. K has exactly
199,861,875,001 bits. The four final integers are specified by finite
formulas, not expanded into their huge binary numerals.

The theorem is a new ordinary mathematical compiler adapter, using the
substantive native compiler/Pell theorems already in ProveIt. It is not a
new end-to-end Lean/Rocq theorem. The executable checks verify the finite
alphabet, support geometry, mass bounds, and finite control examples;
they do not establish the universal inherited compiler lemmas by testing.

Repository snapshot: f0ae4e0991ca44a7bb4e5671d42e33d775e48035.
Inherited local compiler: the folder 11-t4/bridge under
SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms.

## 1. Literal machine and symbols

The machine is the literal candidate-k215/k215.tm, SHA-256
fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090.
There are 430 transition rows on working states 0,...,214. The start is
state 0, blank symbol 0, and halt state 215. Retain the write and movement
of every transition entering halt; only after halt add the padding rules
(215,b)->(b,0,215). The first transition is (0,0)->(1,+1,93).

Retain the 439 T4 cell codes:

* codes 0,1: headless binary tape cells;
* code 2(q+1)+b: a tape cell b with head state q, 0<=q<=215;
* L=434, Q=435, R=436: initialized blank phases, with Q carrying the
  unique initial state-0 head;
* V=437: vertical boundary; H=438: horizontal boundary.

An ordinary four-cell tile is (l,c,r,n), with next-time center n. Begin
with the exact T4 predicate in 11-t4/bridge/check_t4.py. This predicate is
also explicitly copied as old_valid in check_pruned_t4.py. Its original
head filter allows at most one head among l,c,r. Its global overlap
conditions identify these coordinates with actual neighboring cells.

Define a horizontal edge predicate E(x,y):

* if either endpoint is V, they are not both V; a phase immediately to
  the right of V is L; a phase immediately to the left of V is R;
* otherwise, x is H iff y is H; if either is a phase, the pair is one of
  (L,L),(L,Q),(Q,R),(R,R).

For all ordinary tiles impose the following additional conditions:

1. E(l,c) and E(c,r).
2. If any of l,c,r is V, none of l,c,r carries a head or is the headless
   tape symbol 1.
3. If n=H, none of l,c,r is an initialized phase or a nonhalting head.
4. If c=H and l=V then n=L; if c=H and r=V then n=R.

Keep the distinguished Start S=(434,435,436,1). Also include the single
exception E_bad=(438,0,0,438), even though it fails the new edge filter.
E_bad satisfies the old T4 predicate and is globally impossible in every
old T4 tableau: its left H has a non-V right neighbor 0, contradicting
horizontal H propagation at that left cell.

Order the alphabet as S first, E_bad second, then all remaining tiles
lexicographically. This is a bounded finite definition independent of
whether K215 ever halts.

## 2. Why this pruning preserves the blank-halting language

Every retained tile satisfies the old T4 predicate. Therefore every
marked periodic tableau over the new alphabet is an old marked periodic
tableau. The original T4 soundness theorem yields a blank K215 halt.
The exceptional tile E_bad causes no additional global configurations,
because it was already globally impossible before pruning.

Conversely, suppose K215 halts after finitely many steps. Choose the
vertical walls outside the finite visited tape interval with at least
three unused blank cells on each side. The entire run, including its
absorbing halted tail, then has a permanent blank headless margin next
to each wall. Choose width and height independently as sufficiently
large powers of five, as in the original helical construction.

The standard finite rectangle satisfies E on every horizontal edge:
interior H rows propagate across their strip; initialized rows are
L^u Q R^v; all other interior rows are ordinary tape configurations.
Every neighborhood meeting V has only blank headless ordinary cells or
the phase/boundary symbols permitted above, so condition 2 holds.

When n=H in a genuine rectangle, the whole preceding interior row is
the final halted configuration. Every head visible in the triple is
therefore a halt head. This row is not an initialized phase row, because
K215's first transition enters working state 93 rather than halt.
Thus condition 3 holds. The first row following an H row is initialized,
so its first and last interior cells are L and R; condition 4 follows.

The helical extension shifts the neighboring strip by one time step
across each V seam. V blocks horizontal boundary propagation, and the
permanent unused margins are blank and headless at both times. The
additional conditions therefore remain valid across every seam. In
particular a triple centered at V can see unrelated H/phase/ordinary
times on its two sides, which our edge predicate explicitly permits.
The resulting cyclic word has its unique canonical Start and no E_bad.

Thus the same marked periodic-tableau/blank-halting equivalence holds.
Larger independent power-of-five widths and heights remain available;
these are needed by actual-rank dummy-bit tuning and the signed-domain
square-scale construction.

## 3. Finite census and reproducible data

The head filter leaves exactly 46,980 possible horizontal triples over
the 439 cell codes. The added horizontal filters leave 5,215 triples.
Checking all their 439 successors, and then inserting E_bad, gives
exactly 5,252 tiles. Their center-class census is:

| Center class | Number |
| --- | ---: |
| Headless tape symbols 0,1 (including E_bad) | 3,495 |
| Working-state heads | 1,720 |
| Halt-state heads | 16 |
| L | 3 |
| Q | 1 |
| R | 3 |
| V | 9 |
| H | 5 |
| Total | 5,252 |

This census also has a direct class calculation. For an ordinary headless
center, the nonboundary triples have either two headless neighbors
(4 choices), or one of 432 ordinary heads on one side and a headless bit
on the other (2*432*2 choices). They give 1732 ordinary successors for
each center bit. A zero center has three additional blank-boundary
triples (V,0,0), (0,0,V), (V,0,V). Next-H cases have the same count with
432 replaced by the two halted heads: 4+2*2*2=12, plus the same three
boundary cases for a zero center. Thus the zero center contributes
1732+3+12+3+1=1751 including E_bad; the one center contributes
1732+12=1744. Every working-head center has four headless-neighbor
choices and one ordinary successor; every halt-head center has the same
four ordinary successors and four H successors. L and R each have three
allowed phase triples, Q has one, V has three choices on either side,
and H has three interior-phase choices plus the two single-wall cases.

The ordered literal list is pruned_t4_windows.json, SHA-256
baa3d2b5296b818b2e6488c1b06fda29e405d9b4cf5dd19a3c38fbdd1ba658d7.
check_pruned_t4.py regenerates this list from the literal transition
JSON, checks inclusion in old_valid, and checks 18 finite halting control
tableaux across 1,143 local windows. The general padding proof is the
argument in section 2, not an extrapolation from these control examples.

## 4. Complete fixed coefficient recipe

Use a0=439, k=5252, ell=13, A0=2^13, rho=2^78125,
B=rho^1953125=2^(5^16). Write w_i=(l_i,c_i,r_i,n_i) for the ordered
tile list. For 0<=u<=438 put

    e_l(u)=8764+u, e_c(u)=8325+u,
    e_r(u)=7886+u, e_n(u)=7008+u.

The support mathcal_E consists of selector positions 0,...,5251, the
four copy intervals, dummy positions 10520,10521, and anchor positions
11839,23678,35517,82873. It has 7014 elements. Set

    mu=A0-2+sum_{j=1}^{2835} A0^j.

The clause coefficients are

    v_i=1+A0^(1+l_i)+A0^(440+c_i)+A0^(879+r_i)
          +A0^(1318+n_i)+sum_{t=1}^4 A0^(1756+t),
    v_e_l(u)=A0^(1+u),       v_e_c(u)=A0^(440+u),
    v_e_r(u)=A0^(879+u),     v_e_n(u)=A0^(1318+u),
    v_11839=A0^1757, v_23678=A0^1758,
    v_35517=A0^1759, v_82873=A0^1760,
    v_10520=v_10521=0.

Define the following integers by finite sums:

    D_C=rho^1317+rho^605546+rho^23678+rho^59195
          +sum_{e in mathcal_E} v_e
               (rho^(771293-e)+rho^(937043-e)),
    D_R=rho^605107,
    M_F^0=mu(rho^771293+rho^937043)
          +sum_{u=0}^{438}rho^(8325+u)
          +sum_{u=0}^{438}(rho^(613871+u)+rho^(613432+u))
          +rho^35517+rho^82873,
    M_C=B-1-sum_{e in mathcal_E, e!=1}rho^e-2rho^10520,
    M_F^nat=M_F^0+4.

The four ports, taken together, are

    beta=B-1, K=D_C+B D_R, M_C, M_F^src=M_F^nat+B-1.

All powers here have fixed integer exponents. These formulas define four
particular integers. They do not add unknowns, variable exponentiation,
or predicates to any resulting Diophantine equation. Mixing ports from
this recipe with another layout would have no proved interpretation.

## 5. Population, radix, target and synchronization proofs

The padding parameters are p=1075 and m=7013. The population of mu is
12+2835=2847; consequently

    pc(M_F^nat)=2*2847+3*439+2+1=7014,
    pc(M_C)=d-7014,      d=5^16.

The last +1 is the low-bit marker 4. In M_C all 7013 support bits other
than selector 1 are removed, together with the separate upper-dummy bit.
Thus pc(M_C)+pc(M_F^nat)=d. Also

    0<M_C,M_F^nat<B-1,
    M_C=2 (mod 4), M_F^nat=4 (mod 8).

Let M0=11839, Emax=7M0=82873, Hc=605107,
T1=771293, T2=937043, Lcell=1953125. All nonanchor support is below M0.
The bare shifts 2M0 and 5M0 feed source anchors M0 and 2M0 to target
anchors 3M0 and 7M0. They cannot reach a copy target, because the copy
support ends below M0. At 3M0 the 2M0 shift hits exactly M0; at 7M0 the
5M0 shift hits exactly 2M0; the unwanted shifted preimages are absent.
The low copy shift 3a0 cannot connect anchor positions, whose gaps exceed
3a0. Every low shifted support term is below Hc.

The retained copy positions have precisely the same relative geometry
as the T4 compiler: the shift 3a0 maps next copies to center copies;
the shifts Hc+a0 and Hc enforce the two horizontal overlaps. The high
copy band is below T1-Emax. The bands have separation

    T2-T1=2Emax+4,
    T2+2Emax+2 < Lcell,

so they cannot contaminate each other's tested coefficients. The exact
checker exhausts all 1319 copy and anchor targets against the complete
support, plus both center-clause targets.

The original uniform no-carry bound is preserved. Each selector has
nine A0-monomials, while each copy and anchor has one. Put

    mass=(|mathcal_E|+2)(2 sum_e v_e+6).

The exact manageable integer sum has bit length 22893; 4mass+8 has bit
length 22909. The mask mu has bit length 36856. The sufficient scalar
bound bmin=36871 is below b=78125, and direct exact checks give

    4mass+8 < rho,       2mu+4 < rho.

Thus all arbitrary native cells, and the additional possible upper-dummy
bit, satisfy the same no-carry bounds used in the original compiler.

For arbitrary cyclic rotation, at least one of the clause bands is clean:
their separation and its circular complement both exceed the support
diameter. A clean band makes the marked cell's four anchors equal 1.
If the within-radix binary residue is 1,...,b-2, all rotated radix digits
are even. If it is b-1, only the one upper-dummy spill can create an odd
rotated digit. The two distinct anchor tests require two odd rotated
digits, excluding both possibilities. The binary residue is therefore 0.

For an aligned radix rotation, the two targets 3M0 and 7M0 must both lie
in shifted native support. Their difference is 4M0. It occurs in the
ordinary support difference set in exactly one ordered way:
7M0-3M0. Indeed the nonanchor support is below M0, the other three
anchors are M0,2M0,3M0, and the remaining differences involving 7M0 are
5M0,6M0, or more than 6M0. All other differences are below 3M0.
There is no wrapped alternative because Lcell>2Emax. The shift is
therefore 0 modulo Lcell. This proves exactly the whole-cell alignment
that the old anchors supplied, with no additional condition on the
temporal stride.

The overlaps recover the same actual four-neighbor plane. Start forces
positive occupancy, which propagates around the whole cyclic word via
the spatial shift of one cell. The local soundness/completeness theorem
from section 2 now applies.

## 6. Actual-rank tuning and signed-domain compatibility

The difference T2-T1 is 2 modulo 4, and b is 1 modulo 4. Thus the two
clause contributions cancel modulo 5. For this exact layout,

    D_C=2^1317+2^605546+2^23678+2^59195=3 (mod 5),
    D_R=2^605107=3 (mod 5),
    2D_C-D_R=3 (mod 5).

The inherited Boolean dummy-bit construction therefore tunes the
**actual packed rank** R to the required residue modulo dN. It works
using the first dummy position 10520; the unused second dummy may be
kept zero. The proof uses independent sufficiently large power-of-five
width and height, preserved in section 2, and d remains a power of five.
All dummy changes preserve the tile choices and local overlaps.

The canonical origin mask test is unchanged: only the temporal-neighbor
Start contributes to the relevant unit digit, and the canonical tableau
has one Start with a nonzero temporal shift. Dummy contributions have
strictly positive high exponents and do not alter it. Positive raw slack
and fresh Pell witnesses at the final actual rank are therefore supplied
by the same native compiler completeness proof.

Every arithmetic reduction proved over the old four-port blank compiler
interface transfers by replacing the whole tuple. This includes the
ordinary-strong system, normalized 67-operation equation, root
amalgamations, and the signed-domain argument in package 14-integer29.
For the signed argument, the essential additional facts are preserved:
d is an odd power of five; the canonical N is a power of five;
the two mask low-bit congruences are unchanged; and the canonical rank
satisfies R=3 (mod 4). Hence q=2^(dN), w=2^(R-dN) is still a square,
and choosing the odd auxiliary index m=cR still supplies an odd strong
multiplier. No claim that every old witness has these restrictions is
needed; completeness uses the canonical witnesses.

## 7. Logical and Pell dependencies audited

The pinned KEndpoint215.lean states the unconditional exact-table theorem

    BlankHalts machine215 <-> BProv ZFCax_s [] Form.fBot

and its negation. BProv is syntactic finite derivability, with no model
existence or consistency premise. The ordinary calibration in
candidate-k215/proof.md explicitly gives an argument formalizable in ZFC.
The new Diophantine equivalence uses that ordinary calibration; it does
not attempt to infer ZFC-provability from Lean's own soundness.

For the ordinary strong equation (ic^2)^2=Delta(f^2-1), the relaxed
Pell-rank lemma was inspected in PELL_RELAXED_AUXILIARY_PROOF.md. Its
large-rank premise c>A Delta^2 is indispensable. The proof recovers
integrality at the intended Pell parameter using strong divisibility
in the integer-coefficient quadratic ring and the proper-divisor bound.
The subsequent binomial congruence gives c|m, after which c^2|f^2-1
follows. Simply cancelling Delta in the displayed square equation would
be invalid. The arithmetic packages establish the needed large-rank
bound before invoking this lemma.

The main imported native facts are in FIXED_RAW_UNIVERSAL_78_PROOF.md
(carry-free coefficient tests and clean-band/anchor synchronization),
FIXED_RAW_UNIVERSAL_76_PROOF.md (actual-index dummy control), and the
native-stream-queue half-binomial/compiler notes. Their universal
mathematical statements remain dependencies; no finite check here is
described as proving them. The modified anchor proof above explicitly
replaces the only part that depended on the old anchor locations.

## 8. Comparison and reproduction

| Compiler | Tiles | b | Lcell | d |
| --- | ---: | ---: | ---: | ---: |
| Existing T4 | 37075 | 5^8 | 5^10 | 5^18 |
| Pruned tiles, retained anchors | 5252 | 5^7 | 5^10 | 5^17 |
| Pruned tiles, compact anchors | 5252 | 5^7 | 5^9 | 5^16 |

Run `python3 check_pruned_t4.py`. It uses only Python's standard library
and the adjacent literal k215.tm and k215_transitions.json, verifies their
complete row correspondence and the frozen table hash, writes the ordered tile
list and finite verification receipt, and never constructs the four huge
coefficient numerals. The retained-anchor layout is also checked as a
conservative intermediate reduction. No global optimum for coefficient
height, tile count, unknown count, or arithmetic size is asserted.
