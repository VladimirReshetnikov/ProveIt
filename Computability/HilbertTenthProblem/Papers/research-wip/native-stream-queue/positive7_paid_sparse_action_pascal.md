# A paid sparse selected-action circuit for the fixed positive7 alphabet

For the inherited raw alphabet of eight paired letters and two signed
slots per presentation relator, the selected action admits an explicit
arithmetic schedule. At the cut consisting of the seven history words,
their already computed sum, and the retained unhat selected-source words,
the literal schedule costs

    (184+24r)M + (189+24r)A = 373+48r operations.             (1)

Here r is the fixed presentation's relator count, not a supplied variable.
If only the seven recurrence left sides B V_i are consumed, a fused
schedule costs

    (186+24r)M + (189+24r)A = 375+48r operations.             (2)

These are fully charged selected-action blocks, not a whole history or
universal-polynomial ledger. The fixed universal relator list remains
unmaterialized numerically. The sparse selector interface still needs
52+8r selected-source words and 62+10r native lanes; neither number is
an arithmetic-operation count. Root proposed the common baseline and
four-port relator decoder and subsequently the recurrence fusion in(2).
The author derived the explicit paired tables and aggregate schedule.

## 1. Fixed data and the exact circuit cut

Use the alphabet and chart of the frozen
`positive7_selected_action_structure_pascal.md`. Its raw labels are

    a+,a-,b+,b-,z1+,z1-,z2+,z2-,R1+,R1-,...,Rr+,Rr-.

Thus m=8+2r. The first eight six-dimensional matrices have two blocks
S(P), where

    S([p,q;s,t])=[p^2,-2pq,q^2;
                  -ps,pt+qs,-qt;
                  s^2,-2st,t^2].                           (3)

The positive slots have the following two underlying matrices; negative
slots use their inverses in both blocks:

| Label | First block P | Second block P |
| --- | --- | --- |
| a+ | [1,1;0,1] | [1,1;0,1] |
| b+ | [13,-12;12,-11] | [1,0;12,1] |
| z1+ | [-19,25;-16,21] | [-3,1;-16,5] |
| z2+ | [-71,81;-64,73] | [-7,1;-64,9] |

For a relator slot the original six-dimensional matrix is
diag(I3,S(P)), with P=rho(R_j) or its inverse. The actual relator words,
the resulting integer coefficients and the common positive-lift numeral
kappa are fixed compiler data. Computing these fixed tables is distinct
from multiplying a variable by their entries: every such multiplication
used below is charged, including coefficients 1 and -1. Signed fixed
integer coefficients and signed computed intermediates are allowed;
all supplied existential coordinates remain strictly positive.

The action cut supplies H1,...,H7, S=sum H_i already computed, and raw
nonnegative selected-source words Z_sigma,i already computed as
Zhat_sigma,i-1. Its retained ports are:

* a+ and a-: i=2,3,4,5,6,7;
* b+ and b-: i=1,2,3,4,5,7;
* z1+,z1-,z2+,z2-: all seven;
* each relator slot: i=4,5,6,7.

There are w=52+8r such ports. If these unhats are not already paid in
the joined geometry, add w additions/subtractions once. If S has not
already been computed, add six additions once. The action ledger does
not supply these interfaces for free elsewhere in the compiler.

## 2. Exact signed paired coefficient tables

Write D=[I6|-h], h=(1,1,1,1,1,2)^T. For a selected seven-vector Z,

    Q^-1 D Z=(Z1-Z4, Z2+Z4-2Z7, Z3+Z4-2Z7,
              Z4-Z7, Z5+Z4-2Z7, Z6+2Z4-4Z7)^T.             (4)

For each label form its original-coordinate difference
(A_sigma-I6)Q^-1 D Z_sigma. The first table gives its first three
coordinates, with columns ordered (Z1,Z2,Z3,Z4,Z7); the second gives
its last three, with columns ordered (Z4,Z5,Z6,Z7). Missing columns
have coefficient zero. Each semicolon below separates one output row.

| Label | Three first-block coefficient rows, columns(1,2,3,4,7) |
| --- | --- |
| a+ | (0,-2,1,-1,2); (0,0,-1,-1,2); (0,0,0,0,0) |
| a- | (0,2,1,3,-6); (0,0,1,1,-2); (0,0,0,0,0) |
| b+ | (168,312,144,288,-912); (-156,-288,-132,-264,840); (144,264,120,240,-768) |
| b- | (120,264,144,288,-816); (-132,-288,-156,-312,888); (144,312,168,336,-960) |
| z1+ | (360,950,625,1215,-3150); (-304,-800,-525,-1021,2650); (256,672,440,856,-2224) |
| z1- | (440,1050,625,1235,-3350); (-336,-800,-475,-939,2550); (256,608,360,712,-1936) |
| z2+ | (5040,11502,6561,13023,-36126); (-4544,-10368,-5913,-11737,32562); (4096,9344,5328,10576,-29344) |
| z2- | (5328,11826,6561,13059,-36774); (-4672,-10368,-5751,-11447,32238); (4096,9088,5040,10032,-28256) |

| Label | Three last-block coefficient rows, columns(4,5,6,7) |
| --- | --- |
| a+ | (0,-2,1,0); (-2,0,-1,4); (0,0,0,0) |
| a- | (4,2,1,-8); (2,0,1,-4); (0,0,0,0) |
| b+ | (0,0,0,0); (-12,0,0,12); (120,-24,0,-96) |
| b- | (0,0,0,0); (12,0,0,-12); (168,24,0,-192) |
| z1+ | (16,6,1,-24); (-90,-32,-5,132); (464,160,24,-672) |
| z1- | (36,10,1,-48); (-118,-32,-3,156); (368,96,8,-480) |
| z2+ | (64,14,1,-80); (-594,-128,-9,740); (5408,1152,80,-6720) |
| z2- | (100,18,1,-120); (-718,-128,-7,860); (5088,896,48,-6080) |

For direct verification from(3), a row (u,v,w) of the first S(P)-I3
becomes

    (u,v,w,-u+v+w,-2v-2w),                                 (5)

while a row of the second becomes

    (u+v+2w,v,w,-u-2v-4w).                                 (6)

These substitutions also prove that omitted selected ports are absent
from the complete difference, not merely from a private decoder. All
displayed entries and the following counts were derived by handwritten
integer algebra. No source array, coefficient array or scientific helper
was evaluated to produce them.

The nonzero row counts are:

| Label | Counts in rows1,...,6 | Total |
| --- | --- | ---: |
| a+ | 4,3,0,2,3,0 | 12 |
| a- | 4,3,0,4,3,0 | 14 |
| b+ | 5,5,5,0,2,3 | 20 |
| b- | 5,5,5,0,2,3 | 20 |
| z1+ | 5,5,5,4,4,4 | 27 |
| z1- | 5,5,5,4,4,4 | 27 |
| z2+ | 5,5,5,4,4,4 | 27 |
| z2- | 5,5,5,4,4,4 | 27 |
| All eight | 38,36,30,22,26,22 | 174 |

## 3. Relator aggregation and its exact pattern parameter

For each of the 2r relator slots, apply(6) to the three rows of
S(P)-I3. Call the resulting three-by-four fixed integer matrix C_sigma.
Its columns multiply only Z_sigma,4,...,Z_sigma,7. Define

    N_R=sum_(relator slots sigma) number of nonzero entries(C_sigma).

Thus 0<=N_R<=24r, with no nondegeneracy or nonidentity premise on the
relators. Their first three original-coordinate increments are zero.
Aggregate their last triples, together with the last triples of the
eight paired slots, before applying the fixed chart and positive lift.
The correction is consequently paid once, not once per relator slot.

Here is an exact instruction template. In each of six output rows,
list all its nonzero paired terms in the displayed label/column order,
then its relator terms in fixed slot/column order. Multiply each retained
coefficient by its selected word, then sum that row's products from left
to right. Every row has at least one paired term. Call the six resulting
integers (a,b,c,d,e,f). The pattern-pruned template uses

    (174+N_R)M + (168+N_R)A.                               (7)

The six subtractions from the number of additions are the six nonempty
row sums. The counts include no free matrix multiplication, decoder,
or summation of relator triples.

For a uniform literal formula depending only on r, retain all four
coefficient products in each of the three rows of every relator slot,
including products by zero. This unpruned template uses exactly

    (174+24r)M + (168+24r)A.                               (8)

It is a valid, deliberately unoptimized upper schedule. Removing zero
or unit arithmetic may reduce it. Neither(7) nor(8) is a minimality claim.
No runtime operation computes the fixed C_sigma table; its variable
products and all accumulated terms are precisely what(7)--(8) charge.

## 4. A31-operation shared output correction

At the certified selector interface, the exact common-baseline identity is

    V=8H+(kappa-1)k S+F Q(a,b,c,d,e,f)^T,
    F=8E-k*1_6^T, E=[I6;0], k=(1,1,1,1,1,2,1)^T.          (9)

Indeed the positive letter difference is FQ(A_sigma-I6)Q^-1D;
the baseline is L(I6)=8I7+(kappa-1)k*1_7^T. One-hot selection
partitions every history coordinate, so this reconstructs the selected
letter even when only its nonzero difference ports were supplied.

The chart gives Q(a,b,c,d,e,f)=(a+d,b-d,c-d,d,e-d,f-2d),
whose coordinate sum is a+b+c+e+f-3d. Put

    T=(kappa-1)S-(a+b+c+e+f+5d),
    U=T+8d, Voff=U+8d.

The seven outputs are exactly

    V1=8(H1+a)+Voff, V2=8(H2+b)+T,
    V3=8(H3+c)+T,    V4=8H4+Voff,
    V5=8(H5+e)+T,    V6=8(H6+f)+2T,
    V7=8H7+U.                                              (10)

An explicit charged schedule, with no implicit affine operations, is:

| Rows | Computations | M | A |
| --- | --- | ---: | ---: |
| 1--4 | a+b; previous+c; previous+e; previous+f | 0 | 4 |
| 5--8 | d5=5d; sum5=previous+d5; mass=(kappa-1)S; T=mass-sum5 | 2 | 2 |
| 9--12 | d8=8d; U=T+d8; Voff=U+d8; T2=T+T | 1 | 3 |
| 13--17 | H1+a,H2+b,H3+c,H5+e,H6+f | 0 | 5 |
| 18--24 | multiply those five values,H4,H7 by8 | 7 | 0 |
| 25--31 | add the seven offsets in(10), using T2 for2T | 0 | 7 |
| Total | | 10 | 21 |

Combining(7) with this table gives the pattern-sensitive action cost

    (184+N_R)M+(189+N_R)A=373+2N_R.                         (11)

Using(8) gives(1). A preliminary handwritten postprocessing schedule
used8M+26A instead; it was a valid34-operation alternative, superseded
by the31-operation schedule above, not a failed identity.

## 5. Root's paid recurrence-consumer fusion

The current one-AND history relation uses V_i only in B V_i. If these
are the required outputs, compute rows1--8 above to obtain T. Replace
rows9--12 by

    Escale=8B; BT=B*T; Ed=Escale*d;
    BU=BT+Ed; BV=BU+Ed; BT2=BT+BT.

Then output

    E(H1+a)+BV, E(H2+b)+BT, E(H3+c)+BT, E H4+BV,
    E(H5+e)+BT, E(H6+f)+BT2, E H7+BU,                       (12)

where every E means the single computed Escale. Five inner sums,
seven products by Escale and seven final additions are charged as before.
The replacement uses3M+3A instead of1M+3A, so the complete fixed
postprocessor costs12M+21A. Each expression in(12) equals B times
its counterpart in(10) for all integer values of the displayed variables;
no sign or binary-typing assumption is used in this consumer fusion.

Thus the fused action costs

    (186+N_R)M+(189+N_R)A=375+2N_R,                         (13)

giving(2) for the unpruned relator template. Forming the seven V_i first
and then paying seven products by B would cost five more multiplications.
The fusion applies only when no other consumer needs the unscaled V_i;
it is not permission to omit such a consumer in another source.

## 6. Sparse lanes preserve the one-AND projection

The sparse interface keeps all m selector lanes, one selected-source
lane per retained port, the aggregate range lane and the D-power lane.
Hence its native lane count is

    ell=m+w+2=62+10r.                                      (14)

Keep the one global comparison S+Ztot+g=P, where Ztot is the sum of
the w retained raw selected words. Its positive-hat version has the
offset w: S+sum_retained Zhat+g=P+w. The unchanged pretyping argument
gives S<P, Ztot<P and every retained selected word below P. All native
packs are still nonnegative before their equations. The same fixed
power T_native=P^ell and the prescribed-AND theorem recover dyadic P,
dyadic D, dyadic B, the repunit, one-hot selectors and each retained
selected product in exactly the original proof order.

After extraction, the selected coordinates omitted from a label have
zero coefficient in its difference table. Equations(9)--(10) therefore
compute the exact packed positive-matrix action on every candidate
canonical history. The inherited simultaneous nonnegative induction
with aggregate range, initial mass<D and K>C then applies unchanged.
There is no requirement that the signed intermediate corrections in
Sections3--5 be nonnegative on arbitrary supplied assignments.

For completeness, at each digit there is one active label and its
retained coordinates are a subset of all seven. Consequently

    0<=Ztot<=S< P,
    g=P-S-Ztot >= P-2S
      >=((K-2)D+1)J+1>0.                                  (15)

This uses S<=(D-1)J along genuine histories. Every omitted selection
requires no witness; an unused retained selection still has positive
hat1. All selector and selected-source lanes are satisfied, and the
prescribed-AND converse supplies its same21 fresh positive auxiliaries.
Thus the sparse finite relation preserves the inherited ordinary-input,
nonempty unbounded-word projection. The exponent ell in(14) is a fixed
compiler parameter; the unbounded history length is recovered from the
repunit and is not identified with ell. The ordinary x and its loader
have not been replaced by a packed program or history input.

**Remark 1 (sparse selections need not have total mass S).** The dense
identity Ztot=S does not transfer. At a cell labelled a+, coordinate1
is omitted and its actual positive value is lost from the selected sum.
For example on the positive seven-vector (1,1,1,1,1,1,1), this retained
sum is6 whereas the mass is7. This local selector-interface counterexample
is enough to refute equality; no claim is made that it is the universal
input state. The valid inequality and exact slack are(15).

## 7. What the local saving establishes

For comparison, one explicit dense selected-action procedure multiplies
each of the49m strictly positive lift coefficients by its selected word
and accumulates each of seven complete rows. It costs49m M+(49m-7)A,
or777+196r operations. Relative to that procedure, the raw-input sparse
action(1) saves404+148r operations. This is an actual comparison of two
stated local schedules, not a lower bound against optimized dense actions.
Including seven following products by B, the dense procedure costs
784+196r; the fused sparse(2) costs375+48r, a difference409+148r.

The complete source must still pay selector unhats, the w selected
unhats once, S and Ztot sums, loader and initial mass, geometry, three
packs, the fixed power, native64/108 arithmetic, all recurrence right
sides/comparisons and the endpoint. Native lane packing and addition-chain
costs must use the new ell, not be borrowed from a different source.
The sparse relation has m+w+37=97+10r positive supplied witnesses at
the declared one-AND interface with seven separate terminal coordinates.
If terminal coordinates1 and7 are supplied as the same positive variable,
the endpoint equality is automatic and the count becomes96+10r. That
explicit interface identification also removes its separate comparison;
neither witness count is an arithmetic gate count.

No full arithmetic source, source-degree certificate or single-polynomial
ledger is emitted here. The numerical universal r, relator matrices,
kappa and native packing circuit remain to be instantiated. The accepted
group/universality and native-Pell theorems are inherited within their
existing scopes; no fresh external-foundation certification is claimed.
Nor is(9) asserted for arbitrary untyped selected-source inputs: its
action interpretation requires the exact one-hot extraction just proved.

**Open question 1 (root's complete sparse successor).** Compose these
paid blocks with a fully emitted one-AND wrapper, check every changed
pack consumer and the complete zero-set equivalence, then give its
whole-source ledger. The local savings above do not by themselves settle
that source audit or yield a numerical universal Diophantine bound.

## 8. Evidence and execution boundary

The full frozen selected-action structure note, positive7 lift note and
one-AND geometry note were read as text. Their exact bytes and read spans,
and the incoming retention rule, are pinned in the companion JSON.
The algebra, signed tables, row census and postprocessing ledgers are
handwritten proofs; only fresh byte/metadata operations were executed.
No supplied, committed, archived, predecessor or frozen helper was run
or imported; no saved source or coefficient array was evaluated or
degree-propagated. No numerical sampling or build was used. All new
artifacts are in/tmp; repository files, Git and prior frozen artifacts
remain untouched. Root independently checked the complete proof, all
48 signed paired rows, both postprocessors, their counts and the sparse
projection. Root also derived the48 rows with a fresh independent scalar
checker before freezing that checker; its byte pins are recorded in the
metadata as separately authored corroboration. The author neither ran
nor imported that checker. Root's scaled-consumer variant is credited
in Section5; no correction was requested in the full proof challenge.
