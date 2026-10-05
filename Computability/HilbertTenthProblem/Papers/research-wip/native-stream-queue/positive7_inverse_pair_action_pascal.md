# Factoring the eight paired actions: a further144 paid operations

The eight explicit paired-letter increments in the fixed positive7
alphabet can be computed with30M+168A=198 operations, including their
six-coordinate aggregation. The preceding literal coefficient schedule
used174M+168A=342 for the same outputs. The new schedule saves exactly
144 operations while using the same52 raw selected-source ports.

With the preceding relator schedule, the complete selected-action cut is

    (40+24r)M+(189+24r)A=229+48r,                           (1)

or, computing the seven recurrence left sides B V_i directly,

    (42+24r)M+(189+24r)A=231+48r.                           (2)

These replace373+48r and375+48r respectively in the frozen paid sparse
action note. They do not change its native lanes, positive witnesses,
ordinary input, global bound or relator coefficients. A198-row local
graph with this six-output boundary is emitted as inert data; no complete
new wrapper or numerical universal compiler is emitted here.

Root requested the inverse-pair/common-form search while independently
emitting the uniform sparse wrapper. The derivation below is new
handwritten algebra and instruction accounting; no saved scientific
source or coefficient array was evaluated.

## 1. Exact inputs and transformations

Use the full raw cut of `positive7_paid_sparse_action_pascal.md`: seven
history words H_i, their already computed sum S, and each retained raw
selected word Z_sigma,i=Zhat_sigma,i-1. The eight paired slots are
a+,a-,b+,b-,z1+,z1-,z2+,z2-. Their retained ports are unchanged:
six for each a/b slot, seven for each z slot. The two slots of each
inverse pair have independent selected-source fields.

All local identities below hold for arbitrary integer values of these
fields. One-hot extraction is not assumed in factoring this arithmetic.
It remains necessary, with its paid native certificate, for interpreting
the overall baseline as a selected positive-matrix action.

For a symmetric matrix [[v1,-v2],[-v2,v3]], let S(P) be the integral
representation defined in the frozen table note. It obeys S(PQ)=S(P)S(Q),
because it represents G -> PGP^T. Put

    U=[1,1;0,1], V_t=[1,0;t,1].

The actual paired matrices are

    a:  (U,U),
    b:  (U V_12 U^-1,V_12),
    z1: (U V_4 U V_4^-1 U^-1,V_4 U V_4^-1),
    z2: (U V_8 U V_8^-1 U^-1,V_8 U V_8^-1),                (3)

with inverse matrices for the negative slot. These are exactly the
eight fixed matrices in the predecessor table, not replacement dynamic
words in the positive alphabet.

Write v=Q^-1 D Z. The six decoded coordinates are

    v1=Z1-Z4, v2=Z2+Z4-2Z7, v3=Z3+Z4-2Z7,
    v4=Z4-Z7, v5=Z5+Z4-2Z7, v6=Z6+2Z4-4Z7.              (4)

The desired pair increment is

    (A_+-I6)Q^-1D Z_+ + (A_--I6)Q^-1D Z_-.                (5)

The four pair increments will be aggregated to the same six original
coordinates (a,b,c,d,e,f) as the frozen paid action. Copies are free;
every binary addition, subtraction and fixed-coefficient product listed
below is charged. Doubling by x+x is one addition, not a free scalar.

## 2. The a inverse pair:24 additions

For either a slot, compute the following seven additions/subtractions:

    u=Z4-Z7; h=u-Z7;
    v2=Z2+h; v3=Z3+h; v5=Z5+h;
    t6=Z6+h; v6=t6+h.                                     (6)

The outputs are exactly the four needed coordinates in(4). Do this for
both signs, at a cost14A. For either of the two blocks, take
(l_+,m_+)=(v2_+,v3_+) or(v5_+,v6_+), and the corresponding negative
slot. The following five additions compute its increment:

    dl=l_- - l_+; sm=m_+ + m_-; dm=m_- - m_+;
    dl2=dl+dl; A=dl2+sm.                                  (7)

The block increment is(A,dm,0). Indeed

    (S(U)-I)(x,y,z)=(-2y+z,-z,0),
    (S(U^-1)-I)(x,y,z)=(2y+z,z,0).

Equation(7) is their sum on independent input triples. Applying it to
both blocks costs10A. Hence the full a pair costs0M+24A and yields
four nonzero structural outputs in coordinates1,2,4,5; coordinates3,6
are literal zero.

## 3. The b inverse pair:6M+29A

For either b slot, the following nine additions/subtractions give the
first triple after S(U^-1) and the two needed second-block coordinates:

    u=Z4-Z7; h=u-Z7; v1=Z1-Z4;
    v2=Z2+h; v3=Z3+h; w2=v2+v3;
    t1=v1+v2; w1=t1+w2; v5=Z5+h.                          (8)

The first transformed triple begins(w1,w2), because
S(U^-1)v=(v1+2v2+v3,v2+v3,v3). The second begins(u,v5).
Compute(8) independently for both signs, at18A.

For a lower shear of amount12,

    (S(V_12)-I)(x,y,z)=(0,-12x,144x-24y),
    (S(V_-12)-I)(x,y,z)=(0,12x,144x+24y).

For either block take(x_+,y_+)=(w1_+,w2_+) or(u_+,v5_+),
and likewise the negative slot. Compute

    dx=x_- - x_+; sx=x_+ + x_-; dy=y_- - y_+;
    A=12dx; B=144sx; C=24dy; T=B+C.                        (9)

These are3M+4A and give the lower-shear pair increment(0,A,T).
For the first block apply S(U):

    A2=A+A; out1=T-A2; out2=A-T; out3=T.                   (10)

This costs3A; the second block is already(0,A,T) and needs no further
arithmetic. Thus the b pair costs6M+(18+8+3)A=6M+29A.
Its structurally zero coordinate is4.

## 4. Each z inverse pair:12M+54A

Use t=4 for z1 or t=8 for z2. The same instruction pattern works in
both cases; multiplication by these fixed integers is charged.
For either sign, compute the following eleven additions/subtractions:

    u=Z4-Z7; h=u-Z7; v1=Z1-Z4;
    v2=Z2+h; v3=Z3+h; w2=v2+v3;
    t1=v1+v2; w1=t1+w2; v5=Z5+h;
    t6=Z6+h; v6=t6+h.                                    (11)

The first triple after S(U^-1) is(w1,w2,v3); the second original
triple is(u,v5,v6). For each of these triples(x,y,z), compute

    tx=t*x; L=tx+y; Ly=L+y; tLy=t*Ly; M=tLy+z.             (12)

This uses2M+3A and gives

    L=t*x+y,
    M=t^2*x+2t*y+z,

the second and third coordinates of S(V_-t)(x,y,z). Thus (11)--(12)
cost4M+17A per sign, or8M+34A per pair. They obtain exactly the two
coordinates needed to conjugate each signed U-action through V_t;
no uncomputed first coordinate is consumed by the upper-shear difference.

For each block, use (7) on the resulting(L_+,M_+),(L_-,M_-).
Write its output as(A,D,0). This costs five additions per block, hence
10A. Apply S(V_t) to this increment with the five charged instructions

    tA=t*A; D2=D+D; q=tA-D2; C=t*q; B=D-tA.                (13)

Their cost is2M+3A and the resulting triple is

    (A,B,C)=(A,D-t*A,t^2*A-2t*D).

For the second block this is the final output. For the first block apply
S(U) with four additional additions:

    B2=B+B; q1=A-B2; out1=q1+C; out2=B-C; out3=C.          (14)

Indeed S(U)(A,B,C)=(A-2B+C,B-C,C). The two applications of(13)
plus(14) cost4M+10A. Total cost per z pair is therefore

    (8M+34A)+10A+(4M+10A)=12M+54A.                        (15)

Both z pairs have six structural output coordinates. All signs in
(7),(9),(12)--(14) follow from the explicit representation; no division,
choice of square roots or exceptional-factor assumption is involved.

## 5. Aggregation, relators and the final paid cuts

First, the four independently completed pair schedules have this ledger:

| Pair | M | A | Structural nonzero output coordinates |
| --- | ---: | ---: | --- |
| a | 0 | 24 | 1,2,4,5 |
| b | 6 | 29 | 1,2,3,5,6 |
| z1 | 12 | 54 | 1,2,3,4,5,6 |
| z2 | 12 | 54 | 1,2,3,4,5,6 |
| Before aggregation | 30 | 161 | |

For the final schedule, share the last first-block chart as follows.
Omit the three additions in(10) and the four additions in(14) for each
of z1,z2. These11 omitted additions all apply the same linear map S(U).
Before those applications, the b first-block increment is(0,A_b,T_b),
and the two z first-block increments are(A_1,B_1,C_1),(A_2,B_2,C_2).
Compute their sum with five additions:

    A0=A_1+A_2;
    B0_first=A_b+B_1; B0=B0_first+B_2;
    C0_first=T_b+C_1; C0=C0_first+C_2.

Apply S(U) once with four additions:

    B02=B0+B0; q0=A0-B02; G1=q0+C0; G2=B0-C0; G3=C0.

Add the two a first-block outputs to G1,G2 with two additions; its
third output is zero. This is the full first-coordinate aggregation,
at5+4+2=11A. Linearity of S(U) proves exact equality to the formerly
separate chart outputs and sums, on arbitrary integer inputs.

The second blocks are unchanged. Their three sums have3,4,3 terms:
coordinate4 uses a,z1,z2; coordinate5 uses all four; coordinate6 uses
b,z1,z2. They cost2+3+2=7A. The final ledger is consequently

    private arithmetic: 30M+(161-11)A=30M+150A,
    shared charts and complete aggregation: 18A,
    total: 30M+168A=198.

Every decoder, sign combination, fixed multiplier and required sum is
included. No coefficient output is assumed to vanish on a special input.

**Remark 1 (valid preceding136-saving schedule).** The initial draft
completed all four pair outputs independently, then summed each of six
coordinates. Those sums cost15A, giving30M+176A=206 and a136-operation
saving. It was a valid schedule. Sharing the three first-block S(U)
applications as above saves a further eight additions; the final claimed
saving is144. No earlier frozen artifact is changed.

The frozen relator schedule can append all24r coefficient products to
the existing last three accumulators using24rM+24rA. Its optional
fixed-pattern pruning uses N_R of each operation instead, with
0<=N_R<=24r. Hence the new six-increment block costs

    (30+N_R)M+(168+N_R)A.                                 (16)

The frozen31-row positive-output postprocessor costs10M+21A, giving
(40+N_R)M+(189+N_R)A. Root's recurrence-fused postprocessor costs12M+21A,
giving(42+N_R)M+(189+N_R)A. These are(1)--(2) when every relator product
is retained. The comparison with the prior paired increment is

    old: 174M+168A=342,
    new:  30M+168A=198.

The saving is144 multiplications with the same number of additions,
or144 total. No claim is made that these new schedules are optimal.

## 6. Whole-source substitution and remaining boundaries

Equations(5)--(15) prove equality to all48 rows of the frozen paired
table as integer linear maps, not merely on a sample of typed histories.
Both inverse slots may even be nonzero in the same cell for this
arithmetic identity. Therefore replacing precisely the paired increment
subgraph preserves its six boundary polynomials on arbitrary integer
assignments. Relator increments and the postprocessor are unchanged.
Once such a substitution is emitted in a complete parent source, every
downstream comparison and its final sum of squares is the same polynomial
in the parent supplied coordinates. The source emitter and consumer
bindings must still be inspected before claiming that whole-source audit.

The positive7 interpretation is still supplied by the unchanged one-AND
geometry and full positive-zero proof. These arithmetic factors neither
remove selectors nor alter the52+8r selected-source interfaces,62+10r
native lanes, global Ztot bound, native scale, endpoint or ordinary-input
loader. In particular the schedule uses raw selected words already
paid by that interface. If they are not already available, their positive
hat conversions remain charged exactly as in the frozen action note.

**Remark 2 (signed arithmetic factorization is not lifted-word expansion).**
The conjugations in(3) are used to factor a fixed signed linear map inside
one macro-letter's difference. Replacing that macro by several separately
lifted letters would be a different statement. For example the common
baseline satisfies D L(I)=8D but D L(I)^2=64D, so even a two-factor
identity decomposition is not the same positive operator as one identity
letter. No positive-alphabet expansion, extra factor8 or uncharged regular
macro controller is introduced by the present arithmetic schedules.

**Open question 1 (root's emitted successor).** Substitute the new
same-interface paired increment into a complete sparse source and verify
the actual emitted rows, liveness, comparisons and whole-source ledger.
The local144-operation saving is proved above; it is not a numerical
universal gate bound without that source audit and materialization of the
fixed universal presentation. No global minimality or degree is asserted.

## 7. Evidence and provenance

The complete frozen paid sparse-action note and its selected-action
structure dependency were read inertly; exact bytes and spans are bound
in the companion metadata. All new identities and counts here are
handwritten. Root independently checked the final common-chart ledger;
Aristotle independently challenged all conjugacies, pair formulas,
signs, support, stage counts and six-output equality, finding no error.

The newly authored `positive7_inverse_pair_action_pascal.py` constructs
only the local graph described above, directly from these new formulas.
It reads no earlier source arrays or emitter code. The companion JSON
contains its198 rows in[name,op,left,right] form, all52 raw inputs named
selected_SLOT_PORT, and six output names in(a,b,c,d,e,f) order. Slots0--7
are(a+,a-,b+,b-,z1+,z1-,z2+,z2-); ports are the one-based coordinates
in(4). The c output is a free alias of the live joint C0 register.

One original metadata-only emission from`/` passed static checks: stages
0M24A,6M26A,12M50A,12M50A,0M18A; all198 rows and52 raw ports live at
the six-exit cut; topologically ordered rows. No optimized or other
rerun was performed. After adding this evidence paragraph, only the
receipt's note byte/span binding was refreshed; the emitted graph was
copied unchanged. Aristotle also read the full emitter and all198 row
records inertly and confirmed their match to the proof. These checks
count operation labels and trace dependency names only: they do not
evaluate arithmetic, propagate degrees or infer algebraic equality from
sampled values. The six boundary identities are proved in Sections1--5,
independently of the graph.

No supplied, archived, committed, frozen or predecessor helper was
executed/imported; no saved scientific source or coefficient array was
evaluated or degree-propagated; no numerical sampling was used. Only
original local-row emission and fresh static byte/metadata work were
executed. All new files are in/tmp, with repository files, Git and earlier
frozen artifacts untouched. The new emitter itself is not to be rerun
after this packet is frozen.
