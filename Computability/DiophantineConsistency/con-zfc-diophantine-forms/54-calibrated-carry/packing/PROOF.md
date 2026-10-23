# Selective source packing with freely oriented residual rows

## Scope and finite input

This component starts with the pinned 60-gate, 31-variable, 22-residual
quadratic source, SHA-256
`ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.
The file `data/source_system60.json` is inert data. We substitute x+1 only
for F, alpha, z, h, i, j, s, w, eta, zeta, gamma, g. The other nineteen
coordinates are left unshifted. The source component supplies the separate
positivity-recovery proof equating nonnegative solutions of this system to
positive solutions of the original system. The present component does not
replace that proof, the compiler endpoint, or the inherited arithmetic bridges.

Write the resulting rows as q_j(X)=sum_alpha p_(j,alpha)X^alpha, j=1,...,22.
Direct exact reconstruction gives 109 coefficient records and 62 distinct
active monomials: one constant, 22 linear, and 39 quadratic. The universal
quadratic expansion in 31 coordinates has 528 formal monomials.

## Exact extraction, with row orientation

Choose 32 distinct positions c,w_1,...,w_31 in [0,W], where c is the padding
position. For |alpha|<=2 define

m(alpha) = (2-|alpha|)c + sum_i alpha_i w_i,
f(alpha) = (2-|alpha|)! product_i alpha_i!.

Choose signs epsilon_j in {-1,+1} and target positions H_j. Set

C_z(T) = (T^c + sum_i z_i T^w_i)^2,
D(T) = sum_(j,alpha) epsilon_j f(alpha) p_(j,alpha) T^(H_j-m(alpha)).

All displayed source exponents must be nonnegative. The precise finite
condition is, for every active source record (j,alpha), every formal monomial
gamma of degree at most two, and every target H_k,

H_j-m(alpha)+m(gamma)=H_k iff j=k and alpha=gamma.                 (S)

Then [T^H_j](C_z D)=2 epsilon_j q_j(z). Indeed, the only permitted
contribution is the matching formal multinomial term, whose multiplier
2/f(alpha) cancels the coefficient weight. Keeping formal labels makes
this proof valid even when irrelevant expansion monomials share positions.
Consequently all targets vanish precisely when every original residual
vanishes. Changing a row's sign changes neither its support nor its zero set.

Condition (S) also makes all 109 source exponents in D distinct. If two
records occupied the same exponent, multiplying by the second record's
matching monomial would violate (S). Thus overlapping target bands incur
no row-count multiplier in the coefficient bound.

## A combinatorial improvement: do not reserve a last row

Let A_j be the active monomial positions for row j, E all 528 expansion
positions, and F_j={e-a : e in E, a in A_j}. For two distinct rows j,k,
condition (S) is exactly the exclusion of the target differences in
F_j and F_k with the corresponding opposite orientations. Self-row
condition (S) is exactly isolation of each active monomial among all 528.
This decomposes the search into active-pair isolation and a finite
forbidden-difference placement problem. The optional optimizer greedily
places rows in varied orders and checks these exact exclusions.

The earlier packing reserved a particular row with a positive constant as
the highest source term. That is unnecessary. For any placement whose
highest source coefficient is a nonzero ordinary integer, orient that
single row so the coefficient is positive. Its magnitude is unchanged,
(S) is unchanged, and D(B)>0 follows from the ordinary coefficient bound.
This permits unconstrained row ordering. It also covers the small-width
regular certificate, which flips row 22, and the W163 packed certificates,
which flip row 9. No sign change is needed for the two strongest packed
certificates (W174 and W170).

## Bounds and unconditional positivity

Let beta,K0,MC,MF be the four fixed coefficient ports. The verifier checks
coefficientwise that every weighted source coefficient has absolute value
at most

M_* = 6 + |MF| + |MC| + 2|K0| + 2|beta|
      + 2|beta MF| + |beta K0| + 2 beta^2.

The majorant is a convenient portable bound, not necessarily the tightest
numerical bound for the coherent fixed tuple. Any existing source budget
M>=M_* suffices. A tuple-specific exact coefficient budget may be smaller.
Changing row orientation preserves every absolute coefficient bound.

Because all source exponents are distinct, every coefficient of D has
absolute value at most M. For nonnegative z, the coefficients of C_z are
nonnegative and sum to (1+sum_i z_i)^2. Therefore every coefficient of
C_z D has absolute value at most M(1+sum_i z_i)^2, irrespective of irrelevant
collisions. If 0<=z_i<b, this is at most M(31b)^2.

Let d=deg D and suppose the leading coefficient is the certified positive
integer a. For every integer B>M+1, the total magnitude of all lower terms
is at most M(B^d-1)/(B-1)<B^d. Hence D(B)>0, even when a=1. This is an
unconditional base-size argument, not an assumption about source witnesses.

Interior padding does not change digit extraction or these coefficient
bounds. On 0<=g<2bB^W we have B^c+g<=3bB^W; on 0<=g<4bB^W the corresponding
bound is 5bB^W. Use the bound appropriate to the particular arithmetic bridge.

Completeness also preserves the lower bound g>=b. Every nonnegative source
zero satisfies, from rows 10 and 12,

Delta=a^2+4a+3>=3, and D^2=C2 Delta+1>=1, hence D>=1.

These are two distinct digit coordinates with distinct positions; at most
one can have position zero. Thus a positive digit occurs at a positive
position, giving g>=B>=b for the chosen large radix. This argument uses
neither coefficient-port signs nor the rest of the positivity-recovery proof.

## Frozen certificates and tradeoffs

Rows and targets are in original order 1,...,22. The main degree-oriented
certificate has W174, padding81, Dmax4072, Kcode4420, largest target4276,
and leading coefficient1. Its 32 positions are

81,51,169,164,28,174,146,0,32,20,24,154,45,143,140,33,141,
44,123,135,11,119,148,145,18,166,1,158,25,163,29,5.

Its targets are

3112,2855,1994,204,4276,2461,1087,4113,1548,3575,1768,
3738,3354,525,835,1763,3077,2193,2612,1284,1303,3833.

The shared-homogeneous candidate has W170, padding169, Dmax4086,
Kcode4426, largest target4292, minimum target340=2W, leading coefficient1.
Its 32 positions are

169,8,11,6,42,0,112,4,72,116,3,24,1,150,78,9,80,
52,111,170,163,139,159,37,40,87,83,118,114,146,155,45.

Its targets are

383,1219,3528,2539,3833,1063,340,724,4292,3807,2196,
2290,1780,1441,2743,3951,2086,3055,3300,721,3084,1864.

This is the unshifted W170 packed certificate with every target increased
by one. D is consequently multiplied by T, with all identities unchanged.
The minimum target 2W permits a shared degree-two homogeneous evaluator
without negative powers. Compared with the previous shared packed
Dmax4914,Kcode5262, the new shared candidate lowers Kcode by about15.9%.
Compared with previous unshifted Dmax4728,Kcode5076, the W174 certificate
lowers Kcode by about12.9%. Smaller W163 regular and packed variants are
retained for actual operation-count comparisons, not presumed dominated.
The certificate family contains nine variants; see SUMMARY.json.

Every certificate explicitly verifies Kcode=Dmax+2W and
Kcode>=max_j H_j+2, the headroom requested by the sparse one-bit padding
bridge. No equal-spacing hypothesis is used by extraction, so a sparse
carry bridge proved for arbitrary distinct targets can use these layouts.

## Reproduction and limits

Run `python3 verify_certificates.py`. The standard-library-only verifier
reconstructs every polynomial from the original source in a 35-variable
polynomial ring, checks the selective shifts and all coefficient signs,
compares every serialized term and weighted term, and checks all 57,552
source-record/expansion-monomial pairs for each certificate. It checks
nonnegative exponents, unique targets and source exponents, leading positive
coefficient, complete degree statistics, sparse-padding headroom, the
coefficient majorant, and the two positive-coordinate identities.

Neither the serializer, search programs, their seeds, nor upstream scripts
are trusted dependencies. Search results are merely short integer vectors;
all claims used by the theorem are rechecked independently. No optimality
or new end-to-end formalization of the inherited Con(ZFC) endpoint is claimed.
