# Literal source and evidence

Status: complete author-side construction and fresh finite checks; independent review is pending. This packet is a research certificate, not a full article or independently approved publication.

## Theorem represented

There is a single explicitly emitted integer polynomial P(InputPlus,w), with 3,308 positive integer witnesses, such that P=0 if and only if InputPlus−1 is a valid eleven-field code from ARCHITECTURE.md and the decoded physical periodic 3D sandpile plus finite patch admits a finite legal **binary** toppling prefix firing its decoded signed target coordinate.

The claim is conditional on exactly the POWER theorem dependency inherited from the accepted physical-code certificate: mathlib4 commit ac77769fabe23cb237559e7f56578dbead91499f, Mathlib/NumberTheory/PellMatiyasevic.lean, theorems matiyasevic and eq_pow_of_pell. The first-order semantics are over positive integers only. Global stabilization, maximal parallel update, a finite-fold fiber, real-witness equivalence and ordinary unrestricted target-firing equivalence are not claimed.

## Source and exact ledger

The authoritative source is evidence/polynomial-dag.json. It consists solely of the one ordinary positive input, 3,308 positive witness leaves, fixed integer constants, and binary +, −, × gates. Its output is the sum of the squares of all 1,923 named residuals. Every source gate and witness is live. Its 36 exposed ports are metadata identifying expressions; they add no operation, constraint or oracle.

Fixed integer literals are free under the declared arithmetic convention. The exact emitted counts are:

- Body: 3,887 multiplications, 3,156 additions, 1,967 subtractions, total 9,010
- Sum of squares: 1,923 multiplications, 1,922 additions, 1,923 subtractions, total 5,768
- Full polynomial: 5,810 multiplications, 5,078 additions, 3,890 subtractions, total 14,778
- Expanded macro calls: 118 POWER, 30 Sub, five AND, four SPREAD

The source shape does not depend on any input value, physical dimension, witness prism, or duration. The builder's loops range only over fixed lists, ten Cantor fields, and already fixed source nodes; no input dimension is a Python loop bound. This is a fixed-arity polynomial, not an algorithm that builds a new-sized polynomial from the instance.

An explicit accounting of the quantified variables is

118·26 + 30·5 + 5·3 + 4·4 = 3249 macro-associated witnesses.

The 59 outer witnesses are eleven input descriptor/target-code witnesses, nine inner Cantor-code witnesses, three padding multipliers, five tile/patch geometric values, three tile bitplanes, three box-mask factors, one layer count, one time-repetition value, three pre/new/final streams, three neighbor-division streams, five legality bitplanes, and twelve target decoding/bounding witnesses.

The equation count decomposes as

118·15 + 30·3 + 5·2 + 4·4 + 5 + 1 + 10 + 3 + 1 + 1 + 3 + 1 + 12 = 1923.

These are POWER clauses; Sub clauses; AND partitions; SPREAD outer clauses; five tile/patch geometric equations; tile reconstruction; ten Cantor equations; three box-mask equations; time repetition; time recurrence; three exact negative-neighbor shifts; legality threshold; and twelve signed-target clauses.

## Exact degree

Ordinary straight-line degree propagation gives degree at most 18. The fresh checker substitutes a single indeterminate t for the six dimension witnesses and the three padding witnesses, and zero for every other variable, then propagates exact integer univariate coefficient arrays through every emitted gate. The resulting polynomial has degree 18 and leading coefficient 48. The only residuals attaining degree nine under this substitution are patch.shift.eq8, .eq9 and .eq11, each with leading coefficient −4. Thus the degree is exactly 18. The substitution need not satisfy positivity; it is a purely algebraic lower-bound proof.

## Complete macro expansion

All arithmetic primitives are included in the builder and emitted DAG. No upstream Python is imported, loaded, or executed. For each call POWER(b,e,o), put k=e+1 and m=bo, and introduce positive w,T,g,x,y,u,v,s,t,qb,qv,S; a,β≥2; and nonnegative δwb,δwk,δyk,α1,α2,σ1,σ2,τ1,τ2,ρ1,ρ2. The fifteen residuals are precisely:

x²=1+(a²−1)y²; u²=1+(a²−1)v²; s²=1+(β²−1)t²;
β=1+4yqb; β+uα1=a+uα2; v=y²qv;
s+uσ1=x+uσ2; t+4yτ1=k+4yτ2; y=k+δyk;
w=b+δwb; w=k+δwk; T=m+S;
a²=1+((w+1)²−1)(wg)²; 2ab=T+(b²+1);
x+Tρ1=y(a−b)+m+Tρ2.

All a,β are positive adapters plus one; every nonnegative witness is a positive adapter minus one. The macro has 25 positive internal witnesses plus a positive output. Its domain b≥2,e≥0 is proved at every actual use, rather than assumed for arbitrary assignments.

For Sub(M,V), the three POWER calls produce L=2^(M+1), Y=L^V, Z=(L+1)^M. Five outer witnesses q,o,r≥0 and sc,sr>0 obey Z=(qL+2o+1)Y+r, 2o+1+sc=L, r+sr=Y. This exactly tests oddness of the carry-free base-L binomial digit at index V. Lucas parity in base two makes this equivalent to bit containment. M,V are always natural at the call interface.

For AND(X,Y,Z), introduce a,c≥0 and use X=Z+a, Y=Z+c, Sub(X,Z), Sub(Y,Z), Sub(a+c,a). The last forbids overlap of the two residual supports. No primitive bitwise instruction appears in the DAG.

For SPREAD(U,B,n,s), the paid gaps enforce 0≤U<B^n and s≥n+1. Three POWER calls produce P=B^n, C=B^(s−1), E=C^n; the two geometric values satisfy (C−1)G1+1=E and (BC−1)G2+1=EP. Set V=AND(UG1,(B−1)G2). This yields V=Σu_i B^(si). Its three powers, four outer clauses and one expanded AND are all counted above.

All geometric calls use POWER and the explicit equation (base−1)value+1=base^length. Physical source reshaping repeats the already accepted four-SPREAD geometry exactly, using fresh source syntax.

## Positivity and domains

- Six dimensions are positive; three padding multipliers are positive witnesses plus one, hence at least two
- Tile/patch masks have positive bases and lengths; all row/plane radices are powers of 32 at positive exponents
- Every spread has a positive length and an explicit stride-gap equation, hence all copy bases exceed one
- The positive range slacks enforce every spread input's strict upper bound
- All selected streams, bitplanes, quotients and geometric values are natural adapters
- The interior mask is a product of natural factors, so time-frame masks are natural
- K is a positive witness, Q is a power of 32 exceeding one, and the time geometric denominator Q−1 is positive
- Signed-target local coordinates are natural adapters with positive strict upper-bound gaps; their point-mask exponent is therefore nonnegative
- Every Sub mask and value is a natural expression; its generated radix is at least two

The signed-target translation uses only polynomial addition/multiplication. No signed intermediate is passed to a nonnegative POWER exponent.

## Fresh finite evidence

check_target_certificate.py reads only the JSON DAG as inert syntax. It does not import the builder. Its author-side evidence contains:

- 10,620 POWER residual substitutions over six moduli
- 540 Sub, 60 AND and 96 SPREAD outer-residual substitutions
- Six whole-DAG sum-of-squares substitutions
- Exact integer coefficient propagation establishing degree 18
- 17,640 candidate recurrence assignments, including invalid candidates, checked against their exact layerwise meaning
- 9,408 local legality/slack cases over every allowed initial height 0–20, neighbor count 0–6, activation bit, and potential five-bit slack
- 324 padded space–time configurations, checking every neighbor shift over 17,496 slots, including empty interiors, multi-layer frames and the final frame
- All 2,744 three-site path initial height triples in 0–13, comparing parallel binary closure with enumeration of all legal distinct-site prefixes
- 343 signed-coordinate eleven-field Cantor round trips, and the zero-code edge case
- An explicit rejection of the two-height-five overfiring fixture
- An explicit ordinary-but-not-binary firing fixture: adjacent heights 12 and 4, target the height-four site, legal ordinary sequence origin/origin/target
- A one-step accepted target certificate for the uniform height-five background plus one chip at the target, whose endpoint is unstable and whose global evolution cannot finitely stabilize

The last nonstabilization claim has a direct proof: a putative finite nonzero stabilizing odometer has finite support; a neighboring outside site beyond an extremal support point starts with height at least five, receives at least one chip, and never topples, so is unstable. This is not inferred from a finite run.

Finite modular source tests are not exact symbolic identities, and finite semantic regressions are not all-input proofs. A separate independent exact source reconstruction remains required for approval.

## Pins and reproduction

DAG SHA256: 352b6dd9add46ed3c1c8532c21e9725249b28b3afba23003e31330b2503e0504

Builder SHA256: 6a9ced103676ce7ba0b052e00779177fb522101fc5479866273e3908d299c975

Checker SHA256: e7fe5ca8919e305d4daa36edbd09997a137a614fe0ce65e0500160d553e02b52

Run the newly authored local builder and checker with ordinary Python 3. No third-party package, Lean execution, upstream schedule, or historical recoder is required. The pinned Pell proof is an explicit mathematical dependency, not a package imported by these programs.
