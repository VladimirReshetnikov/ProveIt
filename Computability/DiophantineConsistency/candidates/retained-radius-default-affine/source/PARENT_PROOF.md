# Raw integer bijection followed by the signed comparison-base lift

Let r_0,...,r_1176 be the original quadratic source residuals. For
each of the 78 raw guard values v recorded in domain_certificate.json
add G_v=v-a_v^2-b_v^2-c_v^2-c_v, with fresh integer coordinates.
The complete polynomial is Q1493=sum_i r_i^2+sum_v G_v^2. All its
4981 collected monomials are stored, with exact degree 4 and height
427. All coordinates, including source gates and guard witnesses,
range over Z. Integer sum-of-squares zero means every residual zero.

## 1. First reverse all signed projections over Z

Every projected child includes the complete signed monic elimination
and integer inverse certificate. Reverse it first, including its guard
coordinates, to get a literal Q1493 zero. Each inverse is an integer
polynomial; no sign or natural subtraction is assumed. No parent
coordinate is removed as unconstrained. The independent verifier
checks all actual pivot equations and the entire substituted child
residual list.

## 2. Exact raw1493-to-compact901 zero bijection

The full variable metadata identifies the exact 667 retained raw
coordinates. The other 592 coordinates have unique triangular affine
monic recipes. These identities hold over all integers. Restoring
them makes exactly 592 defining rows identically zero and sends the
other 585 raw rows to the literal compact body residuals. Restriction
after restoration is identity on the 667 retained values; restoration
after restriction is identity at any raw zero because its defining
rows hold.

All 78 raw guard values equal their corresponding compact values.
Copying their triples therefore identifies all 78 guard rows exactly.
The entire 1255-row partition in BRIDGE901.json consists of 592 zero
defining rows and each of the 663 compact residuals once. Its full
restriction/extension maps include all 901 body and guard coordinates.
The checker collects every row identity and verifies every triple
position. This establishes a literal Z-zero bijection Q1493 <-> Q901,
with no auxiliary choice, order premise or body change.

It is **not** yet a zero of the old 904 equation: q4 has no guard and
may be negative. In particular the old 79-guard theorem is not applied
with a missing hypothesis.

## 3. At the complete 78-guard source, use the signed-B theorem

Apply the accepted ordinary theorem in research/comparison-base-sign,
as bound by the compact901 proof and complete use audit. All its
arithmetic and source interfaces are pinned. The prefix proof and
positive constructors use none of the omitted q4 sign: all 643 prefix
values are nonnegative, all 15 actual indices k>=1, A>=2 and A>W^W.
Retained YminusK and product factors imply every Y>=k>=1 and V>0.
The common norm gives abs(U)>=A>=2.

The actual equations say B=1+4V(q4+1), B-A=U*bq. For q4>=0,
B>=5; for q4<=-2, B<=-3. The only remaining case q4=-1 would give
B=1 and U dividing A-1, contradicting 0<A-1<abs(U). Hence abs(B)>=3.

The signed comparison-base extension now recovers the main index at
the original signed B, using abs(X), abs(U), sign(X)*S and signed R
as its numerical proof parameters. The two negative-base recurrence
parities are absorbed independently. The old short-interval argument
includes Y=1 and i=n. Thus abs(X)=chi_k(A),Y=psi_k(A). Independently
selected positive-base source calls exclude negative X by the positive
multiple m*n^k+1<T. The separate raw92 pow1 call gives f0 positivity
before the final raw753 modulus sign. This preserves the exact staged
dependency order and uses no downstream interpretation prematurely.

The raw tuple is still unchanged at this stage. The next stage is
the nonpointwise comparison-witness reconstruction; these two stages
must not be confused with a proof that the original q4 is positive.

## 4. Lift with the existing common U,V and fixed guarded values

Read all formulas from the original tuple snapshot. Set

    t=abs(q4)+1,
    q4'=q4+abs(U)*t,
    B'=B+4V*abs(U)*t,
    bq'=bq+4V*sign(U)*t.

Then q4'>=abs(q4)+2>0, B'=1+4V(q4'+1), and B'-A=U*bq'. U remains
signed, nonzero and unchanged. For every already oriented main pair
choose

    S'=chi_k(B'), R'=psi_k(B'),
    sq'=(S'-X)/U, rq'=(R'-k)/(4Y).

Both quotients are integers: base transfer modulo U and base-one
reduction modulo 4Y prove exact divisibility. Their denominators are
nonzero. The fresh comparison norm holds, and no quotient sign is
required. No new common Pell unit, CRT existence or mutual
coprimality of the seed ordinates is assumed.

LIFT904.json records the exact 62 snapshot free-witness recipes and
the complete raw-use boundary. Reevaluate exactly their topological
gate descendants. The independent audit checks all 1029 unit gates
and all 148 nongates in the 1177-row source: precisely 141 gates and
46 nongates change. Each changed nongate has a full original-row
ideal whose only nongate term is itself with coefficient 1; its
displayed target norm/congruence holds at the new witnesses. Hence
every changed actual row is restored. All other original rows are
unchanged or their unchanged defining gates still hold.

All 78 guarded values, the entire prefix, U,V, all 16 main pairs,
every actual power argument/quotient and all bootstrap/frame data
stay fixed. Existing guard witnesses can therefore be copied. The
full raw body zero is restored, although some raw and retained body
values have changed. The exact raw-to667 restriction from step 2
therefore gives the corresponding new compact body zero.

## 5. Three NEW-q4 witnesses into904, then63 witnesses into967

Copy all 78 triples to their exact frozen904 positions. The bridge
checker recollects the entire 78 copied guard polynomials at the
guarded values fixed by step 4 and checks the complete witness
partition. Choose one Legendre triple for q4'>=0 in the precise
target slots850,851,852, guarding CV303/raw657 at its *new* value.
The literal missing target residual is checked. The old q4 value is
not guarded, and no old q4 witnesses were copied.

This gives a literal904 zero. Only now use its frozen pointwise
21-sign theorem and additional 63 Legendre witnesses to reach its
literal967 parent. The downstream bridge is pinned, and the complete
compact901 checker reruns its signed-B author/peer and904 checks in
each mode. Its inherited ordinary calibration is invoked only after
the appropriate literal parent zero exists.

Conversely, any904 zero restricts to901 by forgetting the q4 triple;
step 2 restores a1493 zero. The signed projection equivalences in
step 1 then give all child existence equivalences. There is no claim
that the comparison lift has an inverse or is pointwise natural.

## 6. Complete finite verification scope

Each whole SOS polynomial is independently collected and compared
coefficient for coefficient, giving exact degree4, support size and
height. The entire signed inverse and residual certificates, all
guard identities and the literal901/nonpointwise904 bridge data are
verified. Corrupt row partitions, inverse/whole coefficients, copied
or fresh witness positions and an old-q4 positivity substitution are
rejected. Finite signed controls supplement the universal identities;
the unbounded index/lift argument is the accepted ordinary proof,
not a sampling conclusion. Normal and optimized Python retain all
checks. No frozen candidate, canonical page or Lean file is modified;
no new internal-ZFC theorem is asserted.
