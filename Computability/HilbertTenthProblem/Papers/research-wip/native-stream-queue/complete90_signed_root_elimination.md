# A complete universal polynomial in 90 operations and 17 positive witnesses

The fresh complete source has **90=52M+38A operations**, **17 strictly positive supplied witnesses**, and exact total degree **406** on every inherited valid fixed-program slice. It is obtained from the actual 84-operation polynomial by eliminating its strong-root coordinate `f` through a quadratic field norm.

The exact theorem is:

> On the unchanged positive retained witness domain and valid fixed-program slice, the new polynomial vanishes if and only if there is a **unique positive integer** `f` for which the original complete84 polynomial vanishes on the same retained supplied coordinates.

The algebra first restores a nonzero signed integer f. The accepted, independently reviewed signed-quotient positivity theorem then forces it to be positive. Thus deletion of f gives a bijection of complete positive zero sets, and the parent's full ordinary-input universality transfers without changing any other witness or the fixed-program recipe. This improves the number of positive witnesses to17 at a cost of90 operations and degree406; it is not an operation improvement over84, and the established84/187/18-positive-witness result is unchanged.

## 1. The literal source and complete ledger

The parent is the authenticated `complete84_scaled_strong_output.json`, SHA-256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. Dependency closure on its actual84 rows finds exactly67 computed rows independent of `f`. Retain all67 literally, in their existing topological order, remove the supplied `f`, and append the23 rows below. The seventeen removed computed rows are exactly those depending on `f`; their complete list is recorded in the receipt.

Use the actual retained producers

    Delta=A, c=R10a, c2=c², R=r_lhs,
    T=auxiliary_quotient, y2=aux_y2=y_aux²,
    S=aux_coefficient_root=Delta*i*c², Q=R16=S².

`norm_triple` is the already-paid product of the first, main and input factors. The two remaining f-independent factors are `norm_index` and `norm_transport`. The following names abbreviate the emitted `er_` registers; they are not extra supplied ports:

    k=i*c2; kS=k*S; D=kS+1;
    RD=R*D; b=c+RD; u=c*T; u2=u*u;
    p=D*u2; b2=b*b;
    P5a=norm_triple*norm_index; P5=P5a*norm_transport;
    C=P5*Q; L=C*p; M=C*b2;
    Pc=P5-C; Znew=Pc*y2;
    LM=L+M; LMZ=LM+Znew; alpha_new=LMZ-1;
    alpha2=alpha_new*alpha_new; prod=L*M; four=4*prod;
    out=alpha2-four.

Here `Znew` and `alpha_new` are distinct from the retained supplied ports `Z` and `alpha`. The literal output is `elimination_polynomial`.

| Source part | M | A | Total |
|---|---:|---:|---:|
| All retained f-independent parent producers |36|31|67|
| Complete appended field-norm computation |16|7|23|
| Complete new polynomial |52|38|90|

The multiplication by4 is charged. No power, factor, sign comparison, variable division or other producer is silently supplied. Every one of the90 rows and all24 supplied ports are live. The latter are seventeen witnesses, the ordinary input `x`, and the unchanged six fixed numerals `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`. The original eighteen-witness list loses only `f`; `T,i,y_aux` remain independent positive witnesses. The fixed-program recipe remains the parent's, including its shifted mask convention.

## 2. Exact field-norm identity

All identities in this section are over the integer polynomial ring; they do not assume a zero or positivity. Define proof abbreviations

    D=1+Delta*i²*c⁴,
    b=c+R*D,
    A_rat=Q*(c²*D*T²+b²)−(Q−1)*y²−1,
    B_rat=2*Q*c*T*b,
    P5=norm_first*norm_main*norm_input*norm_index*norm_transport.

Every ingredient other than the proof symbol `f` belongs to the actual retained source. In particular D is computed as the integer polynomial `1+(i*c²)*S`; it is not formed by dividing `(Q+Delta)` by Delta.

The complete appended source gives

    alpha_new=P5*(A_rat+1)−1,
    L=P5*Q*c²*D*T²,
    M=P5*Q*b²,
    4*L*M=D*(P5*B_rat)².

Thus its full output is exactly

    F90=[P5*(A_rat+1)−1]²−D*(P5*B_rat)².             (1)

The use of L and M shares products already needed in `alpha_new`, avoiding separate paid construction of both B_rat and its squared contribution. The complete90 array, not a local-boundary schedule, establishes the ledger above.

For comparison the literal parent has

    V=c*T*f−c−R*f²,
    Na=Q*V²−(Q−1)*y²,
    Ns=Delta*f²−Q,
    F84=P5*Na*Ns−Delta.

Writing `E=f²−D`, direct expansion gives

    Ns=Delta*(1+E),
    Na−1=A_rat−B_rat*f+E*q_aux,
    q_aux=Q*(c²*T²−2*R*c*T*f+2*R*b+R²*E).

In particular the full all-ring relation is

    F84−Delta*[P5*(A_rat−B_rat*f+1)−1]
       =P5*Delta*E*(q_aux+Na).                       (2)

The fresh helper expands the actual auxiliary producers and both complete output expressions at the actual f-independent factor cuts. It checks (1) and (2) coefficientwise. The67 identical retained rows bind these cuts to the original computed values. The new and old full polynomials are different; no same-polynomial or all-real-zero equivalence is claimed.

## 3. The complete signed-integer projection

Throughout this section the retained witnesses are strictly positive integers, the ordinary input and fixed coefficients have the inherited domains, and the valid fixed-program recipe has `Bm1>0`. This already makes

    q=Bm1*Jrep+1>0,
    X=w*q>0, Y=s*q³>0,
    a=Y*(X+1)>0,
    Delta=(a+1)*(a+3)>0,
    c=(eta+zeta)*Y+eta>0.

Consequently Q, T and i are positive. Also

    D=1+Delta*i²*c⁴>c>0.                            (3)

The literal R is an integer even away from any zero. Therefore `b=c+R*D` never vanishes: R>=0 makes it positive, whereas R<=−1 makes it negative by (3). It follows that `B_rat=2Q cT b` is nonzero throughout this retained positive domain. Its sign off the original zero set is not assumed positive. No index equation, native history, R positivity or compiler soundness is used for this nonvanishing fact.

### From a signed parent zero to a candidate zero

Let a nonzero signed integer f satisfy F84=0. Since

    Ns=Delta*(f²−Delta*i²*c⁴),

cancelling the positive integer Delta gives

    P5*Na*(f²−Delta*(i*c²)²)=1.

The last factor is an integer unit, hence ±1. The negative sign is impossible modulo4: `Delta=(a+2)²−1` is0 or3 modulo4, and `f²−Delta*t²` is never3 modulo4 for integral f,t. Thus this factor is1, so `E=0`, `f²=D` and `P5*Na=1`. Equation (2) then gives

    P5*(A_rat+1)−1=(P5*B_rat)*f.

Squaring and using f²=D proves F90=0. This argument itself also excludes f=0, since D>0; the stated nonzero qualifier is automatic at these parent zeros. No auxiliary sign or positivity of f is used.

### From a candidate zero to a signed parent zero

Suppose F90=0. If P5=0 then (1) is1, a contradiction. Together with the already proved B_rat≠0, this permits the rational definition

    f=[P5*(A_rat+1)−1]/(P5*B_rat).                  (4)

Equation (1) gives f²=D. A rational number whose square is an integer is an integer: writing f=p/q in lowest terms, `p²=Dq²` forces q=1. Since D>0, f is nonzero. No extra divisibility witness or division gate is needed for this mathematical inverse; the emitted polynomial computes neither quotient (4) nor a square root.

For this integer f, E=0. By (2), or directly by the auxiliary remainder,

    P5*Na−1=P5*(A_rat+1)−1−P5*B_rat*f=0,
    Ns=Delta.

Hence F84=0 on the identical retained supplied coordinates. Formula (4) also proves uniqueness of the restored signed f. In particular the signed-parent-to-child map is deletion of f and its inverse is (4). The following independently reviewed sign theorem strengthens this to the parent's positive zero set.

The finite residue table in the helper corroborates the mod4 exclusion, but the preceding elementary square-residue argument proves it for all integers. The only local numerical zero examples retained from the rational scout are expressly nonnative component examples; no enormous complete native tuple is computed.

## 4. Positive reconstruction and inherited universality

The accepted proof-only theorem `complete84_signed_quotient_soundness_scout.md`, together with `review_complete84_signed_quotient_soundness.md`, says the following for the **same actual84 source and full valid inherited compiler recipe**: if every witness except T is strictly positive and T is any integer, then every zero has T>0. It recovers the original positive tuple itself. This is not a theorem for arbitrary mask numerals or additional signed coordinates.

Its proof first uses the accepted signed-T rank/bounds argument to obtain odd R and both Pell indices. Ratio estimates recover X=2^R without assuming R modulo4. A parity-free half-binomial extraction and its valuation force the actual population threshold and shifted masks. The valid compiler's low mask then forces R=3 modulo4. The two original unsquared auxiliary congruences, with their strict modulus bounds, jointly remove the possible parity twist and force V>0 and T>0. The full historical positive compiler is invoked only after that restoration. The complete proof and independent review were read inertly for this construction; no historical helper was run.

Apply this result to the signed f supplied by Section3. If f were negative, simultaneously replace

    f by -f,    T by -T.

The actual source has only two direct f consumers, `f*f` and `T*f`, and T occurs directly only in the latter. Both products are unchanged by this simultaneous sign change, so every computed parent value and its output are unchanged. This would produce a parent zero with f positive, T negative and every other witness still positive, contradicting the accepted signed-T theorem. Hence the uniquely restored f is positive. The zero-f sector was already excluded in Section3.

Deletion of f and formula(4) therefore give an exact bijection between the new complete positive zeros and the original complete positive zeros on each valid fixed-program slice. The input x, fixed numerals and every retained witness are preserved. In particular every original accepting input has a new positive witness tuple, and any new positive zero restores an original positive zero and hence an accepting input. There is no separate native completion, weakened input predicate or conditional acceptance claim.

The four added proof/provenance pins are:

| File | SHA-256 |
|---|---|
| `complete84_signed_quotient_soundness_scout.md` | `b2f1c37ebf68216e657006acaebbac0b27faedb325e1603983786085d580f44a` |
| `complete84_signed_quotient_soundness_scout.json` | `0e31841fce2a8db87c930c8f5fcfeeab3e3761547897c218d2c964e1dab906cf` |
| `review_complete84_signed_quotient_soundness.md` | `e392d0c0c904d64a007234ec2a2759921ac6bbb1f2ca058539c15dd6705486f8` |
| `review_complete84_signed_quotient_soundness.json` | `2551ffd6511d2e39254bed4c2f44ec270e71123ea5485389176cff37c59205a9` |

The fresh helper authenticates these accepted proof bytes and their exact actual84/f-consumer/T-consumer binding. The author's proof-only manifest retains its original pending-review status; the separately pinned independent review is PASS. This program does not turn a metadata status into a proof or claim to execute the mathematical theorem.

## 5. Exact total degree406

Give each retained witness and ordinary input degree1 and each of the six fixed numerals degree0. The only inherited leading cancellations needed here are the main and input norms. The helper guards their actual source cones and proves the all-ring expansion

    (X+a*c+g)²−(a²+H)c²
       =X²+2Xg+g²+2acX+2acg−Hc².

For the main norm use the actual X,c,g. For the input norm use `X=W`, `c=index_rhs`, `g=modulus_multiple`, and the same `a=R12,H=a4m5`. This gives exact degrees22,18,32,7,2 for the five retained factors, hence degree81 for P5. The naive uncancelled graph bound for F90 is426; it is not the claimed exact degree.

Set

    Q0=Bm1*Jrep, k0=eta+zeta, gamma0=rho+sigma,
    C1=Q0−F−Z−alpha−twice_cell_bits*x,
    Ttransport=w*C1−transport_quotient*Q0.

The relevant homogeneous top forms are

    P5_top=−32*h*gamma0*delta²*k0³*w¹⁰*s¹³*Q0⁴⁹*Ttransport,
    R_top=Q0³*(Q0−F),
    D_top=i²*k0⁴*w²*s⁶*Q0²⁰,
    Q_top=i²*k0⁴*w⁴*s⁸*Q0²⁸.

The literal `R=r_lhs` has degree4. Degree7 belongs to the distinct `norm_index`, whose highest term is contributed by `−h*UM`. Replacing R by a higher-degree expression valid only at zeros would change this all-value source and is not part of the construction.

The successive exact degrees are

| Register | Degree |
|---|---:|
| P5,Q,R,D |81,46,4,34|
| b,u,p,b2 |38,6,46,76|
| C,L,M,Znew |127,173,203,129|
| alpha_new,alpha2,4LM,F90 |203,406,376,406|

Thus M uniquely supplies the degree203 part of `alpha_new`, and its square uniquely supplies the degree406 part of the output. Its full leader is

    P5_top²*Q_top²*R_top⁴*D_top⁴
      =1024*h²*gamma0²*delta⁴*i¹²*k0³⁰*w³⁶*s⁶⁶
             *Q0²⁴⁶*(Q0−F)⁴*Ttransport².            (5)

The distinguished witness monomial

    Jrep²⁵²*h²*rho²*delta⁴*i¹²*eta³⁰*w³⁶*s⁶⁶
         *transport_quotient²

has coefficient `1024*Bm1²⁵²`, nonzero on every valid slice. This proves uniform attainment without relying on a numerical coefficient assignment. The fresh helper propagates the complete highest homogeneous polynomials after the two guarded norm expansions, independently compares (5), and records its7,533-term digest and distinguished coefficient. The number of expanded leader terms is algebraic evidence, not a paid operation count.

## 6. Evidence, limitations and replay

The fresh standard-library helper authenticates ten dependencies: the complete84 and rational-scout trios plus the four signed-domain proof/review files above. It reads their bytes/source/receipts inertly and executes none of them. It proves source closure and liveness, the exact67+23 ledger, full output identities at the bound actual cuts, the six-term norm expansion, all stated degrees and uniform leader. It guards parent immutability. Thirty-two complete signed/rational source evaluations compare every retained producer (2,144 comparisons) and the field-norm output; these are off-zero checks, not accepting histories.

The helper uses explicit checks in normal and optimized Python, rejects duplicate JSON keys and nonintegral numeric JSON, compares receipts recursively with exact types, and requires exactly one of exclusive `--output` or read-only `--expect`.

    python3 /tmp/complete90_signed_root_elimination.py \
      --root /absolute/path/native-stream-queue \
      --expect /tmp/complete90_signed_root_elimination.json

The writer and fresh read-only normal and `python3 -O` exact replays from `/` all pass.

The complete arithmetic source, uniform degree and exact positive-zero projection are proved here relative to the pinned accepted compiler and signed-domain theorems. No generic rational-substitution compiler, arbitrary signed-domain universality, or global operation/witness optimum is asserted. This is one fully paid17-positive-witness construction.

Final source SHA-256: `5f41f627ef6649b7dc975f3500f99ede576b156fd787423408b2433a1cd0170c`.

Final receipt SHA-256: `ed9595e1ec8077402efac9596a968a10823b20957e3f13740384ef997474cf22`.
