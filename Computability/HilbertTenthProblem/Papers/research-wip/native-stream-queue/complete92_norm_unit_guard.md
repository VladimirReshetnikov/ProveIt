# A 92-operation universal polynomial with 17 positive witnesses and degree325

This complete source computes a universal polynomial in **92=52M+40A operations**, with **17 strictly positive witnesses** and uniform exact total degree **325** on the unchanged valid fixed-program recipe. It has exactly the same positive zero tuples as the accepted90-operation,17-witness polynomial, while lowering the degree from406 to325. The two polynomials are different. This is a degree/operation tradeoff, not an improvement over the separate84-operation construction and not a global optimality claim.

The construction keeps the same67 f-independent computed rows of the actual complete84 source and adds25 fully paid rows. It replaces the prior outer quadratic field norm by an integer-unit guard on the local norm. A modulo4 argument forces that guard to be +1, making the unique reconstructed strong root integral. The already reviewed signed-domain theorem then makes that root positive.

## 1. Actual source, notation and interface

The source parent is `complete84_scaled_strong_output.json`, SHA-256
`8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`.
The independent comparison is the frozen complete90 source/receipt,
SHA-256 `ed9595e1ec8077402efac9596a968a10823b20957e3f13740384ef997474cf22`.
Both are read as immutable JSON data; neither predecessor helper is imported or executed.

The actual source bindings are

    Delta=A, c=R10a, c2=c², R=r_lhs,
    T=auxiliary_quotient, y=y_aux, y2=aux_y2,
    S=aux_coefficient_root=Delta*i*c², Q=R16=S².

The proof symbol `A_rat` is distinct from the retained source register `A=Delta`. Define

    D=1+Delta*i²*c⁴,
    b=c+R*D, u=c*T,
    A_rat=Q*(D*u²+b²)−(Q−1)*y²−1,
    B_rat=2*Q*u*b,
    K=A_rat²−D*B_rat²,
    P5=norm_first*norm_main*norm_input*norm_index*norm_transport.

Every quantity here is computed from the retained source. D is the integer polynomial `1+(i*c²)*S`, not a quotient of computed ports. The actual `norm_triple` already includes the first three factors of P5.

The new full polynomial is

    F92=P5*(K+1)−1.                                  (1)

The supplied list is exactly the complete90 list: the parent's18 positive witnesses with `f` removed, the same ordinary input `x`, and the same six fixed numerals `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`. No other supplied coordinate is introduced, deleted or changed. In particular the auxiliary quotient T, multiplier i and ordinate y remain positive witnesses, and the entire inherited compiler recipe—including the shifted MF convention—is retained.

## 2. The fully paid92-row source

Dependency closure of the actual84 array finds67 rows independent of f and17 depending on f. The former67 are retained literally in their original topological order. They also match the first67 rows of the accepted90 array. Append the following25 instructions, with emitted names prefixed `ng_`:

    k=i*c2; Dminus1=k*S; D=Dminus1+1;
    RD=R*D; b=c+RD; u=c*T;
    u2=u*u; p=D*u2; b2=b*b;
    P5a=norm_triple*norm_index;
    P5=P5a*norm_transport;
    sum=p+b2; gap=sum-y2; Qgap=Q*gap;
    Aplus1=Qgap+y2; A_rat=Aplus1-1;
    Qp=Q*p; Qb2=Q*b2; cross=Qp*Qb2;
    four=4*cross; A2=A_rat*A_rat;
    K=A2-four; unit=K+1;
    product=P5*unit; out=product-1.

The output is `polynomial92`. The factor4 is paid. The identity

    4*(Q*p)*(Q*b²)=D*(2*Q*c*T*b)²=D*B_rat²           (2)

allows the norm to be computed without separately constructing B_rat. Its use in the mathematical inverse is not an uncharged division in the arithmetic source.

| Source part | M | A | Total |
|---|---:|---:|---:|
| Literal retained67 producers |36|31|67|
| Appended local norm and unit guard |16|9|25|
| Complete polynomial |52|40|92|

Every paid row and all24 supplied ports reach the final output. The complete arrays, free/witness/fixed-port lists, topology, liveness, exact counts and removed-parent-row list are saved in the receipt. The original supplied f is absent. No comparison system or uncounted finalizer is substituted for the complete polynomial.

## 3. Exact all-ring algebra and comparison with90

The actual parent has

    V=c*T*f−c−R*f²,
    Na=Q*V²−(Q−1)*y²,
    Ns=Delta*f²−Q,
    F84=P5*Na*Ns−Delta.

Let `E=f²−D`. Expanding gives

    Ns=Delta*(1+E),
    Na−1=A_rat−B_rat*f+E*q_aux,
    q_aux=Q*(c²*T²−2*R*c*T*f+2*R*b+R²*E),
    F84−Delta*[P5*(A_rat−B_rat*f+1)−1]
       =P5*Delta*E*(q_aux+Na).                       (3)

The fresh helper independently reconstructs the actual auxiliary producers and full parent finalizer at the bound factor ports, checks(2) and(3), and expands the complete new tail to prove(1). Because all67 retained rows are literal, the formal boundaries refer to the actual computed source, not independent extra witnesses.

The accepted90 output is

    F90=[P5*(A_rat+1)−1]²−D*(P5*B_rat)².

The exact whole-polynomial relationship is

    F90=P5*F92+(P5−1)*(2*P5*A_rat−1).                (4)

The helper checks(4) by expanding the actual90 and92 output cones. In general the polynomials are unequal: for example, at the formal boundary P5=0, their values are respectively1 and−1. Equality of their positive zero sets needs the integer/unit argument below; it is not inferred from polynomial equality.

## 4. Integer reconstruction and exact positive-zero equivalence

The retained witnesses are strictly positive integers and the fixed numerals/input have the inherited domains. Before any zero equation, the actual source gives

    q=Bm1*Jrep+1>0,
    X=w*q>0, Y=s*q³>0,
    a=Y*(X+1)>0,
    Delta=(a+1)*(a+3)>0,
    c=(eta+zeta)*Y+eta>0,
    D=1+Delta*i²*c⁴>c>0.

Since R is an integer, `b=c+R*D` cannot vanish: it is positive for R>=0 and negative for R<=−1. Thus

    B_rat=2Q cT b != 0                              (5)

on the entire retained positive domain. Neither R positivity, an index equation, a native history nor compiler soundness is needed for(5).

### New zero implies a unique signed parent root

If F92=0, equation(1) says that the two integer factors P5 and K+1 are units. Since B_rat is even,

    K+1=A_rat²−D*B_rat²+1 = A_rat²+1 (mod4).

It is therefore1 or2 modulo4, and cannot be−1. Hence

    K=0, P5=1.

Define the rational number

    f=A_rat/B_rat.                                  (6)

The equation K=0 gives f²=D. A rational square root of an integer is integral: if f=p/q is in lowest terms, `p²=Dq²` forces q=1. Because D>0, f is nonzero. Substituting E=0 and A_rat=B_rat*f into(3) gives Na=1 and Ns=Delta; together with P5=1 these imply F84=0 on the same retained coordinates. No separate divisibility witness or arithmetic division gate is required for this proof of existence.

### Parent zero implies a new zero

For completeness this direction works for a signed parent root as well. At any such F84=0 on the retained positive domain, cancellation of Delta gives

    P5*Na*(f²−Delta*(i*c²)²)=1.

The final factor is an integer unit. Since `Delta=(a+2)²−1` is0 or3 modulo4, `f²−Delta*t²` can never be−1 modulo4. The final factor is therefore1, so f²=D and P5*Na=1.

The auxiliary factor is also never−1 modulo4. Indeed Q=S² is0 or1 modulo4, and

    Na=Q*V²+(1−Q)*y²

is congruent to y² or V², respectively. It follows that Na=1 and P5=1. Equation(3) now gives A_rat=B_rat*f, so K=0 and F92=0. Formula(6) proves uniqueness of the restored signed f.

### The signed root is positive on the valid compiler slice

The accepted `complete84_signed_quotient_soundness_scout.md` and its independent review prove that, for this actual84 source and the **full valid inherited compiler recipe**, a zero with positive f and only T allowed signed necessarily has T>0. The theorem restores the original tuple itself. It does not cover arbitrary mask constants or additional signed coordinates.

The literal source's only direct f consumers are `f*f` and `T*f`; T occurs directly only in the latter. Simultaneously negating f and T preserves every computed parent value and its output. If(6) were negative, this symmetry would create a positive-f, negative-T zero with every other witness still positive, contradicting the accepted theorem. Therefore f>0.

Consequently deletion of f and reconstruction(6) give a bijection between the full positive zeros of92 and84, preserving all retained supplied coordinates. The accepted90 source has the same projection and the same uniquely restored root, so90 and92 have exactly the same positive zero tuples. The original ordinary-input universality transfers in both directions on the unchanged fixed-program recipe.

The accepted signed-domain proof recovers X=2^R from odd-R Pell ratios, obtains the half-binomial population bound without assuming R modulo4, uses the actual shifted compiler masks to force R=3 modulo4, and uses both unsquared auxiliary congruences to restore V>0 and T>0. It invokes the full positive compiler only after restoring positivity. The construction here consumes that reviewed theorem; it does not repeat or execute the historical compiler proof.

## 5. Uniform exact degree325

The degree convention gives every retained witness and the ordinary input degree1 and the six fixed-program numerals degree0. The fresh helper guards the actual main and input cones and separately proves the cancellation identity

    (X+a*c+g)²−(a²+H)c²
       =X²+2Xg+g²+2acX+2acg−Hc².

For the main norm use its actual X,c,g. For the input norm use `X=W`, `c=index_rhs`, `g=modulus_multiple`; both use `a=R12,H=a4m5`. The five factors have exact degrees22,18,32,7,2, so P5 has degree81. All remaining highest components are obtained by literal source propagation. The uncancelled gate bound335 is recorded separately.

Put

    Q0=Bm1*Jrep, k0=eta+zeta, gamma0=rho+sigma,
    C1=Q0−F−Z−alpha−twice_cell_bits*x,
    Ttransport=w*C1−transport_quotient*Q0.

The relevant attained source top forms are

    P5_top=−32*h*gamma0*delta²*k0³*w¹⁰*s¹³*Q0⁴⁹*Ttransport,
    Q_top=i²*k0⁴*w⁴*s⁸*Q0²⁸,
    R_top=Q0³*(Q0−F),
    D_top=i²*k0⁴*w²*s⁶*Q0²⁰.

In particular literal R=`r_lhs` has degree4, not the degree7 of `norm_index`. The subsequent degrees and dominant terms are

    deg(b)=38, deg(p)=46, deg(b²)=76,
    deg(A_rat)=122, with top Q_top*R_top²*D_top²,
    deg(D*B_rat²)=214,
    deg(K)=244, with top A_rat_top²,
    deg(F92)=81+244=325.

The lower-degree cross term cannot cancel the degree244 square, and the final subtraction of1 cannot cancel the product top. The full leader is

    P5_top*Q_top²*R_top⁴*D_top⁴
      =−32*h*gamma0*delta²*i¹²*k0²⁷*w²⁶*s⁵³
             *Q0¹⁹⁷*(Q0−F)⁴*Ttransport.              (7)

The witness monomial

    Jrep²⁰²*h*rho*delta²*i¹²*eta²⁷*w²⁶*s⁵³
         *transport_quotient

has coefficient `32*Bm1²⁰²`, nonzero for every inherited valid slice. This proves uniform attainment without choosing special fixed coefficients or imposing zero-locus identities. The fresh helper independently propagates the source highest components, compares(7), and records its1,456-term digest and distinguished coefficient. Those expanded terms are proof evidence, not arithmetic gates.

## 6. Proof dependencies and fresh evidence

The helper authenticates ten frozen files: the84 and90 source/receipt/companion trios plus these four signed-domain proof/review files:

| File | SHA-256 |
|---|---|
| `complete84_signed_quotient_soundness_scout.md` | `b2f1c37ebf68216e657006acaebbac0b27faedb325e1603983786085d580f44a` |
| `complete84_signed_quotient_soundness_scout.json` | `0e31841fce2a8db87c930c8f5fcfeeab3e3761547897c218d2c964e1dab906cf` |
| `review_complete84_signed_quotient_soundness.md` | `e392d0c0c904d64a007234ec2a2759921ac6bbb1f2ca058539c15dd6705486f8` |
| `review_complete84_signed_quotient_soundness.json` | `2551ffd6511d2e39254bed4c2f44ec270e71123ea5485389176cff37c59205a9` |

The author proof-only manifest retains its original pending-review label; the separately pinned review is PASS. The helper checks their exact actual84 source and f/T-consumer binding. Authentication of a proof file is not execution or formal verification of its theorem. The complete proofs were read inertly.

The fresh evidence includes complete92 source reconstruction, all-row/all-port liveness, the literal67 retention and25-row append, exact all-ring coefficient identities at actual source boundaries, the two guarded norm cancellations and uniform degree proof. Twenty-four complete signed/rational arithmetic assignments check the output, the exact90/92 correction, and1,608 retained-value comparisons. Residue tables supplement the all-integer modulo4 proofs. No complete native Pell zero or new halting witness is materialized, and no supplied/frozen/archived helper is executed or imported.

The standalone standard-library CLI rejects duplicate JSON keys and nonintegral JSON numbers, preserves both input parent objects, uses explicit checks under normal and optimized Python, compares receipts with exact recursive types, and requires exactly one of exclusive `--output` or read-only `--expect`:

    python3 /tmp/complete92_norm_unit_guard.py \
      --root /absolute/path/native-stream-queue \
      --expect /tmp/complete92_norm_unit_guard.json

There is no generic rational-root compiler, unrestricted signed-domain theorem or optimality assertion. The positive universality statement is for this fully emitted source on the unchanged valid compiler recipe.

Final fresh author replay from `/` passed in both normal Python and `python3 -O`, each reproducing the saved receipt with exact recursive type equality. The frozen helper SHA-256 is `cce493645c8935b25f9805d9bd588db5d1aa55b2f9c571d2492fe5138852447b`; the receipt SHA-256 is `ae1f1564cbf8266a621cbcbbe5db9201d94483fe54441f289af245581e065cb3`.
