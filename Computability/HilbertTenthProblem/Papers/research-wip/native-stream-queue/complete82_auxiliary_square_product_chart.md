# A two-coordinate 82-gate chart that erases the auxiliary restriction

This packet emits one complete **82=45M+37A** arithmetic circuit with **18 positive supplied witnesses** and exact degree **185**. It is an **unproved candidate, not an 82-operation universal bound**. The [source](complete82_auxiliary_square_product_chart.py) and [receipt](complete82_auxiliary_square_product_chart.json) start from the actual saved [84 circuit](complete84_scaled_strong_output.md), delete two coordinate-product producers, and retain every other paid row and the complete finalizer.

The new chart has an exact forward polynomial identity. More significantly, its auxiliary and strong equations impose no further restriction on the intended unit sector once the retained computed c is odd and target R is positive. There is also an exact projection theorem for the **complete candidate output**, allowing either sign of the five-factor product. These statements diagnose a lost native constraint; they do not establish a false accepted ordinary input.

## 1. Actual source edit and paid count

The parent supplies positive f and T=`auxiliary_quotient` and computes

    L16=f*f,
    auxiliary_Tf=T*f.

Delete those two multiplication rows. Supply their outputs directly in place of f and T:

    F_aux=L16, U_aux=auxiliary_Tf.

**F_aux is distinct from the still-retained packing witness F.** No packing port is renamed, deleted or made free. The original i remains a positive supplied coordinate.

Every other source row is literally retained, including the computed discriminant Delta (source register `A`), c=`R10a`, R=`r_lhs`, c², Delta*c², and

    S=i*Delta*c²,
    K=S²,
    V=c*(U_aux-1)-R*F_aux,
    Na=K*(V²-y_aux²)+y_aux²,
    Ns_scaled=Delta*F_aux-K.

The final output remains the product of the seven original factor ports minus Delta. In particular all six final product multiplications and the last subtraction are paid. The old f had precisely two consumers, the two deleted rows; old T had precisely one. There are no hidden retained f or T uses. Ac2=Delta*c² stays paid and live in both the main and auxiliary coefficient cones.

| Part | M | A | Total |
|---|---:|---:|---:|
| Complete retained factor producers |39|36|75|
| Full finalizer |6|1|7|
| Complete candidate |45|37|82|

The old total was 84=47M+37A. All 82 rows and all 25 declared free ports are live. The ordinary positive input, six fixed compiler numeral ports and their inherited recipe, and total witness count are unchanged. The count is for an arithmetic candidate whose soundness remains unproved.

## 2. Exact full forward map and the missing inverse

The substitution

    F_aux=f², U_aux=T*f

gives the complete identity

    P82(F_aux=f²,U_aux=T*f)=P84                    (1)

over every commutative ring. The helper checks all 82 retained formal register identities under this substitution. Hence every positive integer parent zero maps to a positive integer candidate zero at the same ordinary input.

On positive integer coordinates, the image of this literal map is precisely the set where F_aux is a square and its positive square root divides U_aux. Only there can one restore

    f=sqrt(F_aux), T=U_aux/f

as positive integers. This circuit supplies neither test. The forward map is injective on positive tuples, but is not onto the candidate's positive zero set, as Section 5 proves.

No generic candidate zero is assumed to have the seven intended factor values. The complete source has a useful exact identity that determines the appropriate sign statement instead.

## 3. Exact projection of the complete output on a stated sector

Let P5 be the product of the unchanged first, main, input, index and transport factors, and put

    Baux=Delta*i²*c⁴,
    Qs=F_aux-Baux.

These are proof expressions, not new free ports or omitted charged source operations. The actual coefficient K=Delta²*i²*c⁴ gives

    Ns_scaled=Delta*Qs,
    P82=Delta*(P5*Na*Qs-1).                         (2)

The helper verifies (2) by a complete sparse coefficient expansion at the mathematical ports and the literal retained source definitions. It is an all-ring identity, using no unit equation or positivity.

Fix every outer supplied coordinate, including i, the ordinary input and fixed numerals. The three refreshed coordinates are only F_aux,U_aux,y_aux. Consider the explicit sector

    Delta>0, c>0 odd, R>0, i>0,
    Baux=Delta*i²*c⁴>1.                              (3)

The last inequality is automatic for the actual positive-source sizes: a=Y(X+1) is a positive integer and Delta=(a+1)(a+3)>=8. Oddness of c and positivity of the computed R are stated sector restrictions, not assumed consequences of every candidate zero.

**Projection theorem.** For a fixed outer tuple satisfying (3), there exist positive integer F_aux,U_aux,y_aux with P82=0 if and only if P5 is +1 or -1.

For necessity, cancel the nonzero integer Delta in (2). The three integers P5,Na,Qs have product 1, so each is a unit. Moreover Na cannot be -1 modulo 4: K=S² is 0 or 1 modulo 4, and

    Na=K*V²-(K-1)*y_aux²

is respectively y_aux² or V² modulo 4. Thus Na=1 and Qs=P5=epsilon for some epsilon in {+1,-1}. This reasoning does not assign signs to the five individual factors beyond their product.

For sufficiency, take epsilon=P5 and set

    F_aux=Baux+epsilon>0,
    S=i*Delta*c².

Because c is odd, choose a positive v satisfying

    v=epsilon*R (mod c), v=3 (mod4).                 (4)

The moduli c and 4 are coprime. This is a finite CRT choice with no condition involving a main Pell index. Define

    V=chi_S(v)/S, y_aux=psi_S(v).

Here S>1. For odd v=2j+1, chi_S(v)=S*Q_j(S²) is an integer-polynomial identity. Since j is odd and c divides S, the zero-argument identity Q_j(0)=(-1)^j*v gives

    V=-v=-epsilon*R (mod c).

Also F_aux=epsilon modulo c. Therefore

    U_aux=(V+R*F_aux)/c+1                            (5)

is a strictly positive integer and satisfies the literal source expression V=c*(U_aux-1)-R*F_aux. The Pell norm at S gives Na=1, while Ns_scaled=epsilon*Delta. Equation (2) now gives P82=0. All three new coordinates are positive.

Equations (4)-(5) construct existential witnesses; they are not uncharged circuit instructions. They prove the full-output projection theorem for fixed outer data and fixed positive i. In particular, if all five retained factors equal +1, the epsilon=+1 case always supplies the two intended auxiliary/strong values. The other sign branch is included because the actual output permits it.

This is the precise arithmetic restriction lost by the chart. It does not prove that every outer tuple satisfying P5=+1 or -1 is a valid accepting computation, nor that the resulting ordinary-input relation differs from the universal parent's relation.

## 4. The scaled wrong-index family no longer needs its old CRT condition

The [scaled first/main family](first_index_scaled_obstruction.md) has, for odd t>=11,

    p=t(t+2), n=t(t+1), X=2^p, Y=2^(t+1),
    E=XY, a=Y(X+1), A=a+2,
    (D,c)=(chi_A(p),psi_A(p)),
    (tau,k)=(chi_(2XY²+1)(n),2psi_(2XY²+1)(n)).

Its first/main norms, strict positive ratio and main-root projection are established by the pinned proof. As in the [native-alias note](free_coefficient83_native_alias.md), set R=2n-1 and h=(k-2n)/E. Then h is positive integral and the actual index factor is +1, although R-p=t²-1>0.

Here c is odd and n is even, so R=3 modulo 4. The positive-sign construction in Section 3 can simply choose v=R. The earlier free-S83 construction additionally required v=p modulo 4p, and therefore gcd(c,p)|(R-p). That extra congruence was needed to restore a quotient divisible by f. This chart removed f and has no such requirement.

The receipt constructs the actual first/main/index data at t=13:

    p=195, n=182, R=363, gcd(c,p)=195.

The old condition fails because 195 does not divide 168=R-p. Nevertheless Section 3 supplies the auxiliary and scaled strong equations, with i=1 and v=363. The computed c has 40,741 bits; the candidate F_aux has 163,379 bits. Both native norm equations, the strict ratio, positive main quotient and positive h are checked as exact integers. V,y_aux,U_aux are defined by the theorem and are not materialized.

This remains a native subsystem example. Its abstract R is not thereby equal to the circuit's computed packing register. The existing modulo-17 obstruction still excludes this dyadic family at the stated B=16 necessary-mask interface for every q=16^ell. Input and transport are not furnished by this construction. There is no full compiler counterexample here.

## 5. A full positive-zero extension outside the literal parent image

A different consequence starts from an actual positive parent zero. Keep its ordinary input and every coordinate used by the five unchanged factors, and set i=1. The parent theorem gives R>0 and odd c>1, together with a positive main root D satisfying

    D²-Delta*c²=1.

Thus Section 3 applies with P5=+1 and produces a **full** positive candidate zero at the same accepted input. Its supplied square coordinate is

    F_aux=Delta*c⁴+1.

It is not a square. Indeed

    (D*c)²-F_aux=c²-1>0,
    F_aux-(D*c-1)²=c*(2D-c)>0,

because D>c. Therefore F_aux lies strictly between two consecutive integer squares. No positive integer f can restore the literal forward chart.

This construction changes i as well as the three newly chosen auxiliary coordinates; i has no consumers outside these two factors. It preserves the five-factor data and the ordinary input. It proves failure of the full positive witness inverse, not the existence of an unaccepted input or impossibility of a different existential soundness proof.

## 6. Uniform exact degree185

Every supplied witness and the ordinary input has degree 1; the six fixed numerals have degree 0. The five untouched factor polynomials and their leading forms are inherited literally from the pinned 84 source and its [independent review](review_complete84_scaled_strong_output.md). Put

    Q=Bm1*Jrep, k0=eta+zeta, gamma0=rho+sigma,
    C1=Q-F-Z-alpha-twice_cell_bits*x,
    Nt_top=w*C1-transport_quotient*Q.

Here F is the original packing witness, not F_aux. The source gives

    c_top=k0*s*Q³,
    Delta_top=w²*s²*Q⁸,
    K_top=i²*Delta_top²*c_top⁴.

The new V has exact degree 6 and leader c_top*U_aux; the R*F_aux term has degree only 5. Consequently Na has degree 58 and leader K_top*c_top²*U_aux². The scaled strong factor has degree 46 and leader -K_top, since Delta*F_aux has degree only 13. The seven degrees are

    22,18,32,58,7,2,46.

Their sum is 185. Multiplying the unchanged five-factor leader by these two new leaders gives

    32 Q^111 h gamma0 delta² i⁴ k0^13 w^18 s^31
        *Nt_top*U_aux².                             (6)

The monomial containing Jrep^112, h, rho, delta², i⁴, eta^13, w^18, s^31, transport_quotient and U_aux² has coefficient -32*Bm1^112. This is nonzero for every inherited admissible fixed-program slice. The final subtraction of degree-12 Delta cannot cancel it. Hence degree185 is exact uniformly; no zero-only equation lowers the formal polynomial degree. Naive gate propagation gives the separate upper bound195.

Two complete dense univariate coefficient executions check every emitted gate, all factor degrees and (6) at diagnostic numeral assignments and moduli. They corroborate the literal sources but do not replace the uniform leading-form proof or assert admissible compiler instances.

## 7. Executable evidence and replay scope

The packet authenticates nine immediate source/proof/data files and reads their bytes or JSON only. It executes no predecessor, archived Python, old builder or historical suite. One complete live 82-row source is saved; there is no metadata-only circuit claim and no general compiler API.

The receipt records 82 formal retained-register identities, 48 whole source evaluations including 24 rational assignments, 3,936 retained-value comparisons, the complete 17-monomial coefficient proof of (2), and both full degree diagnostics. It separately checks 186 exact positive sector extensions covering both signs, positive and negative CRT representatives before adjustment, and small odd c including 1. A 64-case residue check verifies the auxiliary negative-unit exclusion modulo 4.

The t=13 native fixture records a digest and bit lengths of its exact fields. Its huge remaining auxiliary witnesses are not materialized, and it is explicitly marked as not a full compiler zero. The general full-zero construction in Section 5 is proved parametrically from actual parent zeros rather than represented as an enormous numerical example.

Run from any working directory:

    python3 complete82_auxiliary_square_product_chart.py --root ABS_WIP --expect ABS_RECEIPT

`--output PATH` writes the stable receipt. Checks use explicit exceptions and recursively type-exact JSON comparison under normal and optimized Python. Fresh normal and `python3 -O` exact replays from `/` pass. Frozen predecessors and repository files remain unchanged.
