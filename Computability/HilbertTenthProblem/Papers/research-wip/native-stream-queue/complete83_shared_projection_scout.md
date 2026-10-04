# Shared positive projection: an unresolved 83-operation chart

The complete emitted polynomial costs **83=46M+37A**, has **18 strictly positive witnesses**, and has exact degree **187** on each inherited valid fixed-program slice. It saves one multiplication by supplying the positive value previously computed as `rho*(4a+3)` and sharing that value between the main and input roots.

**This is an unresolved relaxation, not a new universal bound.** Every parent84 positive zero maps forward, but the inverse requires a divisibility condition absent from the new circuit. The [mathematical companion](complete83_shared_projection_math.md) proves that the entire obstruction is a common offset in two encoded powers. It also gives a full positive diagnostic zero with a nonzero offset on scalar constants not certified as a compiled program. No rejected-input example or soundness theorem for valid programs is established.

The [independent source review](review_complete83_shared_projection_scout.md) checks every row, the complete all-ring forward identity and uniform exact degree. The [independent mathematical review](review_complete83_shared_projection_math.md) has the separate positive-zero and diagnostic-construction scope.

## 1. The paid coordinate change

The actual parent source has

    a=R12=Y(X+1), H=a4m5=4a+3, Delta=A=a^2+H,
    X=wn2=w*q, Y=sn2=s*q^3, c=R10a,
    D=R14=a*c+X+(rho+sigma)*H,
    mu=exponent_rhs=a*kappa+W+rho*H.

The witness delta in `kappa=u+delta*Delta` is distinct from the discriminant Delta; the literal register named A is Delta, not the Pell parameter a+2.

The earlier joint-root cut showed that sharing `rho*H` by reassociation alone still costs84. The present source changes the positive integer coordinate: replace rho by a new supplied positive U=`shared_projection`, and set

    D=(a*c+X+U)+sigma*H,
    mu=a*kappa+W+U.

Delete `gamma_sum=rho+sigma` and `modulus_multiple=rho*H`; change `gam` to `sigma*H`; insert `shared_main_partial=D1+U`; use that partial in R14 and U in exponent_rhs. The inserted main-root addition replaces the deleted gamma addition, leaving a net saving of one multiplication. All79 other definitions are retained literally. Every loader, norm, bound, auxiliary coordinate and finalizer remains in the full source array.

| Part | Multiplications | Additions/subtractions | Total |
|---|---:|---:|---:|
| Complete seven-factor producer core |40|36|76|
| Six product multiplications and final subtraction |6|1|7|
| Complete polynomial |46|37|83|

All83 rows and all25 free ports are live: eighteen witnesses, ordinary positive input x, and the six fixed numerals `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`. The MF port retains the shifted convention `MF_native+B-1`. Arbitrary numeral assignments accepted by algebraic checks do not certify a valid compiled program.

This differs from independent-gamma83, whose47M36A source removes the dominance relation between the two root quotients. Here the positive difference sigma is retained, while divisibility of their common projection is relaxed.

## 2. Whole-output identity and conditional inverse

Over every commutative ring, the full sources satisfy

    F83(U=rho*H, other coordinates unchanged)=F84.       (1)

Only the two displayed root cuts require algebra: `(rho+sigma)H=rhoH+sigmaH`. Every retained downstream row then agrees inductively, including all seven factors and the final subtraction of Delta. The common register gam intentionally changes, but its only consumer rejoins at the proved main root. The forward identity does not rely on a zero equation or division by H.

Before any equation is imposed on the inherited positive domain, q,X,Y,a,H and Delta are positive. Thus (1) maps every parent positive zero to a child positive zero. Conversely, at a child positive zero with H dividing U, the unique restored witness `rho=U/H` is a positive integer and (1) gives a parent zero with all other supplied coordinates fixed. Without divisibility the same substitution is only rational, which does not establish Diophantine soundness.

The new polynomial still factors identically as Delta times the corresponding normalized product-minus-one. On the positive domain one first cancels Delta, and only then infers integer units and proves the norm signs. It would be invalid to infer seven units directly from a product equal to Delta.

## 3. Exact uniform degree

Give the eighteen witnesses and x degree1, and each fixed compiler numeral degree0. The main and input norm cancellations must be respected; a naive gate-degree recurrence is insufficient. Put `E=X+U+sigma*H` and `E'=W+U`. Exact identities give

    Nmain=E^2+2*a*c*E-H*c^2,
    Ninput=E'^2+2*a*kappa*E'-H*kappa^2.

The new U has degree1, whereas sigma*H has degree7. The main leading term therefore contains sigma in place of the parent's rho+sigma. The input degree32 leader remains `-H*kappa^2`. All other factors retain their leading forms. Their exact degrees are

    22,18,32,60,7,2,46.

For an explicit uniform witness, define

    Q0=(B-1)J, k0=eta+zeta,
    C1=Q0-F-Z-alpha-twice_cell_bits*x,
    Ttransport=w*C1-transport_quotient*Q0,
    T=auxiliary_quotient.

The full leading homogeneous polynomial is

    32 Q0^111 h sigma delta^2 i^4 k0^13 w^18 s^31
       *Ttransport*T^2*f^2.                            (2)

Its monomial with `J^112*h*sigma*delta^2*i^4*eta^13*w^18*s^31*transport_quotient*T^2*f^2` has coefficient `-32*(B-1)^112`, nonzero for every admissible compiler. The final subtraction has degree12 and cannot cancel degree187. The independent reviewer reconstructs both norm identities from the actual source and checks all84 sparse terms in (2), including absence of coefficient cancellation after specializing the fixed numerals.

## 4. What the mathematical companion establishes

On every positive child zero on a valid inherited compiler slice, the unchanged normalized rank argument fixes the main Pell index at R. Positivity of sigma and the shared U then force the input index v<R; its discriminant residue forces the intended index v=u. This argument does not presume q is dyadic or U is divisible by H.

Writing `E_j=chi_(a+2)(j)-a*psi_(a+2)(j)`, the precise surviving conclusions are

    X-W=2^R-2^u,
    e=X-2^R=W-2^u,   |e|<a<H,
    U=H*rho0-e,       sigma=gamma0-rho0,
    rho0=(E_u-2^u)/H, gamma0=(E_R-2^R)/H.

Consequently

    H divides U  iff e=0 iff X=2^R iff W=2^u.            (3)

At e=0 the literal positive parent inverse exists. The nonzero-offset sector remains unclassified on valid programs. Recovering v=u alone is insufficient to decode a halting computation, since the separate input marker and temporal shift may still have moved.

The companion constructs all18 positive witnesses parametrically for

    (Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF)
       =(15,28,8,1,14,19),
    q=16, x=1, R=49023, W=0, X=2^R-512, e=-512.

The original cubed Y-scale, the two exact binary mask conditions, the transport equation and every normalized norm hold; U is512 modulo H. Thus scalar mask/packing conditions and the retained Pell system do not by themselves force the inverse. Those constants are explicitly not claimed to come from the valid compiler recipe. The proof defines immense witnesses by Pell/binomial formulas; no full numeric tuple is materialized.

## 5. Fresh evidence and frozen boundaries

The [fresh source helper](complete83_shared_projection_scout.py) reads the frozen parent as inert JSON/bytes, authenticates its three pins, reconstructs the complete new array and checks topology and liveness. Exact sparse coefficient checks prove the root cuts. Forty-eight complete signed/rational assignments, including24 rational ones, give5,040 retained value equalities and compare every factor/output. Two full dense univariate coefficient diagnostics attain the stated factor degrees and187 at diagnostic numeral assignments; the uniform proof is Section3 and the independent source review, not those samples.

Fresh normal and optimized runs from / reproduce the exact [receipt](complete83_shared_projection_scout.json) before commitment. The independent reviewer executes its own newly authored checker, never the author or predecessor programs, and proves the complete retained-DAG identities and leading form. No archived builder, historical suite or frozen predecessor program runs.

| File | SHA-256 |
|---|---|
| complete84_scaled_strong_output.json | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| complete84_scaled_strong_output.md | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| complete84_scaled_strong_output.py | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| complete83_shared_projection_scout.py | `2ff8bede5f08b0bc452ca50a432ebc6dbcad5ddd18bd5da5acc2b1d5b189ae9c` |
| complete83_shared_projection_scout.json | `dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c` |
| complete83_shared_projection_math.md | `1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c` |

The next mathematical task is to use the full compiler recipe to rule out e≠0, prove a different language-preserving normalization, or construct a valid-program false input. The established universal84/degree187 and85/degree155 points are unchanged.
