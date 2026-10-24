# Independent supplement: twelve-integer four-root carrier

## Verdict and scope

PASS. The construction is a valid ordinary two-way reduction to the reviewed fifteen-integer equation. Its literal polynomial has twelve unrestricted integer variables, exact total degree 500, and 148 live binary operations: 90 multiplications, 35 additions, and 23 subtractions.

The same complete six-integer source34 coefficient tuple is retained. This supplement does not assert a new native/compiler calibration, end-to-end proof-assistant certificate, encoded internal-ZFC derivation, proof of consistency, or global optimum. The already-reviewed fifteen-, fourteen-, and thirteen-integer equations remain separate alternatives. No further extension is part of this review.

## 1. The direct sixteen-sign formula is exact

Let the four scaled radicands be

    ar=4U^2 Dtau, br=36U^2 Df,
    cr=324U^2 Da, er=729U^2 G0,
    G0=budget-1-p2^2-p3(p3+1).

The literal direct formula using p,q4,u,v4,s,k4,l4,m4,Even,Odd was independently expanded and compared with a different construction: start with the standard three-root norm in an indeterminate x, substitute x+t, reduce the even and odd powers of t under t^2=er, and take the resulting quadratic conjugate norm. All 495 coefficients agree exactly.

Thus the output is the product of all sixteen factors with total center Z+U(Aroot+Broot+Croot) and all signs of the four square roots. This identity includes zero or repeated radicands; it is not a generic-only resultant claim. The direct formula's raw radicands are squares of scaled formal roots, so dividing by U^16 produces the monic degree-sixteen integer norm in Z/U+Aroot+Broot+Croot, regardless of the sign of U.

## 2. Monicity obtains CRT before the guard

The inherited affine arithmetic proves U!=0 and gcd(H,2q^2)=1 for every integer assignment. A zero of the direct norm makes the rational total center a root of the monic integer polynomial just verified. It is therefore integral, so U divides Z. Reducing the literal carrier modulo H and 2q^2 gives

    H|Klo, and v=q^2(2v0+1) with v0 integral.

In particular v=0 is impossible and the cubic scale is recovered. This step does not assume the guard is positive, G0 is nonnegative, or any individual radical is rational. There is no exceptional branch hidden behind a division by a radical sum.

## 3. The fourth squareclass really recovers the guard

The unconditional residues from the thirteen-integer argument remain

    Dtau=Df=Da=1 modulo 3.

The norm supplies a rational signed sum of roots weighted by 2,6,18,27. If G0=0, its root is zero and can be omitted; the previously reviewed three-root separation applies exactly.

For G0!=0, decompose every nonzero integer radicand into a signed squarefree representative d times s^2. In each nonrational squareclass, the coefficients contributed by the first three roots, when present, have exact powers of 3 equal to 0,1,2. Their square factors are prime to 3 because those radicands are 1 modulo 3. The fourth coefficient is 27s and has power of 3 at least 3, even if G0 is divisible by 3.

A group containing an earlier root has a unique coefficient of smallest 3-adic order, so its signed sum cannot vanish. A group containing only the fourth root is also nonzero. Linear independence of the distinct squareclass characters over Q therefore excludes every nonrational class. All four nonzero radicands are rational squares and hence integer squares. Negative G0 is ruled out by this argument, not excluded in advance; zero G0 has already been handled without division.

Choose integer roots tau,f,e,g. Then

    budget=1+p2^2+p3(p3+1)+g^2>0,

because p3(p3+1)>=0 for every integer p3. This recovers the original budget guard only after the squareclass argument. The scale and budget now imply c!=0 and Q=(Delta I)^2>=9.

## 4. Auxiliary divisibility and complete witness maps

The integer e with e^2=(Q-1)(QV^2-1) supplies the rational adjacent-Pell ordinate y0=e/(Q-1). The unbounded descent proved in the thirteen-integer review establishes y0 integral. Merely having an integer e would not suffice; this descent is an essential retained step. It applies to either sign of e or V.

Twelve to fifteen: with the integral CRT offsets gproj=Klo/H and v0=(v-q^2)/(2q^2), choose

    p1_15=g, f15=f, y15=y0-V,
    n15=tau-L-gproj-v0.

Retain every other shared coordinate. All first, strong, centered auxiliary and budget rows of the fifteen-variable equation vanish exactly. Thus its complete signed main-root/compiler theorem is applied only after restoring a literal fifteen-variable zero.

Fifteen to twelve: from any fifteen-variable zero set

    tau=|Z15/U+L|, f=|f15|,
    e=(Q-1)(V+y15), g=p1_15,
    n12=2tau+6f+18e+27g-Aroot-Broot-Croot-gproj-v0.

The original auxiliary and guard equations give exactly e^2=Da and g^2=G0. The new total center is one of the sixteen signed root sums, so the direct norm vanishes. The choices e and g can be signed because every sign occurs in the norm. All displayed quantities are integers and n12 is unrestricted.

These maps apply to every zero in both directions. There is no additional canonical choice, rank-tuning requirement, odd-period condition, sign assumption, or hidden root variable in the delivered polynomial.

## 5. Complete finite certificate of exact degree 500

The independent checker first reconstructs the generic centered three-root norm in the eight ports (Z,U,A,B,Croot,aa,bb,cc). It then substitutes Z-U*xi, reduces under xi^2=729G0, and takes the exact quadratic norm. A sparse integer-polynomial expansion produces every one of its 25,106 nonzero terms.

Give the nine ports the weights

    Z:7, U:6, A:11, B:7, Croot:41,
    aa:10, bb:6, cc:38, G0:16.

The complete expansion has weighted degree exactly 500 and a unique maximal-weight term

    2^12*729^2*U^16*A^4*Croot^8*G0^2.

The complete coefficient/exponent list is supplied as the gzip-compressed GENERIC_CENTERED_NORM_CERTIFICATE.json.gz, with an authenticated raw-content hash in CHECK.json. This is an exact finite upper-bound certificate, not merely an attained-degree test on sample lines. It also independently confirms the producer's formal-Laurent-series degree argument.

The actual front-end registers have the stated degrees. Their top parts make G00=-4q0^2Y0^2k0^2 nonzero. Substitution into the unique generic leading term and selection of h^8 and z^8 gives the exact actual coefficient

    [j^228 w^76 v^84 h^8 z^8 r^32 c^64] P12
      =2^488 3^332 beta^228>0.

The exponents sum to 500. The coefficient is nonzero for the authentic positive beta, so the actual total degree is exactly 500 after all fixed coefficient payloads are specialized.

## 6. Literal accounting, reproducibility and limits

The separate checker imports neither the producer builder nor its DAG library. It independently verifies 51 register cuts, all graph references, liveness of every input/coefficient/gate, both complete norm identities, monicity, all centered defects, the degree-500 certificate, and the selected actual coefficient. The exact live count is 148, including all scalar multiplications and squaring operations.

Twenty-six deliberately corrupted live operations are rejected, covering all four scaled radicands, both norm groupings, the direct Even/Odd construction, G0 and the final output. Normal and optimized-Python receipts are included. Runtime requirements are Python 3 and SymPy; the full baseline repository is not required. The six raw coefficient hashes are independently pinned in the checker, with optional complete byte comparison when baseline payloads are present.

These finite certificates establish polynomial identity, exact degree and evaluator accounting. The unbounded arithmetic maps are proved above. The native/compiler/refutation calibration remains the same named inherited ordinary mathematical theorem, not a theorem newly proof-assistant-verified by these finite checks.
