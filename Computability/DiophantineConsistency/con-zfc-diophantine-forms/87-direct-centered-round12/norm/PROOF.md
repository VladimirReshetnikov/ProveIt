# Integral square completion at the final norm

## Scope and completed circuits

This component improves the degree of a completed ten-unrestricted-integer consistency equation by changing one coordinate. It introduces no new Diophantine predicates or number-theoretic assumptions. Combine the shorter guard from ../source/short_guard with the norm-saturated H1868 equation from round11 (480 binary operations, exact degree1,245,324). The literal alternatives are:

- `integer10_polar.json`:471 operations, exact degree1,245,324.
- `integer10_center0.json`:485 operations, exact degree1,179,788.
- `integer10_center1.json`:496 operations, exact degree1,114,252.
- `integer10_center2.json`:545 operations, exact degree1,080,888.

These are degree/cost tradeoffs, not uniform simplifications or global minima. Polarization saves one operation. The exact retiming k=b(3k0+2), K=X+1+k(2Phalf−2) to twice_k=b(6k0+4), K=X+1+twice_k(Phalf−1) saves another. The short guard saves six operations. Finally define uv=halfU*V, halfA=halfU+uv, Phalf=U*uv. Distributivity and associativity show these are exactly the old halfA=halfU*(V+1), Phalf=halfU*U*V, but their joint graph uses four rather than five operations. This shared-product reuse saves one further operation. Fixed integer leaves are free, every binary addition, subtraction, multiplication, squaring and scalar multiplication costs1; reuse costs0. Actual coefficient payloads and native source data are included.

The inherited consistency theorem is stated with all arithmetic source and interpolation dependencies in `BASELINE_PROOF.md`. After the separately proved short-guard replacement, the universal argument below proves an exact bijection between integer zeros of that equation and each centered equation. Thus ZFC proves that each equation has no integer solution iff Con(ZFC), under exactly the baseline's explicitly identified mathematical calibration, without any new formal kernel certificate.

## Short-guard dependency

Replace the old Delta by

    Delta=g(cap−g)K²−cap²(C−KL)².

Keep a0=r+(9Delta−3)(rz)². The source/short_guard component gives the complete soundness and completeness proof. Briefly, the unchanged square-factor and residue argument first proves b,Q are positive squares, hence cap>0; with this established, Delta>0 forces0<g<cap and4(C−KL)²<K², exactly the bounds needed downstream. For canonical packed witnesses the coordinate at weight116 is a≥3, so g≥Bcode^116, and Bcode^116≥b² impliesg³≥cap². The existing approximation |C−KL|<|K|/(4g) and integer cap−g≥1 give Delta/K²>g−cap²/(16g²)>0. The Pell coefficient9Delta−3 still has3-adic valuation1. No assertion is made that the old and new guard inequalities are equivalent on all noncanonical inputs.

## 1. General translation lemma

Suppose all registers other than m are integer polynomials independent of m. Put

    Z=Sigma*m−Theta,
    N=(Z²−Sigma²(a0+a1))²−4Sigma⁴a0*a1.

Let P and J be integer polynomials, independent of m, with a1=P²+J. Define

    T=Z+Sigma*P,
    U=Z²+2Sigma*P*Z+Sigma²(a0−J),
    Nc=U²−4Sigma²*a0*T².

Then Nc(m)=N(m+P), identically. To see this, U=T²+Sigma²(a0−a1), and

    [T²+Sigma²(a0−a1)]²−4Sigma²*a0*T²
      =[T²−Sigma²(a0+a1)]²−4Sigma⁴*a0*a1.

The maps m↦m+P and m↦m−P are inverse bijections on integers even when Sigma=0. No division, nonzero hypothesis, inequality, or correctness of the underlying machine is needed for this algebraic step. A small polynomial defect J reduces total degree because cancellation is exposed instead of hidden inside a1−P².

## 2. First two square completions

Keep all round11 source registers, including

    D=(A²−4)C²+4, E0=C²*xi, E=D*E0,
    F=4(A²−4)C⁴D*xi²+1,
    G=(A/2−1)(F−1)−1,
    Omega=16C²D*xi,
    H=C+F(B−C+Omega*y), I=(G²−1)H²+1,
    a1=DFI.

A/2 is the existing integer polynomial halfA, not an admitted rational operation. For center0 choose

    R0=2AE,
    J_DF=D−16E².

For center1 choose

    R0=2A*E0*(D−2C²),
    J_DF=D+16E0²[(3C²−4)D−4C²(C²−1)].

In both cases DF=R0²+J_DF by expansion. Consequently

    P=R0GH,
    J=J_DF*G²H²−DF(H²−1)

satisfy a1=P²+J. These formulas, composed with section1, are the first two literal circuits.

The structural gain comes from the identity in center1: DF has A-degree6, but DF−R0² has A-degree2. It is a polynomial version of keeping the polynomial part of the Laurent expansion of sqrt(DF), not an assertion that sqrt(DF) is polynomial.

## 3. One further Laurent correction, with no rational coefficients

Here use the center1 R0 and abbreviate c2=C², h=A/2. Define integer polynomials

    L=1+16E0²(3c2−4),
    F0=1+64E0²(c2−1),
    Omega0=−64E0(c2−1),
    H0=C+F0(B−C+Omega0*y),
    GH0=−F0*H0,
    Jf=E0(c2*A²+4−8c2),
    W=B−C+Omega*y,
    Q=(2h²−2)E*H
       −A[Jf(C+(F+F0)W)+4c2*F0²*y].

An exact identity gives

    4c2*xi*A*Q = GH−GH0.

This is an identity, not the definition of Q: the displayed definition uses integer coefficients and no division. It remains valid at A=0, C=0 and xi=0. The formally written quotient has half-integer coefficients in A, but has integer coefficients in h=A/2. Treating it as an arbitrary integer polynomial in A would be incorrect.

Now put

    P=R0GH+LQ,
    J0=−4(c2−1)−256E0²(c2−1)²,
    J=J0(GH)²+c2*L*A*GH[A*GH0−4xi(4−6c2)Q]
       −(LQ)²−DF(H²−1).

Then a1=P²+J. A short derivation avoids trusting a symbolic expansion: write J_DF=c2*L*A²+J0 and R0=2A*c2*xi[A²*c2+4−6c2]. Expand J_DF(GH)²−2R0GH*LQ−(LQ)² and replace GH−4c2*xi*A*Q by GH0. The resulting expression is exactly the displayed J plus DF(H²−1). This proves center2 universally, including all exceptional values.

## 4. Exact degree and what limits this method

The fixed H1868 prefix has degA=16,384, degSigma=81,922, deg(a0)=294,382 and deg(a1)=458,818. The three final degrees are respectively

    72degA+140=1,179,788,
    68degA+140=1,114,252,
    4degSigma+deg(a0)+deg(a1)=1,080,888.

The third bound is reached by the cross-term −4Sigma²*a0*T². Its competing squared-inner term has lower degree. Thus further correction of this same radical cannot lower degree below this cross-term without also changing another part of the construction. These are exact degrees, not merely syntactic upper bounds: the checker propagates actual highest-degree coefficients modulo three primes and obtains nonzero coefficients at each claimed degree. The fixed coefficients used for those certificates are the actual included numeral payloads.

## 5. Checks and reproducibility

Run `python build.py polar`, `python build.py center0`, `python build.py center1`, `python build.py center2`, then `python check.py`. Repeat with `python -O check.py`. The checker imports neither builder nor circuit helper. It verifies the universal polynomial identities by exact coefficient cancellation; verifies integrality in halfA; replays each full source-to-output circuit against the independent original formula with m translated; checks actual fixed numerals, all graph edges, liveness and operation counts; and certifies exact degrees. Three hundred sixty signed modular inputs per candidate are transcription regression checks, not finite substitutes for the universal proof.

The preserved source/compiler/refutation calibration and the norm-saturation reliability/interpolation theorem remain the explicit mathematical dependencies in `BASELINE_PROOF.md`. No smaller Turing machine, historical priority, optimality, or new Lean/Rocq certificate is claimed.
