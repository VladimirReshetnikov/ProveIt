# Independent algebra review of the Report58 boundary certificate

4 October 2026. This review checks the arithmetic certificate described below directly from its equations, conditional on the previously audited geometric validity criterion. No prior executable, physical simulator, or stored collision schedule was executed. The POWER modules are not supplied in this review; all conclusions involving them assume that each module represents exactly its stated nonnegative integer power, including exponent zero.

## Verdict

**PASS for the proposed reduction, bounded modular extraction, and final acceptance condition.** No algebraic flaw was found. The version with positive integers s,t satisfying s+t=5 is equivalent to the quartic residue-selector version. A complete ordinary-integer polynomial certificate still requires separately supplied and proved exact POWER modules and the routine conversion of signed integers and positivity to natural-number polynomial equations.

## 1. Input geometry and exact eta numerator

Let positive integer gaps give D=g1+g2+g3, x=g1, y=g1+g2, and let A=3x−D, B=3y−2D. Define

    delta = 4D²−205(A²+B²),
    U = 6A−13B,
    V = 13A+6B.

The centered coordinates are X=A/3 and Y=B/3. For the audited contact point p=(4/205,−26/615)=(2/615)(6−13i), direct complex division gives

    eta = ((X+iY)/D)/p = (U+iV)/(2D).

The sign is important: V=13A+6B, rather than its negative. Also U²+V²=205(A²+B²), so delta≥0 is precisely the closed critical disk condition. On delta=0, eta has modulus one.

The audited criterion is: accept delta>0; reject delta<0; on delta=0, accept unless eta=((3−4i)/5)^m for some integer m≥0.

## 2. Reduction to the unique common positive denominator

Impose positive integers h,q and signed integers u,v,a,b0,c satisfying

    U=hu, V=hv, 2D=hq, au+b0v+cq=1.

The last equation is equivalent to gcd(u,v,q)=1. These equations make h=gcd(U,V,2D), with the gcd taken positive, and q=2D/h. In particular q is the least common positive denominator of the real and imaginary parts of eta=u/q+i v/q.

For completeness of the denominator claim: if an integer d has both du/q and dv/q integral, then q divides du and dv. Multiplying the Bezout equation by d shows q divides d. Thus no smaller common denominator is possible. Conversely the usual positive gcd supplies h,u,v and Bezout coefficients.

Zero components cause no exception. If U=V=0, then u=v=0, the Bezout equation forces q=1, and h=2D works. This is an interior input, with delta=4D²>0. If just one component vanishes, the same gcd and denominator proof applies without change.

## 3. Unique extraction of the denominator's 5-adic exponent

Impose nonnegative integers n,k, positive integers P,r,s,t, and

    P=5^n, q=Pr, r=5k+s, s+t=5.

Positivity of s and t forces s in {1,2,3,4}; thus r is positive and not divisible by 5. Conversely every positive integer r not divisible by 5 has exactly such a remainder s and nonnegative quotient k, with positive t=5−s. Therefore these equations force n=v5(q), P=5^n, and r=q/5^n. In particular q is a power of 5 exactly when r=1.

The alternative selector product(s−1)(s−2)(s−3)(s−4)=0 with positive s and nonnegative k is equivalent. Positivity of both s and t in the linear version is essential: permitting zero would also allow residue 0 or 5.

## 4. Bounded modular extraction of the complex power

Set b=4P+1 and T=(3+4b)^n. Require signed integers C,S,kappa with

    −P≤C≤P, −P≤S≤P,
    T−C−bS=kappa(b²+1).

Write C_n+iS_n=(3+4i)^n. Its modulus is 5^n=P, so |C_n|,|S_n|≤P. Evaluation at i↦b is valid modulo b²+1, hence

    T ≡ C_n+bS_n (mod b²+1).

Thus the true pair supplies a witness kappa. Conversely, put a=C−C_n and d=S−S_n. Then b²+1 divides a+bd, while

    |a+bd| ≤ 2P(1+b) = 8P²+4P < b²+1 = 16P²+8P+2.

Consequently a+bd=0. As |a|≤2P<b, this implies d=0 and then a=0. Therefore the bounded congruence uniquely forces the desired C and S. No size bound on the signed quotient kappa is needed.

This proof includes n=0: P=1, b=5, T=1, C=1 and S=0 are the unique bounded solution. Thus the zero exponent is covered provided both POWER modules themselves include it.

## 5. Denominator of the inverse power and orientation

For m≥1, the coefficients of (3−4i)^m are congruent to (3,1) modulo 5. Indeed 3−4i≡3+i and (3+i)²≡3+i in (Z/5Z)[i]/(i²+1). Neither coefficient is divisible by 5. Since the only prime dividing the denominator 5^m is 5, the least common denominator of ((3−4i)/5)^m is exactly 5^m. For m=0 the pair is (1,0), with denominator 1.

Therefore, if eta is a forbidden inverse power, the reduced denominator forces m=n and r=1. Its reduced numerator is then (u,v)=(C,−S), where C+iS=(3+4i)^n. Conversely r=1 and this numerator equality directly imply eta=((3−4i)/5)^n.

The test must use v+S, not v−S. For example eta=(3+4i)/5 has reduced pair (3,4), denominator 5, n=1 and (C,S)=(3,4), so v+S=8 and it is accepted. Its inverse has reduced pair (3,−4) and is rejected. Eta=1 has q=P=r=1 and n=0; it is rejected on the boundary. The other integer unit-circle points are accepted.

## 6. Exact final iff

Require delta to be a nonnegative integer and require

    delta²+(r−1)²+(u−C)²+(v+S)² > 0.

Every delta>0 input has all auxiliary witnesses and makes the strict inequality automatic. Negative delta has no witness for the nonnegative delta variable. When delta=0, the sum is zero exactly if r=1 and (u,v)=(C,−S), which Section 5 proves is exactly the forbidden inverse-power orbit. Otherwise it is positive. Hence the complete existential condition is equivalent to the audited validity predicate on positive integer gaps.

The strict inequality is an ordinary polynomial constraint after introducing a nonnegative j and writing the sum=j+1. Positive integer variables can be encoded as one plus a natural variable; every signed integer can be represented as the difference of two naturals. Bounds such as −P≤C≤P can be written C+P=l and P−C=m with l,m nonnegative. These encodings introduce witness nonuniqueness but do not affect the predicate. They require no appeal to real quantifier elimination or an orbit-search algorithm.

## Sources inspected as inert text

- /workspace/shared/signal-dimension-boundary57-20261004/BOUNDARY_AND_ARITHMETIC.md
- /workspace/shared/five-signal-obstruction-independent-audit-20261004/INDEPENDENT_AUDIT.md

The independent audit supports the geometry and rational boundary test used here. This arithmetic review neither repeats nor extends the physical construction audit, and does not establish a literature-priority claim.
