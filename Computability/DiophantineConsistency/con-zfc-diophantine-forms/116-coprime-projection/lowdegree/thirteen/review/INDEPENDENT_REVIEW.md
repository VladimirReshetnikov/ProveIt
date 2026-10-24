# Independent supplement: thirteen-integer triple-centered carrier

## Verdict and precise boundary

PASS as an ordinary two-way arithmetic reduction to the already-reviewed fifteen-integer equation. The sibling has thirteen unrestricted integer inputs, exact total degree 274, and 129 live binary operations: 76 multiplications, 31 additions, and 22 subtractions. The norm alone has exact degree 242; the guard has degree 16.

The fifteen- and fourteen-integer reviews remain separate and unchanged. This supplement establishes no new native/compiler calibration, end-to-end proof-assistant certificate, internal object-ZFC derivation, consistency proof, or global optimum. The same complete source34 coefficient tuple and inherited ordinary semantic theorem are retained.

## 1. The scalar norm and its algebra are exact

For the three centers and errors,

    A=2L+k, B=6(a+2)I, Croot=9(2Q-1)V,
    aa=4-k^2, bb=36(1-I^2), cc=81(4-4Q-V^2),

independent exact polynomial calculation verifies

    A^2+aa=4Dtau,
    B^2+bb=36Df,
    Croot^2+cc=324Da,
    Da=(Q-1)(QV^2-1).

The historical Horner evaluator has quartic coefficients p3,p2,p1,p0 forming the centered two-root norm for A,B. Its pair recurrence is multiplication by Z-Uw in the algebra w^2+2Croot*w-cc=0, followed by the scalar norm a4^2-2Croot*a4*b4-cc*b4^2. The current 129-gate evaluator computes the identical polynomial directly with the standard three-root octic formula. Both formulas are compared below; the lower gate count does not change the polynomial.

The independent checker fully expands the historical generic Horner expression into 568 terms in eight independent ports (Z,U,A,B,Croot,aa,bb,cc). It agrees coefficient-for-coefficient with the standard three-root octic norm evaluated at total center Z+U(A+B+Croot), with scaled radicands U^2(A^2+aa), U^2(B^2+bb), U^2(Croot^2+cc). Thus every denominator is genuinely cleared and every Horner sign is checked. The formal rank-two algebra is only a proof device; no hidden variable has entered the scalar equation.

## 2. Unit-product finalization and monicity close the early branches

The final equation is

    N+G^2+NG^2=0,

equivalently (1+N)(1+G^2)=1. Since 1+G^2 is a positive integer, it must equal one, giving G=N=0. There is no assumption that N is nonnegative away from its zeros.

The inherited affine restrictions prove U!=0 and gcd(H,2q^2)=1 on every integer assignment. At N=0 the rational total center Z/U+A+B+Croot is a root of the monic degree-eight integer norm polynomial. Therefore it is integral, and subtraction of the integer centers gives U|Z. The usual coprime CRT immediately yields

    v=q^2(2v0+1), v0 in Z, and H|Klo.

This excludes v=0 before radical extraction and recovers the full cubic scale. No positivity, square-class independence, nonzero signed radical sum, or prior integrality of any Pell root is needed for this step. The monic property is explicitly checked in the independent symbolic certificate.

## 3. The fixed weights really force individual square roots

Unconditionally modulo 3, q=2, W=1, X=2, a=0, and Delta=0. Since ell=XY^2 is either 0 or -1 modulo 3,

    Dtau=1, Df=1, Q=0, Da=1 modulo 3.

All three integer radicands are nonzero and prime to 3, even before the guard is used. The exact norm factorization supplies a rational signed sum of the weighted roots

    2sqrt(Dtau), 6sqrt(Df), 18sqrt(Da).

Here is a complete ordinary proof of the extraction, including coincident square classes. Write each nonzero radicand as d*s^2 with d a signed squarefree integer and s a positive integer. Both d and s are prime to 3. Group the roots by their rational squareclass d. Distinct squareclasses are linearly independent radical characters over Q in the corresponding multiquadratic extension, including the rational class d=1 and any negative classes. Thus every nonrational class would have to have total coefficient zero.

Within any class, however, the signed integer coefficients are drawn from 2s1,6s2,18s3. Their valuations at 3 are respectively 0,1,2. In every nonempty subset there is a unique smallest valuation; divide by that power of 3 and reduce modulo 3 to see that the sum cannot vanish. Therefore no nonrational class occurs. All three radicands are integer squares. This does not assume distinct squareclasses; the argument explicitly covers their coincidences.

Equivalently, noncancellation can be seen directly for the three positive roots once positivity is known. Two-term cancellations contradict Dtau,Df,Da=1 modulo 3. A three-term cancellation, after dividing by 2 and squaring, would force sqrt(Df*Da) rational and hence integral, and then force Dtau divisible by 9. The squareclass proof is stronger because it also disposes of negative radicands without presupposing their sign.

Choose tau,f,e with tau^2=Dtau, f^2=Df, e^2=Da. Positive tau and f can be selected; the later witness maps allow e either sign.

## 4. The auxiliary rational quotient is genuinely integral

After the scale and guard, c!=0 and Delta>=3. Hence Q=(Delta I)^2>=9 and delta=Q-1>0. From e^2=delta(QV^2-1), the rational number y0=e/delta satisfies

    QV^2-(Q-1)y0^2=1.

It would be invalid simply to assert delta|e from e being an integer square root. The following unbounded descent establishes the missing divisibility.

For any integer Q>1 and rational solution y with integer V to that adjacent-coefficient equation, write |y|=a/b in lowest terms. Then b^2 divides Q-1. If |V|=1, the equation immediately gives |y|=1. Otherwise take V>1,y>0 by signs and apply

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV.

The same norm equation is preserved. V' is integral because b divides Q-1; the denominator of y' in lowest terms is still b, because 2Q-1=1 modulo b and gcd(a,b)=1. The inequalities y>V and (Q-1)y<QV give -V<V'<V. V' cannot be zero by the norm equation. Taking absolute values and repeating strictly descends to |V|=1, forcing b=1. Thus y is integral.

This directly proves y0 in Z and therefore delta|e. It is independent of finite Pell samples or any preselected sign. The producer's alternate proof via least norm-one units and index folding is also valid, but the descent above shows that even the square-Q restriction is unnecessary for this integrality step.

## 5. Every zero has an integral map in both directions

Thirteen to fifteen: the CRT gives integers g=Klo/H and v0=(v-q^2)/(2q^2). Set

    f15=f,
    y15=y0-V,
    n15=tau-L-g-v0.

Retain all other shared coordinates. Then Z15/U=tau-L, making the first row zero; f15^2=Df makes the strong row zero; the centered auxiliary row is exactly the equation in Section 4; and the budget row is unchanged. This is an actual zero of the reviewed fifteen-integer polynomial. The main-root/bootstrap/compiler theorem is invoked only after that zero has been restored.

Fifteen to thirteen: from any fifteen-integer zero choose

    tau=|Z15/U+L|, f=|f15|,
    e=(Q-1)(V+y15).

The original centered auxiliary row proves e^2=Da. With the integral CRT offsets, choose

    n13=2tau+6f+18e-A-B-Croot-g-v0.

Then the total center is 2tau+6f+18e, one of the eight norm sums, so N=0. The unchanged private positivity witnesses give G=0, making the unit-product output zero. Signed e, signed I, and signed root centers cause no problem because all norm signs occur and n is unrestricted.

These maps work for every zero, not only canonical zeros. No new rank tuning, odd-period assumption, or unproved divisibility condition is introduced.

## 6. Exact degree: a complete finite upper-bound certificate

Give the eight generic norm ports weights

    Z:7, U:6, A:11, B:7, Croot:41, aa:10, bb:6, cc:38.

The complete 568-term generic norm expansion has weighted degree exactly 242. Its unique maximal-weight term is

    128 Z U^7 A^2 B Croot^4.

Every generic term and exponent is included in GENERIC_NORM_CERTIFICATE.json. This establishes the upper bound by exact finite polynomial arithmetic, without relying only on the producer's valid formal-Laurent-series argument. The actual front-end registers have exactly those degrees, as separately checked, with Z0=U0*n. Hence

    N242=128 U0^8 A0^2 B0 C0^4 n.

The guard G has degree 16 and nonzero leading part -4q0^2 eta0^2. Thus NG^2 is the unique degree-274 contribution to the finalizer. Taking h^6 from k0^6 and z^4 from R0^4 gives

    [j^124 w^41 v^47 h^6 z^4 r^17 c^34 n] P13
      =2^265 3^174 beta^124>0.

The exponent sum is 274, and beta is the authentic positive fixed integer. This proves attainment after all coefficients are fixed, not only for a generic coefficient ring. In particular the large cancellations in the literal Horner evaluator have not been mistaken for a syntactic degree estimate.

## 7. Independent reproducibility

The checker imports neither the producer builder nor its DAG library. It verifies 45 register cuts, exact liveness and declarations, the complete generic norm against a second formula, monicity, all three centered defects, the weighted degree certificate, actual leading coefficient, and the six authentic coefficient hashes. Where the baseline payloads are available it also compares complete bytes directly.

Twenty intentional live-operation mutations are rejected, including all direct-norm arguments, N, the auxiliary radicand/center, the guard and finalizer. Normal and optimized-Python receipts are supplied. Dependencies are Python 3 and SymPy; there is no runtime dependence on the full source repository. These checks certify finite algebra and accounting, not the inherited compiler theorem or Con(ZFC).
