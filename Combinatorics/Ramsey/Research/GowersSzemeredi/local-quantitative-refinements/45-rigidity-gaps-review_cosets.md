# Internal AI cross-check: coset and collision rigidity

Date: 7 October 2026 UTC.

This report records an internal AI mathematical cross-check of the coset, punctured-coset, and coordinate-collision arguments. It is not external peer review or proof-assistant verification. The argument was first checked against the manuscript's proof notes; the corresponding final theorem statements and hypotheses in `sections/cosets.tex` were also inspected. The scope does not include a worldwide literature-priority determination.

## Verdict

The subgroup construction, exact complement algebra, numerical constants in the defect range \(\varepsilon<1/9\), punctured-coset stability, and the \(\mathcal Q=E\) coordinate-cylinder classification are mathematically consistent. No mathematical error was found in these arguments. The conclusions require a finite nonempty set \(A\) and an abelian ambient group, with finite subgroup cosets used for distance minimization.

## Checks that matter

1. **Pointwise autocorrelation gap.** Let \(m=|A|\), \(r(d)=|A\cap(A+d)|\), \(q(d)=r(d)/m\), and \(\varepsilon=(m^3-E(A))/m^3\). For \(I=\{x\in A:x+d\in A\}\), the overlap inequality applied to \(x-b\) and \(x+d-b\) gives

   \[
   m-r(d)\le m-r(x-b)+m-r(x+d-b).
   \]

   Each restricted sum over \(I\times A\) on the right is at most \(m^3-E(A)\). The left sums to \(mr(d)(m-r(d))\). Division by \(m^3\) gives exactly \(q(d)(1-q(d))\le2\varepsilon\). The factor two is correctly retained.

2. **Canonical subgroup.** For \(a=(1-\sqrt{1-8\varepsilon})/2\), the strict hypothesis implies \(a<1/3\), and the autocorrelation dichotomy is \(q\le a\) or \(q\ge1-a\). If \(d,e\in H=\{d:r(d)>m/2\}\), then \(q(d-e)\ge1-2a>a\), so \(d-e\in H\). The set \(H\) is finite because it is contained in \(A-A\). The proof therefore applies even in an infinite abelian ambient group.

3. **Coset occupancy.** With occupancies \(n_j\), put \(S=\sum_jn_j^2=\sum_{d\in H}r(d)\). The energy estimate \(E(A)\le mS+am(m^2-S)\) gives \(S/m^2\ge1-a/2\). The largest coset contains at least \((1-a/2)m>5m/6\) points of \(A\). If \(t\) points lie outside that coset and \(x=t/m\), then \(x\le a/2\). Combining \(|H|(1-a)m\le S\) with \(S\le m^2[(1-x)^2+x^2]\) gives the claimed preliminary distance \(\delta<1/2\). There is no uncontrolled ambient-size factor.

4. **Outlier quadruples.** An additive quadruple cannot have exactly one entry outside a fixed subgroup coset: after translation, the other three entries are in the subgroup and determine the fourth there. With \(b\) inside points and \(t\) outside points, the bounds \(6bt^2\), \(4t^3\), and \(t^3\) for exactly two, three, and four outlier entries correctly count positions and leave one determined value. These bounds need not be equality-sharp to support the resulting theorem.

5. **Exact complement algebra.** Let \(K=C\setminus A\), \(u=|K|\), and \(A_0=A\cap C\), with \(|A_0|=b\). The identity

   \[
   E(A_0)=b^3-bu(b-u)-(u^3-E(K))
   \]

   is correct. Independent symbolic expansion of the normalized inequality gives exactly

   \[
   \varepsilon\ge\delta(1-\delta)
   +x[2+\delta^2-(8+\delta)x+2x^2]
   +\frac{u^3-E(K)}{m^3}.
   \]

   The coefficient is \(2x^2\). The earlier source 14 uses a different triple-counting estimate with a different polynomial; the two formulas should not be interchanged.

6. **Positive remainder and the sharp envelope.** Because \(\delta\ge x\) and \(x<1/6\), the bracket \(F(\delta,x)\) is at least \(F(x,x)=2-8x+2x^2>13/18\). Together with \(\delta<1/2\), this permits inversion of \(\delta(1-\delta)\le\varepsilon\) onto the smaller root \(\tau(\varepsilon)\). Uniqueness uses

   \[
   \tau(1/9)=\frac{3-\sqrt5}{6}\approx0.127322<\frac15.
   \]

   Two cosets satisfying the bound would have an intersection larger than half of each. Their subgroup indices then force the cosets to coincide. This establishes unique global minimization among all finite subgroup cosets.

7. **All equality cases.** The sharpened remainder coefficient is \(c(\delta)=2-8\delta+2\delta^2\). In the permitted range it exceeds

   \[
   c(\tau(1/9))=\sqrt5-\frac{11}{9}>1.
   \]

   Thus \(\eta=\varepsilon-\delta(1-\delta)=0\) forces \(t=0\) and \(E(K)=u^3\). If \(u=0\), the set is the whole coset. Otherwise maximal energy makes \(K\) a subgroup coset. For index \(r\), the formulas are \(\delta=1/(r-1)\) and \(\varepsilon=(r-2)/(r-1)^2\); the range is exactly \(r\ge9\). In a prime cyclic group, the positive-defect examples in this range begin at \(p=11\). The converse uses uniqueness correctly to exclude a closer alternative coset.

8. **Punctured-coset stability.** The hypothesis \(\eta\le\delta^3/16\) implies \(u/m\ge15\delta/16>0\) and

   \[
   \zeta=1-E(K)/u^3\le256/3375<1/9.
   \]

   Applying the same envelope theorem to \(K\) inside the finite group underlying \(C\) is legitimate. The resulting repair coset \(D\) satisfies

   \[
   \frac{|A\triangle(C\setminus D)|}{m}
   \le\left(\delta^2+\frac{1024}{675}\right)\frac{\eta}{\delta^2}
   <\frac{2\eta}{\delta^2}.
   \]

   The proof includes \(\eta=0\). Properness is explicit: \(|D|<(5/4)u<m/4\), whereas \(|C|>4m/5\). To identify \(D\) as the closest coset in the entire original ambient group, apply the uniqueness part of the envelope theorem there as well. The coset already found inside \(C\) satisfies its bound, so it is also the global closest coset. The final manuscript includes this clarification.

9. **Coordinate splitting.** The homomorphism \(F_i(y,w)=y+e_i(w-y)\) has image exactly \(H+e_iH\): it contains \(H\) by taking \(y=w\), and contains \(e_iH\) by taking \(y=0\). If \(e_iH\) is not contained in \(H\), each fiber has size at most \(|H|/2\). The derived corner estimate

   \[
   C_i(A)/m^2\le\frac12+\frac\delta2+x-x^2<\frac45
   \]

   contradicts \(\mathcal Q(A)/m^3>8/9\). The proof holds for every finite number of coordinates, including one, and arbitrary abelian coordinate groups.

10. **One-coordinate puncture at collision equality.** If \(\delta=\tau(\varepsilon_{\rm cube})\), monotonicity of \(\tau\) and \(\mathcal Q\le E\) force \(\mathcal Q=E\) and equality for energy. Write \(A=C\setminus K\). Since \(|C|<2m\), any pair \(x,w\in A\) with a failed mixed corner admits \(z\in A\) such that \(z+w-x\in A\), by intersection of two translates of \(A\) inside \(C\). This produces an energy triple omitted by the cube-collision injection, a contradiction. Therefore \(A\) is a coordinate product. If its complement is a subgroup coset and at least two coordinate factors are proper, choosing a missing value in another coordinate shows that the complement's subgroup contains every coordinate subgroup. It would then equal the whole group, which is impossible. Exactly one punctured coordinate remains. The converse follows from product factorization and \(\mathcal Q=E\) in one dimension.

## Exposition and scope checks

- The actual energy defect must be distinguished from a supplied upper bound on it, particularly when formulating equality for collision counts. Both versions follow, but an equality classification uses the actual defect. The final statements make that distinction.
- Cosets in distance minimization are finite when the ambient group is infinite. An infinite coset has infinite symmetric difference from finite \(A\) and cannot improve the distance.
- Source 14 already proves the same function \(\tau\) for \(\varepsilon\le1/100\), and its adjoining write note includes missing-subcoset examples. The enlarged range, exhaustive equality classification, structural remainder, and collision-cylinder consequences are the additions checked here.
- A factor-one pointwise inequality \(q(1-q)\le\varepsilon\) is not proved by the argument. It may be asked as a research question, but it must not enter the certified theorem range.

## Limitations

This review checks the algebra and logical dependencies of the stated mathematical arguments. The earlier source 14 theorem was consulted to verify its smaller \(1/100\) range and its different initial coarse-coset construction. This comparison does not establish novelty in the wider literature. The internal AI review is supplementary evidence and is not a substitute for independent human peer review or formal verification.
