# Height and counting of one canonical signed19 negative-restoration family

Research follow-on, 3 October 2026. This packet is separate from Report33 and does not alter it. All source files were read as inert text; no upstream code was executed and no repository file was edited.

## Scope and result

Fix the ordinary input x, an actual compiler export, the repunit choice, and **one** prime/scale choice in the audited signed19 construction. Count only its prescribed canonical auxiliary witnesses: c=psi_A(p), m=pc, Qaux=Delta psi_A(m), S=p+2m, and y=psi_Qaux(S). The main index runs through its final CRT progression; the first-Pell index must lie in the prescribed progression and satisfy the strict ratio. This is one explicit subfamily of negative-restoration witnesses. It is neither the entire signed19 polynomial fiber nor a classification of its other auxiliary choices. “Negative-restoration” means that the computed omitted index is R=-p<0; all nineteen supplied coordinates are positive. No machine-acceptance status is asserted.

Write

    lambda=A+sqrt(Delta), alpha=log(lambda),
    Dp=P^2-1, nu=P+sqrt(Dp), beta=log(nu),
    L=E/2, V=T Q H0, H0=4a+3,
    delta=log(1+1/Y), d_rot=delta/(L beta),
    kappa=delta/(2 alpha V L beta).

Here alpha is a growth logarithm, not the source's fixed supplied coordinate named alpha. Every constant above is fixed. The source establishes alpha/beta irrational. All logarithms in this packet are natural.

**Theorem.** A sufficiently late tail of the canonical family has the following properties.

1. For each CRT-progression value p, there is at most one positive n=n0 mod L satisfying Y<psi_A(p)/(2 psi_P(n))<Y+1. The proportion of progression values admitting it is d_rot.
2. The maximum of the nineteen supplied coordinates is exactly y. Heights strictly increase with p. With C=alpha/(2 Delta),

       log y=C p^2 exp(2 alpha p) (1+O(exp(-alpha p))),
       loglog y=2 alpha p+2 log p+log C+O(exp(-alpha p)).

   A sharper first exponentially small correction is given below.
3. If N(B) counts this tail up to supplied-coordinate height B, then

       N(B) ~ kappa loglog B.

   If B_j is its j-th height in increasing order, then

       loglog B_j ~ j/kappa.

   These are double-logarithmic statements, not multiplicative equivalents for the enormous heights themselves.
4. The continuous height cutoff p_B is

       p_B=alpha^(-1) W(sqrt(2 alpha Delta log B))
              +O(exp(-W(sqrt(2 alpha Delta log B))))
          =[loglog B-2 logloglog B+log(8 alpha Delta)]/(2 alpha)
              +O(logloglog B/loglog B),

   where W is the positive real Lambert W branch.
5. For some effectively computable eta>0 depending on the fixed parameters,

       N(B)=kappa loglog B+O((loglog B)^(1-eta)),
       loglog B_j=j/kappa+O(j^(1-eta)).

   No useful numerical or parameter-uniform exponent is asserted.
6. Using a standard effective linear-forms-in-logarithms theorem, the exact family count has an eventual **exact rotation-discrepancy representation**. In particular, a smooth claimed counting law

       N(B)=kappa loglog B-2 kappa logloglog B+O(1)

   is false. The discrepancy is unbounded by Kesten's theorem. A weaker two-term assertion with error o(logloglog B) would require the additional estimate D(R)=o(log R) for the explicit fixed rotation below; it does not follow from equidistribution or the standard effective algebraic-logarithm bound.

The asymptotic constants and onsets are not asserted uniform as the compiler, input, repunit, or prime/scale changes. Adding or deleting finitely many initial family members changes N by O(1) and none of these conclusions.

## 1. Exact first-Pell window, uniqueness, and density

Put c_p=psi_A(p) and g=log(sqrt(Dp)/(2 sqrt(Delta))). Because psi_P(n)=sinh(n beta)/sqrt(Dp), the strict ratio is **exactly**

    a_p < n beta < b_p,
    a_p=asinh(c_p sqrt(Dp)/(2(Y+1))),
    b_p=asinh(c_p sqrt(Dp)/(2Y)).

For positive z, asinh z has logarithmic derivative z/sqrt(1+z^2)<1. Integrating gives

    0 < b_p-a_p < log((Y+1)/Y)=delta<L beta.

Here delta<=log 2 while L>=1 and beta=arcosh P>log 2. Distinct allowable n differ by L, so there is at most one. For large p any possible n is positive and n=(alpha/beta)p+O(1).

For q=Y or Y+1 define

    epsilon_q(p)=asinh(c_p sqrt(Dp)/(2q))
                    -(alpha p+g-log q).

Binet's formula and asinh z=log(2z)+1/(4z^2)+O(z^(-4)) give, with fixed constants,

    epsilon_q(p)=(4 q^2 Delta/Dp-1) exp(-2 alpha p)
                    +O(exp(-4 alpha p)).

Thus the endpoints are the fixed-length logarithmic window shifted by vanishing, explicitly controlled terms. This is an endpoint estimate, not permission to replace a discontinuous counting test without further argument.

Write p=p_b+Vr, with any fixed sufficiently large CRT representative p_b, and set

    theta=V alpha/(L beta),
    xi=(alpha p_b+g-log Y-n0 beta)/(L beta),
    I=(0,d_rot) mod 1.

The limiting window contains a value n=n0+Lv exactly when {xi+r theta} belongs to I. Since theta is irrational, its visits to I have density d_rot. To transfer density to the exact windows without any Diophantine theorem, fix epsilon>0: all sufficiently late discrepancies lie in epsilon-neighborhoods of the two endpoints. Equidistribution bounds their upper density by 4 epsilon. Let epsilon tend to zero. This proves the stated density and, together with the height asymptotic, the leading counting law independently of the strengthening in Section 4.

## 2. Supplied height and its asymptotic

For real p>=1 extend the definitions by their hyperbolic formulas:

    c=sinh(alpha p)/sqrt(Delta), m=pc,
    q=Qaux=sqrt(Delta) sinh(alpha m), S=p+2m,
    b_aux=arcosh(q), y=sinh(S b_aux)/sqrt(q^2-1).

Along the canonical integer family these equal the original Pell expressions. With ell=(1/2)log Delta,

    b_aux=alpha m+ell+O(exp(-2 alpha m)),
    log y=(2m+p-1)(alpha m+ell)
                +O((m+p) exp(-2 alpha m)).                 (1)

Indeed arcosh q=log(2q)+O(q^(-2)); both log(2q) and log(2 sqrt(q^2-1)) equal alpha m+ell+O(exp(-2 alpha m)); the remaining log(1-exp(-2 S b_aux)) is smaller. Substituting

    m=p exp(alpha p)(1-exp(-2 alpha p))/(2 sqrt(Delta))

in (1) proves, more precisely,

    loglog y=2 alpha p+2 log p+log(alpha/(2 Delta))
      +sqrt(Delta)[1+(log Delta/alpha-1)/p] exp(-alpha p)
      +O(exp(-2 alpha p)).                                (2)

In particular the proposed leading coefficient alpha/(2 Delta) is correct.

To identify the height, the auxiliary norm gives

    U^2=(1-q^(-2)) y^2+q^(-2),

hence U<y when y>1. Consequently j=(U-p)/c<y. Also f=chi_A(m)<q<y eventually, i=q/c^2<y, and o=(U+c)/f<y once c<y and f>=2. The strict main-Pell ratio gives k=O(c), tau=O(c), eta,zeta=O(c), and h=O(c+p); sigma=O(c+p), while Z and rho are affine in p. The remaining supplied coordinates are fixed. Since c=O(exp(alpha p)), equation (1) makes all of these strictly smaller than y eventually. This enumerates all nineteen source coordinates: J,F,alpha,z,f,h,i,j,o,s,w,tau,eta,zeta,y,Z,delta,rho,sigma.

The real function y(p) is strictly increasing for p>=1. The functions m(p), q(p), and S(p) are increasing; writing q=cosh b, sinh(Sb)/sinh b increases in S>1 and b>0. For the latter assertion, its logarithmic derivative in b is S coth(Sb)-coth b>0 because z coth z is increasing for z>0. Thus the family has no height ties.

## 3. Precise height inversion; what it does not prove about counts

Let t_B=alpha^(-1) W(sqrt(2 alpha Delta log B)). It solves

    2 alpha t_B+2 log t_B+log(alpha/(2 Delta))=loglog B.

Equation (2), the positive derivative 2 alpha+2/p, and monotonicity give

    p_B=t_B
      -sqrt(Delta)[1+(log Delta/alpha-1)/t_B] exp(-alpha t_B)
           /(2 alpha+2/t_B)
      +O(exp(-2 alpha t_B)).                              (3)

For example, bracket p_B first within O(exp(-alpha t_B)) of t_B using (2), then Taylor-expand the smooth displayed terms; the uniform residual is O(exp(-2 alpha t_B)). In particular p_B<t_B eventually. Expanding W at infinity gives the formula in the theorem. Replacing p_B by t_B in a progression cutoff can change the count by at most one once |p_B-t_B|<V; it cannot be declared exact at every jump.

Put t=loglog B. A formal continuous count d_rot p_B/V would have the expansion kappa t-2 kappa log t+O(1). Actual selected indices are rotation visits, so this is not yet a two-term counting theorem. Section 4 gives the missing term exactly.

The density proved in Section 1 gives N(B)~d_rot p_B/V~kappa loglog B. If p_j is the j-th selected main index, then p_j~V j/d_rot. Applying (2) gives loglog B_j~j/kappa. This uses strict monotonicity and does not substitute an asymptotic height into a floor.

## 4. Exact discrepancy reduction and the obstruction to a bounded remainder

This section uses standard external results specified in the reference note: effective lower bounds for nonzero linear forms in logarithms of fixed algebraic numbers, and Kesten's interval bounded-remainder criterion.

For an integer n within bounded distance of alpha p/beta and q=Y,Y+1, the relevant boundary form is

    Lambda_q(p,n)=p log lambda-n log nu
                   +log(sqrt(Dp)/(2q sqrt(Delta))).

It is nonzero. If it vanished, squaring the corresponding positive exponential equality would give lambda^(2p) equal to a rational multiple of nu^(2n). Their distinct quadratic fields intersect in Q, so lambda^(2p) would be rational; its norm-one property forces it to be 1, impossible for p>0. (Equivalently, conjugating only sqrt(Delta) makes one side negative.)

The effective logarithmic-form theorem supplies constants c0,C0>0, depending only on the fixed data, such that

    |Lambda_q(p,n)| >= c0 p^(-C0)

for all relevant large p. This dominates the O(exp(-2 alpha p)) endpoint shifts. Therefore, after increasing p_b if necessary, the exact strict-ratio selection agrees **for every r>=0** with the fixed rotation test {xi+r theta} in I. This is stronger than and logically separate from the equidistribution-only density argument.

Define

    D(R)=sum_{r=0}^{R-1} 1_I({xi+r theta})-d_rot R,
    R(B)=max(0, 1+floor((p_B-p_b)/V)).

Then for the chosen tail the exact identity is

    N(B)=d_rot R(B)+D(R(B)).                               (4)

No phase has been smoothed and no approximate real cutoff has been passed through a floor. In particular

    N(B)=kappa t-2 kappa log t+D(R(B))+O(1),
    R(B)~t/(2 alpha V),  t=loglog B.                       (5)

Thus D(R)=o(log R) would suffice for the genuine two-term law with remainder o(logloglog B). An O(log R) bound alone would not identify its second coefficient. Equidistribution supplies only D(R)=o(R).

The interval length d_rot is not in Z+theta Z. Otherwise for integers a,b,

    delta=a L beta+b V alpha,
    (Y+1)/Y=nu^(aL) lambda^(bV).

Both lambda and nu are algebraic units: their monic polynomials have constant term 1, and their inverses are algebraic integers. The right side is therefore an algebraic unit. A rational algebraic unit is +1 or -1, contradicting (Y+1)/Y>1. Kesten's theorem now says D(R) is unbounded. Open versus half-open endpoints changes at most finitely many terms, since an irrational orbit can hit each endpoint at most once.

As B ranges over large real cutoffs, R(B) takes every sufficiently large integer value. Equation (5) therefore proves that the proposed smooth two-term count with O(1) remainder is impossible. This does **not** prove that D(R) fails to be o(log R); the latter is a strictly finer question and is left open here.

### Optional effective error and ranked inversion

The same logarithmic-form theorem, now for the two fixed units lambda and nu, gives effectively computable c>0 and mu>=1 such that

    ||h theta|| >= c h^(-mu)  (h>=1).

Indeed, a nearest integer k to h theta gives the nonzero form h V alpha-k L beta with integer coefficients O(h). The geometric-series bound is

    |sum_{r<R} exp(2 pi i h(xi+r theta))|
        <=min(R,1/(2||h theta||)) << h^mu.

The Erdős–Turán inequality therefore gives

    |D(R)| << R/K+sum_{h<=K} h^(mu-1) << R/K+K^mu.

Taking K of order R^(1/(mu+1)) yields D(R)=O(R^(1-eta)), eta=1/(mu+1)>0. With mu>=1, the logarithmic analytic cutoff term is absorbed by this error, proving assertion 5. Its ranked inversion is elementary: j=N(B_j), the leading law first gives loglog B_j asymptotic to j/kappa, and substitution into the error bound gives loglog B_j=j/kappa+O(j^(1-eta)). This effective error is still much larger than logloglog B and supplies no second counting coefficient.

### External theorem statements and primary/research references

- **Logarithmic forms.** For fixed positive algebraic numbers zeta_1,...,zeta_s, there is an effectively computable C>0 such that every nonzero real form sum b_i log zeta_i, with integer coefficients and B=max(3,|b_1|,...,|b_s|), has absolute value at least B^(-C). This fixed-number corollary suffices here. Primary result: A. Baker and G. Wüstholz, *Logarithmic forms and group varieties*, J. reine angew. Math. 442 (1993), 19–62, [DOI 10.1515/crll.1993.442.19](https://doi.org/10.1515/crll.1993.442.19). The explicit bound used is also stated in Y. Bugeaud, [*B′*, Theorem 1.1, equation (1.2)](https://arxiv.org/pdf/2209.00275), pp. 2–3. Constants are allowed to depend on all fixed algebraic numbers and the common number field.
- **Bounded-remainder interval criterion.** For an irrational theta and a circle interval I, the discrepancy sum_{r<R}1_I({xi+r theta})-|I|R is bounded in R iff |I| belongs to Z+theta Z. A primary new proof with the precise fixed-orbit statement is M. Kelly and L. Sadun, [*Pattern equivariant cohomology and theorems of Kesten and Oren*, Theorem 1](https://arxiv.org/pdf/1404.0455). Original: H. Kesten, [*On a conjecture of Erdös and Szüsz related to uniform distribution mod 1*](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/12/2/96036/on-a-conjecture-of-erdos-and-szusz-related-to-uniform-distribution-mod-1), Acta Arithmetica 12 (1966), 193–212, DOI 10.4064/aa-12-2-193-212. Arbitrary phase xi is covered by translating the interval; changing endpoint conventions affects only finitely many hits.
- **Discrepancy inequality.** The unnormalized Erdős–Turán bound is the displayed R/K plus weighted exponential-sum bound above, with an absolute implied constant. P. Erdős and P. Turán, *On a problem in the theory of uniform distribution*, [Part I](https://www.renyi.hu/~p_erdos/1948-02.pdf), Proc. Kon. Ned. Akad. Wetensch. 51 (1948), 1146–1154, and [Part II](https://www.renyi.hu/~p_erdos/1948-03.pdf), 1262–1269. A further primary statement is Erdős–Koksma, [*On the uniform distribution modulo 1 of sequences (f(n,theta))*](https://users.renyi.hu/~p_erdos/1949-11.pdf), Lemma 2, printed p. 300.

## 5. Comparison with Report25 and evidence boundaries

Report25 counts an **entire** fixed native fiber after proving that seventeen coordinates are forced and parametrizing all remaining witnesses by two Pell indices. Its logarithmic-height law comes from exact finite floor counts, exceptional baseline terms, hyperbola decomposition, and Euler summation. Its unsmoothed square-root second term is established by those uniform two-index estimates.

The present result fixes a prescribed auxiliary choice and follows a **single** CRT main-index progression selected by an irrational-rotation window. It neither reproduces Report25's whole-fiber classification nor transfers its floor-sum error estimate. Both analyses use elementary Pell/Binet growth and careful inversion; these are shared standard tools, not a claim of a generic new method. The substantive additional issue here is the exact rotation-discrepancy term and the algebraic-logarithm control needed to preserve it through the strict ratio's shrinking endpoint perturbations.

No numerical complete child witness is materialized, no uniform bound over varying scales is supplied, and no full article or publishable-novelty claim is made.

## Source binding

The construction and independent audit were read in their frozen forms:

- FULL-SIGNED-COUNTEREXAMPLE.md: SHA256 b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd
- independent/INDEPENDENT-AUDIT.md: SHA256 cd62529a6efcdfcbab43f1426c6b3fe5930575fda2cc865f12c40a5ec6c3bda6
- Report25 report25.tex: SHA256 8c726653a01afc017b1bec52437f01824e07d82742713a094043c284c30b77b7

The first two are in the accompanying construction evidence. Report25 is in the Report 25 context source. The separate independent check notes in this packet are not substitutes for the proofs above.
