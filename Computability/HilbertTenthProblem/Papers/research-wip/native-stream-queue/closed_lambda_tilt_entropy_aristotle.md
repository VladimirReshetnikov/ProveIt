# An entropy bound closes the diverging-alpha ratio frontier

Conditional only on the article's stated single-spine convolution and uniform upper estimate, the proposed sharpening is valid: for every sequence of integer pairs u>=1,b>=0 with

    u -> infinity, alpha=b/u -> infinity, log(b+1)=o(u),

one has

    log R(b,u)/u -> 1/2.                                  (1)

The new step is root's proposal to retain the exact logarithmic tilt loss before bounding it by a binomial coefficient. This removes the additional condition alpha-(1/2)log log u -> infinity in the newly written Proposition18.2. It does not settle the general bounded-alpha regime, determine a second-order term, or reprove the article's global count/localization theorems.

All logarithms are natural. The immutable source is commit24e36bc20f95ce4d8771c0c6bdc3d6d251a0725a, article.tex in SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a135501-closed-lambda-terms. The new proposition is at1361–1416; the frontier it leaves open is at1478. No manuscript bytes were changed.

## 1. Source interface and a finite strengthened inequality

Let C_b be the Catalan number, A(b,u) the common fixed-(b,u) count, and

    R(b,u)=A(b,u)/(C_b*u^(b+1)),
    rho=1/(4u),
    Q_u(x)=product_(m=0)^(u-1) (1-4m*x)^(-1/2),
    H_u=sum_(k=1)^u 1/k,   mu=(u/2)(H_u-1).

The article's exact single-spine subclass and Catalan convolution give, for every0<theta<=1,

    R(b,u) >= Q_u(theta*rho) Pr(J_theta<=b),              (2)

where J_theta has probability generating function

    product_(m=0)^(u-1) ((1-theta*m/u)/(1-theta*m*z/u))^(1/2).

Indeed the coefficient q_j=[x^j]Q_u is nonnegative, the convolution gives R>=sum_(j<=b)q_j*rho^j, and rho^j>=(theta*rho)^j. This is a finite coefficient inequality, not an asymptotic interchange. Its original source is494–529, with the tilted version at1373–1378.

**Finite theorem.** Let K>=0 be real and kappa>=1 be an integer such that H_kappa>=2K+3. For integers u>=4kappa and b>=0 satisfying b>=mu-Ku,

    log R(b,u) >= u/2 - c(u) - (1/2)log binom(u+kappa,kappa)
               >= u/2 - c(u)
                  - (kappa/2)log(e*(u+kappa)/kappa),      (3)

where c(u)=1/2+(1/4)log u+log2. The condition u>=4kappa is explicit; the source's separate trivial R>=1 argument remains available when it fails. No assertion that(3) applies to that omitted small-u range is needed.

## 2. Mean and probability cost, with all finite hypotheses

Take theta=1-kappa/u in[3/4,1). Differentiation of the displayed generating factors gives the mean and variance of a shape1/2 negative-binomial variable as p/(2(1-p)) and p/(2(1-p)^2). Both increase in p. Therefore

    Var(J_theta) <= Var(J_1)
      = (1/2)sum_(k=1)^(u-1) u*(u-k)/k^2 <= u^2.         (4)

The last inequality follows from sum_(k>=1)k^(-2)<2; it can be obtained by the elementary integral bound. There is no singular endpoint because the largest parameter is theta*(u-1)/u<1.

Writing k=u-m, the exact mean reduction is

    mu-E J_theta
      = (1/2)sum_(k=1)^u kappa*(u-k)
          /[k*(k+kappa*(u-k)/u)]
      >= (u/2)sum_(k=1)^u (1/k-1/(k+kappa))
          -(1/2)sum_(k=1)^u kappa/(k+kappa).              (5)

To check the direction, replace k+kappa*(u-k)/u by the larger k+kappa in each nonnegative summand and split the resulting numerator. The first sum is H_kappa-(H_(u+kappa)-H_u)>=H_kappa-kappa/(u+1). The second is at most kappa*log(1+u/kappa), by integrating the decreasing function kappa/(kappa+x) on[0,u].

For x=kappa/u<=1/4, the function x*log(1+1/x) increases, since its derivative is log(1+1/x)-1/(1+x)>0. Hence

    kappa/(u+1)+(kappa/u)log(1+u/kappa)
       <= 1/4+(1/4)log5 < 1.

Thus(5) gives mu-E J_theta >= (u/2)(H_kappa-1). Combining the two finite hypotheses on b and H_kappa gives b-E J_theta>=u. Cantelli and(4) then imply Pr(J_theta>b)<=1/2, so

    Pr(J_theta<=b)>=1/2.                                (6)

This restates and independently checks precisely the finite mean/Cantelli argument of1386–1395. The real value of K and integer threshold b cause no endpoint problem: {J_theta>b} is contained in {J_theta-E J_theta>=u}.

## 3. The entropy loss

At rho the product is Q_u(rho)=sqrt(u^u/u!). The actual logarithmic tilt loss is

    L(u,kappa) = log Q_u(rho)-log Q_u(theta*rho)
      = (1/2)sum_(k=1)^u log(1+kappa*(u-k)/(u*k)).        (7)

Instead of linearizing log(1+x)<=x term by term, use(u-k)/u<=1:

    0 <= L(u,kappa)
       <= (1/2)sum_(k=1)^u log(1+kappa/k)
       = (1/2)log((u+kappa)!/(u!*kappa!))
       = (1/2)log binom(u+kappa,kappa).                  (8)

The equality uses the integrality of kappa; there is no approximation of a factorial or hidden uniformity assumption. Also binom(N,kappa)<=N^kappa/kappa! and

    log(kappa!) >= integral_1^kappa log x dx
                  = kappa*log kappa-kappa+1,

so binom(N,kappa)<=(e*N/kappa)^kappa for every integer kappa>=1. Taking N=u+kappa proves the second line of(3).

For completeness, concavity of log on each[j-1,j], j>=2, gives

    log(u!) <= u*log u-u+1+(1/2)log u,

also at u=1. Thus log Q_u(rho)>=(u/2)-1/2-(1/4)log u. Insert this, (6) and(8) into(2) to prove(3). Only the replacement of the source's loss estimate by(8) is new; the probabilistic construction and its finite constants remain those of Proposition18.2.

## 4. Every diverging-alpha sequence

For each pair define

    K=max(0,(H_u-1)/2-alpha),
    kappa=min{n>=1: H_n>=2K+3}.

The harmonic estimate H_n>=log(n+1) gives a short elementary bound: take n=ceil(exp(2K+3))-1>=1. Then H_n>=2K+3 and n<exp(2K+3). Consequently

    kappa <= e^(2K+3)
           <= e^3*max(1,u*e^(-2alpha)),
    delta=kappa/u <= e^3*max(1/u,e^(-2alpha)).            (9)

Here H_u<=1+log u is the only estimate used in the second inequality. Under u->infinity and alpha->infinity, delta->0, so u>=4kappa eventually and all the finite hypotheses of(3) hold. This verifies the regime condition before using the sharpened bound.

Dividing(3) by u gives

    log R(b,u)/u >= 1/2-c(u)/u
        -(delta/2)log(e*(1+delta)/delta).                (10)

The last expression tends to1/2: delta*log(1/delta)->0 and delta*log(1+delta)->0. This proves the lower half of(1), with no requirement on log(b+1) for that half.

For the upper half, the source's uniform estimate and Catalan bound give

    log R(b,u)/u <= 1/2
      +3*2^(1/3)*(1+alpha)^(1/3)*e^(-alpha/3)
      +log(2u(u+1)(2b+1)(b+1))/u.                       (11)

The exponential term tends to0 when alpha->infinity. The last term tends to0 when u->infinity and log(b+1)=o(u). Equations(10)–(11) prove(1) for every such sequence, with no saddle-admissibility or size-convention restriction on the pair(b,u).

The extension is strict. For example let b=floor(u*sqrt(log log u)) for sufficiently large integer u. Then alpha->infinity and log(b+1)=o(u), but alpha-(1/2)log log u->minus infinity. The former sufficient hypothesis fails while(1) applies. This is an analytic example, not a computed data claim.

## 5. Retained boundaries and exact scope

**Review remark 1 (the previous linear loss is valid, not an identity).** Source1384 bounds L by kappa*H_u/2. That correct upper bound is too large to prove the lower limit for every diverging alpha. The present note retains the actual logarithms and obtains(8); it does not find an error in Proposition18.2 or in its stated sufficient condition. The previously open diverging-alpha portion of item5 at1478 is resolved here under the retained log(b+1)=o(u) hypothesis. Its earlier open status is historical, not silently removed.

**Review remark 2 (bounded alpha and finite-domain restrictions).** One cannot drop alpha->infinity from this conclusion using the same proof. Bound(9) then need not make delta tend to0 or even ensure u>=4kappa; moreover the upper correction in(11) need not vanish. The endpoint b=0 is an explicit boundary to a universal1/2 claim: source409–410 gives A(0,u)=u, hence R(0,u)=1 and log R/u=0. The general bounded positive-alpha rate, the second-order term at the saddle and a full equivalent remain open in this note. Likewise(3) is stated only for u>=4kappa; a limiting eventual condition is not a finite all-u theorem.

**Open question 1 (finer frontier, credited to the article and root).** Determine the general bounded-alpha limit and sharper terms of log R-u/2. This entropy sharpening is a leading-order result and supplies neither a numerical error constant for a full equivalent nor a replacement for global saddle localization. It also does not weaken the log(b+1)=o(u) assumption on the upper half.

The exact source spans read in this task are390–635 and1290–1490. The dependency audit is deliberately bounded: the new tilt proof and the elementary entropy argument above are checked in full; the stated single-spine subclass/convolution, uniform upper proposition and their displayed local proofs were read. Deeper reduced-shape enumeration and all global count, LDP, literature, inverse, executable-check and numerical-evidence claims are not re-audited. The cited source's numerical tests were read as prose only and neither replayed nor adopted as proof. Source archival/placement authentication and the rest of the publication review belong to Riemann's independent lane.

New reasoning is handwritten. No supplied, archived, committed, predecessor or frozen helper was run or imported; no saved source/coefficient array was evaluated; no degree propagation, scientific sampling, emitter or build was used. The metadata companion performs byte, Git-object and read-span authentication only. Files stay in/tmp; repository/Git and the immutable source remain unchanged. Root and Pascal independently read and passed the complete new finite/limit proof, requesting no correction. Pascal also independently checked the cited tilt/convolution source spans. This pair is frozen after those challenges; no manuscript or predecessor bytes were changed.
