# Additional proof and computation details

These notes supplement the full proofs in the article. They contain derivations prepared for this project, not excerpts from the historical sources.

## Analytic radius in the moment lemma

Let rho = 1/[4(1+k)] and |t| <= rho. For integer k >= 0, |2kt^2| <= 1/32. The finite logarithmic term has arguments 1-(k+a)t^2 with 0 <= a < k. Summing the geometric logarithm bound gives an absolute bound of 3/31 (a deliberately loose constant). The removable expression ((1-v)log(1-v)+v)/(2t^2), with v=2kt^2, starts at order k^2t^2 and is bounded by 2/31. Rationalizing sqrt(1-v)-1 bounds the square-root term by 1/2. Each of the finitely many scalar-log corrections is bounded by |lambda_h|4^(-h)[(32/31)^(h/2)+1]. These estimates bound exp(F_J) on the whole complex disk, uniformly in k.

Cauchy's coefficient estimate followed by a geometric tail gives the (1+k)^(J+1)t^(J+1) factor. The scalar expansion is applied at n and n-2k only; no derivative of an asymptotic remainder is taken. It is sufficient to subtract two O(n^(-(J+1)/2)) errors.

## Formal operations and finite computation

Every displayed infinite formal expression is interpreted coefficientwise. At target order J only finitely many scalar coefficients, polynomial Gaussian moments, and power-sum polynomials are required. If E(t)=exp(H(t)) and H(0)=0, then r E_r=sum_{h=1}^r h H_h E_{r-h}. If A(t)=exp(L(t)) with A_0=1, then L_r=A_r-(1/r)sum_{h=1}^{r-1}h L_h A_{r-h}. These exact recursions are used in the extraction script.

Gaussian moments with mean sigma/2 and variance 1/2 satisfy mu_0=1, mu_1=sigma/2 and mu_j=(sigma/2)mu_{j-1}+((j-1)/2)mu_{j-2}. The Touchard transform converts k^r into the Bell polynomial in w. A final falling-factorial transform gives the full point-probability corrections Q_j.

## Numerical truncation of the exact probability polynomial

The exact expansion G_n(z)=sum_k m_{n,k}(z-1)^k has 0 <= m_{n,k} <= 1/k!. The sum of absolute coefficients of (z-1)^k is 2^k. Thus omitting all k>K changes the coefficient vector by l1 norm at most sum_{k>K}2^k/k!. When probabilities are retained only through l=K, the exact probabilities above that range are included in this same bound. To estimate total variation against a Poisson law by summing only l<=K, also add the omitted Poisson tail (1/e)sum_{l>K}1/l!. One half of the combined bound controls the resulting TV error in exact arithmetic; numerical rounding and quadrature still require separate care.

The supplied 110-digit calculation is a sanity check rather than interval arithmetic. Its K=90 tail is far below the precision of the article's printed table. The small-n case K=floor(n/2) has no omitted moment terms, but still has a Poisson comparison tail.

## Inversion conventions

At y=a_n, the smooth logarithmic truncation's root has error O(n^(-(J+1)/2)/log n). For arbitrary thresholds, monotonicity gives only the stated two-ceiling enclosure for the integer index. Constants may be enlarged when replacing the smooth root by a finite Newton iterate.

For an actual log-linear interpolation of the sequence, approximate its logarithm by the piecewise-linear interpolant of L_J at integer nodes. The nodal O(n^(-(J+1)/2)) error remains of that order under interpolation, and the slopes are asymptotic to (log n)/2. This gives the same inverse order. A smooth L_J alone incurs the nonzero chord term theta(1-theta)/(4x)+O(x^(-3/2)) in the logarithm, generally producing an O(1/(x log x)) inverse discrepancy.

## Small-sector interpretation

The exact positive and negative integrals K_n^+ and K_n^- are separately defined quantities. The equality a_n=K_n^+ +(-1)^nK_n^-+R_n with polynomially bounded R_n isolates the smaller component after exact subtraction. Expanding the quotient of their separate series gives

    (a_n-K_n^+)/K_n^+
      = (-1)^n exp(-2 sqrt(n)) [1-31/(12 sqrt(n))+O(n^(-1))].

No finite fixed-order approximation to K_n^+ is asserted to have enough absolute accuracy for this subtraction. A genuinely exponentially accurate truncation theorem would require new large-order analysis.
