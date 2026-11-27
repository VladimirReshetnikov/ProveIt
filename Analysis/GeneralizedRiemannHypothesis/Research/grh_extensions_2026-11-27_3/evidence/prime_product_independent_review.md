# Independent mathematical review: prime-product limit theorem

Reviewed the proof in `agent_arithmetic_notes.md` and the complete manuscript `prime_product_limits.tex` independently on 27 November 2026. The review checked the finite-population expansion, the prefactor-free finite-order decay lemma, both directions of the mixing criterion, the treatment of infinite rates in the compound-Poisson classification, and realization at reciprocal-density boundaries. No mathematical gap was found in these arguments. This is a mathematical review, not machine verification or a certification of worldwide novelty.

## 1. Exact finite-population expansion and remainder

For labelled defects d_i=delta_{x_i}-delta_e, expanding a product over a random h-subset shows that a specified j-set of defects contributes with probability (h)_j/(m)_j. Thus the exact elementary-symmetric convolution expansion is correct. It remains valid when j>h, with the falling factorial interpreted as zero.

For j<=h and j<=t<=m/2, the factorial ratio is

    r_j=product_{0<=l<j}(1-a_l),
    a_l=(l/h-l/m)/(1-l/m).

All a_l lie in [0,1], and a_l<=2l/h. This gives

    0<=1-r_j<=j(j-1)/h.

The second-order comparison is also correct:

    |r_j-1+binomial(j,2)(1/h-1/m)|<=2j^4/h^2.

Indeed the product-versus-sum error is at most (sum a_l)^2/2, while replacing sum a_l by (1/h-1/m)sum l costs at most (2/(hm))sum l^2. These bounds are comfortably within the stated constant. For j>h the same inequalities follow immediately from r_j=0; j=0,1 are exact.

Using ||e_j(d_1,...,d_t)||_1<=binomial(t,j)2^j gives the stated first-order estimate 4 lambda^2 exp(2lambda)/h. The fourth moment of the exponential series is

    sum_{j>=0} j^4 z^j/j!
      =exp(z)(z^4+6z^3+7z^2+z),

so the explicit O(h^-2) remainder and its constant are correct. The sign of the correction is

    mu=nu(u)-(1/(2h)-1/(2m))*u^2 nu''(u)+remainder.

The estimate ||u^2 nu''(u)||_1<=4lambda^2 follows directly by differentiating two distinct Bernoulli factors: the remaining factors form a probability law. It therefore avoids an unnecessary exponential factor in the correction itself.

## 2. Moving Bernoulli law versus limiting Poisson law

The derivative limit is valid in finite-group Fourier coordinates. If u->0 and all scaled rates converge to finite limits, the denominators 1+u(chi(x)-1) stay away from zero; the sum of the individual second logarithmic-derivative terms is O(u lambda), while the square of the first logarithmic derivative converges to the square of the Poisson exponent. Finite Fourier inversion then gives the claimed signed-measure limit

    h(mu-nu(u))->-(1/2) Lambda^{*2}*exp_*(Lambda).

The comparison with the moving Bernoulli law is essential. It must not be replaced by h(mu-P_Lambda) without additional rate assumptions. For an explicit counterexample to that replacement, take a C2 population with t=floor(h/log h) defects, m=h t, and u=1/t. Then lambda=ut=1 exactly, but

    nu_hat(u)=(1-2/t)^t
      =exp(-2)*(1-2/t+O(t^-2)).

Thus the Bernoulli-to-Poisson difference, multiplied by h, has a term asymptotic to -2 exp(-2) h/t, which diverges. The finite-population correction itself remains of order 1/h. The manuscript's stated caution is therefore mathematically necessary.

## 3. Prefactor-free finite-order decay

The pairing argument is valid for every defect proportion and every 1<=h<=m/2. Pairing a largest value class with other classes uses

    r=min(n_max,t,floor(m/4))>=t/max(D,8)

for m>=8. Conditional on pair occupancies, split-pair orientations are independent fair choices; the modulus of each conditional mean is at most kappa=cos(pi/D). This includes D=2, where kappa=0.

The Bernoulli conditioning and tilt remove the potential square-root prefactor correctly. Under the tilted law the unpaired labels still have a Bin(m-2r,h/m) count, independently of the pairs. Since m-2r>=m/2, their variance is at least h/4, so their maximal atom is at most an absolute constant divided by sqrt(h). The original binomial's integer mean h is a mode, and Chebyshev gives a lower bound of the same order for its atom at h. The ratio is therefore bounded by an absolute constant, including h=1. The resulting exponent

    c_D=(1-cos(pi/D))/max(D,8)

is valid. Small m is absorbed in the same absolute prefactor after enlargement.

This lemma supplies decay when lambda=h t/m tends to infinity at an arbitrarily slow rate. The older circle bound with a growing prefactor would not by itself justify that inference.

## 4. Sharp mixing criterion

The upper bound follows from Fourier inversion on the inherited quotient: there are at most D-1 nonprincipal modes, all of order at most D. The character-minority minimum over the entire unit group is at most the minority count of each such mode, so the proposed uniform exponential bound has the correct inequality direction.

For necessity, on a subsequence with lambda=h T_D/m bounded, the sparse-quota assumption u=h/m->0 and h->infinity imply t/m=lambda/h->0. Hence the finite-population estimate applies eventually. After centering at a most frequent root of unity, the Bernoulli coefficient has modulus at least

    (1-2u)^t>=exp(-2lambda/(1-2u)).

Its difference from the true coefficient tends to zero. The coefficient therefore stays bounded away from zero, and a nonprincipal Fourier coefficient is bounded above by the normalized pointwise discrepancy. This proves necessity.

The sparse-quota assumption is substantive: at sampling fraction 1/2, a single C2 defect can have exactly zero coefficient, so the same necessity claim need not hold. Here 'all density' refers to retained-pool density, not to dropping the sparse-quota hypothesis.

The inherited bounded-quotient reduction was compared with `Article/sections/dir.tex`, especially `dir:lem:bias`, `dir:lem:circle`, and `dir:thm:quotient`. Its extension from q^-2 to an arbitrary prescribed q^-A error follows by increasing B. The Gram/word-ball proof quoted in the notes matches the source.

The manuscript's smooth-cutoff version of the endpoint bias argument is also consistent: the contour at real part 1/4 stays a fixed distance from every nontrivial zero under DGRH; the Mellin transform decays rapidly; the zero sum is O_W(sqrt(y) log(2q)); the restored cutoff, prime powers, and omitted Euler factors have the stated costs. Choosing the smoothing width before the cutoff constant gives the required arbitrarily small bias.

The manuscript makes the prefactor in the pair bound explicit as 20. Its displayed atom estimates give a ratio at most (20/3)*sqrt(pi/2)<9, so 20 is valid with room to spare. Its additional bound between the moving Bernoulli and moving Poisson laws, 2u lambda in L1, is correct: a Bernoulli(u) count and Poisson(u) count differ in L1 by exactly 2u(1-exp(-u))<=2u^2, and convolution telescoping gives the result.

## 5. Infinite rates and completeness of the classification

After fixing a bounded quotient A, choosing a largest population fibre is important: its population count is at least m/|A|. With labels normalized by this fibre, extract the finitely many scaled rates in [0,infinity]. Let K be generated by labels having infinite scaled rate.

If a character is nontrivial on K, it distinguishes the core fibre from some infinite-rate fibre. Whatever its largest character fibre is, its minority count is at least the smaller of the core count and that distinguished count. Multiplication by h/m sends both to infinity. The prefactor-free lemma therefore kills that Fourier mode.

On A/K every nonidentity label has finite total scaled rate, because an infinite-rate label lies in K by construction. The rare-defect theorem therefore gives an ordinary compound-Poisson limit there. Fourier inversion on the fixed finite A gives its uniform lift to A, with no missing factor: |A| times the lifted probability equals |A/K| times the quotient probability. Combining this with the inherited normalized pointwise estimate proves the asserted profile in the changing groups G_n.

All finite compound-Poisson Fourier coefficients are nonzero. Thus the surviving quotient is read from the subgroup of nonvanishing limiting Fourier modes, up to the chosen identifications and phase centering. This does not imply that the individual Poisson rates are uniquely identifiable from their law. For example, on C3, a rate 2pi/sqrt(3) at one generator and the same rate at its inverse give identical compound-Poisson laws. The notes do not claim uniqueness of the rates; the final wording should continue to avoid that implication.

## 6. Converse realization, including a=1/d

A finite abelian group of order d is a quotient of the unit group of a fixed squarefree modulus q_0: take distinct primes congruent to 1 modulo its cyclic invariant factors. Passing to q=q_0 r for primes r tending to infinity preserves that quotient. The new factor r eventually exceeds C(log q)^2, and the fixed-modulus prime number theorem gives asymptotically N/d primes in each quotient fibre.

Choosing a largest fibre gives m_0>=N/d exactly. Retaining all its primes and then floor(lambda_x m_0/h) primes in each defect fibre is feasible because these counts are o(N). In particular m>=N/d>=aN even at the boundary a=1/d; no unproved favorable prime-counting fluctuation is required.

Moreover m/m_0->1, m_0/h->infinity, and h t_x/m->lambda_x. The core's Fourier expansion over quotient characters bounds every character not factoring through A by d epsilon after normalization, and adding o(m_0) defects preserves a fixed gap from one. The circle bound then kills the full collection of those modes on the normalized pointwise scale. The realization therefore gives the full arithmetic profile, not merely a projected marginal.

## 7. Presentation and scope checks

- The bounded-quotient theorem, basic hypergeometric/Bernoulli approximation, and general compound-Poisson ideas should retain their prior-work attribution.
- The new package is the all-positive-retained-density sparse-quota criterion/classification, its exact realization, and the uniform signed-measure finite-population correction.
- Arithmetic statements use the supplied Dirichlet GRH input. The probability and group-algebra lemmas are unconditional.
- No assertion of a Lean check, a replay of the upstream GRH proof, or confirmed worldwide priority is justified by this review.
