# Independent mathematical review of the proposed results

Reviewed on 26 November 2026. This review checks the mathematical arguments in `sections/sampling.tex` and `sections/li_heat.tex`. It is a separate human-readable argument review, not Lean formalization or independent compilation of the upstream RH development. No substantive error or missing hypothesis was found in the final fragments reviewed.

## 1. Bounded positive coefficients with invisible power-grid samples

For the main example, the fragment sets

    F(x) = x log x + (1/2) x^(3/5) sin^2(pi x^(1/5)),  x >= 1,
    a_1 = F(2),
    a_n = n [F(n+1) - 2 F(n) + F(n-1)],  n >= 2.

The derivative calculation is correct. For h(x)=x^(3/5) sin^2(pi x^(1/5)),

    x h''(x) = -(6/25)x^(-2/5)sin^2(pi x^(1/5))
                +(2pi/25)x^(-1/5)sin(2pi x^(1/5))
                +(2pi^2/25)cos(2pi x^(1/5)).

The stated bound implies 0<F''(x)<2/x. The triangular-kernel formula for second differences therefore gives strict positivity of every coefficient and a_n<2n/(n-1)<=4 for n>=2. The n=1 coefficient is positive and below 3. These are real coefficients indexed by integers; they are not asserted to be integer-valued.

The identity

    sum_{n<=x} a_n (x/n - 1) = I F(x)

holds because its slope on every interval [m,m+1] telescopes to F(m+1)-F(m), and both sides vanish at x=1. Here I F denotes linear interpolation on the positive integers. Convexity gives

    R(x) = I F(x)/x - log x
         = (1/2)x^(-2/5)sin^2(pi x^(1/5)) + epsilon(x),
    0 <= epsilon(x) <= 1/(2x^2).

The interpolation error is zero at every positive integer. Consequently R(m^5)=0 for every positive integer m, while R((m+1/2)^5)>=(1/2)(m+1/2)^(-2). This verifies the asserted failure of any eventual upper bound of order x^(beta-1) with beta<3/5.

The Mellin decomposition is also correct:

    Phi(s) = 1/[4(s-3/5)] -(5/4) I(2-5s) + H(s),
    I(z) = integral_1^infinity y^z cos(2pi y) dy,

where H is holomorphic on Re(s)>-1. The integration-by-parts recurrence is

    I(z) = -z/(4pi^2) - z(z-1)I(z-2)/(4pi^2).

Its sign and boundary term were checked. Iteration gives an entire continuation of I, with no divisions by variable factors. Therefore the only pole of Phi in Re(s)>-1 is the simple pole at 3/5, of residue 1/4. In particular it cannot be canceled by the oscillatory term or the interpolation error.

The extension to each integer p>=4 is valid. With r=1/p, the derivative bound is

    |x h_p''(x)| <= C_p
       = (2+pi)/p + (2pi^2-3pi-4)/p^2 < 2.

The second coefficient is positive, so C_p decreases for p>=4; C_4=1/4+pi/16+pi^2/8<2. The same construction gives 0<a_n<4, exact R(m^p)=0, and the pole 1-2/p of residue 1/4. The assumption that p is an integer makes m^p an interpolation node and is explicitly present in the fragment.

### Scope and originality boundary

This is a limitation theorem for an abstract class of positive weighted traces. It does not assert that actual von Mangoldt or quadratic-twist coefficients exhibit the constructed behavior. Its continuation is proved on Re(s)>-1, not on the entire plane; it is not claimed to satisfy every part of the repository's global `New.IsPolar` predicate. These distinctions are stated in the fragment.

Setiawan's preceding work already gives the quadratic interpolation loss, fourth-power sufficiency, and a local single-interval sharpness example. The potentially new strengthening here is their simultaneous global realization with bounded positive integer-supported weights, exact zeros on the entire power grid, and an explicit genuine Mellin pole. The source audit records this prior-art boundary.

## 2. Cayley-angle Levy process and its quantitative Cauchy expansion

The general theorem assumes a locally finite multiset of real ordinates, counted with multiplicity, whose two-sided counting function is

    N(T) = (d/pi) T log T + (B/pi) T + O(log(T+2)),  d>0.

The construction uses theta_gamma=2 arctan(1/(2gamma)) for nonzero gamma, theta_0=pi, and the symmetric Levy measure

    nu = (1/2) sum_gamma (delta_{theta_gamma}+delta_{-theta_gamma}).

These hypotheses make nu a Levy measure, of infinite total mass and infinite first absolute moment, with a finite positive second moment V. Local finiteness permits only finitely many ordinates near zero, so central zeros do not create a hidden singularity. The process is symmetric, has no Gaussian component in its Levy triplet, and has infinite variation.

The symbol estimate and its constants are correct:

    Psi(u) = A |u| (log|u|+kappa) + O(sqrt(|u|) log(|u|+2)),
    A=d/2,  kappa=EulerGamma+B/d.

In particular, for a primitive Dirichlet character of conductor q, counted over both signs, d=1 and B=log(q/(2pi))-1. The Lambert scale is exactly

    w = W_0(exp(kappa)/(A t)),
    a = A t w = exp(kappa-w).

For the Dirichlet specialization this is w=W_0(q exp(EulerGamma-1)/(pi t)) and a=t w/2. Both the factor 2 and conductor normalization have been checked.

The counting remainder gives the stated symbol error after partial summation, splitting at gamma approximately sqrt(|u|). Replacing the Cayley angle by 1/gamma introduces a smaller admissible error. The constant kappa follows from the two integrals

    integral_0^infinity (1-cos v)/v^2 dv = pi/2,
    integral_0^infinity (1-cos v)log(v)/v^2 dv
        = (pi/2)(1-EulerGamma).

The all-order profiles

    Q_k(x)=(-1)^k/(pi k!) Re [d^k/dz^k
                {Gamma(z)(1-i x)^(-z)}]_{z=k+1}

are correctly normalized. Q_0=1/[pi(1+x^2)]. The displayed formulas for Q_1 and Q_2, including the pi^2/6-5/4 term in Q_2, agree with the digamma and trigamma values at 2 and 3.

For every fixed nonnegative integer K and r, the fragment proves

    sup_x |d^r/dx^r [a f_t(a x)-sum_{k=0}^K Q_k(x)/w^k]|
        = O_{K,r}(w^(-K-1)+sqrt(a)).

The uniform derivative estimate follows from a weighted L1 estimate on the Fourier integrands, not merely pointwise characteristic-function convergence. Splitting the scaled frequency at sqrt(a) handles the region where the symbol asymptotic cannot be used uniformly. Above that cutoff the exact exponent and the model exponent are both bounded below by a positive multiple of the scaled frequency. The remaining exponential bound makes every fixed polynomial Fourier weight integrable. This verifies the claim for arbitrary fixed r, including uniformity over the whole real line.

The circle kernel has Fourier coefficients exp(-t Psi(n)) and is normalized as a density with respect to Lebesgue measure, with factor 1/(2pi). For complex Dirichlet characters these frequencies are Re(lambda_chi(n)); conjugating the character is necessary to pair the nonreal Li coefficients. The fragment correctly uses symmetrization and does not identify the symbol with the full complex coefficient.

The local scaled expansion on the circle is stated only for bounded x, as required by periodicity. The Riemann-sum error for the model is controlled by its uniformly integrable first derivative. The trace constants agree with 2pi p_t(0)=(2/a)[1-(1-EulerGamma)/w+Q_2(0)pi/w^2+O(w^-3)].

## 3. Fractional moment transition and long-time behavior

The final added section is correct. With L=log(1/t), it gives

    0<p<1:  E|X_t|^p ~ a^p/cos(pi p/2),
    p=1:    E|X_t|   ~ (A/pi) t L^2,
    1<p<2:  E|X_t|^p ~ t integral |y|^p nu(dy),
    p=2:    E|X_t|^2 = t V.

The fractional-moment Fourier identity has the correct constant 2 Gamma(1+p) sin(pi p/2)/pi. For p<1 the scaled integral admits a valid integrable majorant; the small region where the symbol asymptotic fails contributes O(t a^(-p))=o(1). For p>1, dominated convergence after division by t is justified because Psi(u)u^(-p-1) is integrable at both zero and infinity. Tonelli then identifies its constant with the Levy measure moment.

At p=1, the upper cutoff 1/t and lower cutoff 1/(t L^2) yield the same leading coefficient A/pi. The quadratic approximation error below the lower cutoff is O(t), and the omission of 2 log L from the logarithm affects only lower-order terms. Thus the stated transition has no missing factor 2.

The large-time central limit theorem follows from Psi(u)=V u^2/2+o(u^2), valid by dominated convergence using the finite second moment. It does not conflict with the small-time Cauchy limit: the two limits use different scales and different parts of the symbol.

## 4. Remaining limits of this review

The analytic arguments are conventional rigorous proofs and have not been formalized in Lean. The review checks the displayed hypotheses and constants and finds the proofs sufficient. It does not establish global priority in the literature. Li's positivity criterion, Schoenberg's semigroup principle, and the broader RH/infinite-divisibility connection are established ingredients; the candidate contributions are the quantitative all-order Lambert-scaled expansion, the moment transition for this Cayley-angle construction, and the bounded-coefficient hidden-pole realization above.
