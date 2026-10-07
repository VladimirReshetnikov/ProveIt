# Independent proof review: the uniform high-order comparison constant

The section filenames in this review refer to the modular drafting sources, which are incorporated in the single delivered TeX article. Initial proof-note reviews were supplemented by the final section and integration audits.

Reviewed `norm_gap_proof_notes.md` in full, together with the finite-cardinality
bounded-function proof in `notes/bounded_odd_norm.md`. This is an internal AI
mathematical review. It is not Lean verification, external peer review, or a
publication-priority certification.

## Verdict

The arguments establish

    c_d^odd = sup ||f||_{U2}^4 / ||f||_{Ud}^4,
    lim_{d -> infinity} c_d^odd = 1/3,
    1/3 <= c_d^odd <= 1/3 + 10*2^(-floor(d/8))  (d>=80),

where the supremum is over every finite abelian group of odd order and nonzero
real centered functions. The key upper bound is uniform in the underlying group;
there is no interchange of a fixed-group limit with an unrestricted supremum.
No substantive mathematical gap was found. Standard facts used explicitly are
the Gowers norm triangle inequality, translation invariance, Fourier inversion,
the derivative recursion, and monotonicity of normalized Gowers norms.

## 1. Sharp bounded-function inequality

The two separately affine inequalities at cube vertices give
`R(2h)>=2*abs(R(h))-1`. Since `R(2h)>=-1`, the shorter derivation is to square
`1+R(2h)>=2*abs(R(h))` and average. Doubling preserves uniform measure, and the
mean of R is zero, yielding `1+S>=4S`. The alternative telescoping quadratic
potential in the notes is also correct: its derivative is nonnegative on [-1,1],
and its displayed identity is valid on both sign intervals.

The finite-cardinality refinement is valid. An extreme point of
`{f in [-1,1]^N: sum f=0}` for odd N has N-1 coordinates at the endpoints and one
coordinate equal to zero. Convexity therefore gives `R(0)<=1-1/N`. The slack at
zero is `(1-r)(1+3r)`, a concave function of r. Its minimum on
`[0,1-1/N]` is at least `4/N-3/N^2` for N>=3. Retaining that single slack yields

    S <= 1/3 - 4/(3N^2) + 1/N^3.

The proposed cyclic function `(0,+1,...,+1,-1,...,-1)` has the claimed
autocorrelation and attains this bound. Thus the order-N universal bound is
sharp, without implying attainment on every abelian group of that order.

## 2. Fourier tail and factorial normalization

With `||f||Ud=1`, monotonicity gives `S=||f||U2^4<=1`. Centering removes the
trivial character. Odd order ensures every remaining character has a distinct
inverse, so the selected orientations in the balanced-word count really are
different labels.

For r distinct character pairs, each appearing once in each orientation, there
are `(2r)!` words. Each pair contributes `lambda_j^2=v_j/2`. The retained moment
is therefore `(2r)!/2^r * e_r(v_j)`. The birthday bound gives
`r! e_r >= v^r/2` whenever `v>=r(r-1)/(K+1)`. The resulting coefficient is exactly
`(2r)!/(2^r*r!)=(2r-1)!!`, not a factorial off by r! or a power of two.

Other additive relations can add zero-frequency words; they cannot subtract any,
because all Fourier coefficients of the autocorrelation are nonnegative.
The empty-tail and fewer-than-r-pairs cases obey the same upper bound. The
estimate `tau(r,r^3)<=3/r` for r>=16 follows from `(2r-1)!!>=r!>=(r/e)^r`
and the elementary numerical inequalities in the notes.

## 3. Positive smoothing under arbitrary character relations

All Fourier coefficients of P_j are nonnegative integers after collecting
aliases. Consequently every correlation `<P_j,chi*P_j>` is a nonnegative real
number. This verifies both

    ||P||_2^2 >= (J+1)||P_j||_2^2
    ||(1-chi_j)P||_2^2 <= 2||P_j||_2^2.

The normalized Fourier coefficient of |P|^2 is real, so its real-part estimate
is the asserted lower bound `muhat(chi_j)>=J/(J+1)`. This is the important point
that remains correct when powers coincide or selected characters are dependent.
The smoothing is a probability average of translations, hence a contraction in
every Ud norm. Its Fourier support lies in the stated finite character box.

## 4. Uniform recovery of the maximum for the smoothed function

For each support character, choose any allowed exponent representation. A
telescoping product bound gives `|chi(y)-1|<=2*pi*K*J*rho(y)`, independently of
relations. Summing at most M coefficients, each at most one in modulus, gives
the Lipschitz constant L.

The Bohr probability bound is valid even if the character image is a proper
finite subgroup of the torus: a partition into at most `ceil(1/t)^ell` boxes has
one box of the required probability, and subtracting one of its preimage points
maps it into the Bohr ball. No independence of character coordinates is used.

For the selected small increments, every vertex value differs by at most eta
from its base value. The `2^(d-1)` factors form an even number. If the base has
absolute value at least eta, they share its weak sign and their product is
nonnegative. Otherwise a product is bounded below by `-(2eta)^s`. This global
negative contribution is explicitly subtracted; thus there is no illegitimate
restriction of a signed cube integrand to a favorable region.

On the peak neighborhood the product is at least `(A-2eta)^s`, and
`2eta/(A-2eta)<=1/3` when `A>=1/2`, `eta<=1/16`. The stated condition on beta
makes the face average positive with its claimed lower bound.
The exact square identity then permits restriction to the chosen increments,
because its integrand is now a square. All exponents in F and in the recovered
maximum `A<=2eta+F^-1` match taking the `2^d`-th root.

## 5. Uniformity and finite rate

The main estimate holds with parameters r,K,J,eta chosen independently of the
group. For fixed choices, `-log F=O(d log(d)/2^d)` and the cancellation condition
eventually holds. Taking r large, then J large and eta small, proves the uniform
limsup bound. This is stronger than merely observing that Ud tends to Linfinity
on any one finite group.

For the explicit choice d=8k, r=2^k, K=r^3, J=r, eta=1/r, the formula for
`t=-log F` is correct. Two convenient complete checks of the polynomial estimates
are:

    (8k+1)(5k+4)+(8k-1)log(8k-1)+2
       <=104k^2+21k+7 <=2^(3k),
    B_k=(8k+1)(k+2)+1=8k^2+17k+3,
    B_10=973<=1024,
    2B_k-B_(k+1)=8k^2+k-22>0 for k>=2.

These imply `t<=1/r`. The cancellation condition follows from
`r^2/2>=k+4`; the displayed inequalities are far inside their valid ranges at
k=10. The elementary expansion
`(1+5/r)^4=1+20/r+150/r^2+500/r^3+625/r^4<=1+21/r`
holds for r>=1024. The final errors are exactly `7/r+3/r=10/r`.
Monotonicity `c_d<=c_(8 floor(d/8))` gives the asserted bound for all d>=80.

## 6. Sharp lower model

The interval has no wraparound at its sumset scale, so its energy is
`(2n^3+n)/3`. Removing the zero Fourier coefficient gives the stated centered
U2 formula. After division by the fourth power of its maximum, the quotient
simplifies to `n(n^2+n+1)/(3(n+1)^3)`, which tends to 1/3. Bounding Ud by the
maximum produces a lower bound for every d. Attribution to the earlier
repository report for this construction should be retained.

## Exposition recommendations

* State d>=2 wherever a Gowers norm rather than a seminorm is needed.
* Explicitly say the Fourier correlations of P_j remain nonnegative after
  collecting aliases; this resolves the main torsion concern.
* Keep the negative-product subtraction in the maximum-recovery lemma.
* Distinguish the proved universal order-N sharp bound from an unproved equality
  classification on each individual odd group.
* Describe the result as resolving the repository's limiting-constant question;
  broader literature priority needs its own search and is not certified here.
