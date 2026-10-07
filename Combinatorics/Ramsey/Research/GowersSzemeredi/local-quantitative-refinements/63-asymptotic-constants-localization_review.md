# Independent mathematical review: dimension-sensitive face cover

The section filenames in this review refer to the modular drafting sources, which are incorporated in the single delivered TeX article. Initial proof-note reviews were supplemented by the final section and integration audits.

Reviewed the complete `phase_face_cover_notes.tex` and the positive-cover interface,
finite Proposition 17.7 specialization, definition of the asymptotic coefficient,
and ceiling proof in `sources/library/article(20261007-014857).tex`.

## Conclusion

The statements F1--F9 and their stated comparison with the previous coefficient
are mathematically valid under the displayed hypotheses. No proof gap was found.
This is an internal AI mathematical review, not formal verification or a priority
claim. The finite result inherits the explicitly cited phase-removal interface;
the new cover and its passage to the lattice have been checked independently.

## Exact cover

* The unrestricted integral in `r` free coordinates is
  `2^(r+1) t_+^(r+2)/(r+2)!`.
* When `w <= ell/2`, at most one boundary in any coordinate contributes. At a
  midpoint with `w=ell/2`, both potential boundary contributions have zero kernel,
  so choosing either nearest face creates no missing positive contribution.
* Every boundary excluded by inclusion-exclusion replaces one two-sided distance
  variable by a one-sided variable starting at `d_i`. Thus F3 has the correct
  power of two, sign, shift, and factorial.
* After multiplication by the proposed face density, the factorial cancels
  exactly. For `T=J union S`, setting `u=(w-d_T)_+`, the sum over `J subset T`
  is `u^(k-|T|+2) (w-u)^|T|`, with the displayed power of two.
  If `u=0`, every exponent is at least two, so all terms vanish.
* The empty subset contributes the whole unrestricted integral. All remaining
  summands are nonnegative. At the corners the extra terms vanish; the cover
  level there is exactly the stated lower bound.

## Rounding and lattice mass

For every integer target, absolute value is affine on each individual closed unit
interval in a center coordinate. Hence the kernel is convex in that coordinate
on each closed unit cell, even though it is not globally convex. Conditional
Jensen, applied successively to independent mean-preserving rounding in the free
coordinates, proves simultaneous domination for every integer target. This is a
single rounding kernel independent of the target.

An interior integer receives integrated weight one from its two adjacent unit
intervals; a boundary integer receives one-half from its sole adjacent interval.
Face-fixed coordinates have mass one and are not rounded. Summing the resulting
face measures gives exactly F5. The full-dimensional part has total mass
`(2h)^k`; every codimension-j face has mass `(2h)^(k-j)` times its face density.
Thus the total is F1 with `ell=2h`, with no extra endpoint factor.

## Finite localization interface

The earlier positive-cover corollary has coefficient
`E_A*kappa/(N^2*T*U^(k+2))`. Its Proposition 17.7 input is
`E_A >= alpha*N^2*m^k`. Substitution gives exactly F6. The rounded centers stay
inside the original increment box, as the inherited recentering argument needs.
The field, degree, normalization, and progression-size hypotheses match the
prior result. The additional width hypothesis `w<=h` is stated openly.

With `m>=15` and `m>3k`, one has
`w<L+1 <= m/(3k)+2 <= (m-1)/2`, uniformly over `N>=m^2`.
Indeed `M=floor(N/L)>=L` gives `w<L+1`; the last inequality is hardest at `k=1`
and reduces to `m>=15`. The finite coefficient need not dominate the previous
finite coefficient in every small case; the notes correctly avoid that claim.

## Asymptotics and ceiling

For fixed k, uniformly over `N>=m^2`,
`w/m=1/(3k)+O_k(1/m)`, `w/(L+1)=1+O_k(1/m)`, and `(m-1)/m=1+O(1/m)`.
These yield F7. The product in F8 decreases factor by factor, giving the stated
exponential bound. The lower bound is the empty and singleton contributions.
The previous ceiling applies because the new output remains within the same
admissible class; using `U=L+1` if the actual maximum is L only weakens the lower
bound, which is harmless for admissibility.

The optional expansions in the notes are correct:

    D = 1 + 2/(3k) - 10/(9k^2) + 148/(81k^3) + O(k^-4)
    1/D = 1 - 2/(3k) + 14/(9k^2) - 292/(81k^3) + O(k^-4).

A simplifying identity is

    binom(k,j)*(k-j+2)!/(k+2)!
      = (k-j+1)*(k-j+2)/(j!*(k+1)*(k+2)).

For k>=2 the termwise comparison is strict already at j=1. The new denominator
tends to one, so the first-order asymptotic equality to the universal ceiling is
proved. No fixed-k exact optimum or relative 1/k correction is proved.

## Optional generalization

For every real s>0, use `K=(w-||x||_1)_+^s` and codimension-j face density
`Gamma(k-j+s+1)/Gamma(k+s+1)*w^j`. The same proof gives the exact convolution

    Gamma(s+1)/Gamma(k+s+1)
      * sum_{S subset [k]} 2^(k-|S|) d_S^|S|
          (w-d_S)_+^(k-|S|+s).

The empty term is the unrestricted integral
`2^k*Gamma(s+1)/Gamma(k+s+1)*w^(k+s)`. The lattice rounding proof also holds for
every real s>=1. This generalization is independent of the phase-removal
application, which uses s=2.

## Supplemental review: joint scale corollary

Independently checked Corollary `loc:cor:joint-scale` in the final section.
No mathematical issue found. The exact factorization is

    R/v = (m/(m-1))^k * (w/(L+1))^(k+2) / H_k(2w/(m-1)).

The coefficientwise bound follows from
`(k-r)/(k+2-r) <= k/(k+2)` for each admissible r, hence
`1 <= H_k(z) <= exp(k*z/(k+2))` for every z>=0. This proves the
stated finite exponential bounds without an asymptotic assumption.

For the uniform rounding bound, `m>3k` gives
`L=ceil(m/(3k))<2m/(3k)`; `M=floor(N/L)>=N/(2L)` follows since
`N/L>=2`. Writing `N=LM+r`, primality and `2<=L<N` ensure
`0<r<L`, so `0<w-L=r/M<L/M<=2L^2/N<8/(9k^2)`.
All constants are independent of the ambient prime.

If m/k^2 tends to a positive finite lambda, then L is asymptotic to
lambda*k/3, the first and third logarithmic factors tend to zero, and
the middle one tends to -3/lambda. The same estimates give limit zero
for its logarithm when m/k^2 tends to infinity. The error terms
`O(k/L^2)+O(1/(k*L))` vanish in both regimes. If m/k^2 tends to zero,
then `L=o(k)` and `k/(m-1)<=1/3`; the displayed upper bound with
`w<=L+1/2` tends to zero. Thus all three claimed limits are valid,
uniformly for prime `N>=m^2`. The corollary correctly confines its
scale threshold to this explicit construction rather than claiming a
necessary threshold for the unknown optimal finite theorem.
