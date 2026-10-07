# Independent review of the bounded centered real U2 theorem

Reviewed the parent proof in `notes/bounded_odd_norm.md` on 7 October 2026.
This is a mathematical review, not a Lean verification or a priority audit.

## Result

The argument is correct as stated. For a finite abelian group of odd order
N >= 3 and centered real f with |f| <= 1, it proves

    ||f||U2^4 <= 1/3 - 4/(3 N^2) + 1/N^3.

The displayed cyclic interval example attains the bound for every odd N.
The compact-group conclusion with coefficient 1/3 is also valid when
doubling is a continuous surjective homomorphism.

## Checks

1. The inequality uv + vw - uw <= 1 holds at all eight corners of the
   real unit cube and is separately affine, hence holds everywhere on
   that cube. Replacing v by -v gives the other sign. Averaging with
   (u,v,w) = (f(x), f(x+h), f(x+2h)) yields
   R(2h) >= 2 |R(h)| - 1. Both sides of
   1 + R(2h) >= 2 |R(h)| are nonnegative, so the squaring step is valid.

2. Doubling permutes a finite group of odd order. Also E_h R(h) = 0
   follows from centering. Consequently
   E_h [(1+R(2h))^2 - 4 R(h)^2] = 1 - 3 S, exactly.

3. At h=0 the slack equals 1 + 2r - 3r^2 = (1-r)(1+3r),
   where r = E f^2. The polytope sum f = 0, -1 <= f <= 1 has at
   most one interior coordinate at a vertex: two interior coordinates
   admit a nontrivial opposite perturbation preserving their sum.
   With N odd, the remaining N-1 endpoint coordinates sum to an even
   integer, so the last coordinate must be zero; the signs balance.
   Maximizing the convex sum of squares at a vertex therefore gives
   r <= (N-1)/N.

4. The concave quadratic (1-r)(1+3r) has its minimum on this interval
   at an endpoint. Its endpoint values are 1 and 4/N - 3/N^2; the
   latter is <= 1 for N >= 3. Retaining only the h=0 contribution
   gives 1 - 3S >= 4/N^2 - 3/N^3, with the stated finite correction.

5. For the cyclic example f(0)=0, f(1),...,f(m)=1 and
   f(m+1),...,f(2m)=-1, N=2m+1, the correlation formula is
   R(0)=(N-1)/N and R(h)=1-4h/N for 1<=h<=m, with R(-h)=R(h).
   The two elementary power sums give exactly the claimed S.
   A stronger equality check is available: at every nonzero h,
   1+R(2h)=2|R(h)|. Thus the proof discards no positive nonzero-h
   slack on this example.

6. A continuous surjective homomorphism of compact groups sends
   normalized Haar measure to normalized Haar measure. This is all
   the compact extension needs. The circle square wave has the
   triangular correlation R(h)=1-4 dist(h,Z), whose square integrates
   to 1/3. Values at its jump points do not affect this calculation.

## Scope to preserve

- Sharpness for all odd orders is attained by C_N; it does not assert
  that every abelian group of the same order attains the finite bound.
- Centering and real-valuedness are essential hypotheses for the stated
  form. The calculation alone gives only the displayed, not necessarily
  sharp, extension at nonzero mean.
- The proof bounds U2^4, not U2 itself. Scaling is by the fourth power
  of the L-infinity norm.
- The compact assertion assumes doubling is surjective; this cannot be
  dropped for groups with a nontrivial obstruction to doubling.
- No equality classification beyond the explicit cyclic example was
  established in this review.
