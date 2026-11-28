# Exact checks for local norm cancellation

Run with Python 3.10 or newer, using only the standard library:

```sh
python3 check_norm_cancellation.py --output checks.json
```

The checks use the eight prime parameters `d = 7, 23, 31, 47, 71, 79, 103, 127`, each congruent to 7 modulo 8. Unramified test primes range from 2 through 47. All odd-prime lifts are checked through precision `p^7`; split-at-2 lifts are checked through `2^12`. Every tested ramified prime `p=d` is included even when it exceeds 47.

## What is checked

1. **Odd inert primes.** Work exactly in `(Z/p^k Z)[w]/(w^2+d)`. Find an element with norm `-1` modulo `p` and exact multiplicative order `2(p+1)`. Lift the norm equation by changing a coordinate with unit derivative. Independently construct the Teichmuller representative by repeated `p^2` powering, and check its exact order, its `p`-power/conjugation identity, and `zeta^(p+1) = Norm(zeta) = -1` at full precision. The norms of `1` and this element add to zero.
2. **Split primes, including 2.** Lift a root `r` of `r^2=-d`, take `b=r^-1`, and check the pair associated to `alpha=b*sqrt(-d)`. Its chosen embedding is 1, its conjugate embedding is -1, and its norm is -1. Thus the norms of `1` and `alpha` add to zero. At 2 the code keeps every root branch while lifting; ordinary derivative-invertible Hensel does not apply, and greedy branch selection is unsafe. The selected final root gives a compatible sequence at all lower precisions.
3. **Ramified primes.** The norm of a unit reduces modulo `d` to a nonzero square. The code exhaustively checks that no two such squares sum to zero, since `d` is 3 modulo 4. It then finds all nonzero-residue solutions of `a^2+b^2=-1` (there are `d+1`), chooses one, and lifts it. The three rational scales `1,a,b` therefore have square norms summing to zero through the tested precision.
4. **Formal cancellation.** For formal `g(0)=0`, coefficients through degree 10 verify
   `product exp(-g(delta_i*z)) = exp(-(sum s_i)*g(z)) * product exp(s_i*g(z)-g(delta_i*z))`.
   Four examples have zero norm-weight sum; two control examples have a nonzero sum and retain a nontrivial residual. The unit/inverse identity is also checked. These are formal rational calculations, not numerical evaluations of the analytic theta function. The arbitrary rational `delta_i,s_i` used here check algebra only, and are not asserted to be actual CM norm pairs.

## Scope

The finite congruences support the stated local constructions and catch signs, order conditions, and the special behavior at 2. They do not prove convergence, the CM integral-series theorem, the least-valuation argument, or the global Riemann-hypothesis theorem. Those mathematical obligations belong to the accompanying report. No new Lean kernel check is claimed.

The JSON output records every residue witness and every lift, so a reader can independently inspect or reproduce the finite computations. The code does not access the network or modify the source repository.
