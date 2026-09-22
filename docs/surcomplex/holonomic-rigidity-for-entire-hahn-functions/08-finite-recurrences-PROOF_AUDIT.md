# Proof audit and scope controls

This is a review record for the written arguments, not an independent referee
report and not a proof-assistant certificate.

## Common assumptions

The coefficient field is C with trivial valuation. Gamma is a nonzero set-sized
ordered abelian group. All supports are well ordered sets. All recurrences,
operators, and polynomial coefficient lists are finite. Index integers are
ordinary nonnegative integers. The external derivative D_z is zero on K_Gamma.

Algebraic closedness, real-valued norms, spherical completeness, and a global
Hahn-series field with a proper-class exponent set are not used.

## Critical checks of the argument

### 1. Escape direction and cancellation

From A_0(n)a_n = -sum_{j>0} A_j(n)a_{n+j}, some right-hand term has valuation
at most v(A_0(n)a_n). Hence the successor coefficient has valuation cost at
most v(A_0(n))-v(A_j(n)), with this sign and not the opposite sign.
Subtracting j*delta makes the selected evaluated leading exponent strictly
smaller. Cancellations can raise the valuation of the right-hand sum but
cannot invalidate this minimum inequality. The selected successor is nonzero.

One nonzero coefficient at or beyond the common starting index already
produces an infinite path. Thus the conclusion includes a common degree bound,
not just eventual termination for each solution separately.

### 2. Integer evaluations

Normalize a polynomial by the minimum valuation of its coefficients.
Its residue polynomial is nonzero. Ordinary integer roots give only finitely
many exceptions in characteristic zero. The valuation is eventually exactly
the coefficient minimum, not merely bounded below by it.

### 3. Unit q with root-of-unity residue

Write q = zeta*(1+u), with v(u)>0 and u != 0. For ordinary n>0,
(1+u)^n - 1 has valuation v(u) and leading coefficient n*lc(u).
The coefficient at the minimum possible exponent in P(q^n), on each residue
class of n, is a nonzero polynomial in n with distinct powers. This permits
finitely many exceptional n but supplies an eventual finite valuation range.
No logarithm, infinite binomial series, or ordinary convergence is assumed.

### 4. Nonunit q in higher rank

The candidates beta_k + k*n*v(q) have eventually fixed pairwise order because
each difference is strictly monotone. It is NOT asserted that the smallest
or largest degree eventually wins. Coefficient valuations in larger
Archimedean classes can prevent such a shortcut.

When |v(q)| is noncofinal, one element eta dominates all integer multiples,
including M*n*|v(q)| for a fixed integer M. Adding a bound for the finitely
many intercepts gives the bounded valuation cost required for escape.

### 5. Positive converse

An order unit mu lets each fixed argument valuation and each target valuation
be bounded by ordinary multiples of mu. The quadratic theta coefficient
valuation dominates both. Cofinally increasing term valuations imply strong
summability even when Q has arbitrary higher Hahn tails.

For negative v(q), the positive-shift equation was obtained by substituting
q^2*z into the equation for Q=q^{-1}. Both versions were checked exactly.

### 6. Multivariate restriction

The finite derivative span is represented using derivatives of F themselves,
so they remain formal power series before restriction. A countable family of
nonzero homogeneous parts is preserved by a generic complex line; finitely
many rational denominators do not vanish identically on that line.
Denominators may vanish at the origin, which is harmless in K((w)).
Finite-block grouping of the original strongly summable evaluation family
proves entireness of the restricted series. A finite rational differential
system then proves its D-finiteness.

### 7. Surreal interpretation

The concrete exponent group is a set-sized additive subgroup of No.
The embedding uses Conway monomials t^gamma -> omega^{-gamma}.
The explicit entire example is tested on this fixed workspace, not all No[i].
The article exhibits a strictly descending support after an explicit larger
scale is adjoined, so it does not conflict with whole-class rigidity.

## Deliberate exclusions

- Finite-order q is excluded from the main classification; periodic-support
  counterexamples are provided.
- Mixed operators at unit valuation are not classified.
- No nonlinear differential algebraic rigidity is claimed.
- No complete algorithm for arbitrary surreal comparisons or cofinality is claimed.
- The 3,705 finite checks do not prove any infinite theorem.
- No Lean verification or independent mathematical review is claimed.
- Novelty of the exact formulation is proposed, not certified.
