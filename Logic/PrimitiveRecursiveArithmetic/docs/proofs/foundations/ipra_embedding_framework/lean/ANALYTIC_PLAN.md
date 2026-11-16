# Lean completion plan for the separated simple branch

## Status

`FiniteBranch.lean` compiles with Lean 4.32.0 and `Std` only. It implements
Gaussian-rational coefficients, finite coefficient arrays, truncating
convolution, bivariate substitution, fixed-point iteration, and the stabilized
coefficient extractor. Five coefficient computations for
`Q(X,Z) = (X - Z^2)/2` are proved by kernel reduction (`decide +kernel`).

`KernelGoals` is a structure listing unproved goals. There is deliberately no
instance or value of this structure. Compilation of its declaration does not
prove its fields. The contraction, stabilization, tail, perturbation,
regular-name, normalization, and object-language derivability proofs remain
to be formalized. The mathematical arguments are in `paper/03_analysis.tex`.

The five computation theorems' axiom reports contain `propext`,
`Classical.choice`, and `Quot.sound` through the imported rational/finite-array
infrastructure. They are kernel-checked Lean metatheory results, not claims of
intuitionistic object derivability. The intended iPRA representation uses raw
signed integers and positive denominators, with explicit primitive recursive
operations and arithmetic proofs, as described below.

## Concrete finite data

- `GQ` is a pair of Lean `Rat` values; `norm1` is the rational sum of coordinate
  absolute values. No real or complex type is used.
- `Poly` is an array of `GQ`; `coeff` returns zero outside its stored range.
- `Term` stores two natural exponents and one Gaussian-rational coefficient.
  `Bivariate` is a finite array of these terms.
- `polyMul K`, `polyPow K`, `shiftScale K`, and `substitute K` keep coefficients
  only through degree `K`.
- `iterate K q n` performs `n` substitutions starting from zero.
- `branchCoeff q k` takes coefficient `k` after `k` iterations with cutoff `k`.
- `partialSum q K` uses cutoff and iteration count `K`.
- `weightedNorm r u` sums `norm1 (coeff u k) * r^k` over the finite array.
- `admissible D B q` says `D >= 2`, `B >= 1`, the coefficient norm sum is at
  most `B`, degrees are bounded by `D`, and terms at positions `(0,0)` and
  `(0,1)` are zero.

The sparse-array representation permits repeated exponents. This causes no
problem for the finite majorant and stabilization targets: the sum of term
norms bounds the norm of the combined coefficient. For the name-perturbation
theorem, use a fixed dense array of `(D+1)^2` positions, or use the actual
finite array length as the parameter `m` and require the exponent array to be
the same at every precision.

## Main finite lemmas and dependency order

1. **Gaussian-rational arithmetic.** Prove additive identities, distributivity,
   the triangle inequality, and `norm1 (mul a b) <= norm1 a * norm1 b` by
   coordinate expansion and rational inequalities. Arithmetic proofs may use
   Lean's rational ordered-ring interface at the metalevel. For an iPRA proof,
   separately replace `Rat` by signed integer pairs with a positive denominator
   and use denominator-cleared versions of those lemmas.

2. **Truncation correctness.** Prove that addition, multiplication, powers, and
   bivariate substitution preserve the coefficients at indices `k <= K` when
   compared with an untruncated finite expression. Use finite convolution, not
   an appeal to formal power-series completeness.

3. **Weighted norm inequalities.** Show that truncation cannot increase the
   norm, and prove the addition/product inequalities by finite double-sum
   expansion. Prove the difference-of-powers factorization.

4. **Finite contraction.** Define `s=1/(4DB)` and `r=1/(16DB^2)`. For all
   finite polynomial arrays with norm at most `s`, show that substitution has
   Lipschitz constant `1/4` and maps the ball into the ball of radius `s/2`.
   Fill `KernelGoals.invariant` by natural-number induction. In the eventual
   object proof, the invariant is a rational comparison and finite-array
   well-formedness check.

5. **Order of vanishing.** Define

   ```lean
   def VanishesBelow (u : Poly) (n : Nat) : Prop :=
     forall k, k < n -> coeff u k = zero
   ```

   For the arithmetic translation, replace this display by a primitive
   recursive Boolean fold over `List.range n`. Prove equivalence of the fold
   and the bounded proposition externally. Show that zero-constant `u,v`
   with difference vanishing below `n` have substitution difference vanishing
   below `n+1`. This fills `KernelGoals.stable` and `residualLow` after the
   truncation lemmas. No integral-domain argument is needed.

6. **Full residual.** For `S_K`, construct the *untruncated* array
   `Q(X,S_K)-S_K`, with an explicit bound such as `D*(K+1)` on the degree.
   Its coefficients through degree `K` vanish and its weighted norm is at
   most `2s`. Do not mistake a zero residual in the truncated quotient for
   equality of the full polynomial. Evaluation on `norm1 x <= r/2` gives
   the bound `s*2^(-K)`; the finite series tail is at most
   `s*2^(-(K+1))`.

7. **Perturbation.** For two coefficient arrays with entrywise difference at
   most `delta`, prove `E_(n+1) <= E_n/4 + m*delta`, hence
   `E_n <= 2*m*delta`. Prove the polynomial-evaluation Lipschitz bound `s/r`
   on the disk of radius `r/2`. These proofs give explicit, iteration-independent
   precision loss.

## Named coefficient and root targets

Represent a Gaussian-rational name by a function `Nat -> GQ` in the Lean
metalanguage. Its regularity proposition is

```lean
forall p q, norm1 (sub (a p) (a q)) <= dyadic p + dyadic q
```

This host-level function is a fixed schematic parameter. Its object-language
instance must come from a specified primitive recursive evaluator term; do
not quantify over codes for all primitive recursive programs and add a
universal total evaluator.

For a regular dense coefficient family `q(i,j,p)`, require the two excluded
positions to be literally zero. Obtain a uniform rational `B` from the
precision-zero data using formula (A11). Define `lambda(u)` by bounded search
for a power of two at least `max(1,u)`. Define:

- `C(k,n)` by coefficient `k` after `k` substitutions at input precision
  `n + lambda(2*m*r^(-k)) + 2`;
- `T_K(p)` by evaluating the degree-`K` truncation after `K` substitutions
  at the rational point `x(p)`;
- `Y(n)` by formula (A15), using `K=n+3` and
  `p=n+lambda(2*m+s/r+1)+3`.

Prove regularity of `C(k,.)` by the perturbation inequality and regularity of
`Y` by comparing two finite expressions with a common coefficient precision.
This is a direct rational proof and needs no completion type. Theorem (A19a)
supplies the final residual cutoff for the original polynomial.

## Separation and normalization targets

The inverse constructor takes a coordinate and an index `t` with
`abs (coordinate (d t)) >= 4*dyadic t`. Prove denominators are bounded below
at every precision `p >= t+2`; implement formula (A17). This is a bounded
calculation, not a search until a nonzero approximation appears.

Normalize the original polynomial by a finite binomial expansion of
`Z - d^(-1)*P(X,y0+Z)`. The two zero entries are written as zeros because
the supplied root equation and derivative definition prove those identities.
This is proof-directed rewriting, not a decision procedure for exact
equality of names. Iterated addition/product precision schedules are given
explicitly in the chapter. Prove the normalization identity at each requested
precision from the supplied root and inverse certificates.

## Object-language integration

The final integration should produce a derivation in the repository's
`Prf PRAAx` type of each finite contract, after instantiating the fixed
primitive recursive evaluator symbols. In particular:

1. Supply PR representations and correctness lemmas for rational encodings,
   finite arrays, the bounded loops, and `lambda`.
2. Translate the finite rational invariants into quantifier-free formulas.
   Prefix properties become finite Boolean folds over computed bounds.
3. Build the iPRA derivation for each finite induction argument and for the
   primitive recursive schedules.
4. Invoke universally quantified input contracts only at explicit numerical
   arguments, then universally close the final target.
5. Transport the resulting derivation through the actual ConciseIPRA bridge.

A theorem in Lean about arbitrary complex power series is useful as an
independent semantic check; it cannot replace steps 1--5. None of those
object-language obligations is claimed completed by this executable file.
