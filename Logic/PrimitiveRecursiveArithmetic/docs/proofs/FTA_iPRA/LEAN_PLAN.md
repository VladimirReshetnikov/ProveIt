# Lean formalization plan

**Status:** `lean/Specification.lean` is an **uncompiled specification and proof
outline**. No Lean executable was available. It defines finite rational
specifications, explicit object-language formulas, and types of derivation
certificates. No certificate is supplied, and no FTA theorem is postulated.
The article contains the complete non-formalized argument.

## 1. The full constructive target

The input is a finite tuple of Gaussian-rational coefficient names
a_i(s), 0<=i<=n, satisfying

```text
|a_i(s)-a_i(t)| <= 2^(-s)+2^(-t),
```

together with integers 1<=k<=n and h satisfying the finite comparison

```text
N(a_k(h+2)) >= 2^(-2h).
```

Here N(x+iy)=x²+y². The index n is an upper degree. Higher coefficients may
have undecidable equality to zero; monicity and a decidable leading
coefficient are unnecessary.

The output is a specific primitive-recursive rational name alpha. For all
t and u>=t,

```text
N(alpha(u)-alpha(t)) <= (2^(-t-2))².
```

With S(t)=J(t)+L, the arithmetic root specification is

```text
N(sum_(i=0)^n a_i(S(t))*alpha(t)^i) <= (2^(-t-2))²,
s>=S(t) -> N(sum_(i=0)^n a_i(s)*alpha(t)^i) <= (2^(-t))².
```

There is also a uniform radius bound N(alpha(t))<=R². The second residual
statement makes the root identity explicit under every later coefficient
sample, without quantifying over a completed complex field.

## 2. Existing repository interface

Use ProveIt commit `b03925cccc76d55b9dc2a00864a5e0544b64aa7f`,
Lean/mathlib `v4.32.0`. The existing Lake library `ConciseIPRA` uses
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean`.

Minimum object-theory dependencies:

```text
ConciseIPRA.Syntax -> ConciseIPRA.Deduction -> ConciseIPRA.PR
```

Namespace: `LeanProofs.ConciseIPRA`. The actual endpoint is

```lean
Prf PRAAx [] (ftaSentence arithmeticCodes inputProgram outputProgram)
```

The blueprint constructs `ftaSentence` explicitly from the repository's
`Fm.eq`, `Fm.and`, `Fm.imp`, and `Fm.all` constructors. Its formulas
state the coefficient Cauchy assumption, the finite apartness witness, the
two residual inequalities, the Cauchy bound, and the radius bound.

The program/code structures are interfaces to implement, not mathematical
hypotheses granted without proof. Their interpretation must be proved
before their derivation certificates mean the FTA.

An ordinary Lean theorem about `Nat`, `Rat`, or `Complex` is not this
endpoint. After the endpoint is constructed, the existing
`pra_iff_native` in `ConciseIPRA.NativeBiInterpretation` optionally
transfers it to the native concise calculus.

## 3. Constants and the finite invariant

All constants are computed before the main iteration:

```text
B = 2 + ceil(|Re a_0(0)| + |Im a_0(0)|)
D = 2^n * 4^(2n²)
q = 1 - 1/(4D)
Q = 1 - 1/(8D)
K = 8nD
rho = 1 - 1/K
C = Bn * 2^(n+h+1)

choose A0 with 2^A0 >= 2CK
T = K A0
R = 2(1+C)^T

choose L>=h+2 with 2^L >= 16D(n+1)R^n
P_j(X) = sum_(i=0)^n a_i(j+L) X^i
z_0 = 0
z_(j+1) = z_j + rationalDescent(P_j,z_j)

U_0 = 1
U_(j+1) = U_j(1+C rho^j)
```

One can use bitLength for A0 and H and a bounded search for L. The code and
proof must agree on the convention for bitLength; only the stated upper
power-of-two inequalities are required.

The invariant, entirely about finite rational values, is

```text
N(P_j(z_j)) <= (B Q^j)²
N(z_j)     <= (U_j-1)²
N(w_j)     <= (U_j C rho^j)²
1 <= U_j <= R.
```

The proof of U_j<=R splits the product at T. Its finite tail sum is <=1/2,
and the finite product estimate product(1+x_i)<=1/(1-sum x_i) bounds the
tail by 2. There is no infinite product.

Choose H with 2^H>=RCK and put J(t)=K(t+H+2), alpha(t)=z_(J(t)).
The finite inequality rho^K<=1/2 yields the Cauchy and residual bounds.

## 4. Key exact local lemmas

### Rational descent with a radius certificate

For nonconstant rational P of upper degree n, translate P at z to
b_0+...+b_n X^n. The routine returns a step w and rational r0>=0 such that

```text
N(P(z+w)) <= q² N(P(z))
N(w) <= r0²
1<=i<=n -> N(b_i) r0^(2i) <= N(b_0).
```

If b_0=0, return w=r0=0. Otherwise let b>=1 be the largest binary digit
count of the absolute numerators and positive denominators of every
component of every b_i, and set E=2b+3. Search for the largest integer
e in [-E,E] with max_i N(b_i)*2^(2ei)<=N(b_0), and set r0=2^e.
The two endpoint inequalities are strict, so the next exponent crosses
the target. A scan has 2E+1 entries; bounded binary search is also valid.
No unbounded termination argument is needed.

### Translation estimate

If 1<=k<=n and U>=1 with N(z)<=(U-1)², prove

```text
N(p_k) <= (n2^n)² * max_(1<=i<=n) [N(b_i) U^(2i)].
```

Use the inverse translation identity and finite Cauchy-Schwarz, followed
by binomial coefficient bounds. This is the replacement for the monic
step-size bound, and is what permits the full positive-nonconstancy theorem.

### Finite table formulation

For a finite horizon m, the table contains a_i(0), a_i(h+2), and
a_i(L+j) for j<=m. A Boolean predicate checks:

- the apartness witness at h+2;
- each row's comparison with the apartness anchor, giving the lower bound
  |a_k(L+j)|>=2^(-h-1);
- the base comparison at precision 0;
- adjacent coefficient comparisons used for perturbation estimates.

All comparisons are squared rational comparisons. A bounded Boolean fold
checks all required indices. Its induction matrix is a quantifier-free
equation to 1; it is not a quantified “Cauchy real” predicate.

The finite-table theorem is the central object-theory result. The fixed-name
schema follows by generating the needed table from the fixed PR coefficient
program and applying that theorem at the requested horizon.

## 5. Module sequence

| Module | Required result and implementation strategy |
|---|---|
| `GaussianCode` | Encode signed integers, positive-denominator rationals, Gaussian pairs, finite tuples; prove coded arithmetic, rational order, N(zw)=N(z)N(w), and rational-upper-bound triangle estimates. |
| `FinitePrograms` | Construct `PR` syntax for powers, sums, products, maxima, bounded least witnesses, Boolean folds and bisection. Use `PR.comp`, `PR.prec`, `PRA.precZero`, `PRA.precSucc`, and `PRA.qfInd`. |
| `SqrtBisection` | Prove the rational squared-bracketing invariant and width bound for fixed-length bisection on [0,1] and [1,2]. No executable real square-root operation. |
| `FiniteBinomial` | For c_0=1, c_(j+1)=c_j(1/k-j)/(j+1), prove |c_j|<=1; coefficient cancellation in P_N(T)^k-(1+T) through degree N; and a finite weighted coefficient majorant. |
| `Direction` | Combine three algebraic half-angle constructions and the finite binomial polynomial. Verify bounded bisection and finite polynomial bounds to obtain a rational direction with norm<=1 and 1/16 accuracy. Intermediate radical notation is eliminated by finite interval estimates. |
| `Plateau` | Translate P, run the bounded radius search, prove the maximizing indices decrease, and find an equal triple among 2n+1 indices. Derive the off-dominant sum bound and U>|P(z)|/D. |
| `Descent` | Prove the local contraction and radius-certificate inequalities. Keep executable direction accuracy 1/16 and use 1/12 in the descent proof for slack. |
| `TranslatedCoefficient` | Prove the squared inverse-translation estimate above, and derive |w_j|<=U_j C rho^j without computing an nth root. |
| `ProductBound` | Internalize finite Bernoulli, geometric sums, the finite product estimate, and U_j<=R. |
| `TableIteration` | Construct the finite trajectory by primitive recursion and build the quantifier-free induction proof of the full invariant. |
| `BlockModulus` | Prove rho^n>=Q, rho^K<=1/2, and the explicit sampled Cauchy/residual bounds, including later coefficient samples. |
| `NameCompiler` | Compile each fixed PR coefficient syntax tree to coefficient tables, trajectory, constants, sampled root, and polynomial evaluator. Prove the defining equations. There is no PR universal evaluator. |
| `ObjectFTA` | Instantiate the explicit formula builders and construct `Prf PRAAx [] (ftaSentence ...)`. |
| `Evaluation` | Use finite polynomial telescoping and the radius bound to identify the arithmetic residual statement with the Cauchy-name equation p(alpha)=0. |
| `RationalInput` | Specialize the coefficient program to constant names from a finite polynomial code. Establish valid code -> input hypothesis and obtain one degree-uniform first-order theorem. |
| `Factorization` | For monic or apart-leading known degree, use exact synthetic division and repeat the root theorem. Each fixed degree gives finitely many PR compositions; a uniform all-roots algorithm needs an explicit majorant for nested precision requests. |

## 6. What the blueprint already specifies

`Specification.lean` provides:

- readable Gaussian-rational specifications, using only squared norms;
- the general local descent contract with a radius certificate;
- all principal constants and sampling arithmetic;
- `FixedCoefficientProgram`, whose numerical selectors can include n,k,h
  among its ordinary parameters;
- `CompiledNameProgram`, including the later-sample polynomial evaluator;
- explicit object formulas for every input and output condition;
- the actual object-derivation endpoint types;
- a rational-input specialization whose coefficient-name program ignores
  the precision argument by a literal `PR.comp` construction.

The arithmetic comparison codes and the compiler are to be implemented.
They are not postulated correct or already completed. The blueprint contains
no arbitrary placeholder FTA formula: the intended formula's structure is
written explicitly.

## 7. Representation and trusted-boundary obligations

Completion requires:

1. Proved correctness of every rational-code operation.
2. Proved correctness of every PR Boolean predicate.
3. Proved equations for the compiled coefficient and root programs.
4. Verification that the formula builders use the correct de Bruijn indices.
5. An object-theory derivation assembled from the permitted constructors.

A proof that the same statement holds in the standard model does not
discharge item 5. No semantic reflection principle may be introduced.

Retain the unbounded coefficient-name assumptions in the context. At each
finite horizon, derive the finite table assumptions, and perform induction
only on Boolean-coded finite rational invariants. Do not use induction on
a formula containing the universal name condition.

## 8. Completion gates

1. Compile the interface against the pinned repository and fix any API drift.
2. Implement the encodings and compare exact arithmetic examples against the
   supplied Python direction subroutine.
3. Finish the local descent and translated-coefficient internal lemmas.
4. Finish the finite-table derivation before constructing field quotients.
5. Assemble the fixed-program schema and rational-input specialization.
6. Inspect the final theorem type and run `#print axioms`.
7. Rebuild the complete declared dependency closure from the pinned sources.

Standard Lean metatheoretic axioms in the construction of an object
derivation do not become axioms of iPRA. Conversely a small axiom report
on a mathlib complex-analysis theorem is not an iPRA audit.

## 9. Scope that remains deliberate

Positive information that some nonconstant coefficient is apart from zero
is required. The proof does not replace this by merely negated equality.

For arbitrary PR coefficient functions, the result is a first-order theorem
schema after fixing the coefficient program. Its finite-table theorem and
finite rational-input specialization are ordinary first-order statements.
No function quantification or higher-type recursor is silently added.

This package does not claim a completed Lean formalization.

