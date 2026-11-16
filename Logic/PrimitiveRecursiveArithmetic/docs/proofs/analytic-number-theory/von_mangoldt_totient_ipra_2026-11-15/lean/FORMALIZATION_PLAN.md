# Lean formalization plan

## 1. Goal and trust boundary

The final target is not merely a host theorem about `Nat`.  It is a derivation in the object theory

```lean
LeanProofs.ConciseIPRA.PRAAx
```

followed by faithful transfer to

```lean
LeanProofs.ConciseIPRA.TeqAx
```

through `pra_theorem_iff` from `ConciseIPRA.BiInterpretation`.

Mathlib theorems are used only for specification comparison and regression tests.  No completed theorem may be closed by importing `Nat.sum_totient` or `ArithmeticFunction.vonMangoldt_sum` and calling it an iPRA proof.

## 2. Existing repository lemmas to reuse

At ProveIt revision `5fb2ca5dda188a4a3c7ce9ba6f28030bd0fe8322`:

- `ConciseIPRA.PR`
  - `PR`, with constructors `zero`, `succ`, `proj`, `comp`, `prec`;
  - `PTm`;
  - `PRAAx`;
  - recursion equations `PRA.precZero`, `PRA.precSucc`;
  - quantifier-free induction `PRA.qfInd`.
- `ConciseIPRA.TeqRec`
  - `Tm.prc`;
  - `Q.prc_zero`, `Q.prc_succ`.
- `ConciseIPRA.Interpretation`
  - `Interp.sound` and formula translation lemmas.
- `ConciseIPRA.BiInterpretation`
  - `pra_theorem_iff`, `teq_theorem_iff`;
  - `pra_roundTrip`, `teq_roundTrip`.

The recommended proof language is ordinary `PRAAx`.  Transfer the closed result at the end.

## 3. Representation choices

### 3.1 Booleans

Use naturals `0,1`.  Every predicate has a characteristic PR function and a normalization theorem:

```lean
isBool (P x) = 1
```

or, more conveniently, a theorem that its value is either zero or one and equations connecting value one with the intended formula.

Required Booleans:

- `eqB`, `ltB`, `leB`, `zeroB`;
- `dvdB`, `coprimeB`, `primeB`, `primePowB`;
- `squarefreeB`, `divisorB`.

### 3.2 Signed integers

Use pairs `(pos, neg)` with interpretation `pos - neg`.  Equality is cross addition:

```text
(pos1 + neg2) = (pos2 + neg1).
```

Normalize only when convenient; universal theorems should not depend on canonical normalization.

### 3.3 Rationals

Use `(num, den)` with a proof/Boolean invariant `den > 0`.  Equality and order are cross-multiplied.  The object theory never needs quotient types.

### 3.4 Finite arrays and polynomials

Use a base-`B` code with a proved digit bound, or nested pairing.  For the first implementation, base coding is simpler:

```text
digit(code, B, i) = (code / B^i) % B.
```

Polynomial equality is coefficient equality up to an explicit degree bound.  Signed coefficients use signed pairs.

## 4. Foundational module sequence

### Stage A: bounded folds

File: `IPRA/BoundedFold.lean`

Definitions:

```lean
bsum    : PR (k+1) -> PR (k+1)
bprod   : PR (k+1) -> PR (k+1)
bcount  : PR (k+1) -> PR (k+1)
bmin    : PR (k+1) -> PR (k+1)
bmax    : PR (k+1) -> PR (k+1)
```

The last argument is the bound.  Prove zero/successor equations and generic induction/fusion lemmas.

Acceptance tests:

1. equations translate to `Tm.prc` through `FromPRA.sigma`;
2. no classical decision procedure is used in an object proof;
3. sum/product reindexing is proved for bounded rectangles and bounded divisor triangles.

### Stage B: division and gcd

File: `IPRA/Divisibility.lean`

Implement total division by bounded maximum, then remainder.  Define `dvdB`, `gcd`, `lcm` and a fuelled extended Euclidean trace.

Core theorems:

```text
x = (x / y) * y + x % y                 (y > 0)
x % y < y                               (y > 0)
gcd x y | x, gcd x y | y
d | x and d | y -> d | gcd x y
bezoutPos/bezoutNeg certificate
lcm x y * gcd x y = x*y                 (positive inputs)
```

All invariants should be quantifier-free equations/inequalities.

### Stage C: factorization

File: `IPRA/Factorization.lean`

Implement:

- least divisor `leastFactor`;
- `primeB`;
- valuation `vp` by bounded maximum;
- least-factor trace with fuel `n`;
- factor-vector code;
- `primePowB`, `ppBase`, `ppExp`.

Core theorems:

```text
leastFactor n is prime                       (n > 1)
trace reaches 1 by fuel n                    (n > 0)
reconstruct n = product p^(vp p n)
vp p (x*y) = vp p x + vp p y                 (positive x,y, p prime)
prime-power representation is unique
```

This module is the largest common dependency.  Finish it before defining either arithmetic function.

### Stage D: Mobius and finite convolution

Files: `IPRA/Mobius.lean`, `IPRA/DirichletConvolution.lean`

Define `mu : PR 1` in signed-pair form.  Prove the bit-vector expansion

```text
sum_{d|n} mu(d) = delta(n,1).
```

Then define finite convolution and prove identity, commutativity, associativity, and Mobius inversion.  Reindexing must be an explicit bijection between bounded triples `(a,b,c)` with `abc=n`.

## 5. Totient development

### 5.1 Basic definition and product formula

File: `IPRA/Totient/Basic.lean`

```text
phi(n) = bsum n (fun a => coprimeB a n)
```

Prove:

1. `phi 0 = 0`, `phi 1 = 1`;
2. prime and prime-power formulas by counting multiples;
3. a generic finite-bijection/cardinality lemma;
4. CRT map and inverse from the Bezout certificate;
5. multiplicativity;
6. product formula through the factor trace.

Suggested theorem formulas are equations of `PTm` applications, not host propositions about `Nat`.

### 5.2 Divisor identities

File: `IPRA/Totient/Divisor.lean`

Prove the map `a ↦ d*a` between coprime residues modulo `n/d` and the gcd-`d` fiber.  Sum fiber counts to obtain `sumPhi`.  Apply the generic Mobius inversion theorem.

For the summatory identity, define the coprime-pair count in two ways and prove the bounded sum swap.

### 5.3 Local-factor identities

File: `IPRA/Totient/Identities.lean`

Avoid repeating global combinatorial proofs.  Prove a generic lemma:

```text
if two multiplicative PR functions have equal local values on all p^a,
then they are equal on positive n.
```

Instantiate it for power, gcd/lcm, radical and general multiplication identities.  For divisibility, construct the quotient from exponent differences.

### 5.4 Units and applications

Files: `IPRA/Totient/Units.lean`, `IPRA/Totient/Applications.lean`

Represent reduced residues by a bounded Boolean.  A “permutation” is a PR map plus a PR inverse and bounded range equations.

Prove:

- negation pairing and evenness;
- totative sum;
- multiplication permutation and Euler theorem;
- least order and order divisibility;
- RSA by separate prime-modulus cases plus CRT;
- Menon through local CRT counts;
- `m | phi(a^m-1)`;
- `n | phi(a^n+b^n)`;
- Subbarao classification.

### 5.5 Bounds

File: `IPRA/Totient/Bounds.lean`

Never introduce a real square root.  State:

```text
2 * phi(n)^2 >= n
r^2 <= n < (r+1)^2 -> composite n -> phi(n) <= n-r
```

The limsup/liminf results should be theorem schemas producing explicit witnesses.  Reuse the finite factorization/Euler-product proof from the existing `prime_reciprocal_ipra_2026-11-15` package after porting its helper lemmas to `PRAAx`.

## 6. Mangoldt development

### 6.1 Parameterized weights

File: `IPRA/Mangoldt/Basic.lean`

The object theory cannot quantify over PR symbols internally.  There are two implementation options:

1. **Meta-parameterized module:** Lean takes `w : PR 1` and builds `Lw w`, `lambdaW w`, plus derivations assuming explicit weight-domain equations.
2. **Compiler theorem:** define a code for PR functions and an evaluator.  This is more general but much larger.

Use option 1 initially.

Definitions:

```text
Lw(w,n)      = sum_{p<=n} primeB(p) * vp(p,n) * w(p)
lambdaW(w,n) = if primePowB(n) then w(ppBase(n)) else 0
psiW(w,N)    = sum_{n<=N} lambdaW(w,n)
```

Prove complete additivity of `Lw`, then the divisor sum by enumerating prime powers in the divisor list.

### 6.2 Convolution and lcm

Files: `IPRA/Mangoldt/Convolution.lean`, `IPRA/Mangoldt/Lcm.lean`

Instantiate Mobius inversion for all standard formulas.  Define `lcmUpto` by a bounded fold, prove its valuation is the maximum exponent, and derive the quotient and `psiW` identities.

### 6.3 Formal series

File: `IPRA/FormalSeries.lean`

Do not formalize completed infinite series.  Define only coefficient extraction up to an input index `N`.  For ordinary formal power series, a coefficient uses a bounded sum.  For Dirichlet series, multiplication is finite divisor convolution.

Targets:

- Lambert coefficient identity;
- `phi = id * mu`;
- weighted derivation Leibniz rule;
- `lambdaW = mu * Lw`;
- rational prime-power coefficient `H(p^a)=1/a` and `D_w H=lambdaW`.

### 6.4 Binomial bounds

File: `IPRA/Mangoldt/Bounds.lean`

Develop factorial valuation and Legendre's formula by counting multiples of powers.  Prove each floor difference is Boolean.  This yields both divisibilities in the report.  Keep logarithms out of the object theorem; add a later rational-log interval layer if desired.

## 7. Transfer endpoint

File: `IPRA/Transfer.lean`

For each closed or universally closed formula `phi : Fm PTm n`:

```lean
have hPRA : ([] : List (Fm PTm n)) ⊢[PRAAx] phi := ...
have hTeq : ([] : List (Fm Tm n)) ⊢[TeqAx]
    phi.map (fun _ => FromPRA.sigma) :=
  (pra_theorem_iff phi).mp hPRA
```

Record both theorem names.  This makes the ordinary iPRA proof and its concise-calculus translation separately inspectable.

## 8. Host comparison layer

`VonMangoldtTotientHost.lean` imports current mathlib files and records exact theorem names.  It should eventually prove that the executable PR definitions evaluated in the standard natural model agree with:

- `Nat.totient`;
- `ArithmeticFunction.vonMangoldt` after logarithmic interpretation;
- `Nat.lcmUpto` and `Chebyshev.psi` where applicable.

This layer is a semantics/regression bridge, not part of the object derivation.

## 9. Milestones and acceptance criteria

1. **M0 - infrastructure:** bounded folds, division, gcd, signed pairs compile without `sorry`.
2. **M1 - factorization:** reconstruction and valuation uniqueness compile.
3. **M2 - basic totient:** prime powers, CRT, product formula, divisor sum compile.
4. **M3 - complete elementary totient:** identities, Euler, Menon, bounds compile.
5. **M4 - weighted Mangoldt:** divisor and Mobius identities, lcm quotient, `psiW` compile.
6. **M5 - formal coefficient layer:** Lambert, Dirichlet and cyclotomic remainder theorems compile.
7. **M6 - applications:** RSA, Subbarao, plus-power theorem, finite extremal witnesses compile.
8. **M7 - transfer audit:** every advertised I/F theorem has a `PRAAx` theorem and a `TeqAx` transfer theorem.
9. **M8 - axiom audit:** run `#print axioms` on host wrappers; object proofs contain no new axioms, `sorryAx`, classical choice, or imported analytic theorem standing in for the finite argument.

## 10. Estimated proof-risk areas

- Polynomial/cyclotomic encoding is mechanically large but conceptually routine.
- Generic finite bijection/cardinality infrastructure will save substantial duplication.
- The finite Euler-product liminf witness should be ported from the existing ProveIt package rather than reproved ad hoc.
- Rational logarithm enclosures are independent of the arithmetic core and should be a final optional layer.
- The current archive's `.lean` files contain declarations/placeholders; they are not the milestone-M0 implementation.
