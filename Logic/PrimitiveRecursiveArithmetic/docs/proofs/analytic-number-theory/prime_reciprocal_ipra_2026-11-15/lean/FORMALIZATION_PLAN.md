# Lean formalization plan

This plan targets the ProveIt root workspace at commit
`0e834f7851375f4b22ae8892000495cb6fa9eee8` and its `ConciseIPRA` library.
The accompanying `PrimeReciprocalIPRA.lean` is a signature scaffold with
`sorry` placeholders. It is not claimed to be a completed kernel-checked
proof.

## 1. Recommended file split

1. `PrimeReciprocal/Defs.lean`
   - finite prime set;
   - `primeProduct`, `primeNumerator`, `eulerDenominator`;
   - `harmonicNumerator`, `witness`;
   - positivity, divisibility, and rational-denominator lemmas.
2. `PrimeReciprocal/FactorTrace.lean`
   - bounded least divisor;
   - fuelled quotient trace;
   - primality of selected divisors;
   - reconstruction and exponent-vector injectivity.
3. `PrimeReciprocal/Euler.lean`
   - finite product expansion;
   - finite geometric bound;
   - `harmonicLeEulerCross`.
4. `PrimeReciprocal/LocalFactor.lean`
   - factorial lower bound;
   - binomial estimate;
   - `localFactorBound`.
5. `PrimeReciprocal/ProductControl.lean`
   - `eulerPowerBound`;
   - power monotonicity/cancellation;
   - harmonic upper bound from a prime-sum upper bound.
6. `PrimeReciprocal/Dyadic.lean`
   - interval block cardinalities;
   - reciprocal lower bound inside each block;
   - `dyadicHarmonicLower`.
7. `PrimeReciprocal/Main.lean`
   - `quantitativeDivergenceNat`;
   - rational and existential corollaries.
8. `PrimeReciprocal/IPRA/PRCodes.lean`
   - `PR` codes for Boolean arithmetic, bounded folds, quotient/remainder,
     vector digits, primality, and all theorem functions.
9. `PrimeReciprocal/IPRA/Proof.lean`
   - syntactic `PRAAx` derivations using only `PRA.qfInd` for induction.
10. `PrimeReciprocal/IPRA/Scalar.lean`
    - transfer with `FromPRA.interp.sound`.

## 2. Semantic layer proof obligations

### Definitions and denominators

- `prime_dvd_primeProduct`
- `primeProduct_pos`
- `eulerDenominator_pos`
- `factorial_pos`
- exact division lemmas for `primeProduct n / p` and `factorial n / m`
- `primeReciprocalSum_eq`
- `harmonicSum_eq`
- `eulerProduct_eq`

### Factorization

The implementation closest to the iPRA proof is preferable:

```lean
def leastDiv (x : Nat) : Nat := ...
def factorStep (x : Nat) : Nat := if x <= 1 then 1 else x / leastDiv x
def factorTrace (m i : Nat) : Nat := Nat.iterate factorStep i m
```

Required lemmas:

- `leastDiv_dvd` for `1 < x`;
- `leastDiv_prime` for `1 < x`;
- `factorStep_lt` for `1 < x`;
- `factorTrace_eq_one` by time `m`;
- a product invariant reconstructing `m` from selected factors;
- exponent count bounds;
- injectivity of the exponent-vector code.

The semantic prototype may instead use `Nat.factorization`, but the explicit
trace should eventually be proved because it internalizes directly.

### Euler domination

Prove a finite injection from `Finset.Icc 1 n` into exponent-vector indices.
The cleanest denominator-free statement is:

```lean
theorem harmonicLeEulerCross (n : Nat) :
  harmonicNumerator n * eulerDenominator n <=
    Nat.factorial n * primeProduct n
```

Suggested intermediate objects:

- `truncatedGeom p n : Rat := sum e in range (n+1), 1 / p^e`
- `truncatedEuler n : Rat := product p in primesUpTo n, truncatedGeom p n`
- `harmonic_le_truncatedEuler`
- `truncatedGeom_le_factor`

Then clear denominators once, and use the integer theorem downstream.

### Local factor

Prove:

```lean
theorem factorial_ge_pow_two (j : Nat) (hj : 1 <= j) :
  2^(j-1) <= j.factorial

theorem binomialThreeBound (a : Nat) (ha : 1 <= a) :
  (a+1)^a <= 3*a^a

theorem localFactorBound (p : Nat) (hp : 2 <= p) :
  p^p <= 4*(p-1)^p
```

The first version can be rational and then denominator-cleared. For the iPRA
layer, keep an integer proof with explicit powers of two.

### Product control

For every selected prime `p`, show `p | primeProduct n`; rewrite the exponent
`primeProduct n` as `p * (primeProduct n / p)`. Multiplying the local bounds
must yield exactly:

```lean
primeProduct n ^ primeProduct n <=
  4 ^ primeNumerator n * eulerDenominator n ^ primeProduct n
```

Then prove strict monotonicity of `x |-> x^d` for positive `d`, and derive:

```lean
primeNumerator n <= k * primeProduct n ->
primeProduct n <= 4^k * eulerDenominator n
```

### Dyadic harmonic lower bound

Partition `Finset.Icc 1 (2^(2*t))` into the initial singleton and blocks
`Ioc (2^j) (2^(j+1))`. Prove each block has cardinality `2^j`, each term is at
least `1 / 2^(j+1)`, and therefore each block contributes at least `1/2`.
For the integer theorem, clear the common factorial denominator.

### Main theorem

Set `t = 4^k` and `n = 2^(2*t)`. A hypothesis

```lean
primeNumerator n <= k * primeProduct n
```

gives `harmonicNumerator n <= t * n.factorial`; the dyadic theorem gives
`(1+t) * n.factorial <= harmonicNumerator n`. Contradict positivity of the
factorial. Decidable natural order converts `not (<=)` into `<`.

## 3. Internalization in `PRAAx`

### 3.1 Boolean formulas

Do not leave bounded quantifiers in induction matrices. Use 0/1-valued
primitive recursive functions:

- `eqB`, `ltB`, `leB`, `dvdB`, `primeB`;
- `allLe f n = product i<=n f(i)`;
- `anyLe f n = sign (sum i<=n f(i))`.

The target body is an equality `ltB(...) = 1`, hence quantifier-free.

### 3.2 Sequence coding

Encode a vector of length `n-1` with digits at most `n` in base `n+1`.
Digit extraction is `(code / base^i) % base`. All operations are primitive
recursive. The factor-trace invariant and reconstruction can then be stated
as equations over coded sequences.

### 3.3 Induction discipline

Every use of induction must be visibly routed through `PRA.qfInd` from
`ConciseIPRA.PR`. In particular:

- trace termination: induction on fuel;
- reconstruction: induction on trace length;
- bounded sums/products: induction on upper bound;
- binomial theorem: induction on row or exponent;
- power monotonicity: induction on exponent;
- dyadic blocks: induction on block count.

No semantic completeness or reflection theorem should be used to infer a
`PRAAx` derivation merely from a Mathlib theorem about `Nat`.

## 4. Transfer to the concise scalar core

`ConciseIPRA.PRAToScalar` already supplies:

- `FromPRA.code : PR k -> Tm k`;
- the term/formula morphism;
- proofs that all `PRAAx` axioms map to `TeqAx` theorems;
- `FromPRA.interp : Interp PRAAx TeqAx`.

After constructing

```lean
theorem primeReciprocalDivergencePRA :
  ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.all targetBody := by
  ...
```

the scalar result is:

```lean
def primeReciprocalDivergenceTeq :=
  FromPRA.interp.sound primeReciprocalDivergencePRA
```

## 5. Completion criterion

The formalization is complete only when:

1. all `sorry` declarations are gone;
2. `lake build ConciseIPRA` succeeds in the pinned root workspace;
3. the final theorem is a derivation in `PRAAx`, not only a semantic theorem;
4. the translated `TeqAx` theorem type-checks through `Interp.sound`;
5. an audit confirms every induction matrix is `Fm.QF`.
