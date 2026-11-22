# PA Statement of the Riemann Hypothesis

- Created (UTC): 2026-07-09T02:52:30Z
- Repository HEAD: f85dee4a19d270bd81c69db3145c1a29e8edef82

## Objective

Formalize, in Lean, a concrete sentence of first-order Peano arithmetic whose
standard interpretation is a known number-theoretic equivalent of the Riemann
Hypothesis.  The current goal is the statement only, not the proof of
equivalence with the analytic RH.

The implemented sentence is in
[`Lean/RiemannHypothesis/PAStatement.lean`](../Lean/RiemannHypothesis/PAStatement.lean).
It reuses the existing PA syntax from `SetTheory.PAHF.PASyntax`.

## Candidate Comparison

### Mertens/Littlewood Growth Criterion

Chosen statement:

```text
for every q > 0, there exists C such that for every n,
  |M(n)|^(2*q) <= C * n^(q+1),
```

where `M(n) = sum_{k <= n} mu(k)` is the Mertens function.

This is the integer-power form of the classical criterion
`M(n) = O(n^(1/2 + epsilon))` for every `epsilon > 0`.  For a given `q`, it
uses `epsilon = 1/(2*q)`, then raises both sides to the natural-number power
`2*q`.  Conversely, any real `epsilon > 0` is larger than `1/(2*q)` for some
positive natural `q`, so the integer-power family recovers the usual
all-positive-epsilon form.

Why this is the best first target:

- The final statement is purely arithmetical: natural-number quantifiers,
  addition, multiplication, order, divisibility, finite sequence coding, and
  bounded counting.
- The existing PA infrastructure already has order, divisibility, remainder,
  and Gödel beta-sequence formula macros, plus standard-model semantic lemmas
  for many of them.
- The future equivalence proof can follow the standard analytic route through
  the Dirichlet series `1/zeta(s) = sum mu(n)/n^s`; the PA-formalization layer
  is not entangled with exact real-computation predicates.

Reference status: this is Littlewood's Mertens-function criterion for RH.
The original source is Littlewood (1912); a modern paper by Lewis quotes the
same theorem explicitly and points to Edwards's later detailed proof.

### Lagarias / OEIS A057641, A079526, A306348

Lagarias proves RH equivalent to

```text
sigma(n) <= H_n + exp(H_n) * log(H_n)
```

for all positive `n`, with the usual equality exception at `n = 1`.  The OEIS
sequences Vladimir cited are variants around the same expression:

- `A057641`: `floor(H_n + exp(H_n)*log(H_n)) - sigma(n)`, nonnegative for all
  `n` iff RH.
- `A079526`: `floor(exp(H_n)*log(H_n)) - sigma(n)`, positive for `n > 60` iff
  RH according to the OEIS comment.
- `A306348`: exceptional `k` with `exp(H_k)*log(H_k) <= sigma(k)`, finite with
  no further terms if RH is true.

These are mathematically elementary and aesthetically excellent, but not the
least expensive PA target.  To make them literal PA sentences, Lean must encode
exact comparison of `exp(r)*log(r)` at rational harmonic values, or exact floor
predicates for that expression.  That means formalizing computable-real
approximations, error bounds for `exp` and `log`, and enough monotonicity to
certify floor/comparison decisions.  This is feasible, but it is a substantial
real-analysis arithmetization layer before the RH statement itself becomes
simple.

### Robin and the Caveney-Nicolas-Sondow Reformulation

Robin's criterion uses

```text
sigma(n) < exp(gamma) * n * log(log n)    for n > 5040.
```

The Caveney-Nicolas-Sondow paper at arXiv:1110.5078 gives another elementary
reformulation using `G(n) = sigma(n)/(n log log n)` and a condition over prime
factors and multiples of a composite number.

These are less attractive for a first PA formalization than Lagarias:
Euler's constant and `log log` comparisons introduce exact real constants and
transcendental approximation predicates, while the Caveney-Nicolas-Sondow
condition also adds a more complicated global extremality shape over multiples.

### Farey / Franel-Landau Criteria

The Farey-sequence regularity criteria are genuinely arithmetical after
clearing denominators: they involve finite rational sequences, Euler's totient,
absolute deviations, and big-O bounds.  They avoid `exp`, `log`, and special
constants.

They are a plausible second target, but the PA statement is structurally larger
than the Mertens one: it needs an exact definition of the sorted Farey sequence
or an equivalent enumeration, totient counts, and a finite absolute-deviation
sum.  The analytic equivalence proof is also less directly aligned with the
existing PA/HF machinery than the Möbius/Mertens route.

### Redheffer Determinant

The determinant of the Redheffer matrix equals `M(n)`, so RH can be expressed
as a determinant-growth statement.  This is arithmetical, but it adds finite
matrix and determinant coding only to arrive back at the Mertens function.  It
is better as a later bridge theorem than as the primary PA statement.

## Implemented Lean Surface

The module defines:

- `notF`, `dvdTermAt`, `evenTermAt`, `oddTermAt`, `primeTermAt`,
  `squarefreeTermAt`;
- `completePrimeFactorizationTraceAt`, using Gödel beta coding to represent a
  complete prime-factor trace;
- `mobiusPositiveTermAt` and `mobiusNegativeTermAt`, defining `mu(n)=+1` and
  `mu(n)=-1` as squarefree factorization-parity predicates;
- `mertensCountsTraceAt`, beta-coding the two cumulative counts of positive
  and negative Möbius values up to `n`;
- `powTraceAt` and `powRelAt`, beta-coding exponentiation by a natural
  exponent;
- `mertensRiemannHypothesisBody`, the readable quantified criterion;
- `mertensRiemannHypothesisSentence`, the sealed PA sentence;
- `mertensRiemannHypothesisSentence_sentence`, proving syntactically that the
  exported formula is a PA sentence.

The implementation deliberately stays in the standalone, mathlib-free
`SetTheory` Lean workspace.  That keeps it aligned with the existing PA syntax
and proof-calculus code rather than importing analytic mathlib definitions.

## Future Proof Targets

The next useful checkpoints are:

- Prove standard-model semantics for the new formula macros, especially
  `primeTermAt`, `squarefreeTermAt`, `completePrimeFactorizationTraceAt`,
  `mertensCountsTraceAt`, and `powRelAt`.
- State and prove a semantic theorem connecting
  `Sat PA.natModel _ mertensRiemannHypothesisSentence` to the usual
  integer-power Mertens bound.
- In the root mathlib-backed workspace, connect the semantic Mertens bound to
  an analytic RH definition, probably through the standard Dirichlet-series
  equivalence for `1/zeta`.
- Optionally add Lagarias as a second PA sentence after a reusable exact
  computable-real comparison layer exists.

## Sources Consulted

- J. E. Littlewood, "Quelques conséquences de l'hypothèse que la fonction
  ζ(s) de Riemann n'a pas de zéros dans le demi-plan ℜs > 1/2",
  *Comptes Rendus de l'Académie des Sciences* 154 (1912), 263-266.
- [Mark P. Lewis, *A Formula for Mertens' Function and Its Applications*](https://www.m-hikari.com/imf/imf-2022/1-4-2022/p/lewisIMF1-4-2022.pdf)
- [Lagarias, *An Elementary Problem Equivalent to the Riemann Hypothesis*](https://arxiv.org/abs/math/0008177)
- [Caveney, Nicolas, Sondow, *Robin's theorem, primes, and a new elementary reformulation of the Riemann Hypothesis*](https://arxiv.org/abs/1110.5078)

