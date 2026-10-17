# Exact Cantor graphs over open-induction arithmetic

`ArithmeticCantor.lean` implements the literal pairing needed by the numerical
C254 checker. In every model of Foundation's IOpen arithmetic it proves the
unique bounded decomposition

```text
p = cantor(a,b)  iff  2*p = (a+b)*(a+b+1) + 2*b,
a <= p, b <= p.
```

Triangular numbers satisfy their exact successor recurrence and monotonicity.
An application of open least-number induction to the polynomial inequality
finds the triangular interval containing any model element. Injectivity and
surjectivity then give both inverse identities and fixed bounded Sigma0 graphs
for pairing and its two projections. The inclusive bounds include zero. There
is no assumption that the arithmetic model is standard or satisfies full PA.

The standard-natural adapter identifies these functions on every input with
the actual `Code254.P` and both components of `SetTheory.Cantor.ofNat`. It uses
the triangular recurrence and inverse uniqueness, without assuming the model's
choice-defined division is definitionally `Nat.div`. The same three graph
formulas are transferred to the actual functions. Four callers additionally
check the exact base4 formula constructors and pairing orientation.

Pinned Lean4.32 freshly checked the235-line module and stored audit. All27 axiom
reports and20 generic/standard-natural callers pass with only `propext`,
`Classical.choice` and `Quot.sound`. Five unnecessarySimpa linter suggestions
remain. The [verification record](results/arithmetic-cantor-verification.json)
records commands, outputs, source identities and the ten reused project
dependencies. Foundation is pinned at
`32e1a0956a8622fad067328ca1959729a7634428`; its existing objects and Mathlib objects
were reused, without a dependency rebuild. The independent source review is in
[the review record](results/arithmetic-cantor-review.json).

This module is checked separately from the Std-only163-unit umbrella because it
uses Foundation and Mathlib. With an existing built dependency checkout and a
checked core cache, run:

```sh
uv run --no-project python -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py \
  --dependency-root /path/to/built/ProveIt \
  --core-evidence Computability/BusyBeaver/Research/ZFC/results/code-tuple-order-integration-verification.json
```

If the recorded temporary core cache has moved, supply `--core-cache` pointing
to matching checked objects. The runner validates the actual Code254 transitive
source closure, records reused object identities, and checks the new source and
stored callers serially in scratch. It neither builds nor downloads dependencies.
Repeated `--library-path` arguments can override automatic built-library discovery.

These are semantic arithmetic graph theorems, not the complete internal PA
checker or machine comparison. The remaining work is represented dense/sparse
history evaluation, proof/trace coding and correctness, followed by the actual
ZF/ZFC finite-proof transport. No machine transition or state count changed.
