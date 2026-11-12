# Main Pell ordinate parity in a model: source-only client

`PellOrdinateParity.lean.src` is an **unelaborated** candidate for the
standalone statement, in an arbitrary model `V` of `IΣ₁`,

```
ycoord n b % 2 = n % 2
```

for every model-natural index `n` and base parameter `b`. It contains no graph
hypotheses and makes no equation or endpoint claim. It has not been accepted
by Lean; imports, providers, type inference, and proof terms are unchecked.

The intended argument uses stronger existing source rather than introducing
another induction:

* `ZRowsPellEvenChebyshev.sign_index b t` gives the **odd-index** equality
  modulo `2*(b+3)` for arbitrary internal `t`. Its pinned source uses
  `ISigma1.sigma1_succ_induction` and `definability`. The represented Pell
  coordinate has a `𝚺₁-Function₂` instance in the pinned recurrence source.
* On an even index, `ArithmeticPellPeriodicity.double_y` gives an explicit
  factor of two in the ordinate.
* `even_or_odd` splits an arbitrary model natural, and
  `ArithmeticPellResidueClasses.mod_reduce` descends the odd-index equality
  to modulus two because `2` divides `2*(b+3)`.

Those are source interfaces and the proposed mathematical composition, not a
claim that this draft or its transitive imported providers have been built.
Unlike checking finitely many standard indices, the intended upstream
induction ranges over the model. To apply the result to the eta-zero route,
one must still prove the exact modified graph supplies an even first
ordinate `k`, `c=Y*k`, a main Pell index `c=ycoord R b`, and an odd-index
condition such as `2*n=R+1`, all in the intended model. The generalized
`P72Exact` source draft, graph bindings, source/provider checks, internal
proof translation, and both zero maps are separate obligations.

From this directory, reproduce the **lexical** interface receipt with

```
python3 -I -S -B check.py > /tmp/pell-main-parity-check.json
cmp result.json /tmp/pell-main-parity-check.json
```

The receipt pins five source files and the client bytes; it does not execute
Lean or verify theorem proofs. The `.lean.src` extension marks the draft as
inert. The cited sources are the original repository files; no existing
source was modified.
