# Model-proof route for natural 80/107 forced gamma

This is a source audit and proposed proof route for the external
[80/107 forced-gamma argument](../ordinary14-natural-forced-gamma80/), not
an internal theorem or an elaborated Lean proof. The checker pins the named
existing source files, checks selected signatures, and confirms the target
graph count; it does not run Lean, validate their compilation/axioms, or
bind a symbolic coefficient to physical bytes. Several 74/81 graph and model
dependencies named below are explicitly **unelaborated research drafts**.
All model lemmas below use an `ORingStructure` satisfying `𝗜𝚺₁`; that
interface alone does not establish an iPRA derivation.

Subsequent source-only drafts now propose the literal 80 graph and narrow
gamma-zero arithmetic; neither has been elaborated. An [independent source
review](../../reviews/ordinary14-natural80-gamma-model-route-independent/README.md)
checks the cited signatures, partial-shift cuts and missing hypotheses, not a
model theorem or endpoint.

## Available source and limits

* `OwnZeroProduct74Draft.factor_units_of_zero` is an unelaborated draft
  taking represented positive beta, positive 74 slots 0, 6, and 7, a 74
  own zero, and three explicit mod-four exclusion premises. It returns the
  first natural Pell equation and unit equations for the other four
  factors. It does **not** require every 74 input, or gamma, to be positive.
  `FactorResidues74Draft.restricted_residues` is the corresponding
  unelaborated source proposal for those three premises.
* `OwnZeroGuardStrict74Draft.guard_eval` is an unelaborated literal guard
  cut with represented beta and K0. Its `strict_of_zero` client assumes
  **all** 74 coordinates positive, so it cannot be applied to the target
  gamma-zero case without a new narrower lemma. A guard-unit equation plus
  the cut should instead be used to prove `F+alpha<q` directly.
* `ArithmeticAdaptiveRankWindow2011.scalar_rank_window` assumes positive
  beta, J, F, alpha, `MC<beta`, `MF<2*beta`, `q=beta*J+1`, and
  `F+alpha<q`. It concludes, among other things,
  `R+q³+q+1<=q⁴`. Instantiation requires model representations and the
  stated inequalities for all symbolic ports; none is assumed silently.
* `DirectMainNorm.direct_main_orientation (U X Y k eta G R : V)` assumes
  `0<U`, `8<=Y`, `0<k` and its explicit signed-magnitude main norm. It
  concludes a positive main quotient and oriented balance. **It does not
  assume `G>0`**, so it is a plausible way to handle `G=gamma=0` once the
  literal 74 main factor is bound to its magnitude premise.
* `ArithmeticPellClassification.solution_index` classifies a model
  solution of `x²=1+delta a*c²`. `Direct80IndexOne.impossible` excludes
  `eta+zeta=2` given a matching main Pell ordinate and explicit positive
  inputs. For this graph its parameters can be instantiated with
  `Y` as Y, `S=a+1`, and the lemma's `X` argument set to 0, so its base
  `S*(0+1)−1` is `a`; one must prove `Y<=a+1` and the graph-to-ordinate
  equality. This avoids incorrectly identifying its general `S` with Y.
* `ArithmeticPellFirstNorm.positive_parameter_solution` classifies a
  positive-parameter solution of `r²=1+m*(m+1)*k²`. The proof pattern in
  `TraceNormKpos.first_index_ge_two` and `graph_rank_size` excludes index
  zero and one and derives `8*m+4<=k` by recurrence monotonicity. Those
  existing graph clients assume positivity of **all** their own slots;
  their arithmetic pattern needs a new fact-level wrapper, not a direct
  invocation with target gamma zero.

## Concrete proposed composition

1. Transcribe the literal 80 graph into Lean syntax and prove its
   J/guard-unit exclusion in the model, adapting the unelaborated
   [81 J-shift draft](../ordinary14-natural81-jshift-model-draft/). This
   argument uses the represented strict `K0>0` but is independent of gamma.
   The separate [strict symbolic K0 draft](../ordinary14-strict-k0-symbolic-source-draft/)
   proposes the required symbolic representation and positivity.
2. Bind an 80 zero to a 74 own zero at the **partially shifted natural
   valuation**: J, f, r, y, and gamma are direct coordinates; F, alpha, i,
   T, w, s, eta, zeta, and h are increased by one. The h shift incorporates
   the guard quotient change. This is not a same-valuation polynomial
   identity. Derive the exact ring identity and model conversion rather than
   substituting `gamma−1` into the natural model when gamma is zero.
3. Apply the 74 own-zero factor extraction and residue drafts with only J,
   w, and s positive. Bind the main unit to the explicit signed-magnitude
   norm expected by `DirectMainNorm.direct_main_orientation`. Use the
   represented guard cut and guard unit to prove `F+alpha<q`, without
   importing the all-positive `strict_of_zero` hypothesis. Supply beta,
   K0, MC, and MF representations and rank-window bounds explicitly.
4. Use the main oriented quotient and `ArithmeticPellClassification` with
   the adapted `Direct80IndexOne.impossible` parameters above to prove
   `k>2`. Use the first Pell classification and the cited recurrence proof
   pattern to derive `8*m+4<=k`. Together with `X>=q` and `Y>=q³`, this
   yields `k>R+1` and `c>X`.
5. In the gamma-zero case, `DirectMainNorm.direct_main_orientation` gives
   the natural balance

   ```
   U*(X+a*c)+H*(R+1) = H*k + U*d,
   d²=1+(H+a²)*c²,  d>0.
   ```

   Prove by square comparison that `d>(a+1)*c>X+a*c`. The inequalities
   `k>R+1` and `d>X+a*c` make the right side of the balance strictly
   larger than the left, contradiction. This formulation avoids silently
   treating model subtraction as ring subtraction.
6. Only then prove a natural predecessor for gamma and transfer 80 zero
   existence to 81 by an explicit coordinate map. Elaborate the model
   bridge, compose the [81 endpoint draft](../ordinary14-natural-forcedj81-ipra-draft/),
   inspect all axioms, and establish the exact iPRA provability claim. The
   remaining symbolic-to-byte and PDF bindings are independent obligations.

```
python3 -I -S -B research/ordinary14-natural80-gamma-model-route/check_sources.py > /tmp/natural80-gamma-route.json
cmp /tmp/natural80-gamma-route.json research/ordinary14-natural80-gamma-model-route/result.json
```
