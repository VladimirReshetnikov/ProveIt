# Source-only bounded formula for the explicit Pell period

The existing representation and bounded-characteristic APIs support a **specific proposed formula**, not yet an iPRA period theorem. `PellPeriodBounded.lean.src` defines a candidate Σ₁ graph for the `h=2mc` equalities, applies the existing `bnd` transformation to obtain a candidate Σ₀ formula with a third bound parameter, and proposes use of the generic classical-PRA characteristic-code theorem. All declarations in this new `.lean.src` are **unelaborated**; `#print axioms` lines have not run. Its `DiophantineConsistency.ExplicitPellPeriod` import names the separate inert period draft as a prospective source provider; no such provider is materialized or authenticated by this packet.

For inputs `(m,a)`, the proposed `periodDef` says

```text
∃ c h x y r t,
  yDef(c,m,a) ∧ h=2*m*c ∧ xDef(x,h,a) ∧ yDef(y,h,a)
  ∧ x=1+c*c*r ∧ y=t*c*c.
```

`xDef` and `yDef` are the existing represented Pell graphs, whose source specifies the context `(output,time,parameter)`. The multiplier is `a+2`, matching the earlier period draft. `PeriodEvaluationBridge` explicitly assumes the equivalence between evaluation of this exact quoted formula and the corresponding model-coordinate witnesses, including the two input positions. Under that hypothesis, `period_holds_if_evaluation` proposes to assemble the previously drafted all-`IΣ₁` period lemma. No evaluation lemma is silently asserted to have been checked.

`boundedPeriod := bnd periodDef.val` adds a **last** parameter w and bounds each previously unbounded existential, including witnesses nested inside the Pell graph formulas. The proposed hierarchy lemma applies `StrictSigmaOneInduction.hierarchy_bnd`; `ParsonsHierarchyMap.hierarchy` maps it into the candidate PRA language. The proposed `boundedPeriod_characteristic` then applies the existing `PRA_proves_boundedBooleanCharacteristic` interface exactly in the pattern used by `PRARhoBoundedCharacteristic`: it asserts existence of a 3-argument primitive-recursive bit code and a classical-PRA correctness derivation for the bounded formula. `characteristicMatrix_open` supplies the associated open matrix. This is a source-level proposal until a coherent guarded Lean check succeeds.

## The remaining transfer obligation

The resulting matrix depends on `(m,a,w)`; neither `bnd` nor a characteristic code gives a bound w. `eval_bnd_imp` points from a bounded instance to the original formula. The converse `eval_bnd_of` is a separate model theorem with its own strict-induction-model premises and yields some bound, not a uniform candidate-PRA term for these particular Pell computations. To use `PRAISigmaOneOpenComparison.comparison`, one still needs a closed IΣ₁ derivation and the theorem's explicit implication to a packed open existential goal; a `PRAWitnessTransfer.transfer` route instead needs its actual bounded-instance, replacement-graph and candidate-PRA domination premises. The code and correctness/majorization of Pell evaluations, including histories used inside `xDef`/`yDef`, have not been supplied here.

A bound polynomial in the original `(m,a)` is insufficient for this **particular bounded formula**. Set a=0. Its Pell recurrence has `y_1=1` and `y_(j+1)≥2*y_j`, so `c=y_m≥2^(m−1)` for m≥1. With `h=2mc`, the general recurrence bound `y_h≥h` yields `y_h≥m*2^m`. Because `bnd` bounds the explicitly quantified y along with the internal graph witnesses, any bound w for these instances must exceed y_h and therefore eventually exceeds every fixed polynomial in m. This does not rule out a primitive-recursive, exponential or larger bound, a different encoding or a direct constructive proof.

Even after a classical-PRA derivation, the existing Gödel–Gentzen transfer yields a negatively translated sentence. Recovering the intended positive, unbounded existential in intuitionistic PRA requires a separate constructive witness or justified stability step. Conversely, the repository's generic whole-expression `PolynomialBridge` assembly can yield its selected iPRA no-zero endpoint when its **complete** all-model bridge is proved; the isolated period formula does not itself meet that premise. The graph-to-period binding and the conditional parent-lift hypotheses remain open.

The checker pins the proposed source and the exact source APIs, and runs four small matrix-growth controls. These controls and source signatures do not validate Lean syntax, tactics, characteristic-code elaboration, a resource bound, provider compatibility or any proof object. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-pell-period-bounded-formula-draft/check.py | cmp - research/ordinary13-pell-period-bounded-formula-draft/receipt.json
```

No Lean, build, staging, axiom report or iPRA derivation was performed.
