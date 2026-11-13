# Author self-check of the bounded-period contexts

This is a **self-check by the draft's author**, not an independent Lean review. Source inspection found no concrete mismatch between the intended `(m,a)` argument order, the three uses of the Pell coordinate graphs, and the extra last parameter introduced by `bnd`. It does not prove that the quotation macro elaborates to the intended syntax; the evaluation equivalence remains an explicit premise in the draft.

The source defines `xDef` and `yDef` with arguments `(out,time,b)`, and the existing `ArithmeticPellRecurrenceChecks` source applies them respectively to `![xcoord time b,time,b]` and `![ycoord time b,time,b]`. The draft applies them as `(c,m,a)`, `(x,h,a)` and `(y,h,a)`, matching its intended c at m and x/y at h. The prior `ArithmeticPellPowerRecovery.comparisonDef` uses the same multi-parameter quotation and nested `!yDef` style, but this analogy is not elaboration of the new formula.

Under the intended quotation convention, after introducing the six nested existential binders in printed order `c,h,x,y,r,t`, the expected de Bruijn stack is

```text
#0=t, #1=r, #2=y, #3=x, #4=h, #5=c, #6=m, #7=a.
```

Thus the expected graph argument indices at that scope are `[5,6,7]`, `[3,4,7]` and `[2,4,7]`. The equality `h=2*m*c` and the two witness equalities use those same named positions. This is a model of the intended binder layout, **not** an inspection of a Lean-generated AST.

`bnd` changes a two-variable arithmetic semisentence into a three-variable one and `eval_bnd_imp` evaluates it under `Fin.snoc e w`. If the formula's first two slots are `(m,a)` as intended, its bounded outer vector is therefore `![m,a,w]`, with w at the last index, and remains last when additional local binders are introduced (`Fin.cons_snoc_eq_snoc_cons`). The source bounds every syntactically unbounded existential, including those in expanded coordinate graphs; no uniform value for w follows from the hierarchy lemma alone.

The source proof's six explicit witnesses match the stated model bridge in order: `c=ycoord m a`, `h=2*m*c`, `x=xcoord h a`, `y=ycoord h a`, followed by r and t from the proposed period specialization. Its four reflexive equalities precede the two specialized equalities. The exact `.mkSigma` quotation, instance search, `ring`/rewrite steps in the upstream period draft, `sigma_prop` elaboration, application of the generic bounded characteristic theorem and the logical import of the inert `ExplicitPellPeriod` provider all require an actual compatible Lean build. The existing characteristic theorem concerns **classical PRA** and a bounded formula; it does not yield an unbounded or intuitionistic period witness.

The separate checker pins the inspected source texts, validates the expected named layout and API signatures, and evaluates four moderate natural-number controls, including an asymmetric `(m,a)` case. These controls do not execute Lean's quotation elaborator, establish `PeriodEvaluationBridge`, authenticate providers or check axioms. Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-bounded-context-self-check/check.py | cmp - reviews/ordinary13-pell-period-bounded-context-self-check/receipt.json
```

No Lean, build or staging was performed.
