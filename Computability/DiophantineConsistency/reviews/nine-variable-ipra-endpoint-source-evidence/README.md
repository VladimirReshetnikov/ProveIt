# Nine-variable iPRA endpoints: source and build-evidence inspection

The merged source at commit `d9947ea4ea` states two **different**
nine-variable endpoint families. Their native, standard and equality-only
declarations have no explicit proof or consistency hypotheses in their
statement. This review inspects their source and the available build claims;
it does not run Lean or independently establish the full transitive proof
closure.

* `IPRAExplicitZFCFinal` states the equivalences for
  `ExplicitZFCSyntax.expression`, the executable enumerator-based expression.
  Its two formerly conditional model obligations are supplied in the source
  by `ModelJonesNine.jonesModel` and
  `ModelProgramLink.sourceModel ModelRepFinal.precCase`.
* `IPRANineCurrent` applies the Jones construction to the quartic gate system
  of `ObjectCurrentEquation2011.naturalExpression`, the maintained
  14-variable equation. Its source uses the same Jones model theorem and
  `ModelCarrierCurrent.currentBridge`; this is a distinct construction from
  the enumerator-based expression.

Both standard declarations conclude that the corresponding natural no-zero
sentence is equivalent in the repository's `IPRAStandardTheory.standardTheory`
to intuitionistic negation of the selected mapped Foundation refutation
predicate. The source includes an equality-only variant using the repository's
order erasure. These are statements about derivability, not proofs of the
consistency sentence or unsolvability on their own. No new assertion is made
here about an unprinted literal derivation or global optimality.

[`EXPLICIT_EQUATION.md`](../../EXPLICIT_EQUATION.md) names
`ExplicitZFC.expression` and gives a finite recipe and compact polynomial
presentation; its coefficients have not been printed as a numerical payload.
The separate source theorem `ExplicitZFC.expression_eq_syntax` identifies
that Lean expression with `ExplicitZFCSyntax.expression`, using
`CompactedJones.expression_ofIff`. It is a formal syntax equality statement,
not a formal parser or proof about the Markdown bytes. The compact algebra in
the document remains a human-readable transcription of the named recipe;
this review does not independently prove the whole document's typography or
bind a PDF. The endpoint source directly names the Matrix-free syntax; the
plan records that importing the Mathlib-side equality and Foundation model
modules together requires care because of a `Matrix.map` name collision.

## What the available evidence establishes

The upstream commit message `d9947ea4ea` reports that every module was built
serially and that the printed endpoint axioms were only `propext`,
`Classical.choice`, and `Quot.sound`; the [author plan](../../research/nine-variable-ipra/PLAN.md)
and the repository README also report author builds. These are author
statements, not retained compiler-output or source/object guard receipts in
the `research/nine-variable-ipra` directory, which contained only `PLAN.md`
at inspection. The two endpoint `.olean` files were absent from this
worktree's `.lake/build/lib/lean/DiophantineConsistency` at inspection. That
does not imply they were absent on the author's machine or from every other
provider. A separate historical source-drift issue applies to previously
reused providers, so a fresh or carefully pinned build is needed to verify
the current source closure here.

[`audit.py`](audit.py) pins the inspected endpoint, model, syntax and
document sources; checks their relationship to the endpoint commit; and
verifies that the 54 Lean files changed in that commit contain no lexical
`sorry`, `admit` or top-level `axiom` markers. It also records the direct
local-object and plan-directory observations. This lexical scan does not
inspect the entire transitive import closure, prove that no additional axioms
occur there, or replace the claimed `#print axioms` output. The normal audit
exited 0, and optimized Python was rejected. It used no Lean process.
