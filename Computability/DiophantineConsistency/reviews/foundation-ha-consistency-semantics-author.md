# Fixed ordinary consistency semantics: author record

26 October 2026. **Frozen; final main/checks PASS.** I authored and fully
read the 56-line main and 40-line checks, complete private replay driver,
accepted generic support/semantics interfaces, retained fixed predicate and
normalization definitions, and source semantic negation law before execution.
Independent review/replay by Root remains separate.

The two actual retained formulas now have PAHF `Formula.Sentence`
certificates. Their valuation independence holds in arbitrary PAHF
premodels, without arithmetic or induction hypotheses. The positive
standard-Nat theorem identifies `ordinaryRefutation` with the truth of the
actual source `rho`. The primary negative theorem identifies
`ordinaryConsistency` over Nat with exactly

```lean
¬ _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s []
  _root_.SetTheory.Form.fBot
```

This is the exact body of the repository's external `ConZFC` definition.
The new leaf does not import the broad `Bridge` module or claim a compiled
theorem naming that constant. It retains the explicit fully qualified
refutation proposition used by the accepted fixed-source semantics.

The new proof first applies generic ordinary interpretation semantics to
the actual positive predicate, then uses the literal retained source
identity and Foundation's `Semiformula.EvalAux_neg` to compare its **outer**
HA negation with source consistency truth. Finally it composes the accepted
`source_nat_iff_no_refutation`. The latter's source PA soundness and C254
refutation conventions are used only in their already checked standard-Nat
scope. No checker coding or positive witness is reconstructed here.

The packet does not introduce a new HA derivation, compare independent
checkers in HA, provide the current-equation PA equivalence, identify
ordinary NNF negation syntactically with outer HA negation, or add Markov,
positive-Σ₁ DNE, model-standardness, or arbitrary-model consistency premises.
The optional positive BProv double-negation corollary and conditional
current-equation proof composition were omitted. The checks' one HA
implication is a direct reuse of the previously accepted normalization,
not a semantic reflection step.

## Frozen sources and replay

Main `FoundationHAConsistencySemantics.lean` SHA256:
`fd3b7765dd24c838f8fdc464598fa8ac7cd170c188547a75eab7f2d359301a85`.
Checks SHA256:
`e2f0e9852a669bf613b9f4a8c2cae8ed968be3c53ac2f9cf96096154ff65bc03`.

Final private directory:
`/tmp/foundation-ha-consistency-semantics-author-qttml1s2/lib`.
The main object SHA256 is
`a1740b052539ec7a219d80caeb443424fdef99aebbc318db1b02891800fc96d4`;
checks object SHA256 is
`16c50a18cb7694c8330bd8bacba9067a11085f24acb9509d7f3080e98868178d`.
Final fresh invocations passed in 2.315 and 2.097 seconds, with empty main
output and no warnings or errors. All seven axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`; the fixed source carries
its inherited metatheory dependencies. No new axiom or HA rule is added.

The cache was reauthenticated before implementation in
`research/ha-fixed-consistency-semantics-pins.json`, SHA256
`49d945e66e3b01e1b3926cea74e4fdc0a112bda963422d868357fd7f5b74b64a`.
It selects Root's accepted generic Ordinary object and the independently
replayed accepted Normalization object, retaining original author records.
Exact scope is 457 current-source cached modules, 139 Foundation modules,
874 compiled artifacts including recorded companions, and 57 explicit
external boundaries. No provider or package boundary is new. All 2,184
unique inherited and explicit pins matched before and after each build.
No reused client imports either new leaf.

Only the two new leaves were freshly compiled, under the pinned Lean
4.32.0 binary with `-M6000 -j1 -DElab.async=false`, one worker, explicit
package search paths, no `LEAN_SRC_PATH`, and a 512MiB disk reserve.
Outputs were absent beforehand and are regular private files; cached
dependency symlinks are never used as output paths. No Foundation or other
dependency build, source edit, shared-object overwrite, vendor edit,
shared-document edit, or Git action occurred.

## Preserved development record

The first main compile failed in 1.875 seconds: rewriting through the
logical homomorphism left Foundation's Prop negation notation unsimplified.
The corrected proof explicitly changes to the existing `EvalAux` and
rewrites its exact `EvalAux_neg` lemma. No statement, assumption, target,
or cache policy changed. The failed source/log/timing/terminal record is
retained; the second main and first checks compile both passed. No failed
metadata preflight occurred. A draft driver artifact-count typo was
caught during the required full read and corrected before any execution.

Durable [replay summary](foundation-ha-consistency-semantics-replay.json)
SHA256 `7deefd7018bd347026d0a738dab908f7b934ffc6ee4b263696542c69cb12f602`.
The complete 24-member
[manifest](foundation-ha-consistency-semantics-replay/FILES.json) has SHA256
`599da711a8fceb23a41b4e42e80cdf1add3ab42e4caaaca4be2482b94613a66c`.
All executed source snapshots, driver, input pins, proposal, logs, timings
and terminal results are saved. Compiled objects are pinned at their
private paths and are not copied into the repository.
