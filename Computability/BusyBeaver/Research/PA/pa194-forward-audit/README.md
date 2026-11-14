# PA194 forward compiler: induction audit and prerequisites

The desired direction starts with an internal Foundation PA refutation and
must construct an accepted numerical proof, a halting scheduler word, and
ultimately a literal PA194 run. A standard-natural proof compiler alone does
not provide this construction for nonstandard proof codes.

The upstream PA196 chain contains genuine arbitrary-model transports, but
its assumptions include a full PA model (`theory := Peano`) as well as IΣ₁,
and it uses a different verifier and command encoding. Two explicit uses of
full induction are:

* [`ordinary_derivation_requested`](../jamesyc-upstream/pa196/PA196/Arithmetic/Transport/NumericPAeqSequentDerivation.lean)
  uses `InductionScheme.succ_induction (C := Set.univ)` on
  [`budgetedDerivationInvariant`](../jamesyc-upstream/pa196/PA196/Arithmetic/Transport/NumericPAeqSequentBudgetInvariant.lean).
  It quantifies over smaller derivations and all environments, then requires
  a [`RequestedCertificate`](../jamesyc-upstream/pa196/PA196/Arithmetic/Transport/NumericPAeqSequentDerivationInvariant.lean)
  for every covered parameter assignment. This invariant is presented as
  unrestricted arithmetic syntax; it has not been shown Σ₁.
* [`fuel_invariant`](../jamesyc-upstream/pa196/PA196/Arithmetic/CompilerInvariant.lean)
  also uses `C := Set.univ`. Its
  [`fuelInvariantFormula`](../jamesyc-upstream/pa196/PA196/Arithmetic/CompilerInvariantFormula.lean)
  universally quantifies the table bound and expresses a table-wide realization
  condition; it has not been shown Σ₁.

The upstream original-PA-presentation conversion also invokes
[`original_induction_axiom_supplier`](../jamesyc-upstream/pa196/M6PA/Calibration/FoundationPAeqCodeOriginalInductionSupplier.lean).
Its `additive_matrix_witness`, `canonicalSuccessorAxiom_provable`, and
`successor_proof_to_additive` are individually stated under IΣ₁ alone; the
latter two construct internal proof codes. The supplier nevertheless relies on
`translated_induction_witness` and, through it,
[`formulaCode_subst`](../jamesyc-upstream/pa196/M6PA/Calibration/FoundationPAeqCodeSubstitution.lean).
The upstream substitution-translation compatibility theorem explicitly uses
`C := Set.univ` induction over an invariant quantifying all vectors, depths,
and translation parameters. Its local constructor step is already proved
under IΣ₁ alone. Reproving the global agreement through a suitable internal
Σ₁ or Π₁ structural induction is a concrete remaining task; the existing
full-PA proof cannot be assumed to work in IΣ₁ models. A current-Foundation
replacement has since been proved in every IΣ₁ model, including for
nonstandard codes; see [`pa194-paeq-formula-subst`](../pa194-paeq-formula-subst/README.md).

The replacement handles the changing depth and lifted substitution vector in
the quantifier cases using Foundation's substitution-construction induction.
This removes one full-PA dependency, but the uniform induction-axiom supplier
and the rest of the PAeq-to-numerical-proof compiler remain open. The generic
∀/∨ substitution inversions needed for the matrix step are in
[`pa194-source-subst-inverse`](../pa194-source-subst-inverse/README.md).

An IΣ₁ replacement needs a model-uniform construction of certificate witnesses
for actual internal nodes, together with a coded history or a bound that makes
the required induction predicate Σ₁. For the word stage it also needs an
internal word transformer and a corresponding model-length execution
argument. The existing PA194 target proof relation, rule closures, and source
node/choice decoders are ingredients, but do not yet construct those witnesses
from every PA derivation. No full-PA argument is silently transferred to IΣ₁.

`PA194VerumNode.lean` is a small checked first step for the current Foundation
and PA194 source language. In every candidate-PRA model with IΣ₁ arithmetic
reduct, `selected_verum` states that, when an actual internal LK derivation
has decoded rule tag 1, the fixed finite PRA context decoder returns a valid
formula set containing `qqVerum`. `context_node` gives its exact arbitrary
pair decoding equation. This identifies a real base-rule input to a future
certificate constructor; it does not construct that certificate or prove
any PA194 halting reduction. The result is uniform at nonstandard node codes.

Run from the repository root, using matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-forward-audit/check.sh
```

The final module passed a fresh suffix check using the separately checked
universal-rule inversion object and retained prerequisite overlays; the
printed axioms contain no `sorryAx`. The full nested wrapper replay remains
pending.

An independent suffix replay rebuilt the verum-node module against separately
checked scheduler and proof-code objects and retained deeper prerequisites.
It passed without `sorryAx`; this was not a full nested replay.
