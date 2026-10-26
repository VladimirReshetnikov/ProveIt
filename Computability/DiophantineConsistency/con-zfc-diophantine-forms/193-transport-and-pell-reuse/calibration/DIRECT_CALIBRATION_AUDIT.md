# Calibration source audit

Audit date: 25 October 2026. Repository pin:
`cdfea7d90176775d74c1c30afbe49fa78ade9897` of
VladimirReshetnikov/ProveIt.

## Conclusion

The two named logical interfaces are actual unconditional Lean theorem
declarations with explicit proof bodies. Their source statements do not
assume Con(ZFC), a machine-simulation hypothesis, an omega-standard model,
or a transitive model. The relevant project source import closure contains
no explicit global axiom declaration or proof placeholder. This supports
the stated **ordinary mathematical composition**; it is not a fresh Lean
kernel build of the logical development or of the new polynomial.

The source inspection found no additional premise that must be inserted
into the direct polynomial theorem. The report must continue to identify
the inherited arithmetic compiler and logical calibration as proof
dependencies, and must not call the complete polynomial theorem newly
machine checked or a serialized ZFC derivation.

## Exact first interface

Path:
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean`.

Git blob: `bdf3a570fe02e5e0becf6c12f562957cf03fc8d5`.

Lines 44-45 declare:

```lean
theorem c222_iff_zf_refutation :
    KCode222.C222 Code254.F ↔ BProv ZFax_s [] Form.fBot :=
  ⟨KUpper222.zf_refutation_of_c222, c222_of_zf_refutation⟩
```

The complete namespace is
`SetTheory.BusyBeaver.ZFC.KEndpoint`.
The declaration is before the subsequent `section` containing
machine-specific variables and `include` statements. Those later
hypotheses do not qualify it.

The lower direction (lines 37-41) applies
`KEind222.c222_complete DerivableNF (fun _ h => h)`, constructs a
full seed via `fullSeed_direct_of_derivable`, converts it by
`formSeed_of_fullSeed`, and invokes `zf_consistent_of_formSeed`
against the given syntactic ZF refutation.
The upper direction is the actual theorem in
`KUpper222.lean`, lines 220-225; it applies first-order completeness
and constructs the relevant seed interpretation in the constructible
submodel of a hypothetical ZF model.

The actual completeness theorem in
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEind222.lean`,
lines 296-312, has hypotheses about a theory of named formulas and the
absence of an irreflexive model of that theory. These are explicitly
discharged inside `KEndpoint.c222_of_zf_refutation`; they are not
unfilled parameters of the final equivalence.

## Exact second interface

Path:
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean`.

Git blob: `0f14fc8890363d7abb9c4e9aa89cae80553735cc`.

Lines 55-57 declare:

```lean
theorem zf_refutation_iff_zfc_refutation :
    BProv ZFax_s [] Form.fBot ↔ BProv ZFCax_s [] Form.fBot :=
  ⟨BProv_theory_mono (fun _ hb => Or.inl hb),
    choice_refutation_remove⟩
```

The complete namespace is
`SetTheory.BusyBeaver.ZFC.ConstructibleChoice`.
The preceding model-parameter section ends at line 42. The equivalence
therefore has no model, regularity, power-set or Choice hypothesis.
The removal theorem (lines 46-52) applies first-order completeness and
soundness to the constructible substructure, using
`L_models_ZFC`. Choice in that substructure is established by
`ConstructibleOrder.choice_of_VL`, not postulated as a new axiom.

## The refutation predicate is syntactic

`Logic/FirstOrder/Lean/FirstOrder/Completeness.lean`, line 308:

```lean
def BProv (B : Form → Prop) (G : List Form) (phi : Form) : Prop :=
  ∃ Gb, (∀ x ∈ Gb, B x) ∧ Prov (Gb ++ G) phi
```

Thus it is provability from a finite list of theory axioms in the
inductively defined first-order proof calculus. It is not a redefinition
of consistency using the new Diophantine equation.

`SetTheory/ZF/Lean/ZF/Zf.lean`, lines 129-142, defines the ZF schema
from extensionality, pairing, union, power set, infinity, regularity,
separation and replacement, then universally closes its axioms in
`ZFax_s`.
`SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/Choice.lean`,
lines 178-188, adds the Choice formula, defining
`ZFCax_s f := ZFax_s f ∨ f = sealF Choice_form`.

Relating this explicit conventional presentation to any other usual
effective ZFC proof presentation uses the ordinary finite translation of
logical proofs and equivalent axiom schemata. No altered theory or
assumed consistency is needed.

## Transitive source scan and its limits

The audit followed all project-local imports recursively from the six
mathematical roots listed in DIRECT_SOURCE_LEDGER.json. It retrieved
**83 project modules**, totaling **1,040,345 source characters**:

- 71 BusyBeaver modules;
- 8 BoundedZFCConsistency modules;
- 3 FirstOrder modules;
- 1 ZF module.

The only terminal import outside this project closure was `Init`.
After removing nested block comments, line comments and quoted strings,
the scan found no tokens `axiom`, `sorry`, `admit`, `sorryAx`,
`unsafe`, `native_decide` or `implemented_by`.
The two endpoint source files were also read directly; neither contains
a proof placeholder or explicit global axiom declaration. Their blob
identities match the retained package-156 calibration copies.

The scan deliberately starts from the mathematical dependencies used by
the C222 equivalence. KEndpoint also imports machine-simulation modules
for unrelated later theorems; no claim is made to have scanned that
unneeded simulator closure. This is a syntactic source audit, not the
output of `#print axioms` from a newly elaborated environment.
Lean's ordinary foundational principles remain in scope. No new claim
about the exact kernel-axiom list or freshness of historical build logs
is made.

## Why the new ordinary proof composes

The retained arithmetic source proves zero existence equivalent to
`KCode222.C222 Code254.F`. The new signed frame and recycled center
preserve zero existence by explicit soundness and cofinal completeness.
All subsequent unit projections are exact integer-polynomial
reconstructions and preserve integer zero sets.

The first logical equivalence gives a finite ZF refutation, and the
second gives a finite ZFC refutation. Negating the resulting existence
equivalence gives the requested Con(ZFC) statement. All new arithmetic
arguments use finite integer recursions, Pell identities, CRT, simple
Hensel lifting, and elementary induction. The inherited semantic
arguments use ordinary first-order completeness, set-model construction,
well-founded parts and constructibility, all available as mathematical
arguments in ZFC. No external standardness assumption is introduced by
the new argument.

This audit does not freshly verify every unbounded arithmetic statement
in the full inherited compiler chain. That remains the named, retained
ordinary proof boundary. Finite polynomial certificates establish the
new literal algebra and costs, and are not substitutes for that boundary.

