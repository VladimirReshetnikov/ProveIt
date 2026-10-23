# Ordinary ZFC provability and the separate object-calculus obligation

This is an internal mathematical scope review from the research session,
not a newly checked formal derivation. The source snapshot is
`beb0192cb8dc36f78c369c080f2adfbc1887a486` in
<https://github.com/VladimirReshetnikov/ProveIt>.

## Conclusion and logical distinction

The ordinary theorem that ZFC proves the displayed solvability/refutation
biconditionals is justified by composing proofs *within ZFC*. It must not
be inferred solely from an external Lean theorem, truth on standard
numerals, or a finite program's output.

The preserved `upstream/OBJECT_ZFC_STATUS.md` identifies an uncompleted
formalization: an actual `BProv ZFCax_s []` derivation of an equivalence
between two particular `SetTheory.Form` sentences. Its warning is
substantive. In a nonstandard model, an internally finite proof need not
be an externally finite Lean object. No such conversion is used here.

Instead, perform the ordinary coded proof in ambient ZFC. Its quantifiers
then range over the ambient theory's entire omega, and the same proof
applies inside any model of ZFC with that model's natural numbers. The
machine/run compiler, finite syntax manipulations, Pell arguments, and
new polynomial transformations use uniform induction and finite codes.
The mathematical calibration's semantic steps use ordinary set models
and first-order completeness, all available in ZFC. No newly exported
object-language derivation is supplied by this package.

## Inspected calibration chain

1. `KEndpoint215.p215_boot_iff` and the literal binary/source simulations
   connect finite machine runs with the numerical calculus.
2. `KEndpoint.c222_iff_zf_refutation` connects that calculus with finite
   ZF refutability. One direction interprets the numerical calculus in
   the constructible submodel of a set model of ZF; the converse uses
   first-order completeness for the derivable named theory, a seed
   model, and a quotient interpretation to obtain a set model of ZF.
3. `ConstructibleChoice.zf_refutation_iff_zfc_refutation` connects finite
   ZF and ZFC refutability by the usual constructible-model argument,
   soundness, and completeness.
4. The dominated-source compiler, quantified runtime theorem, and exact
   finite blank startup bind this calibration to the literal K215 table.
   The ordinary proof of that composition is included verbatim in
   `upstream/K215_CALIBRATION_PROOF.md`.

The domain of every model used here can be a set. Relations, quotients,
and the satisfaction relation for a set structure are sets. The
constructible domain inside a set model is an ambient subset of its
domain. This does not require a satisfaction predicate for the ambient
universe, or a transitive model of ZFC.

The critical well-foundedness point is explicit in
`WellFoundedPartCore.lean`: `InternallyWellFounded` quantifies over
represented sets, rather than every external subset. The interpreted
domain is not claimed to be externally well-founded. Thus the model
construction does not silently strengthen consistency to existence of
a transitive model or introduce inaccessible-cardinal strength.

The new adapters then compose with the ordinary arithmetic/compiler
proofs, using the same finite proof convention. A standard alternative
presentation of the ZFC calculus may be used through primitive recursive
proof translations. This yields, as an ordinary theorem formalizable
in ZFC, the required equivalence with finite syntactic refutability,
followed by its negation. This is not a proof of either consistency or
inconsistency.

## Exact source locations

All following paths refer to the pinned ProveIt commit above. The Lean
interfaces are evidence for identifying the mathematical construction;
the internal theorem is not obtained by an automatic Lean-to-ZFC rule.

| Path | Inspected content |
|---|---|
| `Computability/DiophantineConsistency/OBJECT_ZFC.md` | Precise remaining object-language derivation and nonstandard-model warning. |
| `Computability/BusyBeaver/Research/ZFC/candidate-k215/proof.md` | Ordinary exact-table calibration, explicitly formalizable in ZFC. |
| `Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/proof.md` | Uniform dominated-axiom recovery, finite derivation compilation, cofinal enumeration and runtime argument. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint215.lean` | `p215_boot_iff`; `blank_halts_iff_zfc_refutation`. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEndpoint.lean` | `c222_of_zf_refutation`; `c222_iff_zf_refutation`; final endpoint composition. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KEind222.lean` | `c222_complete`, using first-order completeness. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KUpper222.lean` | `seed_in_VL`; `bundles_in_L`; `zf_refutation_of_c222`. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KLowerQHyp.lean` | `tag_qhyp`; `zf_consistent_of_formSeed`. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KQ1ZF.lean` | Quotient interpretation, internally well-founded part, and `zf_consistent`. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WellFoundedPartCore.lean` | Internal well-foundedness definitions and formula interpretation. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/WFModelCore.lean` | `domain_models_ZF`, uniform in the formula parameter. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleChoice.lean` | `L_models_ZFC`; `choice_refutation_remove`; `zf_refutation_iff_zfc_refutation`. |
| `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ConstructibleReflect.lean` | Formula-recursive reflection and internally indexed omega iteration. |
| `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/README.md` | Distinction between the external kernel theorem and ZFC's own syntax. |

No extra foundational hypothesis was identified in this inspection.
The additional formalization and ordinary-proof dependencies remain
stated explicitly; this review is not a kernel certificate for them.
