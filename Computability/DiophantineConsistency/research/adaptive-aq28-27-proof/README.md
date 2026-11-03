# Draft AQ28, AQ27 and AQ26 model and native bridges

**Promoted (3 November 2026).** The Lean files of this directory were copied byte for byte into `Lean/DiophantineConsistency/` and built there against current sources; see the [promotion record](../../reviews/aq22-28-current-source-promotion/README.md). The tree copies are now canonical; the copies here are retained as the audited historical inputs.

These generated source drafts follow the existing AQ29 pattern: decompose each literal into a sum of squared residuals, project away the deleted positive coordinate, reconstruct it using the defining expression, transport each residual via substitution, and assemble the fixed-port native bridge. AQ28 reconstructs `mainScaleVariable²`; AQ27 reconstructs `ellVariable * (ellVariable + eta + zeta)`, and AQ26 reconstructs `cSquareVariable * i`. The candidate graphs and exact polynomial checks are documented separately.

The corrected drafts have completed one [author-only Lean extension](../../reviews/aq26-author-trial-v2/README.md)
over the fresh AQ29 author provider, and its [independent artifact audit](../../reviews/aq26-author-independent-audit/README.md)
passed. They remain outside the main project Lean source tree. This is a
historical hybrid, not a paired Lean replay or current-source result; the
parent's package-transitive, dynamic and Foundation-wrapper limitations remain.
A combined standard-theory client is being checked separately.

The [first fresh-author attempt](../../reviews/aq26-author-attempt-1/README.md)
passed the first three AQ28 modules but failed in `AdaptiveAQ28Transport`:
the unqualified `subst_id` was not in scope. The generator and all three
transport drafts now refer explicitly to the already imported
`DiophantineConsistency.AdaptiveAQ30Transport.subst_id`. The regenerated
sources pass the finite literal and witness-binding controls and were used in
the successful author-only extension above. The previous additions manifest pins the failed source
and is preserved as historical. The corrected source's [v2 additions
manifest](author-additions-v2.json) and [provisional survey](author-survey-v2.json)
pin all 24 current drafts and 75 exact diagnostic names; they are not a Lean
replay or a proof.

`generate_model.py` and `generate_transport.py` prepare the draft sources; `verify_literals.py` checks every draft literal gate against its pinned graph. This finite comparison is not Lean type-checking.

The AQ28 `sum_zero` draft previously quantified over `Fin 18` even though its
residual vector has 19 entries. A sequential text replacement generated
`Fin 20 → Fin 19 → Fin 18`; the generator now uses a noncolliding placeholder,
and the draft states `Fin 19`. Parent AQ29 source templates are hash-pinned.

`verify_witness_binding.py` compares residual expression trees and folded
sum syntax, deleted-coordinate reconstruction, syntactic positivity shape,
projection/extension/fill vectors and transport case indices against the
pinned graphs. It also checks selected model/native wiring text.
`test_witness_binding.py` performs isolated regeneration from the pinned
templates and rejects mutations, including the original AQ28 arity error.
These checks do not type-check Lean, validate the entire positivity or
transport proofs, or establish native equivalence; the wiring checks inspect
selected text rather than parsing a complete Lean declaration.

`survey_author_extension.py` prepares a provisional author-only extension graph
and a tracked-source additions manifest. The [recorded survey](author-survey.json)
uses 1,209 parent modules, 24 draft modules and six check modules; no declared
external import is new relative to the parent manifest. The accompanying
[additions manifest](author-additions.json) pins every draft to a tracked Git
blob and records all 75 diagnostic declaration names, including reports emitted
inside non-check modules. The survey deliberately
does not rehash the parent, check source drift or Lean's actual imports, or
compile any draft. A separate author-only guarded driver must reauthenticate
the completed author provider, freeze these bytes and check all dependencies;
its output cannot be called a matched peer proof. The parent remains historical,
with its documented package/dynamic ancestry and unobserved Foundation wrapper
exit. Run the survey with two unused paths via `--output` and `--manifest-output`.
