# Draft AQ28, AQ27 and AQ26 model and native bridges

These generated source drafts follow the existing AQ29 pattern: decompose each literal into a sum of squared residuals, project away the deleted positive coordinate, reconstruct it using the defining expression, transport each residual via substitution, and assemble the fixed-port native bridge. AQ28 reconstructs `mainScaleVariable²`; AQ27 reconstructs `ellVariable * (ellVariable + eta + zeta)`, and AQ26 reconstructs `cSquareVariable * i`. The candidate graphs and exact polynomial checks are documented separately.

**Compilation is pending.** These drafts are kept outside the project Lean source tree, do not establish the stated theorems, and may need proof or elaboration changes. The prior provider used for AQ29 has missing project build dependencies; its native replay did not pass. A replacement Foundation provider has since been audited, but the full project-source replay is still running. Compiling the complete AQ29 → AQ28 → AQ27 → AQ26 chain and guarded model and native replays remain necessary. All three generated native endpoints also inherit the independent issue of identifying the formalized candidate theory and the mapped refutation with the intended arithmetic and ZFC statements.

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
