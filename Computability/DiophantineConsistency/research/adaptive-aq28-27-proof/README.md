# Draft AQ28 and AQ27 model and native bridges

These generated source drafts follow the existing AQ29 pattern: decompose each literal into a sum of squared residuals, project away the deleted positive coordinate, reconstruct it using the defining expression, transport each residual via substitution, and assemble the fixed-port native bridge. AQ28 reconstructs `mainScaleVariable²`; AQ27 reconstructs `ellVariable * (ellVariable + eta + zeta)`. The candidate graphs and exact polynomial checks are documented separately.

**Compilation is pending.** These drafts are kept outside the project Lean source tree, do not establish the stated theorems, and may need proof or elaboration changes. The prior provider used for AQ29 has missing project build dependencies; its native replay did not pass. Restoring an independently checked provider and compiling the full AQ29 → AQ28 → AQ27 chain are required, followed by guarded model and native replays. Both generated native endpoints also inherit the independent issue of identifying the formalized candidate theory and the mapped refutation with the intended arithmetic and ZFC statements.

`generate_model.py` and `generate_transport.py` prepare the draft sources; `verify_literals.py` checks every draft literal gate against its pinned graph. This finite comparison is not Lean type-checking.
