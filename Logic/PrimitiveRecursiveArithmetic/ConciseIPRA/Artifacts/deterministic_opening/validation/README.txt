EXECUTABLE VERIFICATION
=======================

From the package root, run:

  python3 validation/verify.py

This regenerates both fixture families, independently replays the old proofs,
runs the proposed and old checkers in fresh ordinary and python -O processes,
tests deletion of three essential guards in each proposed checker, and writes
evidence/verification.json and evidence/independent_metrics.json.

The primary presentation is code/checker_open.py: automatic witness opening.
Its 16 valid and 19 invalid closed fixtures are under examples_open/. Each
valid fixture has a corresponding independently generated old proof of the
same end theorem in examples_open/matched_old_proofs/. These old proofs are
accepted by the unchanged explicit witness-discharge checker and replayed by
the independently implemented inherited reference kernel. This correspondence
is a collection of explicit constructions, NOT a generic executable
translation out of the automatic-opening calculus.

The appendix presentation is code/checker.py: deterministic witness discharge.
Its 17 valid and 20 invalid fixtures are under examples/. For this system,
translate.py is a generic checked producer to the earlier explicit
witness-discharge format. It inserts either the first-row clause-use proof
of b=t or a reflexivity proof b=b, retaining the exact end sequent. The source
is checked before translation; the unchanged old checker and independent
reference kernel both check the result. Example command:

  python3 validation/translate.py < examples/positive/successor_congruence.json

One local sequent with two genuinely distinct free parameters is checked for
each presentation. The files validation/opening_parameter_sequent.json and
validation/open_parameter_sequent.json are local-sequent records, not inputs
to the closed-goal public CLI. A further targeted opening experiment checks
the difficult substitution transition from default mode to extraction:
the source proof passes, passive-only substitution fails, and the combined
substitution on the original smaller branch passes. See
evidence/substitution_transition.json and validation/fallback_to_extraction.json.
This experiment is not a generic executable substitution compiler.

Meaningful positive cases include derived symmetry, successor congruence,
transitivity, repeated template positions, passive occurrences of the source,
nested iterator binders, live induction hypotheses, nested D formulas,
ordinary opening in both selection modes, and a selected replacement that
still contains the fresh witness. The appendix also tests direct normalized
export through nested formula binders and a fresh-alias case repair.

The two selection guards are tested semantically. Removing the requirement
that the first row's left side be the fresh witness accepts 1=0. Removing the
exact 0=0 base test also accepts 1=0 in the opening calculus (and a false
closure in the discharge calculus). Removing outer-goal scope checking lets
an eigenparameter escape. The mutant files are temporary test artifacts and
are not shipped as alternate checkers.

Metrics use CPython 3.12.14, remove the module docstring, normalize with
ast.unparse, and append one newline. Significant token counts exclude layout
and comments; AST nodes are counted after removing the docstring. All source
bytes, imports, parsing, syntax validation, normalization, scope checks, rule
dispatch, and verdict handling in the complete standalone modules are counted.
The validation producers are not trusted imports of any checker.

Finite executions and mutation controls supplement the mathematical proof.
They do not establish universal soundness, completeness, or bi-interpretability
and do not constitute a Lean or Rocq verification.

Reference provenance and byte-identity checks are recorded in
evidence/validation_provenance.json. The inherited reference kernel is copied
unchanged from the pinned incoming witness_discharge archive; the two-row
proof constructions are explicitly adapted and their changed row order is
documented in macros.py.
