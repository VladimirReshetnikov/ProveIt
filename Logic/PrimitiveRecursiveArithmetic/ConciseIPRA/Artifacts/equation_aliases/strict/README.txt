STRICT NATIVE CHECKER REFINEMENTS
12 November 2026

These are complete standalone implementations of the existing native scalar
iPRA presentation. They are NOT implementations of the separate theorem
restricting Alias and Back to equations.

The strict interface validates the entire JSON integer/list alphabet,
including unused prefixes, and the canonical closed native Eq/D goal.
Each consumed instruction has four fields [m,s,u,t]. Input is multiline JSON.
Acceptance is normal exit with exactly ACCEPT followed by LF; exceptions
reject. Python -O is supported. The arithmetic and logical theory, scope
checks, rule selectors, and major-premise proof obligations are inherited.

                     Significant tokens    AST nodes    Normalized bytes
tokens338.py                  338              390             637
ast386.py                     342              386             641
bytes633.py                   342              392             633

The identified strict native envelope improves from (342,391,637) to
(338,386,633), using DIFFERENT programs. The compact guarded-public-goal
envelope (248,270,479), which omits the strict validation contract, is NOT
improved. No absolute minimality or new arithmetic axiom deletion is claimed.

The exact source size convention is whole-source ast.unparse plus one LF
under CPython 3.12.14. Standard-library JSON and the Python runtime are
shared with the controls. Nothing in this directory is an uncounted import
of a checker: every acceptance module imports only json.

REPRODUCE
  python3 measure.py
  python3 verify.py

The first script measures every complete source. The second checks exact
documented source transformations and runs the 56 inherited native proof,
capture, context, and malformed-input cases on all three profiles under
ordinary and optimized Python. The fixture hashes are checked before use.
These finite executions supplement the universal arguments in PROOFS.txt;
they are not a formal proof of calculus soundness or bi-interpretability.

CONTROLS
strict637.py is the exact incoming immediate_application strict checker.
context_phase_strict666.py is the exact checker620 with the explicit whole-
alphabet input gate (the matched strict control for tokens338 and ast386).
three_field_native666.py is the earlier exact strict native checker that
already attained 342 tokens and 391 AST nodes; it explains why comparing
only against strict637 would overstate the old coordinate envelope.

Inherited code and fixtures retain the attached MIT-0 source license.
PROVENANCE.json and evidence/ contain exact source hashes and audit receipts.
The enclosing report explains the native theory and the separate new
mathematical theorem.
