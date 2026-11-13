iPRA WITH NONTRADITIONAL PROOF INPUTS
13 November 2026

START WITH THE REPORT
  ipra_nontraditional_inputs.pdf
  ipra_nontraditional_inputs.tex

STATUS
The requested new mathematical axiomatization, or one checker below every
current complexity minimum, was not established. This package contains
verified input-interface refinements of the existing scalar calculus.
The arithmetic and full first-order iPRA bi-interpretation are inherited.
No absolute-minimality or new Lean/Rocq verification is claimed.

PREFERRED COMPACT RESULT
  sequent_input/checker_sequent458.py
  265 significant tokens / 297 AST nodes / 458 normalized UTF-8 bytes.
  Matched theorem-input control: 266 / 299 / 460.

Its header is [Gamma, A, 0]. Acceptance means Gamma proves A, not A alone.
For ordinary theorem proofs use Gamma=[].
All root assumptions and the conclusion must be closed canonical guarded
public formulas in the inherited shifted encoding. These public syntax
and exact-integer/list promises are not validated by this compact module.
The original proof packets are unchanged.

The new function S(g,a,k) exactly simulates the old C([0]+g,a,k). Hence
the theorem translator only changes [A,0] to [[],A,0]. All scope checks,
inference rules and fresh-name scheduling remain.

EXPRESSION-INPUT RESULTS
  expression_input/code/checker_tokens299.py    299 / 350 / 632
  expression_input/code/checker_ast338.py       311 / 338 / 667
  expression_input/code/checker_bytes575.py     308 / 358 / 575

These replace JSON with a lexically checked integer/list expression
language. The entire inference, substitution, scope, and sorted-goal
validation code is AST-identical to each matched control.
The independent minima 299 / 338 / 575 are attained by DIFFERENT programs.

The expression parser's fixed nesting budget is a material qualification.
The mathematical correspondence idealizes its parser stack; physical
CPython can reject deep literals accepted by json.loads. The broad
sorted-goal validator also remains incomplete for certain noncanonical
padding aliases. Canonical completeness is the precise inherited claim.

BASELINE AUDIT
The pinned repository, including all seven current incoming archives, has:
  compact extrema:                239 / 255 / 460
  alphabet + sorted validation:    302 / 340 / 584
  exact canonical-image control:   581 / 641 / 1424
Different programs attain the first two triples. They are observed upper
bounds on the unknown optimum, not universal complexity lower bounds.

SECONDARY FILES
The seeded-header 238-token and 455-byte examples in sequent_input move
the administrative zero into the external context convention. They are
included for transparency, not used as the preferred general-context
claim. No single delivered program beats all compact coordinates.

REPRODUCTION
Use CPython 3.12.14 for the exact published source normalization.

  python3 reproduce.py
  python3 reproduce.py --tests

The first verifies the top-level manifest and remeasures the selected
programs. The second additionally runs the existing regression suites.
Check the delivered manifest BEFORE rebuilding or regenerating receipts.
Regression evidence is not a formal proof of all-certificate soundness.

  python3 build_report.py

This compiles the standalone LaTeX report with installed TeX and standard
AMS/LaTeX packages. It downloads nothing. A private format fallback is
provided for TeX source installations without cached formats.

DIRECT EXAMPLES
  python3 sequent_input/checker_sequent458.py < sequent_input/sequent_examples/zero_computation_empty_context.json
  python3 sequent_input/checker_sequent458.py < sequent_input/sequent_examples/identity_false_assumption.json

The second certifies the valid sequent 0=1 |- 0=1, not a contradiction
without assumptions. A successful process prints exactly ACCEPT and LF.
Exceptions and all other results reject.

CONTENTS
  sequent_input/       Preferred program, controls, translator, examples,
                       proof of simulation, verification and receipts.
  expression_input/    Three complete programs, controls, input converter,
                       reader proofs, fixtures and evidence.
  reference/           Exact pinned article LaTeX, license, baseline audit.
  evidence/            Report build/visual checks and selected measurements.
  PROVENANCE.json      Source pin and all incoming archive hashes.
  STATUS.json          Machine-readable limits of the claims.
  MANIFEST.sha256      Integrity of all delivered files except itself.

SOURCE PIN
  https://github.com/VladimirReshetnikov/ProveIt
  e88ebf229bb61bd870bb229b9c97caaa1e044e6e
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The inherited ordinary theory uses the whole numerical domain, actual
equality, both formula round trips, and identity numerical comparison
graphs. The report states all eight native rules, the ordinary axioms,
logical macros, the interpretation maps and further research questions.
No remote repository files were changed.
