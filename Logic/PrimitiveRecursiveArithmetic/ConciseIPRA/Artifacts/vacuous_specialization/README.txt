VACUOUS CLOSURE SPECIALIZATION FOR iPRA
=====================================
Prepared for Vladimir Reshetnikov, November 12, 2026.

RESULTS AND LIMITS
------------------
1. New mathematical presentation V: Use, Close, and Export, with a fixed
   universal-reflexivity clause. Neither Use nor Close takes an arbitrary
   numerical term; both use the newest parameter (or zero at the closed
   root). Export infers its substitution from its formula. A new vacuous-
   matrix selector makes these restrictions complete together. The written
   equivalence proof and explicit compiler recover all open judgments of
   the liberal source calculus and retain its whole-domain iPRA bridge.

   Exact matched complete checkers, CPython 3.12.14:
                       tokens   AST nodes   normalized bytes
   conditional_copy      646         748               1844
   new V                 645         745               1830

2. Independent compact implementation composition: an existing eager
   selector applied to the current computation-leaf checker reduces its
   normalized source from 474 to 473 bytes. It checks the existing guarded
   scalar calculus, not V. Its tokens increase from 270 to 272; AST nodes
   remain 308. The other compact records, 243 tokens and 264 AST nodes,
   are attained by different programs and are unchanged.

The observed compact envelope therefore changes from 243/264/474 to
243/264/473. No single program attains those three minima. The mathematical
1830-byte reference checker does not beat the compact byte record, and
absolute simplestness or a theoretical lower bound is not claimed.

The new equivalence is written mathematics plus a concrete compiler and
regression evidence. No new Lean/Rocq verification is claimed. Numerical
terms still occur in the formulas supplied to rules; their separate
instruction arguments, not their information content, have been removed.

START HERE
----------
ipra_vacuous_specialization.pdf
  Complete report: exact axioms/rules, selector soundness, explicit
  conditional-copy construction, scope-sensitive source induction,
  iPRA interpretations and round trips, provenance, comparison, limits,
  and further research questions.

ipra_vacuous_specialization.tex, completeness.tex, verification.tex
  Compilable LaTeX sources. Keep these three files together.

calculus/
  Complete new checker, exact matched control and liberal source control,
  untrusted proof builders/compiler, fixtures, tests, receipts, provenance.
  Its README.txt specifies the numerical and formula encodings and all
  three proof packet formats.

compact/
  Complete 473-byte checker and exact 474-byte control, the independent
  relative correctness proof, fixtures, tests, metrics and archive audit.
  Its contract promises exact-integer/list certificate data and a canonical
  closed guarded public goal; it is not an arbitrary-JSON syntax validator.

CLAIMS.json, REPRODUCTION.json, MANIFEST.sha256
  Machine-readable claim boundaries, reproduced results and file hashes.

REPRODUCTION
------------
Use CPython 3.12.14 to reproduce the exact quoted normalization metrics.
The checkers themselves use only Python's standard library.

  python3 reproduce.py

That command replays the focused mathematical-checker suite, normal/-O CLI
cases, and the compact comparison. Expected results are 39/39, 8/8, and
101 cases in 404 isolated compact executions, with no failed expectations.

Individual example:

  python3 calculus/checker.py < calculus/fixtures/reflexivity_two.json
  python3 -O calculus/checker.py < calculus/fixtures/exists_one.json
  python3 calculus/translate.py < calculus/fixtures/exists_one_liberal.json > translated.json
  python3 calculus/checker.py < translated.json

Build the report with a standard LaTeX installation:

  pdflatex -interaction=nonstopmode -halt-on-error ipra_vacuous_specialization.tex
  pdflatex -interaction=nonstopmode -halt-on-error ipra_vacuous_specialization.tex

If the installed TeX format/cache is incomplete but the TeX sources and fonts
are installed, the included build_pdf.py can generate a private temporary
format without downloads or global configuration changes:

  python3 build_pdf.py

SOURCE SNAPSHOT
---------------
VladimirReshetnikov/ProveIt
12197d86f63e9ec73b2d91399c4de2a8cb0077ee
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All five incoming archives at that snapshot were inspected and Git-hash
checked. Relevant inherited sources and the exact controls are identified
in calculus/SOURCE_PROVENANCE.json and compact/SOURCE_AUDIT.json.
This is not a fresh exhaustive semantic census of every repository file.

The ordinary bridge and normalizer are inherited mathematical dependencies,
identified precisely in the report. The 473-byte change composes established
implementation ideas; it is not credited as a new axiom deletion.
