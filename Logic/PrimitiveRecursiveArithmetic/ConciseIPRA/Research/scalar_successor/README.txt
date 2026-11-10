SCALAR SUCCESSOR RECURSION FOR INTUITIONISTIC PRA
Prepared for Vladimir Reshetnikov, 10 November 2026
================================================

MAIN MATHEMATICAL RESULT
-----------------------
The numerical language has only zero and a scalar iterator R(n,a;u.h).
Successor is the abbreviation S(a)=R(0,a;u.0). The two computation schemas:

    R(0,a;u.h)  = S(a)
    R(Sn,a;u.h) = h[R(n,a;u.h)/u]

The update receives only the preceding state, not the old counter.
This package constructs a term P and proves P(0)=0 and P(Sn)=n internally.
The proof resolves the explicit open left-inverse problem in the current
ipra_shared_continuation_2026-11-10 draft. The candidate equations and
final initialization compiler were already stated there; the missing
finite-swap/affine-comparator predecessor construction is supplied here.

Ordinary initialized iteration is then

    I(n,a;u.h) = P(R(n,a;v.S(h[P(v)/u]))).

Together with the explicitly stated inherited Choice-DI logical rules,
this gives whole-domain bi-interpretability and equiconsistency with full
first-order intuitionistic PRA. Both domain composites are internally
isomorphic to the identity through x=y, with actual equality.

The proof is written mathematics with an independent written audit.
It is not a Lean or Rocq formalization. All logical and nonlogical
schemas and inference rules are stated in the report.

COMPLETE-CHECKER COMPARISON
---------------------------
                              Tokens    AST nodes    Normalized bytes
  Current corpus envelope        281          315                 685
  code/checker.py                279          319                 686
  code/checker_bytes.py          279          321                 681
  code/checker_ast.py            282          314                 708
  New family envelope            279          314                 681

All three new programs are complete standalone checkers. Different
programs attain the three minima; NO ONE program beats all three old
coordinates simultaneously. These are finite-corpus upper bounds,
not an absolute minimality theorem or a universal lower bound.

The mathematical basis reduction and the small implementation improvement
are separate contributions. Constructing each computation's source counter
inside the checker saves redundant validation. That interface also helps
the older initialized-I basis; matched controls are included and measured.
The byte and AST profiles additionally use ordinary import/driver changes.

START HERE
----------
report.pdf                           Complete research report.
report.tex                           Editable modular source.
ipra_scalar_successor_standalone.tex  Source compiling without other files.
theory/scalar_successor.tex          New predecessor bootstrap.
theory/checker.tex                   Exact implementation correspondence.
code/checker.py                      Main complete compact kernel.
code/checker_bytes.py                Smallest-byte delivered R kernel.
code/checker_ast.py                  Smallest-AST delivered R kernel.
code/readable_checker.py             Explanatory standalone implementation.
code/FORMAT.txt                      Certificate protocol and scope.
code/arithmetic_model.py             Exact-definition numerical experiment.
tests/producer.py                    Untrusted named proof-packet producer.
tests/fixtures/                      Individually runnable certificates.
evidence/                           Measurements, receipts, and audits.
reference/                          Attributed proofs and matched controls.
sources/                            Nine pinned original draft archives.
CLAIMS.json                         Exact claims and limitations ledger.
reproduce.py                        Read-only verification driver.
MANIFEST.json                       SHA-256 and byte size of all payloads.

REPRODUCE
---------
From a freshly extracted directory, run:

    python3 reproduce.py

This checks the distributed manifest, recreates the pinned archive census
in a temporary directory, remeasures complete checkers, verifies symbolic
packet regeneration, executes all complete-program tests and guard controls,
and reruns the arithmetic experiments. It does not rewrite the deliverables.
Only Python and its standard library are required; exact metrics were
recorded with CPython 3.12.14.

For an individual proof:

    python3 code/checker_bytes.py < tests/fixtures/equation_progress.json

To rebuild the PDF with an installed pdfLaTeX distribution:

    python3 build.py

The build uses no network or shell escape. Rebuilding a PDF can change
metadata and therefore its manifest hash; verify the distributed manifest
before rebuilding, or use a working copy. The standalone source also
compiles independently with pdfLaTeX.

VALIDATION SCOPE
----------------
248 complete-program executions passed (31 packets x 4 programs x 2 Python
modes). Six targeted mutant executions exercise the successor construction,
equation-only induction, and parameter-scope checks. Separately, 542 finite
arithmetic identities passed under the exact defining recursor interpreter.
These are implementation and standard-model experiments, not substitutes
for the written whole-domain interpretation proof.

The snapshot is ProveIt commit
4a04139595eadc3e8818f1df2a94838ed4851d83. All nine direct source ZIPs were
checked against their Git blob hashes. The recursive census includes 415
Python occurrences and 164 distinct contents. Inherited code/proofs are
attributed in the report and evidence, with the repository license included.
