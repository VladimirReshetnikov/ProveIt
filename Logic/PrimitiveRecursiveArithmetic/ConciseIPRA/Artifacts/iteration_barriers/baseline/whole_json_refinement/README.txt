iPRA: TWO WHOLE-JSON CHECKER REFINEMENTS
Prepared for Vladimir Reshetnikov, November 12, 2026
=================================================

STATUS
------
This is a verified partial result, not a solution of the full requested
mathematical minimization problem.

Two complete whole-JSON profiles:

                             tokens   AST nodes   normalized bytes
code/checker_tokens248.py       248         277                615
code/checker_ast268.py          254         268                613

The inspected whole-JSON coordinatewise envelope changes from 249/269/473
to 248/268/473, attained by different programs. The 473-byte minimum is
unchanged. Stream-reading records 243 tokens and 264 nodes are also
unchanged. Neither new module is below every coordinate.

These modules combine the existing computation-leaf protocol with the
existing whole-JSON framing. No logical or nonlogical axiom is deleted.
The full-domain identity bi-interpretation with iPRA is inherited from
the identified calculus and arithmetic/logical bridge.

CONTENTS
--------
ipra_whole_json_refinement.pdf
    Research report: explicit ordinary axioms and native inference rules,
    exact input contracts, new framing simulation proof, bi-interpretation
    dependencies, shared recursion-uniqueness lemma, negative evidence,
    comparisons, limitations, further research questions and full code.

ipra_whole_json_refinement.tex
relative_recursion_uniqueness.tex
    Compilable report sources. Keep the archive's directory structure intact:
    the report also reads the exact new checker sources for its listings.

code/
    Two new complete standalone checker modules. Each imports only the
    standard-library JSON reader. No other project module is imported.

reference/
    Exact stream controls, three selected whole-JSON incumbent modules,
    inspected base/certificate chapters and the inherited computation-leaf
    report. Inherited chapter/report fragments are reference sources, not
    independently compilable documents in this directory.

fixtures/ and evidence/
    Twenty finite regression fixtures and actual process/measurement receipts.
    New checkers and controls: 56 paired comparisons, 112 isolated process
    executions, including normal and optimized Python; zero failed checks.
    These tests supplement the written proof, not replace it.

negative/
    An explicitly rejected 465-byte parity-deletion mutant, its original
    473-byte control, and a canonical false-goal certificate. The control
    rejects and the mutant accepts, both normally and under -O.
    The original obstruction is inherited; this is its adaptation to the
    current computation-leaf protocol. The mutant must not be used as a
    proof checker.

audit/
    Verified identities of all eight inspected incoming archives,
    independent selected-baseline measurements, and a bounded corpus audit.

PROOF_NOTES.txt
    Universal framing simulation, hypotheses, exact scope and attribution.

CLAIMS.json
    Machine-readable boundaries of the results.

MANIFEST.sha256
    Checksums of the delivered files, excluding the manifest itself.

INPUT CONTRACT
--------------
Compact checkers assume finite exact-integer/list trees and a canonical
closed guarded Eq/D public formula. They do not independently validate
all of these promises. Do not treat them as arbitrary-JSON syntax validators.

The whole-JSON certificate is [p_n,...,p_1,goal], with each p_i a three-field
packet; its end is consumed first. Pretty-printed multi-line JSON is valid.
Accept means exit zero and exactly ACCEPT followed by LF. Exceptions reject.
For exact simulation, resource limits are excluded as in the inherited model.

REPRODUCTION
------------
Use CPython 3.12.14 for the exact quoted source-normalization metrics.
No network is used.

    python3 reproduce.py

Individual examples:

    python3 code/checker_ast268.py < fixtures/local_computation_successor.json
    python3 -O code/checker_tokens248.py < fixtures/global_computation_zero.json

To build the PDF with an installed TeX distribution:

    python3 build_pdf.py

Or, with an already configured pdfLaTeX installation:

    pdflatex -interaction=nonstopmode -halt-on-error ipra_whole_json_refinement.tex
    pdflatex -interaction=nonstopmode -halt-on-error ipra_whole_json_refinement.tex

Reproduction updates process receipts. Check the manifest before reproducing;
regenerated files may differ under another runtime or TeX environment.

SOURCE SNAPSHOT
---------------
https://github.com/VladimirReshetnikov/ProveIt
6c6a164d211f0af34e913d55c9f46f8ef7cb560f
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All eight incoming archive byte sizes and Git blob hashes were checked.
The bounded source census inspected 297 distinct small acceptance modules.
This does not establish global novelty or theoretical lower bounds.

No repository modification was performed. No new Lean/Rocq verification
of the Python modules is claimed. The shared recursion-uniqueness lemma
is a written proof consolidation; it does not reduce checker size.

Inherited material is attributed in the report and under the repository's
MIT No Attribution license. New material uses the same license.
