COMPUTATION AS A PROOF LEAF
A smaller checking presentation of iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026
================================================

MAIN RESULT

Computation equations now close the current goal directly. The complete
checker no longer supplies a fresh computation hypothesis and checks a
continuation under it. The established mathematical guarded-source
calculus and its whole-domain bi-interpretation with full first-order
intuitionistic primitive recursive arithmetic are preserved.

Against the current inspected compact coordinate envelope 244/265/477,
the new envelope is 243 significant tokens / 264 AST nodes / 474 normalized
UTF-8 bytes. These are minima attained by THREE DIFFERENT programs. No
single program attains all three, and no absolute minimality is claimed.
The compact contract promises exact-integer/list trees and a canonical,
closed, guarded Eq/D public goal; it is not full arbitrary-JSON validation.

The package additionally supplies a fully validated native Eq/D checker,
checker_strict.py, of 625 normalized bytes. It validates the whole input
alphabet and public grammar. This companion is larger than the incumbent
strict byte record of 621; it is not included in the compact comparison.
An unsafe preliminary 620-byte draft was rejected during boundary review
and is not a delivered checker. Progress is restricted to literal equations.

A supplementary 45-node scalar predecessor combines the current fused
factor map with the current reversed comparison, improving on 46 nodes.
Its universal correctness has a written equational proof. This term-size
reduction is independent of the complete-checker improvement.

START HERE

ipra_computation_leaves.pdf
    Full research report: all primitive rules, input contracts, direct-leaf
    soundness, canonical completeness, full logical and arithmetic bridge,
    both identity comparison graphs, measurements and limitations.

report.tex
    Complete manuscript source. The final appendix loads the measured
    checkers from code/, so extract the whole archive before compiling.

code/checker_tokens.py, code/checker_ast.py, code/checker_bytes.py
    The three complete compact standalone checkers. No other project
    module is imported by any of them. An accepting process must exit 0
    and print exactly ACCEPT followed by a newline.

code/checker_strict.py
    Recommended when input syntax has not already been validated.
    Checks the full input alphabet and native public goal grammar.
    Its proof protocol has a separate atomic-case/progress marker.

code/checker_native.py
    Native public-goal validator with the exact-integer/list proof promise.

code/compile_*.py, code/verify_*.py
    Untrusted translators and independent process verification utilities.
    Produced certificates are checked independently by the standalone
    programs. Translators support the documented inherited formats;
    the universal completeness theorem is the written derivation argument.

controls/
    Exact attributed incumbent sources for matched reproduction.

fixtures/
    Positive proofs, source-to-leaf conversions, and negative controls.
    Includes actual-used-hypothesis induction, logical elimination,
    shared computation inlining, scope leakage, and malformed-input cases.

evidence/
    Metrics, input-contract audit, source provenance, complete source
    census, process outcomes, arithmetic diagnostics and PDF QA.

reference/
    Attributed inherited arithmetic and checker proofs, the current
    repository README, a bridge theorem's Lean source, and the two
    predecessor components. The inherited LaTeX chapter fragments are
    reference sources, not independent compilable articles.

REPRODUCE

    python3 reproduce.py
    python3 reproduce.py --pdf
    python3 reproduce.py --verify-only

The reference metric runtime is CPython 3.12.14. No network is used by
reproduction. PDF compilation requires pdfLaTeX and the packages listed
in report.tex. The supplied helper can create a private format from an
installed TeX distribution when the system format cache is missing.

Run the manifest check before modifying files. Reproduction regenerates
receipts and optional PDF bytes; later hash checks can differ after such
regeneration, especially under another runtime or TeX environment.

STATUS

Universal claims: written mathematical proofs, with an explicitly inherited
arithmetic/logical bridge. New checker correspondence: not formalized in
Lean or Rocq. Finite tests are implementation evidence, not universal proofs.
Both interpretation domains remain whole, equality actual, and numerical
comparison graphs x=y. The full intuitionistic first-order language is
recovered; induction remains restricted to the iPRA strength.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 2fa4637b3bf922beea0052a5210c22b14482950b
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All seven current incoming archives were inspected. The executable-source
census covers 3,102 Python/compressed-Python paths and 1,852 unique blobs.
The records are empirical source-size comparisons under stated contracts,
not theoretical lower bounds. The work did not modify the repository.

Inherited material is attributed in the report and covered by the included
MIT No Attribution license. New material uses the same license.
