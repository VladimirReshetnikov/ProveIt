THREE-FIELD CERTIFICATES FOR iPRA
November 12, 2026

Read report.pdf for the complete report. report.tex and all its input files
are included. No external source download is needed to build the report or
run the verification.

RESULT
The pinned ConciseIPRA compact coordinate envelope is (251, 273, 499), for
significant Python tokens, AST nodes, and normalized UTF-8 bytes. The new
family attains (249, 271, 495), in DIFFERENT complete programs:

  code/checker_tokens.py      three-field, global scope   249 / 278 / 607
  code/checker_ast.py         three-field, local scope    255 / 271 / 606
  code/checker_bytes.py       four-field, local scope     267 / 299 / 495
  code/checker_native.py      validated native interface 342 / 391 / 666

The first two implement the new protocol: infer the elimination major from
the endpoint, reuse the source field as that major, and clear the seed to
select the major-checking branch. The byte profile is a separately identified
composition of established four-field mechanisms. The native interface
validates the entire certificate's integer/list alphabet and the canonical
closed native Eq/D public goal. Its matched comparator is 344 / 393 / 673.

The compact checkers assume the canonical guarded public-goal contract;
their source does not separately validate that public grammar. These sizes
must not be described as sizes of the fully validated interface.

MATHEMATICAL STATUS
The ordinary scalar theory is unchanged. The new protocol preserves its
canonical public theorem set and hence the inherited whole-domain
bi-interpretation with full first-order iPRA. Both numerical round trips
are internally the identity graph x=y, and equality remains actual equality.
The report provides explicit axioms and rules, protocol proofs, both
interpretations, and attributed internal arithmetic foundations.

This is a proof-checker complexity improvement, not an absolute smallest
axiomatization or a new deletion of an arithmetic/logical axiom. The new
protocol has a written proof and executable regression evidence; no new
Lean/Rocq formalization is claimed. Finite tests do not prove metatheorems.

RUN
  python3 code/checker_tokens.py < tests/minimal.json
  python3 reproduce.py
  python3 reproduce.py --pdf

Use CPython 3.12.14 for the exact frozen ast.unparse measurements. The test
programs use only the standard library. PDF rebuilding requires latexmk,
pdflatex, and the packages declared in report.tex. A checker acceptance is
normal exit and exactly ACCEPT followed by a newline; exceptions reject.

The token and AST profiles allocate fresh names differently. Use global
fixtures with checker_tokens.py and local fixtures with checker_ast.py.
Do not pass three-field certificates to the four-field checkers. The
derivation-aware translator in tests/translate.py describes the old/new
protocol boundary; blindly deleting the first field is not a compiler.

CONTENTS
  report.tex / report.pdf     complete mathematical report
  sections/                  new protocol and composition arguments
  reference/                 attributed inherited proofs and source licence
  code/                      complete standalone acceptance modules
  controls/                  pinned predecessor acceptance modules
  tests/                     certificates, compiler, and offline verification
  evidence/                  measurements, receipts, provenance, live inventory
  measure.py                 normalized whole-module size measurements
  reproduce.py               one-command verification and optional PDF build
  MANIFEST.sha256             integrity checks for delivered files

REPOSITORY BASELINE
  VladimirReshetnikov/ProveIt
  5c6c2d8d68da11f89cf2937cf7aca3b85805fd41
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All nine incoming archives were included. A live recursive inventory checked
all 5,825 Research Python paths (1,380 unique blobs) against the frozen census;
none was missing. The actual pooled token minimum is 251, not the 255 stated
in one concurrent incoming report. The sources used for exact comparisons
are bundled, with hashes. The Research inventory is an audit record, not an
unmeasured dependency of a checker.

Inherited repository material retains the MIT-0 attribution in
reference/LICENSE-ProveIt.txt. The new deliverable code and text may also be
used under that licence. Further research questions are in the report.
