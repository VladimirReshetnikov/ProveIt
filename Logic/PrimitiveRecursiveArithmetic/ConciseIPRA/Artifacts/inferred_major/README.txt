iPRA WITH INFERRED ELIMINATION PREMISES
Prepared for Vladimir Reshetnikov, 12 November 2026
================================================

RESULT

The new proof-certificate protocol reconstructs the major formula required
by an elimination, then still checks its proof. It reduces the compact
token and AST coordinates. A separate truthy-result implementation reduces
the byte coordinate. A private-Boolean-mode simplification reduces the
complete native public-goal checker while preserving its entire acceptance
relation.

The identified compact coordinate envelope changes from
    256 significant tokens / 278 AST nodes / 506 normalized bytes
to
    253 significant tokens / 275 AST nodes / 503 normalized bytes.
These are different programs, not one program attaining all three minima.
The 505-byte companion uses the ordinary k - 1 spelling and also improves
the old byte incumbent.

The separately measured full native public-goal checker improves from
    333 tokens / 379 AST nodes / 656 bytes
to
    327 tokens / 375 AST nodes / 643 bytes.

The mathematical native scalar calculus is inherited. This package does
not delete a new arithmetic or logical axiom, claim absolute minimality,
or present a new proof-assistant formalization. Its improvements concern
the user's stipulated measure: complete standalone proof-checker size.

START HERE

report.pdf                 Compiled paper with all proofs and appendices.
report.tex                 Complete standalone LaTeX source; no input files.
code/checker_native.py      Complete native Eq/D public-goal checker.
code/checker_tokens.py      Inferred-major compact token profile.
code/checker_ast.py         Inferred-major compact AST profile.
code/checker_bytes.py       Compact byte profile, same certificates as control.
code/checker_bytes_readable_decrement.py
                           Companion using k - 1 rather than ~-k.
code/checker_readable.py    Explanatory implementation of the inferred protocol.
code/translate_inferred.py  Expand effective majors for the old checkers.
code/controls/             Exact pinned source controls.
code/fixtures/             Positive, negative, and changed-major certificates.
code/PROOFS.txt             Implementation proofs in plain text.
evidence/metrics.json       Complete-module measurements.
evidence/validation.json    Reproducible verification results.
evidence/independent_review.txt
                           Independent review of the changes and boundaries.
evidence/source_provenance.json
                           Pinned source paths and authenticated Git blob hashes.
CLAIMS.json                Machine-readable claims and limits.

MATHEMATICAL GUARANTEE

The public theory is bi-interpretable and equiconsistent with full
first-order intuitionistic PRA. Both numerical domains are the entire
original domain, interpreted equality is actual equality, and both
composite isomorphisms have graph x=y. The paper includes the complete
native axioms and rules, all intuitionistic logical macros, the ordinary
falsity bridge (0=S0)->bottom, and the arithmetic bridge through predecessor,
actual-equality reflection, quantifier-free induction, and primitive
recursion. These foundations are inherited and explicitly attributed.

INPUT BOUNDARIES

The compact profiles assume the inherited canonical guarded Eq/D public
goal contract; they do not include a separate public-grammar validator.
They admit administrative auxiliary objects in proofs. Their theorem is
not an identity-language bi-interpretation on every raw auxiliary object.
The native profile includes its complete inherited Eq/D public-goal syntax
and scope validation. Unused leading certificate entries are allowed.
Do not compare a compact profile and a native profile as though their
validation obligations were the same.

Each checker reads a JSON array from standard input. Its last item is the
goal; earlier packets are consumed from the end. Acceptance means exit
status zero and exactly ACCEPT followed by a newline on standard output.
Nonzero exits or any other output are rejection. Physical memory and
recursion limits remain ordinary implementation limits.

EXAMPLES

python3 code/checker_ast.py < code/fixtures/inferred_major_local.json
python3 code/checker_tokens.py < code/fixtures/inferred_major_global.json
python3 code/checker_bytes.py < code/fixtures/computation_zero_local.json

The first two fixtures intentionally supply zero instead of the required
major. The new checker reconstructs and proves it. Each corresponding old
control rejects that unmodified fixture; the *_translated.json fixture is
accepted by the old control.

REPRODUCE

python3 reproduce.py
python3 reproduce.py --pdf

The first command verifies the pinned source hashes, compiles and exercises
the checkers, reproduces the certificate translations and scanner checks,
and writes fresh measurements and validation results. The second command
also compiles report.tex with pdfLaTeX. CPython 3.12.14 is the reference
measurement runtime. A conventional TeX Live installation is sufficient.
To rebuild only the PDF, run python3 build_pdf.py. The helper makes three
passes, first using installed pdfLaTeX. If installed TeX sources are present
but the format or filename cache is missing, it constructs a private format
in a temporary directory and uses explicit installed search paths. It does
not download dependencies, modify global TeX configuration, or reuse a format
from another workspace. Detailed diagnostics are in evidence/pdf_build.log.
All measured checker modules use only the Python standard library. No
translator, test, reference file, or report builder is imported by them.

The PDF was also rendered and visually checked. The archive's source and
checksums describe its delivered version; rerunning reproduction may
change evidence metadata under another Python version.

ATTRIBUTION

Baseline repository: VladimirReshetnikov/ProveIt
Commit: 62396b06020f794fa6dc01b4025a6a5db9d4d28a
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The exact upstream controls and inherited foundations retain the included
MIT No Attribution license, LICENSE-ProveIt.txt. New explanatory prose and
the measured transformations are identified separately throughout.
