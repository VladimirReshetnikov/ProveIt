A SMALLER CHECKED PRESENTATION OF iPRA
=====================================
Prepared for Vladimir Reshetnikov, 12 November 2026.

START HERE

ipra_checked_presentation.pdf is the complete mathematical report.
ipra_checked_presentation.tex is its editable source. All TeX inputs are
included under reference/foundations; the PDF includes them as attributed
appendices, along with the complete selected source listings.

RESULT

The main fully validated native Eq/D checker is native/checker.py:

                              Bytes   Tokens   AST nodes
Matched exact-type control       849      370         426
New exact-type native checker    673      344         393
Reduction                        176       26          33

The reduction is 20.73% in bytes, 7.03% in tokens, and 7.75% in AST nodes.
Its whole-certificate alphabet, closed native Eq/D public grammar, scope
handling, JSON reader, and output are all included in the measured file.
Unused certificate prefixes are allowed, but their types are validated.

A separate compact guarded profile is compact/code/checker_compact.py:
502 bytes / 269 tokens / 301 AST nodes, against its 506 / 267 / 303 control.
It assumes the inherited integer/list and canonical guarded-goal contract.
The optional wrapper which enforces that contract is 1172 bytes; its matched
control is 1176 bytes. Do not attribute 502 bytes to that strict interface.

EXACT LIMITS

These programs present the inherited native scalar calculus. They do not
delete a mathematical axiom or establish an absolutely simplest theory.
The ordinary realization remains bi-interpretable and equiconsistent with
full first-order intuitionistic primitive recursive arithmetic: whole
numerical domains, actual equality, both numerical composites x=y.
The complete inherited proofs are reproduced and attributed in the report.

The current compact coordinate envelope is 253 tokens / 275 AST / 506 bytes,
achieved by different programs. The new compact byte result changes it to
253 / 275 / 502. No single delivered program beats all three coordinates.
The entire request for a genuinely new mathematical axiomatization below
every coordinate is therefore not established by this work.

PINNED SOURCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 6ffc49f55d355b548f7a8e1530570aee5de086b3
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All 90 Research packages and the three current incoming archives were
considered. The source census matched 5825 Python paths and verified 1380
distinct Git blobs. The 506-byte incumbent was embedded in the separate
implementation supplement of deterministic_introduction. The closest
matched whole-certificate-typed Eq/D control is
Research/validated_presentation/code/native_typed_eqd.py.
Exact paths, Git hashes and contract classifications accompany the code.

RUN

    python3 reproduce.py
    python3 build_pdf.py

Use CPython 3.12.14 for the exact normalized metrics. Checking and verification
use only the standard library. PDF rebuilding requires pdfLaTeX with the
packages listed in the preamble; shell escape is disabled. The build uses
a temporary directory and writes the final PDF and a build receipt.

Examples:

    python3 native/checker.py < native/fixtures/computation_zero_local.json
    python3 native/checker.py < native/fixtures/old_atomic_case_local.json
    python3 native/checker.py < native/fixtures/unproved_contradiction.json

The first two accept; the last rejects. Acceptance means zero exit status
and exactly ACCEPT followed by a newline. Exceptions reject. Critical
checks work under python -O; the verification harness itself should be run
with ordinary Python.

VALIDATION

Native: 42 complete-certificate comparison pairs (84 processes), plus
whole-prefix and top-level tests, for 145 standalone processes in total;
972 independent alphabet comparisons; exact hashes for 24 frozen files.
Compact: 292 standalone processes, with 142 expected acceptances and
150 expected rejections. Both normal and optimized Python are exercised.
All recorded checks passed. These are finite implementation checks;
general claims rely on the written proofs. No new Lean or Rocq verification
is claimed, and the upstream Lean project was not rebuilt.

CONTENTS

native/              Selected complete checker, matched controls, fixtures,
                     audit, provenance and a dedicated reproduction script.
compact/             Compact checker, strict wrapper, controls and fixtures.
reference/           Pinned project README and attributed foundational TeX.
review/              Independent proof reviews and a rejected-rule audit.
evidence/            Actual measurements, source census and PDF review.
CLAIMS.json          Machine-readable claims and limitations.
MANIFEST.sha256      Hashes of the delivered files except the manifest itself.

The report contains explicit logical and nonlogical rules, the arithmetic
dependency order, both interpretation composites, input-contract proofs,
and Further research questions. Repository content was read only.

The inherited sources retain their permissive MIT No Attribution license.
New material is distributed under the same terms. No external account
write, repository change, commit, or pull request was performed.
