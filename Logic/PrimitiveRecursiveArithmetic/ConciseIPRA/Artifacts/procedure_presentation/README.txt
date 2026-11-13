SMALLER COMPLETE CHECKERS FOR iPRA
November 12, 2026

Open report.pdf for the complete result and qualifications. report.tex and
foundations.tex are its editable LaTeX sources.

The new fully validated checker family has separate minima:
  320 significant Python tokens
  362 AST nodes
  600 normalized UTF-8 bytes
The pinned fully validated comparison class has 322 / 364 / 606.

The new compact offset procedure has 267 tokens / 298 AST nodes / 462 bytes.
Including the explicitly inherited return-reservation profiles gives the
compact coordinate envelope 240 / 261 / 462, versus the repository's
241 / 262 / 469. Different files attain different coordinates.

These are implementation refinements of the existing axiomatization.
No new reduction of the arithmetic or logical axioms, absolute minimality,
or mathematical breakthrough is claimed. The complete public theories
retain the inherited bi-interpretation with full first-order iPRA, actual
equality, whole numerical domains, and both formula/numerical round trips.

Reproduce with Python 3.12.14:
  python3 reproduce.py

Rebuild the PDF (pdfLaTeX and standard AMS/LaTeX packages):
  python3 build_pdf.py
The helper can generate a private format from installed TeX sources when
the installation has no format cache. It downloads nothing.

Examples:
  python3 code/checker_strict_procedure.py < validation/validated/fixtures/computation_zero_local.json
  python3 code/checker_compact462.py < validation/compact/fixtures/computation_zero_local.json
  python3 code/inherited_tokens240.py < inherited/return_reservation/fixtures/reserved/global_computation_zero.jsonl

Successful checking prints ACCEPT and exits with code zero. Malformed or
invalid input may fail with an exception. The certificate formats differ:
do not feed one profile's fixtures to another profile without the included
translator. The fully validated programs check the whole JSON certificate;
the smallest stream profiles retain their stated integer/list contract.

code/checker_strict_annotated.py adds comments and line breaks to the
600-byte program. It has the exact same AST and behavior. It is a useful
entry point for reviewing the compact implementation.

The main proofs are in report.pdf:
  * explicit native arithmetic/logical rule inventory;
  * ordinary theory and iPRA interpretation maps and both round trips;
  * procedure-return operational equivalence;
  * exact neutral-list extension equivalence;
  * scope and public-language requirements for offset composition.
The foundations and offset presentation are inherited and explicitly
attributed. The new Python changes have written proofs and regression
evidence, not an end-to-end Lean verification.

Pinned repository:
  VladimirReshetnikov/ProveIt
  dd308d5d938b20dce41a1150fa5db49fc53c5d4e
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All 19 incoming archives are included in the source census.

Directories:
  code/                 selected standalone modules and gzip-9 copies
  controls/             frozen matched baseline sources
  validation/           self-contained comparison scripts and fixtures
  evidence/             measurements, results, independent audit
  reference/            pinned census, manifests, upstream source chapters
  inherited/            attributed prior return-reservation work

The two code/inherited_* files are unchanged prior research artifacts.
The archive does not represent them as newly discovered in this report.
All new transformations, origins, and limitations are recorded explicitly.


Integrity check from the extracted directory:
  sha256sum -c MANIFEST.sha256

