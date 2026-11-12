CONSTRUCTING COMPUTATION SOURCES FOR iPRA
Research prepared for Vladimir Reshetnikov, November 10, 2026

Main result
-----------
The complete selected checker has 279 normalized Python tokens, 314 AST
nodes, and 682 normalized UTF-8 bytes. The current nine-draft coordinate
envelope is 281 / 315 / 685. The same initialization profile applied to
the old generator measures 283 / 315 / 683.

This is a small, proved certificate-format reduction, not an absolute
minimum or the significant mathematical breakthrough requested. The
native numerical and logical basis and its iPRA bridge are inherited.
The new generator constructs successor sources from predecessors and
validates recursive images only when their state is used. The report
also proves a finite-range obstruction to simultaneously restricting
DI witnesses and QE targets as proposed in an earlier draft.

The ordinary realization is bi-interpretable and equiconsistent with
full first-order intuitionistic primitive recursive arithmetic. Both
numerical composites use identity on the whole domain. Complete written
proofs, including attributed inherited appendices, are supplied. No
Lean/Rocq formalization or external human peer review is claimed.

Read first
----------
ipra_constructed_computation.pdf - complete report and proofs
ipra_constructed_computation.tex - self-contained LaTeX source
report.tex                      - modular authoring source
code/readable_checker.py         - descriptive checker
code/checker.py                  - selected complete measured checker

Reproduce
---------
Requirements: Python 3.12 (measurements recorded on CPython 3.12.14).
The checker itself requires Python 3.8+ and the standard JSON library.
Rebuilding the PDF requires PDFLaTeX and the packages in report.tex.

    python3 verify.py
    python3 build.py

After rebuilding or verifying, regenerate the file manifest and ZIP with:

    python3 package.py

To check an example:

    python3 code/checker.py < tests/fixtures/contextual_induction_seed_congruence.json

Input is a JSON array, ending with the requested closed formula. Earlier
four-field packets are consumed from the end. A hypothesis closes without
consuming a packet. An unread prefix is inert. ACCEPT with exit code zero
means successful checking; REJECT with nonzero exit means failure.

Computation packets use [m,s,u,t] with false m and t, s=[predecessor,seed,
update], and canonical mode u=0 (base) or u=1 (successor). The checker
constructs the source counter. This differs from the old submitted-counter
format. tests/convert.py converts canonical legacy packets; it is not
imported by the checker. Do not apply old malformed-counter expectations
to the new predecessor format without translating their intended formula.

Files and trust boundary
------------------------
code/       Complete selected, explicit, AST, and descriptive checkers.
tests/      Untrusted named producer, converters, fixtures, finite tests,
            and independent numerical falsification audit.
reference/  Old comparators, matched initialization control, and unchanged
            whole-program measurement utility.
appendices/ New source-construction proof and restriction obstruction;
            five unchanged inherited logical/arithmetic proofs.
evidence/   Hashes, metrics, pinned sources, reviews, execution receipts,
            build and PDF quality records.
sources/    All nine unchanged source ZIPs at the pinned repository snapshot.

No producer, testing decoder, converter, comparison source, or theorem
library is imported by the measured checker. All numerical operations in
the object theory are fixed finite descriptions, not a universally total
interpreter. Finite tests supplement the written metatheorems.

Verification recorded
---------------------
144/144 complete-program and malformed-input runs; 3/3 mutation controls;
all 28 legacy fixtures accounted for, with 4 additional CLI comparisons;
76,960 generator packets, 57,640 successful generations, and 518,760
standard-model valuations of their zero instances, with no counterexample
or resource-bound skip in the fixed audit.

Source snapshot
---------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit:     4a04139595eadc3e8818f1df2a94838ed4851d83
Draft tree: cec0cd82d69646386c802841068c17ff76d188fc

The original repository was read, not modified. Source attribution and
identities appear in ATTRIBUTION.json and evidence/source_manifest.json.
The inherited source license is reproduced in LICENSE.txt.

