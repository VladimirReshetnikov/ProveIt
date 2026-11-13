SMALLER CHECKING PRESENTATIONS OF iPRA
Research note and reproducible implementations -- 13 November 2026

START HERE

Read report.pdf, or compile report.tex. The report states the complete
mathematical rule inventories, the interpretation maps, the correctness
arguments, the size comparisons, and their limitations.

This is a partial answer to the strongest reading of the requested research
problem. It gives smaller complete proof-checking presentations of existing
iPRA-equivalent calculi. It does not give a new deletion from the mathematical
axiom basis, prove absolute minimality, improve the 264-node compact AST
record, or produce one checker below all current coordinate minima.

All comparisons use the frozen ProveIt snapshot:
  12197d86f63e9ec73b2d91399c4de2a8cb0077ee
  https://github.com/VladimirReshetnikov/ProveIt/tree/12197d86f63e9ec73b2d91399c4de2a8cb0077ee/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The census includes the five incoming ZIP archives at that snapshot. Its
observed minima are not mathematical lower bounds over all presentations.

RESULTS AND CONTRACTS

1. Compact guarded public theory; integer/list proof alphabet and canonical
   closed guarded Eq/D goal are promised by the interface:

   code/checker_tokens.py
     242 tokens / 269 AST nodes / 606 normalized bytes / 336 gzip-9 bytes.
     Exact token control: 243 / 271 / 616 / 343.
     A continuation loop becomes a tail call. Successful ideal traces agree
     with the exact control, including global fresh-parameter allocation.
     Physical Python call-stack use increases; Python does not optimize
     these tail calls.

   code/checker_bytes.py
     272 tokens / 308 AST nodes / 473 normalized bytes / 311 gzip-9 bytes.
     Exact byte control: 270 / 308 / 474 / 314.
     Eager any-based scope selection saves one normalized byte. Soundness
     follows by simulation; canonical completeness preserves the theorem
     set. Arbitrary raw acceptance languages need not be identical.

   The compact coordinate envelope changes from 243 / 264 / 474 to
   242 / 264 / 473. These coordinates are attained by different programs.
   The exact 264-node incumbent is also included for measurement.

2. Native public Eq/D theory; public goal is validated, but proof data keep
   the inherited integer/list alphabet promise:

   code/checker_native.py
     328 tokens / 372 AST nodes / 581 normalized bytes / 361 gzip-9 bytes.
     Uses CPython 3.12.14's exact-integer unary-plus identity property.

   code/checker_native_portable.py
     328 tokens / 369 AST nodes / 587 normalized bytes / 367 gzip-9 bytes.
     Uses an explicit boolean exclusion and an integer bitwise operation,
     avoiding unary-plus identity dependence.

   Exact native byte control: 332 / 373 / 594 / 371.
   Neither candidate improves the class-wide 317-token or 358-node minima.
   These programs may ignore malformed unused prefixes. They are not the
   whole-input validation profile below.

3. Native public Eq/D theory; complete parsed input alphabet, public goal
   constructors, scalar parity, and scope are validated:

   code/checker_strict.py -- RECOMMENDED FOR ARBITRARY JSON CERTIFICATES
     334 tokens / 378 AST nodes / 608 normalized bytes / 385 gzip-9 bytes.
     Exact whole-input byte control: 340 / 382 / 616 / 390.
     The class-wide 328-token and 368-node minima are not improved.

   All three validated candidates canonically encode numerical zero as
   scalar 1, so the numeral one is [1]. Bound slots remain 3,5,7,... .
   Administrative zero markers keep their separate roles. The opener is
   the previously established O+ operation. This is a certificate-encoding
   refinement, not a new arithmetic constant or axiom.

The native public theory permits unguarded atomic D matrices. It is distinct
from the compact guarded public interface. Both theories are equiconsistent
and bi-interpretable with full first-order intuitionistic PRA through the
inherited bridge. The report gives the formula translations and internal
round trips; all numerical domains are whole, equality is actual equality,
and both comparison graphs are x=y.

No program imports a package-local helper or executes a compressed payload.
Standard Python and its standard-library JSON reader are the ambient
runtime. The .py.gz files are deterministic compressed copies for size
inspection, not hidden code used by the checkers. Existing packed-source
wrappers belong to a different accounting class and are not claimed to be
beaten here.

RUN A SMALL CERTIFICATE

From the extracted directory:

  python3 code/checker_strict.py < fixtures/uniform/additional/direct_zero_supply.json

Expected output:

  ACCEPT

The certificate is:

  [[0,0,1,1],[[1,1,1],1]]

It proves I(0,0;u.0)=0. Its first two zeros are administrative markers; its
expression leaves 1 denote numerical zero. The last array item is the goal;
earlier four-field records are consumed from right to left.

The compact token profile instead reads a JSON-lines stream, goal first,
then three-field packets. The compact byte profile reads a reversed JSON
stack with a final [goal,0] item. These protocols are not interchangeable.

Acceptance means exit status zero and exactly ACCEPT followed by a newline.
All other outcomes are nonacceptance, including host resource exhaustion.
Completeness theorems concern ideal finite execution with unbounded finite
resources. A real interpreter has stack, memory, and input-size limits.

REPRODUCE THE EVIDENCE

  python3 reproduce.py

This checks the integrity manifest, recomputes complete-module measurements,
replays 956 isolated normal/optimized checker executions on 319 distinct
fixture files, and verifies 92 field-aware recodings. All expected outcomes
matched in the included receipt. To save your receipt outside the archive:

  python3 reproduce.py --output ../my_reproduction.json

For measurements and integrity without replaying the process tests:

  python3 reproduce.py --metrics-only

Exact recorded counts use CPython 3.12.14. The normalization is
ast.unparse(ast.parse(whole_source)) plus one LF. No docstrings are removed.
Significant tokens exclude comments, layout, encoding and end markers.
AST nodes count ast.walk, including operator/context nodes. Gzip uses
compresslevel=9, mtime=0 on normalized UTF-8 source. Python and zlib versions
are recorded in evidence/reproduction.json.

To reproduce the source census against a checkout of the pinned commit:

  python3 audit_baseline.py /path/to/ProveIt --output ../census.json

The census parses but never executes the audited sources. Eligibility as a
sound complete checker is a mathematical classification, not something a
size census proves. The supplied census covers 4,942 occurrences, 1,788
distinct decoded raw sources, and 1,664 distinct normalized modules.

BUILD THE REPORT

  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

Use a normal LaTeX installation with the packages named in report.tex.
Run from this directory so the measured code listings resolve. The reference
chapter snapshots are attributed source dependencies, not standalone
documents to compile. Rebuilding the PDF can change its metadata and hash;
the manifest records the delivered edition.

PACKAGE MAP

  report.tex, report.pdf       Complete research note.
  code/                       Five standalone candidate checkers and gzip copies.
  controls/                   Five exact upstream comparison modules.
  fixtures/                   Positive, negative, original, recoded and false-goal cases.
  reproduce.py                Untrusted, read-only reproduction harness by default.
  recode_certificate.py        Untrusted converter for canonical inherited fixtures.
  audit_baseline.py            Portable source-census script.
  evidence/                   Measurements, proof audits, independent receipts and census.
  reference/                  Pinned article/README snapshots and CPython source excerpt.
  PROVENANCE.json              Source commit, archive hashes and exact control origins.
  CLAIMS.json                  Machine-readable statements and explicit nonclaims.
  SHA256SUMS.txt               Integrity manifest for delivered files except itself.
  LICENSE-upstream.txt         License of the reused ProveIt material.

The written proofs establish the universal arguments. Finite regression
tests are supplementary evidence, not proofs of consistency or of arbitrary
program correctness. No new Lean or Rocq formalization of these refinements
is claimed. The stronger all-coordinate or smaller-axiom-basis
research problem remains unresolved in this deliverable.
