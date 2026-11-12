A SMALLER CHECKED PRESENTATION OF iPRA
Prepared for Vladimir Reshetnikov, November 11, 2026

Read report.pdf first. The complete LaTeX source is report.tex.
foundations.pdf compiles the attributed inherited mathematical proofs;
foundations.tex, sections/, and reference/foundations/ are its sources.

RESULT
The inspected current primary checker envelope, including six incoming
archives, is 257 significant tokens / 279 AST nodes / 522 normalized bytes.
This package reaches 256 / 278 / 521 with THREE DIFFERENT complete programs.

This is a modest implementation improvement of an existing axiomatization.
It is not a new mathematical axiom deletion, a mathematical breakthrough,
an absolute optimum, or a new Lean/Rocq formal verification.

The implemented theory is the inherited guarded-source public calculus.
The report states every primitive axiom and rule, the public/auxiliary
language distinction, both interpretations, and their composites.
Bi-interpretability is on whole numerical domains with actual equality;
the numerical composite graph is x=y. Full first-order logic is available,
while induction remains quantifier-free in iPRA.

FILES
  report.tex, report.pdf       Main result, proofs, limitations, and questions
  foundations.tex, .pdf        Attributed inherited mathematical chain
  code/checker_tokens.py      Token profile: global scopes, tuple context loop
  code/checker_ast.py         AST profile: local scopes, scalar neutral premise
  code/checker_bytes.py       Byte profile: local scopes, scalar neutral premise
  code/checker_strict.py      Complete checker plus closed public-goal validation
  code/readable_checker.py    Standalone expanded local checker
  tests/                     Certificates, scope attack, reproduction helper
  reference/                 Exact comparator code, certificates, proof sources
  review/                    Independent same-run assistant reviews
  evidence/                  Sizes, hashes, provenance, and process receipts
  CLAIMS.json                Machine-readable scope of the claims
  MANIFEST.sha256            Checksums of the delivered files except this manifest

REPRODUCE
  python3 reproduce.py
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error foundations.tex
  pdflatex -interaction=nonstopmode -halt-on-error foundations.tex
  pdflatex -interaction=nonstopmode -halt-on-error foundations.tex

build_foundations.py regenerates the extracted inherited mathematical section
from the frozen original source. It does not download anything.

CHECK A CERTIFICATE
  python3 code/checker_bytes.py < tests/certificates/<name>_local.json
  python3 code/checker_tokens.py < tests/certificates/<name>_global.json

Use the actual filenames in tests/certificates/. Local and global protocols
are distinct. Acceptance requires exit status zero and exactly ACCEPT plus
a newline. Exceptions and resource failures are rejection. Unused prefix
packets are inert, as in the predecessor convention.

INPUT CONTRACT
Compact profiles rely on the public goal being in the canonical guarded
encoding. They can accept other administrative true formulas and do not
validate the full public grammar. checker_strict.py additionally validates
the closed public goal; it is not an exact-type validator for the entire
certificate. Its full size is 1201 normalized bytes (gzip-9: 571 bytes).

All checkers are standalone and import only Python's JSON library. They do
not import proof producers, measurements, theorem databases, or this README.
The support scripts and reviews are outside the trusted checking boundary.

PROVENANCE
VladimirReshetnikov/ProveIt commit:
a4e5e96c456303cf231eab2aeeb3291d8889833f
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The numerical foundation, guarded-source rules, arity representation, and
bi-interpretation are inherited, with attribution in report.tex and the
frozen source material. ProveIt uses the MIT No Attribution license, a copy
of which is included in reference/.

The equality-rule refinement in report section 5 is an auxiliary theorem
about the unrestricted-source native kernel. It is NOT the rule used by
the 521-byte checker and is NOT assigned that checker's size.

VALIDATION
The delivered reproduction uses CPython 3.12.14 and zlib 1.3.2. It records
210 candidate/control comparisons (420 processes), plus 4 explicit scope
controls: 424 processes, zero mismatches. Finite tests support the written
proofs; they do not establish universal soundness by themselves.
