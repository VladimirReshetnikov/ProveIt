IPRA: NEUTRAL PREMISES AND LOCAL SCOPES
Research prepared for Vladimir Reshetnikov, 10 November 2026

RESULT AND LIMIT
================
The requested significant new axiomatic breakthrough has NOT been established.
This package delivers a verified composition of existing checker techniques,
the complete inherited axiomatization and mathematical bridge, and an audited
comparison with all 20 current draft archives at the pinned commit.

The smallest delivered complete checker is 529 normalized/raw Python bytes,
266 significant tokens, 310 AST nodes, and 333 bytes under ordinary gzip level 9.
It improves the current 542-byte minimum by 13 bytes (about 2.40 percent).
The explicit-list version is 537 bytes and avoids the compact list idiom.
A separate 610-byte generic loop reaches 290 AST nodes, against the old 291.
The old 261-token minimum is unchanged. No one program improves all coordinates.

The arithmetic is initialized scalar iteration with the inherited Choice-DI
logic. The programs do not implement the newest alternative self-seeded or
monus arithmetic bases. The claimed equivalence is full first-order iPRA,
with whole-domain numerical identity composites and proved formula round trips.
The metatheory is a written argument with attributed proofs, not a Lean/Rocq
formalization or external human peer-review certificate.

OPEN FIRST
==========
ipra_neutral_scope.pdf     Complete 44-page report and attributed proof appendices.
ipra_neutral_scope.tex     Fully expanded, independently compilable LaTeX source.
report.tex                Modular authoring source; all included files are present.
code/checker_explicit.py   Recommended compact source for ordinary inspection.
code/checker.py            Entire 529-byte measured implementation.
code/readable_checker.py   Standalone explanatory expansion, not a trusted import.
code/checker_ast.py        Auxiliary generic iterable/immutable-loop profile.
AXIOMS.txt                Compact inventory of every native schema and rule.
CLAIMS.json               Machine-readable claim boundary.

The generic AST profile retains the existing qualification that nonempty
malformed strings can diverge under an ideal unlimited stack. Actual CPython
rejects them through its recursion limit. The primary and explicit-list
openers terminate structurally on finite JSON, subject to ordinary resources.

REPRODUCE OFFLINE
================
python3 verify.py
python3 measure.py
python3 build.py

Verification needs only Python's standard library and no network. Exact
recorded measurements use CPython 3.12.14 and zlib 1.3.2. Other versions may
change ast.unparse or gzip bytes. The verification checks all payload hashes,
remeasures all 484 frozen historical source files without executing them,
and runs 408 complete-process expectations (156 accepts and 252 rejects),
plus four mutation-control outcomes. All expectations passed.

The control that replaces initial [[]] by [0] accepts a forged 1=0 proof.
The control that replaces the loop's tuple context by a shared list accepts
0=S0. Both correct implementations reject their corresponding attacks.
These finite checks support the implementation proof; they do not prove the
universal metatheorems or nonstandard-model claims by themselves.

Building needs PDFLaTeX and the standard packages listed in the TeX source.
No shell escape is used. PDF metadata can change on rebuild, so verify the
distributed manifest first and experiment in a working copy.

To check a positive fixture:
python3 code/checker_explicit.py < tests/example_accept.json

Success means exit status zero AND exactly the line ACCEPT. Exceptions reject.
The certificate is a JSON stack ending with its closed goal; packets are
consumed backwards. Unused prefixes are inert. No certificate is executed as
Python. Supporting producers, historical source files, build scripts, and
measurement tools are not imports of any small checker.

PROVENANCE
==========
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: b9c4d74a0018bdafc5bc06e755a0145f4ed2b8d6
Directory: docs/drafts

All 20 direct ZIP identities were checked. The recursive census has 35
distinct archive payloads and 484 distinct Python sources, zero parse failures.
All 41 sources at/below a frontier coordinate were inspected: three are
complete checkers and 38 are supporting utilities. Corpus minima are achieved
upper bounds on an unknown optimum, not proven mathematical lower bounds.

The composition inherits neutral-major checking from the monus report, local
scopes from the local-scope/selfseed work, and the Boolean-chain continuation
from the uniform-zero control. The mathematics, representations, and zero
normalization are explicitly inherited. The two new measured gains are
implementation composition, not removal of native axioms.

reference/source_corpus stores all 484 frozen historical Python source byte
strings by SHA-256. evidence/corpus.json preserves original member paths and
metrics. reference contains the three unchanged old minimum-attaining checkers,
the complete inherited mathematical sources, and the upstream MIT-0 license.
evidence preserves source identities, tests, and independent assistant reviews.
The latter are review notes, not formal verification.

No changes were made to the GitHub repository. Further research questions are
in the report. The broader request for a significant smaller axiomatization
remains unresolved.
