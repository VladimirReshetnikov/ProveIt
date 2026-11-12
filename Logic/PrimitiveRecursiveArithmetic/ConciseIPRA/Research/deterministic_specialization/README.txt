DETERMINISTIC SPECIALIZATION FOR iPRA
Prepared for Vladimir Reshetnikov, 11 November 2026

RESULT

Clause application no longer takes a numerical term argument.
Store clauses newest first. The newest clause is specialized at 1=S(0);
every older clause is specialized at the newest eigenparameter. A Use
certificate contains only the clause index and its antecedent proof.

All arbitrary numerical specialization is recovered by naming the desired
term t through

    N_t = D_(x,y) (C(y,0,x) = C(y,0,t)),

then transporting along the resulting equality b=t. The completeness
proof handles the fact that extending a scope can change an existing
Use instruction: it regenerates persistent premise proofs rather than
silently applying weakening. It combines formula-rank recursion with
structural recursion on the original proof.

The complete presentation has five primitive schemes:

    Refl, Step, deterministic Use, D elimination, D introduction.

Terms are zero-normal scalar iterator terms. Formulas are equations and
the paired binder D. The report specifies every rule, binder, normalization
operation, and freshness condition. The iterator, arithmetic interface,
five-rule architecture, and scalar-to-iPRA bridge are inherited; the
deterministic specialization restriction and its proof compiler are new
relative to the reviewed snapshot.

The written theorem proves exact consequence equivalence with the
unrestricted clause calculus. Its ordinary realization remains
bi-interpretable and equiconsistent with full first-order intuitionistic
primitive recursive arithmetic. Both numerical domains are whole,
equality is actual equality, and both numerical composites have graph x=y.
The logical and arithmetic bridges are reproduced in the report.

MEASURED COMPLETE CHECKERS

CPython 3.12.14. Remove the true module docstring, apply ast.unparse,
append one LF, and count the entire standalone module. Gzip is level 9
with timestamp zero and is informational.

                                             Bytes  Tokens  AST  gzip9
Unrestricted Use, explicit scope               2950    829    902   1004
Deterministic Use, explicit scope              2938    829    903    999
Unrestricted Use, scope from context           2926    819    895   1000
Deterministic Use, scope from context           2914    819    896    997

The controls above use the same newest-first context order. The exact
incoming oldest-first checker has the same first three coordinates and
gzip size 1005. The rule restriction itself saves 12 bytes, ties tokens,
and adds one AST node. Removing redundant scope state independently saves
24 bytes, 10 tokens, and 7 AST nodes. Together they save 36 bytes,
10 tokens, and 6 AST nodes relative to the explicit unrestricted control.
The readable primary source including its documentation is 3597 bytes,
and its maximum-compression gzip size is 1346 bytes.

An independent supplement fuses public grammar validation with the first
scope traversal in the unchanged native Eq/Q/D calculus:

                                             Bytes  Tokens  AST  gzip9
Exact scalar_uniqueness full-validator control   866    381    439    504
Fused grammar/scope traversal                    820    360    412    493

The 820-byte program implements the old native calculus, not the new
deterministic clause calculus. Its certificate format is different.
Neither comparison proves a repository-wide or absolute minimum.

FILES

report.tex, report.pdf     Standalone LaTeX paper and compiled report.
paper/                    Editable assembly sources.
code/checker.py           Entire primary trusted checker.
code/translate.py         Untrusted forward compiler and reverse expansion.
code/arith.py             Untrusted arithmetic proof constructors.
code/source_certificates/  100 unrestricted positive certificates.
code/translated_certificates/
                          Corresponding deterministic certificates.
code/reverse_certificates/ Expanded certificates checked by the old checker.
code/verify.py            Portable translation, CLI, and metric suite.
code/normalized/          Actual normalized programs and gzip-9 files.
reference/                Exact source control and authenticated bridge files.
audit/                    Independent deterministic/scope boundary audit.
supplement/scope_fusion/   820-byte unchanged-calculus refinement and its audit.
examples/                 Selected small and compound demonstrations.
evidence/                 Measurements, receipts, provenance, review notes.
CLAIMS.json               Exact claims and limitations.
MANIFEST.json             SHA-256 ledger for distributed files.
reproduce.py              Portable verification and optional PDF build.

RUN

    python3 reproduce.py
    python3 code/checker.py < examples/induction.json
    python3 code/translate.py < examples/compound_source.json
    python3 code/translate.py --reverse < examples/compound.json
    python3 reproduce.py --pdf

Python 3.10 or later is needed for structural pattern matching. Exact
reference metrics use CPython 3.12.14. There are no nonstandard Python
dependencies. PDF rebuilding needs TeX Live; the build helper includes
a local-cache fallback if installed TeX files lack format/font caches.
The standalone report.tex can also be compiled directly with pdfLaTeX.

VALIDATION AND LIMITS

The main suite checks 100 forward translations and 100 reverse expansions
with identical final formulas, then performs 600 standalone CLI checks
in ordinary and optimized Python. Independent tests exercise compound
formula ranks 1-3, older free parameters, both coordinates bound by D,
nested iterator binders, and persistent antecedents that themselves use
compound clauses.

The separate operational audit checks 209 fixtures and 956 CLI executions,
1200 proof mutations, 93 forced false conclusions, and 157 independently
evaluated closed equations. The scope invariant held in all 25,047 observed
explicit-scope calls. The native fusion audit checks 22,350 entry shapes
and 248 CLI executions. These are implementation checks, not a substitute
for the universal mathematical proof.

The largest main-suite expansion is 699 compact JSON bytes to 175640 bytes.
The arbitrary specialization argument is removed from the trusted checker
at the cost of potentially much larger certificates. No polynomial bound
on translation size is claimed. Finite interpreter memory, time, and
recursion limits may reject sufficiently large valid certificates.

The new theorem has a written proof and independent review, not a new
Lean/Rocq formalization. Existing upstream Lean work is not described as
a formal verification of this new deterministic target restriction.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned commit: 5d85023b0688e03b75f0ec3a04bb43ef0bb51705
Subtree: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

The exact incoming uniform-Step checker is reference/unrestricted.py.
The five inherited mathematical files match their pinned current Git
blobs byte for byte. See evidence/source_blobs.json. The separate native
control has Git blob 00361c25eb276ab835103d18c767e80e85b6a04d.
The supplied MIT No Attribution license is reference/LICENSE-ProveIt.txt.
New material is distributed under the same license.
