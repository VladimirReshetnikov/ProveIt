CONCISE iPRA: SHARED VALIDATION
Prepared for Vladimir Reshetnikov, 11 November 2026.

RESULT
The main fully validated Eq/Q/D checker is 897 normalized Python bytes,
401 significant tokens, 468 AST nodes, and 505 gzip-9 bytes.
The exact matched incoming control is 1049 / 450 / 514 / 540 in the
same ordering. This is a 152-byte (14.49%) reduction with the SAME
full-certificate integer/list type contract and public formula grammar.

The equality/D public variant is 878 bytes / 390 tokens / 454 AST /
498 gzip-9, against its matched 1000 / 424 / 484 / 522 control.
The 1000-byte Eq/D control is a derived matched restriction of the existing
full control, not a separately delivered record. Q remains available as an
intermediate closure and is definable publicly.

The separate compact guarded coordinate envelope is
256 significant tokens / 278 AST nodes / 521 normalized bytes,
versus the already incoming 257 / 279 / 522. Different programs attain
these coordinates. This comparison assumes a canonical guarded goal;
its stronger goal-validating profile is counted separately.

WHAT THIS IS
A smaller complete implementation of the existing iPRA proof
presentation, under the requested proof-checker-size criterion.
Its mathematical rule basis, intended theory, whole numerical domain,
and actual equality are unchanged. The report states every primitive
axiom and rule, both interpretations, both formula round trips,
equiconsistency, and correctness of the implementation transformations.

WHAT IS NOT CLAIMED
No newly shorter arithmetic axiom basis, no absolute minimum,
no new Lean/Rocq verification of Python, and no mathematical breakthrough.
The existing Lean bridge was inspected but not rebuilt.
The result is a modest reproducible simplification.

START HERE
ipra_validated_core.pdf       Complete report with attributed proof appendices.
ipra_validated_core.tex       LaTeX authoring source.
code/native_typed_full.py    Primary complete validated Eq/Q/D checker.
code/native_typed_eqd.py     Same kernel, Eq/D public language.
code/readable_native.py      Annotated standalone equivalent checker.
code/guarded_tokens.py       256-token profile, global freshness, tuple scopes.
code/guarded_ast.py          278-node profile, local freshness.
code/guarded_bytes.py        521-byte profile, local freshness.
code/guarded_goal_checked.py Guarded public-goal validator plus checker.
CERTIFICATE_SPEC.txt        Input contract and packet conventions.
reference/                  Frozen controls, provenance, inherited proofs.
evidence/metrics.json        Whole-module size measurements.
evidence/validation.json     Detailed verification receipts.
CLAIMS.json                 Exact claims and exclusions.
SHA256SUMS                  Released file hashes.

RUN A CHECKER
From the package root, with Python 3.12:
    python3 code/native_typed_full.py < tests/native_computation.json
    python3 -O code/native_typed_full.py < tests/native_computation.json
Both print exactly ACCEPT and exit normally.
An exception or any other outcome rejects.

REPRODUCE
    python3 reproduce.py
    python3 build_report.py
The first command runs offline using only the Python standard library.
It regenerates whole-module metrics, gzip artifacts, and the frozen test
receipt. The second requires pdflatex and standard LaTeX packages and
compiles the report. It also regenerates the tables from the metrics.
The frozen report was compiled with the files in this archive.

VALIDATION RECORDED
642 checker process invocations, normal and -O:
256 expected acceptances; 386 expected rejections; zero unexpected outcomes.
18,060 scoped-validator comparisons and 3,834 raw-type comparisons:
zero differences.
Two additional demonstrations confirm that a deliberately unsafe mutant
accepts a false theorem; that mutant is not a delivered checker.
These finite controls support the written proofs; they do not replace them.

COMPARISON PIN
Repository: VladimirReshetnikov/ProveIt
Commit: a4e5e96c456303cf231eab2aeeb3291d8889833f
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All six ZIP archives already in docs/incoming were inspected.
The comparator is stronger than the older main README envelope.
Exact ZIP Git blob hashes, SHA-256 hashes, and selected source identities
are in reference/source_provenance.json and reference/PROVENANCE.json.

NEW IMPLEMENTATION IDEAS
One recursive validator has raw-tree mode d=0 and public-syntax mode d=2.
Its two invariants share typing and grammar checking without dropping
data. The formula/term arity table is shared; diagonal triples add Q.
The remaining prefix and advertised goal are checked in one input guard.
The final 35 bytes of the 152-byte full reduction include sharing that
guard and its diagnostic; the separate-guard version is 932 bytes.
An immutable tuple loop reduces the compact token profile without
leaking local assumptions. Scalar neutral truth and exact-root
introduction are inherited; their composition is explicitly attributed.

ATTRIBUTION
Inherited mathematics and controls come from ProveIt under its MIT
No Attribution license (reference/LICENSE-ProveIt.txt).
The appendices preserve their original attribution and terminology.
Independent reviews in evidence are additional assistant reviews,
not external human reviews or proof-assistant certificates.

