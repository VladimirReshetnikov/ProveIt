A SMALLER CHECKED PRESENTATION OF iPRA
Single-binder universals and a 487-byte kernel
Prepared for Vladimir Reshetnikov, November 12, 2026
=================================================

START HERE

ipra_single_binder.pdf   Complete mathematical report.
ipra_single_binder.tex   Standalone TeX: no external input/listing files needed.
sections/               Editable modular source used to assemble that TeX.
reference/              Attributed inherited foundations and protocol proofs.
code/                   Complete checkers, converter, and macro experiment.
controls/               Exact frozen comparison modules, including native666.py.
tests/                  Matching certificates and adversarial cases.
evidence/               Metrics, validation, provenance, and independent review.
CLAIMS.json             Machine-readable claims and explicit limitations.
MANIFEST.sha256         SHA-256 hashes of the delivered package files.

RESULT AND LIMITS

The new derived universal macro is

    U_x A(x) = D_{u,z} G_z A(P(z)),

where u is unused, P is the already-derived scalar predecessor, and G is
the inherited formula gate. It has one paired binder and one copy of A.
Introduction uses P(Sv)=v and a successor gate; elimination opens D,
supplies the provable zero gate, and specializes at St.

This preserves both formula interpretation composites. The ordinary
realization remains bi-interpretable and equiconsistent with full first-order
iPRA; both numerical domains are whole, equality is actual, and each numerical
composite is internally the identity graph x=y. The report includes the full
arithmetic bootstrap and logical interface.

For the specified n-variable sum example under n universal quantifiers,
the fully expanded old/native tree has (4n+39)*2^n+2n-35 nodes, while the new
one has 85n+4. At n=10 this is 80,881 versus 854, and paired-binder ranks
20 versus 10. Predecessor is charged in full (75 nodes). At n=1 and 2 the
new tree is larger. These are full native formula-tree counts, without
sharing or normalization; extra embedding into the compact public grammar
and serialized proof sizes are not included.

No new arithmetic or logical axiom is deleted. No globally simplest theory,
universal source-size lower bound, or new Lean/Rocq formalization is claimed.
The mathematical improvement concerns the definitional translation.

COMPLETE CHECKER METRICS

The current pinned union, including every docs/incoming archive, has the
coordinate envelope (249 tokens, 271 AST nodes, 495 normalized bytes).
Different complete programs attain those minima.

Profile                             Tokens    AST    Normalized bytes
controls/tokens_control.py              249    278         607
code/tokens248.py                       248    277         609
controls/ast_control.py                 255    271         606
code/ast270.py                          254    270         608
controls/bytes_control.py               267    299         495
code/bytes488.py                        271    304         488
code/bytes487.py                        276    308         487
code/strict_guarded.py                  556    633        1544
controls/native666.py                   342    391         666

The new family envelope is (248,270,487), not one program's size.
The token and AST gains come ENTIRELY from one-line JSON input framing.
The equally reframed controls are included and are literally identical.
Thus those two gains are a format choice, not a new proof-kernel argument.

The byte reduction uses the original multiline JSON interface. It composes
the already-known truth-valued-return method with the current context-first
495-byte checker: 488 bytes in function form, 487 in outer-lambda form.
The truth-return method is credited to Article/ch11_cert.tex, Proposition
cert:prop:truthy. No mathematical inference is removed.

Measurements count the full module under CPython 3.12.14: remove genuine
docstrings, ast.unparse, append one LF, count significant tokens/all AST nodes/
UTF-8 bytes. JSON is the only imported library of each compact checker.
The strict guarded companion's docstrings are also removed in measurement.

INPUT CONTRACTS

The compact checkers assume finite exact-integer/list syntax and a canonical
closed guarded Eq/D goal. They include scope checking but do not separately
validate that public grammar. strict_guarded.py checks both the alphabet
throughout the input and the guarded goal before running the four-field
kernel; its larger complete size is reported separately.

The unchanged native666.py has the different, broader full native Eq/D public
grammar and its own four-field protocol. It is supplied as an attributed
reference, not as a new implementation. Do not identify its grammar with the
strict guarded grammar or infer that compact counts include validation.

All programs consume the input array from its right end; its last element
is the public goal. Unused prefixes are inert for compact checking.
Acceptance is normal exit plus exactly ACCEPT and one LF. Exceptions reject.

tokens248.py: three-field packets, global fresh-name supply, first-line JSON.
ast270.py:    three-field packets, local scope, first-line JSON.
bytes487.py and bytes488.py: four fields, local scope, ordinary multiline JSON.

Do not mix the fixture protocols. Later physical lines are outside the
tokens248/ast270 frame and are ignored. A blank or malformed first line
rejects; no final newline and CRLF are supported. Whole-byte-stream
equivalence with json.load is NOT claimed.

EXAMPLES

    python3 code/bytes488.py < tests/byte/context/computation_zero_local.json

    python3 code/strict_guarded.py < tests/byte/context/computation_zero_local.json

For a three-field global certificate, first serialize it on one line:

    python3 code/to_one_line.py < tests/three_field/global/computation_zero_global.json > example.jsonl
    python3 code/tokens248.py < example.jsonl

The converter performs no proof processing and is not a trusted dependency.

REPRODUCTION

Verify the delivered files before rebuilding them:

    sha256sum --check MANIFEST.sha256

Then reproduce the measurements and checks:

    python3 measure.py
    python3 verify.py
    python3 code/universal_macro.py

Or all of them, with optional PDF rebuilding:

    python3 reproduce.py
    python3 reproduce.py --pdf

The final finite checker suite has 726 process executions with no failures:
680 control/candidate comparisons, 40 strict-interface checks, five framing
checks, and one converter round trip. Both normal and optimized Python are
used. Fixtures include compound and induction proofs, wrong endpoints,
missing premises, future-variable capture, and context leaks.

The macro script verifies exact tree sizes, ranks, and scopes for prefix
lengths 1-10 and evaluates the expanded predecessor at 0-4. These finite
checks supplement written universal proofs; they do not replace them.

For TeX, a conventional installed pdfLaTeX works directly:

    pdflatex ipra_single_binder.tex
    pdflatex ipra_single_binder.tex

build_report.py --pdf assembles the modular source and compiles three times.
If installed TeX format caches are missing, build_pdf.py creates a temporary
private format from installed sources, without network access or global edits.
The latter helper is adapted from the incoming constantfree package.

PROVENANCE

Repository: VladimirReshetnikov/ProveIt
Snapshot: 42fba2a76aea6eb41a8c4acfe7761620f58956ee
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

All three current incoming ZIPs were examined and their Git blob hashes
verified. The controlling three-field archive's blob is
152c09e61c95029a143198d019e94e570898f980. Detailed receipt:
evidence/baseline_audit.json and evidence/source_fixtures.json.

Inherited material retains the included MIT-0 attribution in LICENSE.txt.
The new code and text can also be used under that license.
