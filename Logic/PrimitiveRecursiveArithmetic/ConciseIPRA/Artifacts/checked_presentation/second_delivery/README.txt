SMALLER COMPLETE CHECKING PRESENTATIONS OF iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026

RESULT
The pinned direct compact-source envelope (248 tokens, 270 AST nodes,
487 normalized bytes) improves to (244, 267, 479), in THREE DIFFERENT
standalone programs. The numerical domain, logic, and arithmetic theory
are unchanged. The ordinary theory remains equiconsistent and whole-domain
bi-interpretable with full first-order intuitionistic primitive recursive
arithmetic, with actual equality and identity numerical composite graphs.

This is a verified implementation/presentation refinement. No new axiom
or inference-principle deletion, single all-coordinate winner, or absolute
minimality is claimed. Read CLAIMS.json and the paper for exact limits.

READ FIRST
ipra_checked_presentation.pdf  Full paper, explicit theory and proofs.
ipra_checked_presentation.tex Flattened standalone LaTeX source.
code/readable_checker.py       Descriptive fully validated standalone checker.
code/checker_strict.py         Small fully validated native interface (637 bytes).
proofs/program_proofs.txt      Universal compact implementation arguments.
proofs/validated_program_proofs.txt  Native and strict arguments.

COMPLETE PROGRAM METRICS: tokens / AST nodes / normalized UTF-8 bytes
code/checker_tokens.py        244 / 272 / 608
code/checker_ast.py           249 / 267 / 606
code/checker_bytes.py         272 / 304 / 479
code/checker_native.py        334 / 381 / 614
code/checker_strict.py        344 / 392 / 637

The compact byte profile retains the old whole-JSON-array interface. The
compact token and AST profiles use sequential JSON records: goal first,
then one three-field packet per requested line in execution order. Their
inference code is identical to the respective controls. Applying the same
framing change to those controls gives the new candidates exactly.

The compact modules assume finite exact-integer/list trees and a canonical
closed guarded Eq/D public goal. They check scope but do not themselves
validate the entire public grammar or certificate alphabet. The 637-byte
strict program and readable checker validate the full native Eq/D public
goal and all parsed certificate data, including unused prefix elements.
These are different acceptance contracts and are measured separately.

RUN EXAMPLES
python3 code/checker_bytes.py < examples/computation_zero.json
python3 code/checker_bytes.py < examples/reflexivity.json
python3 code/checker_tokens.py < examples/computation_zero_global.jsonl
python3 code/checker_ast.py < examples/computation_zero_local.jsonl

A successful process exits normally and prints exactly ACCEPT and a newline.
Exceptions reject. The stream profiles use different scope conventions;
keep proof files with their matching checker. The byte checker has FOUR
packet fields; the stream checkers have THREE. to_stream.py only reverses
record order and changes framing. It does not translate packet schemas or
scope conventions. No checker imports the converter or any local module.

REPRODUCE OFFLINE
python3 reproduce.py
python3 reproduce.py --pdf

The first command verifies the delivered manifest, replays the full source
census, measures all candidate/control modules and executes 954 packaged
checks (730 primary plus 224 readable checks). The separately recorded
independent stream review had 40 further process executions. All completed
with zero unexpected outcomes. Finite checks supplement the written
universal proofs; they do not establish the arithmetic bridge by themselves.
The PDF build requires pdfLaTeX and the packages in the TeX preamble. build.py
can use installed TeX trees with missing filename databases and construct a
private local format; it does not alter the system TeX installation.

The original manifest is checked before reproduction. Reproduction rewrites
its generated receipts, so a later run may report a changed receipt if its
runtime version differs. Source hashes and Git blob identities remain the
independent reproducibility anchors.

SOURCE AUDIT
Repository revision: ecae4653f69184a25ade2b1aeaa346f7a7817b78
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
All 2490 Artifacts Python paths (1314 unique blobs) and all Python members
of nine incoming archives were included. Their union is 1509 unique sources.
Exact source bytes are in reference/corpus; provenance and eligibility are
in evidence/. The cited upstream base-theory and protocol chapter excerpts
are also included in reference/article, with verified Git identities. They
are reference excerpts, not standalone LaTeX documents. The census only parses and measures these historical files.
It does not execute them or certify all of their mathematical claims.

The two compressed 459-byte loaders and small report/test utilities are
explicitly excluded from the direct unpacked standalone-checker class.
All sources reaching an incumbent coordinate threshold have a classification.

ATTRIBUTION
The mathematical scalar/guarded theory, logical and arithmetic interpretation,
slot codec, three-field protocol, frozen controls, and inherited fixtures
come from the supplied ProveIt repository and incoming packages. See
reference/LICENSE-ProveIt.txt. New refinements and explanatory material may
also be used under that MIT-0 license. The cited Lean results are inherited;
no new proof-assistant build or external peer review is asserted.
