A UNIFORM-PREMISE PRESENTATION OF iPRA
Research prepared for Vladimir Reshetnikov, 10 November 2026

RESULT

Every non-hypothesis instruction now verifies a major premise. Computation
and introduction use the already proved neutral truth [], retained in the
initial context [[]]. A simultaneous induction on successful checking traces
shows that all goals and hypotheses are array rooted. The compulsory proof
therefore excludes dangerous scalar majors without a separate type guard.

The native scalar-iteration Eq/Q/D theory and its full first-order iPRA
consequence relation are preserved. The complete report states all numerical
and logical primitives, proves soundness and canonical completeness of the
new certificate presentation, and includes the attributed whole-domain
bi-interpretation and equiconsistency proofs.

This is a structural reduction of the proof presentation, not a new arithmetic
foundation. An absolute simplest axiomatization or the requested major
foundational breakthrough has not been established.

MEASUREMENTS (ENTIRE STANDALONE PROGRAMS)

                                        bytes  tokens  AST  gzip-9
  Current supplied coordinate minima      558     262  296      --
  New code/checker.py (recommended)        548     262  303     347
  New code/checker_compact.py              537     263  308     342

The supplied minima belong to different programs. Both new programs beat the
source-byte minimum; neither strictly dominates all three supplied minima.
Raw and normalized source bytes coincide for the two compact measured files.
Comments/docstrings are removed before ast.unparse normalization; the entire
module, including import, input and verdict, is counted. Python/json platform
costs are common to all rows. Gzip is informational, maximum level 9, mtime=0.
Exact measurements use CPython 3.12.14 and zlib 1.3.2.

The comparison is pinned to ProveIt commit
76a2651601d17b34d46753f189ea026a21ce8d29:
17 immediate archives, 32 distinct recursive ZIPs, 443 distinct Python sources.
All 443 source byte strings and their occurrence/hashing metadata are included.
Tiny producer/build/test helpers are not silently counted as complete checkers.

READ

  ipra_uniform_premise.pdf   Full compiled report and attributed appendices.
  ipra_uniform_premise.tex   Standalone source; compile this single file.
  report.tex                Modular main authoring source.
  theory/                   New opening, trace and certificate arguments.
  reference/                Unchanged inherited proofs, license, source corpus.
  code/FORMAT.txt           Input grammar, modes and canonical completeness.
  code/readable_checker.py  Complete explanatory expansion; not a dependency.
  evidence/                 Measurements, provenance, reviews and test reports.

RUN FROM THE EXTRACTED DIRECTORY

  python3 reproduce.py
  python3 code/checker.py < examples/certified_zero.json
  python3 code/checker.py < examples/scalar_false_sentinel_attack.json
  python3 build.py

The false-sentinel example must reject with nonzero status. Acceptance is
exactly exit status zero plus the line ACCEPT. A traceback is a rejection
diagnostic, not an incomplete verdict. No assert statement controls acceptance.

reproduce.py checks the manifest, remeasures every frozen source, and runs 184
ordinary/-O CLI expectations plus 4 deliberately unsafe mutation controls. It
also regenerates 31 named producer cases. It requires no network and does not
execute historical comparison sources during measurement. The two measured
checkers import only the standard json module. The producer is untrusted and
is not imported by either checker.

To refresh measurements deliberately after editing:
  python3 measure.py --write
To replay the selected certificates only:
  python3 verify.py
To regenerate example data without overwriting the frozen test list:
  python3 tests/producer.py

build.py requires a normally configured pdfLaTeX installation. It expands the
modular sources to the standalone .tex and compiles without shell escape.
Editing or rebuilding changes hashes; verify the original manifest first,
or work on a copy. package.py intentionally refreshes the manifest and ZIP.

VALIDATION BOUNDARIES

46 cases (20 accept,26 reject) across 2 checkers and 2 Python modes give 184
passing CLI expectations. The 4 mutation checks delete the compulsory major
proof and confirm that the resulting UNSAFE mutants accept 1=0. This is a
concrete test of the guard replacement, not just a happy-path demonstration.

A separate earlier explicit-list candidate received 22,248 negative checks
and 9 CLI controls. Its exact source is reference/reviewed_boolean_checker.py;
the report does not misattribute that run to the final conditional file.

The general claims depend on the written trace and interpretation proofs.
They are not Lean/Rocq formalizations. Canonical completeness concerns the
native Eq/Q/D language, not every semantically meaningful raw alias. Finite
recursion/memory limits can reject large valid proofs; mathematical completeness
assumes adequate resources, as with the comparison checkers.

ATTRIBUTION

Scalar iteration, complementary introductions, Eq/Q/D logic, the arity opener,
the generated computation interface and certified nonempty zero are inherited.
The new contribution is the verified neutral major and successful-trace
invariant. Its novelty is relative to the inspected current corpus only.
The five mathematical appendix files are unchanged from the certified-zero
archive at the pinned commit. Exact origins/hashes and the repository's MIT
No Attribution license are retained. See ATTRIBUTION.txt and evidence/.
