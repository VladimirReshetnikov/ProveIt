UNIFORM PREDECESSOR CERTIFICATES FOR INTUITIONISTIC PRA
Prepared for Vladimir Reshetnikov, 10 November 2026
=====================================================

RESULT AND LIMIT
----------------
The complete selected checker is 269 normalized tokens, 307 AST nodes,
629 raw/normalized UTF-8 bytes, and 373 bytes under gzip level 9.
The current 16-archive corpus minima are 277 tokens / 311 AST / 672 bytes,
attained by different complete programs. The selected file is below all
three unchanged minima.

This comparison has an essential qualification. Rejection is now ordinary
nonzero process exit; the redundant catch/print-REJECT/rethrow wrapper is
removed. With the same convention, the old flat checker is 269 tokens,
306 AST nodes, and 628 bytes. The new arithmetic packet interface is thus
one AST node and one byte larger than that matched comparator. All leading
matched-driver controls and their gzip sizes are included.

The actual protocol improvement constructs a successor from a supplied
predecessor, eliminating the separate successor-shape recognizer and
allowing direct computation at scalar parameters. A formerly boxed
three-command step becomes one command. The supplied contextual-induction
derivation shrinks from 48 to 40 command records. This is a certificate
interface improvement, not a new primitive-recursive arithmetic basis.

The significant new axiomatization/breakthrough requested has NOT been
established. The package preserves full first-order iPRA, with written
whole-domain bi-interpretability and equiconsistency proofs, and provides
a broader new restricted term-definability obstruction. It makes no
absolute-minimality claim.

NEW MATHEMATICAL RESULT
-----------------------
Single-body initializer fusion still cannot define addition, unrestricted
selection, or injective pairing after adding arbitrary fixed finite
register vectors, fixed finite body probes, counter-dependent probe maps,
fixed PR combining maps, all unary PR functions, and all bounded PR
observations. The exact hypothesis is that passive data and retained state
reach the seed/update combiners only through evaluations of one supplied
body. Every resulting term remains globally bounded or bounded by a unary
PR function of one input coordinate.

Effective extraction of a bound requires bound witnesses for arbitrary
bounded primitive operations; the unrestricted existence theorem does
not require a uniformly computable witness extractor. Direct register
retention, another independent data/body input, and relational or changed-
domain interpretations are outside the theorem. This extends the existing
tied-seed invariant; it does not prove that every smaller theory is impossible.

OPEN FIRST
----------
report.pdf                  Complete mathematical report.
report.tex, theory/         Modular LaTeX source.
ipra_uniform_predecessor.tex Fully expanded, independently compilable source.
code/checker.py             Entire selected trusted checker.
code/checker.py.gz          Exact gzip-9 compressed selected source.
code/readable_checker.py    Separately executable readable explanation.
code/FORMAT.txt             Syntax, scope, instructions, aliases, examples.
tests/producer.py           Untrusted named proof producer.
tests/fixtures/             Individually runnable positive/negative packets.
reference/                 Frozen old programs, matched controls, full proofs.
evidence/                  Hashes, measurements, test results and written reviews.
ancillary/                 Prior Python encoding choices applied to new packet.

REPRODUCE
---------
From a fresh extraction, using the recorded CPython 3.12.14 runtime:

    python3 reproduce.py

This is read-only apart from operating-system temporary files. It checks
the payload manifest, every source and gzip measurement, matched-driver
transformations, named fixture regeneration, all finite executable tests,
mutation controls, old/new certificate comparisons, and numerical diagnostics.

To check one proof:

    python3 code/checker.py < tests/fixtures/I0_arbitrary_seed.json

Success means exit status 0 and the line ACCEPT. A parsing or checking
exception rejects with a nonzero exit status; a traceback is diagnostic.
Do not infer acceptance from a message alone or ignore the process status.

To rebuild the report with a normal installed PDFLaTeX distribution:

    python3 build.py --check-standalone

Building can change PDF metadata and therefore the manifest hash. Verify
the distributed package first, or rebuild in a separate working copy.
The standalone .tex file has no local include dependencies.

To regenerate measurements/tests after intentional edits:

    python3 tests/producer.py
    python3 measure.py --write
    python3 tests/verify.py --write
    python3 build.py --check-standalone
    python3 package.py

VALIDATION BOUNDARY
-------------------
248 complete-program expectations passed (31 cases x four implementations
x ordinary/-O Python), plus 24 malformed-input runs, three targeted mutation
controls, and 28 old/new certificate-comparison executions. The independent
arithmetic diagnostic generated 15,168 equations from 27,600 attempted
packets and checked 60,672 parameter valuations, with no counterexample
and no evaluation-budget skip.

These are finite implementation checks. The metatheorems and the complete
inherited arithmetic bootstrap are written proofs, not Lean/Rocq
formalizations or external human peer review. Large valid proofs may exceed
physical Python resource limits. The selected parser is explicit; the
ancillary AST profile has extra aliases and recursion-limit-dependent
rejection of nonempty strings and is not the recommended checker.

PROVENANCE
----------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 0300a290bedee5019c974291850b798378438b2e
Directory: docs/drafts
16 current archives, all verified against Git blob identities.
393 direct and 2,249 recursive Python occurrences; 297 distinct contents.
All 23 smaller non-checker utilities were inspected and classified.

Full old ZIPs are not recursively duplicated in this package. Their pinned
paths, Git identities, SHA-256 hashes and full source census are supplied;
all leading comparison programs and all used proof appendices are included.
Run audit_corpus.py with a directory containing the 16 pinned ZIPs to repeat
the recursive census. Upstream license and intellectual attribution are
preserved. No change or publication was made to the GitHub repository.
