iPRA: coverage before cancellation and smaller proof kernels
============================================================
Prepared for Vladimir Reshetnikov, 10 November 2026.

READ THIS FIRST

Open ipra_coverage_and_kernel.pdf for the complete mathematical report.
ipra_coverage_and_kernel.tex is a self-contained, compilable source file.
report.tex and theory/ contain the corresponding modular source.

The result is a partial research advance, not a claim to have found an
absolutely simplest axiomatization or the requested major breakthrough.
The new arithmetic lemmas and the complete proof-checker improvements have
different scopes and must not be conflated.

WHAT IS ESTABLISHED

1. In the precisely stated weak scalar self-seeded F theory, without
   successor injectivity, a protected orbit proves whole-domain numerical
   coverage. The theory also proves that successor has no fixed points and,
   for every externally fixed standard k >= 1, the finite theorem
       S(x) = numeral(k)  <->  x = numeral(k-1).
   This is an external family of finite derivations, not a single theorem
   quantifying over k. With injectivity retained, the resulting predecessor
   construction needs corrections only at 0 and 1.

2. In the complete initialized-I native calculus, one D binder over a
   literal equation represents exactly the explicitly prenex existential-
   universal quantifier-free class, up to provable equivalence. Permitting
   progress on those matrices therefore supplies induction for that class.
   This is not a proof of a strict strength separation or an obstruction
   to every possible alternative bi-interpretation.

3. New standalone checkers implement the inherited complete Choice-DI
   calculus, whose full-domain bi-interpretation with iPRA is included and
   attributed. The byte profile is 531 normalized bytes; the recommended
   explicit-list version is 539. A different profile has 289 AST nodes.
   The baseline envelope is 542 bytes / 261 tokens / 291 AST nodes, attained
   by different programs. No new program improves all three coordinates;
   no token improvement is claimed. These are small implementations of
   existing arithmetic, not a complete checker for an injectivity-free
   self-seeded foundation.

LIMITS

- Successor injectivity in the weak self-seeded theory remains open here.
  Neither its full iPRA bi-interpretability nor a full countermodel is given.
- The reported minima are empirical minima of an inspected corpus, not
  mathematical lower bounds on all presentations or all programs.
- Mathematical proofs are written proofs with independent assistant review,
  not a Lean/Rocq formalization or external human peer review.
- Finite tests support implementation claims; they do not prove the
  metatheorems about arbitrary or nonstandard elements.
- checker_ast.py has an abstract malformed-string divergence qualification.
  Real CPython rejects such recursion at its resource limit. Prefer
  checker.py for structurally finite traversal of every finite JSON tree.
- Acceptance means normal exit and exactly ACCEPT followed by a newline.
  Exceptions, resource failures, nonzero exits and other output reject.
  Completeness presumes adequate resources for the finite proof at hand.

MEASUREMENTS

Whole standalone module       normalized bytes   tokens   AST   gzip-9
Baseline byte leader                 542           263    309     343
Baseline token leader                578           261    295     346
Baseline AST leader                  642           263    291     353
code/checker.py                      539           266    308     340
code/checker_bytes.py                531           266    310     335
code/checker_ast.py                  613           263    289     349

Convention: CPython 3.12.14; remove genuine docstrings; ast.unparse plus a
newline; count UTF-8 bytes, significant tokens, and every AST node. All
selected modules include JSON input and their verdict driver. The shared
Python/JSON runtime is excluded, as in the inspected drafts. Gzip uses
level 9 and mtime=0; it is informational, not an optimization objective.
The recorded compressor runtime is zlib 1.3.2. Exact normalization and
compressed-byte comparisons require those recorded runtime versions.

REPRODUCE

From this extracted directory, before changing or rebuilding any file:

    python3 verify_manifest.py

Then remeasure sources and regenerate the finite evidence:

    python3 reproduce.py

The suite uses only the Python standard library. It remeasures seven
selected comparison profiles and 484 frozen distinct Python sources,
checks 756 complete-process expectations and six mutation expectations
under ordinary and optimized Python, and runs the arithmetic diagnostics.
The recorded result is PASS with zero mismatches.

For a focused measurement:

    python3 measure.py code/checker.py code/checker_bytes.py code/checker_ast.py

To rebuild the standalone source and PDF:

    python3 build.py

This requires pdfLaTeX with ordinary TeX Live packages, listed in report.tex.
The script compiles three passes with shell escape disabled. It writes
intermediate files under tmp/latex and retains a build receipt in evidence/.
The PDF build is not claimed to be byte-for-byte deterministic across
platforms or build times. Regenerated evidence and PDFs may consequently
no longer match the original delivery manifest.

The measured checkers read a finite JSON array from standard input; the
last element is the goal, and preceding four-field commands are consumed
in reverse order. Named examples and their expected outcomes are in
evidence/local_cases.json. The report specifies the complete protocol.
No checker imports the producer, test suite, measurement tools or proof text.

A saved arithmetic certificate, already covered by the recorded suite:

    python3 code/checker.py < tests/example_computation.json

Expected output: ACCEPT followed by a newline.

SOURCE SNAPSHOTS

Initial audit: VladimirReshetnikov/ProveIt at
    b9c4d74a0018bdafc5bc06e755a0145f4ed2b8d6
    docs/drafts/

The audit covers 20 direct archives, 35 distinct nested archive contents,
2,744 Python occurrences and 484 distinct Python source byte strings.
The 48 boundary sources were classified as 10 complete theorem checkers
and 38 support programs. The audit does not execute arbitrary corpus code.

Final read-only recheck:
    89f5bdfef815cd2b2c5422978896edc9c819af3f
    Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/

The repository curated the archives into 16 maintained packages. All 2,769
retained research files match original archive contents, including all
1,605 Python files and 187 TeX files. All three comparison leaders remain
unchanged. The two new subtree files are README.md and .gitattributes.
This migration does not change the comparison. Evidence is retained in
evidence/latest_snapshot_recheck.json.

To repeat archive identity verification against a checkout of the initial
snapshot, run:

    python3 audit_corpus.py /path/to/ProveIt/docs/drafts

The distributed source corpus already supports network-free remeasurement;
the much larger original ZIP archives are not duplicated in this package.

CONTENTS

ipra_coverage_and_kernel.pdf / .tex  Complete report and standalone TeX
report.tex, theory/                 Modular sources
code/                              Four complete checkers and gzip copies
tests/                             Producers, fixtures, negative controls
reference/                         Frozen incumbents, original proof sources,
                                   and the upstream MIT-0 license
evidence/                          Measurements, source identities, reviews,
                                   validation receipts and 484 source strings
CLAIMS.json                        Machine-readable claims and explicit limits
AXIOMS.txt                         Exact two-theory scope summary
ATTRIBUTION.txt                     Provenance and inherited-work notices
MANIFEST.json                      SHA-256 identities of delivered payloads
verify_manifest.py                 Verify original delivered payload
measure.py                         Whole-module measurement convention
reproduce.py                       Repeat measurements and executable checks
audit_corpus.py                    Repeat the static archive audit
build.py                           Rebuild standalone TeX and PDF

The report ends with concrete further research questions. The principal
remaining mathematical problem is whether the weak self-seeded source
theory proves S(x)=S(y) -> x=y, without using cancellation, a hidden
general primitive-recursive compiler, or induction beyond its stated rules.
