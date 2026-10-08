# Integrating arithmetic continuations into ProveIt

`fast_arithmetic_continuations.patch` applies at the **ProveIt repository root**.
Every path begins with `Topology/UnknotRecognition/fast/`. It contains the source
changes, the new arithmetic and local-obstruction modules, both new test files,
two local PD examples, their certificates and the updated `fast/README.md`.
The tests use only files installed under `fast/`; they do not depend on this
research package's `experiments/` directory.

## Apply the patch

The patch was generated against the exact supplied
`upstream/Topology/UnknotRecognition/fast` snapshot. `patch_manifest.json`
records SHA-256 hashes for every baseline and resulting noncache file. It
identifies file bytes rather than asserting an unverified repository commit.
The baseline contains 73 files; the patched directory contains 81 files.
Thirteen paths are changed or added. No files are deleted.

From the repository root, use the actual path to the unpacked research package:

```bash
git apply --check /absolute/path/unknot_arithmetic_continuations/integration/fast_arithmetic_continuations.patch
git apply /absolute/path/unknot_arithmetic_continuations/integration/fast_arithmetic_continuations.patch
cd Topology/UnknotRecognition/fast
python -m unittest discover -s tests -p test_rational.py -v
python -m unittest discover -s tests -p test_tangle_obstruction.py -v
python -m unittest discover -s tests -v
```

`git apply --check` detects changed surrounding source before applying
anything. If your checkout has advanced beyond the supplied snapshot, review
and reconcile those differences before application. The package performs no
commit, push, or other repository publication.

## What is integrated

- Complete arithmetic recognition of a supplied finite Montesinos presentation,
  with actual PD construction and checked source provenance.
- A nonexpanding Python arithmetic API for binary continued-fraction coefficients.
- An opt-in local non-embeddability obstruction with a fixed pattern catalogue,
  exact four-port diagram matching and independently replayable certificates.
- Source/pickle/mirror checks, constructor-reinitialization protection, explicit
  expansion budgets and a clean `use_rational=False` / `--no-rational` ablation.
- The example PDs and certificate JSON files used by the local-pattern tests.

The ordinary recognizer does not run local catalogue search by default.
`recognize_with_subtangles` is an explicit Python wrapper. A bare arbitrary PD
never acquires a Montesinos source promise. The general Khovanov fallback and
its exponential worst-case scope remain in place.

## Recorded verification

[The final combined test log](../results/integrated_tests.txt) records:

```text
Ran 152 tests in 30.415s
OK
Process exit code: 0
Measured wall seconds: 30.651362
```

This run contains all 134 inherited test methods plus 12 new rational-arithmetic
and construction methods and six local-pattern methods. Test methods include
many enumerated or randomized examples; the count is not a count of diagrams.

[The isolated patch replay log](../results/patch_verification.txt) records a
second, specifically scoped integration check:

1. Copy all 73 exact baseline noncache files to a new temporary directory.
2. Verify every baseline file against its recorded hash.
3. Run `git apply --check`, then apply the patch at the temporary repository root.
4. Compare all 81 resulting files byte-for-byte with the delivered `fast/` tree.
5. Run `test_rational.py` and `test_tangle_obstruction.py` from that temporary
   `fast/` directory, with `PYTHONPATH` removed and no experiment-package imports.

Both new suites pass there. The patch and manifest exclude bytecode and cache
directories. These integration checks support the executable implementation;
the topological theorems and complexity claims are addressed separately in the
accompanying article.

## Scope of the command-line interface

The ordinary CLI loads and validates a Diagram. Its Montesinos converter has
a default 100,000-crossing expansion limit. Huge binary coefficients should
use `fastunknot.montesinos_certificate(e, tangles)` directly, which performs no
crossing expansion. This is a separate explicit API, not an implicit CLI mode.

Examples, input grammar, certificate semantics and the optional local wrapper
are documented in the new final section of `fast/README.md` installed by this
patch. Raw benchmark results are retained in
[`results/benchmarks.json`](../results/benchmarks.json), including censored
baseline outcomes and regressions from the optional local search.
