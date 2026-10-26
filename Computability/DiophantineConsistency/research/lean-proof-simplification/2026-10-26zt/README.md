# Three further Lean proof simplifications

This packet proposes three residual simplifications for ProveIt/DiophantineConsistency after treating all earlier recommendations as available.

Proof/patch baseline: `f00ba53b331833c6cb64707bd90e48489e5610f5`. Closing source/exclusion cutoff: `60fcb2a69b7f1fdd4c3592ea5f164223cad50abe`, with **43 prior packets**. All fourteen audited target/dependency/build-pin identities are unchanged, while other transitive modules did change; no full build at the later commit is asserted.

The detailed, source-linked explanation is in **report/report.pdf**; its complete LaTeX source is **report/report.tex**.

## Findings

1. **Recover a redundant source guard.** The first two literal source rows and only `x 24 > 0` imply `x 0 > 0`, `ports 0 > 0`, and `8 ≤ x 16`. Natural-coordinate types supply the other sign conditions. The independent beta-positive argument can therefore be removed from appropriate source-facing bootstrap theorems.
2. **Compare the two rotation parameters directly.** Equality of the partial-bit phase and the cyclic whole-digit quotient gives equality of binary rotations for arbitrary natural digits. This removes the Boolean hypotheses from the recent `rotation_eq` and `normalization_rephase` statements. The same idea proves exact period reduction modulo `v*n`.
3. **Use interval separation for internal division.** The proof `qd+r < qd+d ≤ q'd ≤ q'd+r'` removes a remainder-gap witness and an artificial self-inequality witness. An optional checked version uses the previously proposed ordered-semiring interface to remove both gap witnesses.

The full explanation includes the nearest prior proposals, guard boundaries, and counterexamples. Generic source-scale decoding, host-Nat division uniqueness, and prior cyclic-word APIs are not counted as new work.

## Verification scope

Five Lean files have passed Lean 4.32.0, with fifteen printed endpoint audits containing only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, or subsets.

- The beta client is freshly elaborated against the actual `SplitCertificate59.sourceRows` definition. The cached import's full source is byte-identical to the reviewed version; its entire dependency closure was not rebuilt.
- The current `NativeCyclicConvolution` and `NativeCyclicRotation` modules were freshly compiled before the final rotation-kernel checks. Deeper dependencies were reused.
- The private internal-division proof skeleton is checked abstractly with its required order laws.
- Both production patches apply to the pinned source. The complete rephase and ObjectDivision modules, their downstream clients, and the full beta-signature migration are **not** claimed as built or integrated.
- The local rephase patch removes two physical lines and two hypotheses. The local division declaration removes two nonblank lines and adds no helper/import. Explanatory kernels are additional code, so there is no claimed package-wide or counterfactual net reduction.

See `evidence/packaged-validation.json` and the original logs for exact observations. The report and closing audit identify the baseline and any later source/corpus refresh.

## Files

- `lean/`: five checked Lean files.
- `patches/`: two candidate production patches.
- `candidates/`: complete corresponding candidate source files for inspection.
- `evidence/`: hashes, original compiler receipts and logs, call sites, novelty audit, and independent review.
- `scripts/replay.py`: portable focused replay without applying source patches.
- `scripts/build-report.sh`: LaTeX build.
- `SHA256SUMS`: deliverable integrity manifest.

## Reproduce

Use a checkout with the exact source bytes recorded by `evidence/source-manifest.json`, the pinned Lean 4.32.0 toolchain, and its Lake dependencies.

```sh
python3 scripts/replay.py /path/to/ProveIt --plan-only
python3 scripts/replay.py /path/to/ProveIt
sh scripts/build-report.sh
```

The plan-only command verifies target identities, kernel hashes, and patch applicability. The complete command builds the focused prerequisites and compiles the five kernels into `replay-results/`. It does not apply either production patch. Building the complete patched production modules is a distinct integration step.

No repository commit, pull request, or external publication is included in this deliverable.
