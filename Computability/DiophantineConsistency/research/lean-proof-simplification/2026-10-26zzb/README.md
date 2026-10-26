# Residual Lean proof simplifications for ProveIt

Research date: 26 October 2026.

Reviewed repository: https://github.com/VladimirReshetnikov/ProveIt

Final reviewed commit: `3b51c69d42ff99bc420698532af3fe1d1f9bd356`.

Start with **report.pdf** for the complete argument, mathematical statements, source accounting, exclusion decisions, and references. Its complete editable source is **report.tex**, together with **validation-summary.tex**.

## The three retained proposals

| Proposal | Baseline | Established benefit |
| --- | --- | --- |
| Whole-list Horner certificate | Current 426-line common-modulus `CurrentKernelResidues2011.lean` | Complete proposed module has 183 lines: 243 fewer physical lines and 10,765 fewer bytes; one kernel-checked whole-list certificate replaces 59 numerical chunk facts. |
| Constructor-only Option decision | The 85-line semantic module from incoming proposal A | Complete cleaned module has 76 lines: nine fewer lines and three fewer private declarations, including the narrower import. |
| Direct signed rank-prefix congruence | Existing rank polynomial and natural four-block parity route | A weaker theorem interface works with signed upper fields and before natural packing bounds. No positive net line saving is claimed. |

The Horner count is an exact comparison with the reviewed maintained file, **not an aggregate incremental total against an imaginary merge of all prior proposals**. Earlier generic block assembly work may already remove some length/append boilerplate. The additional whole-list traversal and deletion of the remaining 59 closed numerical chunk facts are the new residual mechanism.

The Option patch assumes the earlier supplied-program-to-computability migration has already been applied. The much larger migration, semantic split, and removal of 32 private `pr_*` proofs are prior work and receive no new credit here.

## Contents

- `report.pdf`, `report.tex`, `validation-summary.tex`, `Makefile`: report and build inputs.
- `lean/HornerResiduePilot.lean`: proved accumulator invariant and actual 941-row numerical replay.
- `lean/RankPrefixPilot.lean`: direct signed rank-prefix theorem, natural witness adapter, and separating examples.
- `lean/TagOnlyDecision.lean`: exact predecessor reconstructed under a separate namespace, compared by `rfl` with the separately compiled cleaned module.
- `lean/TagOnlyTargetAudit.lean`: checks the actual cleaned semantic declarations and their axioms.
- `proposed/DiophantineConsistency/`: complete proposed Horner and semantic modules.
- `patches/`: the two production deltas, each with a different explicitly stated baseline.
- `baselines/`: exact predecessor files for reproducible patch checking.
- `scripts/verify_horner_data.py`: ordered-data and residue audit against a ProveIt checkout.
- `scripts/check_patch_baselines.py`: apply each patch in an isolated temporary directory and verify exact agreement with the supplied proposed file.
- `evidence/`: compiler outputs, source and dependency provenance, source measurements, final snapshot, and novelty inventories.
- `notes/`: detailed supporting notes for the three proposals.
- `REPOSITORY_LICENSE.txt`: license accompanying the repository-derived code and fixtures.
- `SHA256SUMS`: hashes of all other packaged deliverable files.

Working-machine paths in historical validation receipts identify the commands actually run. The portable commands below reproduce the same proof checks from a normal checkout; the historical helper and cached binaries are not required.

## Verified results and limits

The checks used **Lean 4.32.0**, compiler commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, and **mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`**, as pinned by the repository.

- Horner: the general invariant and whole actual row fixture passed Lean checking. The finite residue used `decide +kernel`. The ordered fixture agrees with the maintained data. The complete changed production module and downstream clients have not been rebuilt.
- Option: the complete cleaned production module compiled. Its 14 repository semantic dependencies were source-matched and freshly compiled. The exact predecessor's halting observation equals the cleaned observation by `rfl`. The patch applies to the exact predecessor. This is a target-module check, not a complete replay of the prior migration or a whole-repository build.
- Rank: the exact polynomial prototype, prefix theorem, natural adapter, and closed stress examples passed Lean checking. The production consumer was not integrated or rebuilt.

The pilots introduce no axioms, `sorry`, or `native_decide`. The Horner invariant reports `[propext]`, and its finite certificate reports `[propext, Quot.sound]`. The rank theorems and actual semantic endpoints report the ordinary `[propext, Classical.choice, Quot.sound]` dependencies. The generic Option constructor observation is axiom-free. These reports do not imply an axiom-set reduction for the actual semantic function.

No performance improvement is claimed. No whole-repository build is claimed.

## Reproduce the Lean checks

Use a full checkout at the reviewed commit with its pinned dependencies. Let `review_bundle` be the absolute path to the extracted archive directory. The commands below do not apply patches or replace maintained source files.

```bash
cd /absolute/path/to/ProveIt
review_bundle='/absolute/path/to/extracted/proveit_lean_residual_simplifications_2026-10-26'

# Install/retrieve the pinned mathlib dependencies using the repository's usual setup.
lake exe cache get

lake env lean --root="$review_bundle/lean" "$review_bundle/lean/HornerResiduePilot.lean"
lake env lean --root="$review_bundle/lean" "$review_bundle/lean/RankPrefixPilot.lean"

python3 "$review_bundle/scripts/verify_horner_data.py" "$PWD"
python3 "$review_bundle/scripts/check_patch_baselines.py"
```

For the complete cleaned semantic module and its comparison checks:

```bash
lake build BusyBeaver.ZFC.EnumPerm
lake build Mathlib.Computability.Primrec.Basic
mkdir -p "$review_bundle/.build/DiophantineConsistency"

lake env sh -eu -c '
  review_bundle=$1
  export LEAN_PATH="$review_bundle/.build:${LEAN_PATH:-}"

  lean --root="$review_bundle/proposed" \
    -o "$review_bundle/.build/DiophantineConsistency/EnumeratorSemantics.olean" \
    "$review_bundle/proposed/DiophantineConsistency/EnumeratorSemantics.lean"

  lean --root="$review_bundle/lean" \
    "$review_bundle/lean/TagOnlyDecision.lean"

  lean --root="$review_bundle/lean" \
    "$review_bundle/lean/TagOnlyTargetAudit.lean"
' sh "$review_bundle"
```

The current directory remains the repository root, preserving relative Lake paths. The explicit source roots give the proposed semantic file its proper module name. The `.build` prefix makes both audits import the freshly compiled semantic module. The broad Primrec import is required by the predecessor reconstruction in `TagOnlyDecision.lean`; the cleaned production file itself uses the narrower Encodable import.

## Patch baselines and future integration

**Horner patch:** `patches/current-kernel-horner.patch` targets the current common-modulus module at the final reviewed commit. Its baseline SHA-256 is:

`f16f792f4449e423bfa6165f81a6b6e3d8c872531b4e428aaf0bebafd178a659`.

**Option patch:** `patches/tag-only-option.patch` targets the semantic module introduced by `patches/01-certificate-dependency.patch` inside the prior incoming archive `ProveIt_Proof_Simplification_Review_2026-10-26.zip`. Apply that earlier proposal first. The new patch is not intended to apply directly to the unmodified current repository. Its baseline SHA-256 is:

`4d9cc3b56f5a5d7a07bc443fbe0eee2a2201f2e8cd5ddbb0cfd3f7ce1b30b11d`.

Inspect and rebase either patch if its target has changed. After applying the Horner patch in a review branch, the focused production integration gate is:

```bash
lake build \
  DiophantineConsistency.CurrentKernelResidues2011 \
  DiophantineConsistency.CurrentKernelResidues2011Checks \
  DiophantineConsistency.CurrentControllerUnits2011 \
  DiophantineConsistency.CurrentControllerUnits2011Checks
```

Those are future integration commands, not a record of a build already performed. The rank pilot has no production patch because the interface decision and the complete helper-plus-client change should be reviewed first.

## Novelty review

The final exclusion snapshot contains **43 placed proposal packets and seven incoming ZIP archives**, 50 packet packages in total. Its incoming inventories contain 2,051 member entries. The combined text inventories have 4,155 entries, including copied source, tests, patches, and supporting notes. The principal-report pass initially indexed 117 TeX inputs; the four late incoming archives were inspected separately.

`evidence/novelty/freshness-addendum.md` and `candidate-decisions.json` give the final decisions and take precedence over historical working-stage observations. `novelty-audit.md` supplies the broader mechanism comparison. The manifests distinguish inventory/search coverage from reading each file in full. No claim of absolute mathematical novelty is made.

The initial and final snapshots differ by twelve commits. A late incoming proposal exactly matched an initially investigated code-derived-computability refactor; it was withdrawn. Its much larger patch and generic prototype are deliberately absent from this archive. Only the separate nine-line cleanup of its deliberately retained state scaffold remains.

## Rebuild the PDF

Install XeLaTeX, latexmk, the packages used in `report.tex`, and the fonts Latin Modern Roman, DejaVu Sans, and DejaVu Sans Mono. From this directory run:

```bash
make pdf
```

The PDF is a rendered twelve-page research report. Its code blocks, equations, tables, citations, and page boundaries were visually checked. Rendered QA images and TeX intermediate build files are not packaged.
