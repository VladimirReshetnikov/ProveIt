# Corrected-code publication updates through 86267b8a3

**Bounded review: mathematical and repair-status transfer passes; one reproducibility correction is supplied.** The new text accurately describes the corrected Tree Calculus, reset-net and sparse-lattice APIs and preserves the previously printed formal mathematics. The historical replay instructions need to distinguish the recent checkout containing the replay helper from the historical checkout supplying its authenticated input files.

The reviewed range is exactly `3aa123856b850f016cfa100b4684fa7902d2cecd` through `86267b8a30bcf1e15e9254f4f4aa595d55481b2a`. It comprises the Tree update `c8d3ff5cb87e56cd4405ef92d315e05053fd75db`, reset update `5ac948652fe7c8f44856290ebb1fe7f438d8577e`, and sparse update `86267b8a30bcf1e15e9254f4f4aa595d55481b2a`: only each report's README, TeX article and PDF, nine paths in total. No program, fixture, receipt or correction note changes in this range.

The [portable checker](review_batch80_correction_publication_86267b8a3.py) authenticates every before/after blob, the relevant earlier review artifacts, historical replay helper/inventory, and three earlier API patches before checking them. The [deterministic receipt](review_batch80_correction_publication_86267b8a3.json) contains all full hashes. Git is used read-only; PDF inspection and patch application use temporary directories.

## New reproducibility issue and narrow repair

**P3 — invoke the later helper against the historical checkout, rather than from it.** At the pinned final revision:

- `canonical-diophantine-certificates/README.md:2421` directs the historical restoration to a checkout of `a7ae02511` without saying that the helper must come from a later checkout.
- `quadratic-orthant-certificates/README.md:764` repeats that description; the command at line 891 explicitly says to run the repository-relative helper from the root of the historical checkout.
- `signal-machine-collision-certificates/README.md:919` gives the helper with `--repo .`; the qualification at line 933 tells the reader to use the historical checkout.

Neither `replay_placed_substrates_a7ae02511.py` nor its required sibling `placement_a7ae02511_inventory.json` exists at the historical commit `a7ae02511c5584086ef9152f92d59ba77efa6148`. Thus the explicit reset recipe cannot find its script there. Conversely, passing the recent corrected checkout as `--repo` fails the helper's original-byte authentication, as the new documentation correctly warns.

The [README-only patch](batch80_historical_stager_launch.patch) fixes five passages in the three READMEs. Run the later helper from a recent checkout with its sibling inventory, while passing an unchanged historical worktree as `--repo`. This follows the actual helper interface: placed file bytes are read under the supplied `repo`, while the default inventory is resolved beside the helper. The preferred alternative—extracting the corrected archive into a disposable original-layout directory—remains unchanged. No TeX or PDF rebuild is required for this patch.

The checker proves the helper and inventory absent at the historical commit, authenticates their later bytes, checks the relevant source/CLI interface, and applies the proposed patch to private copies. It does **not** rerun the old full stager. Expected patched README hashes are:

| Report | Patched README SHA-256 |
|---|---|
| Tree | `8b877a0658a8ce8e159de0bd9c24d59b80d4ff70a4e94499e3bc2bfb043b7a6e` |
| Reset | `03c9c42c190499eae0f52d7616dbcaaebb2183a237fa20a5ba7207bfd2172836` |
| Sparse | `5e1818b7adc2a243437601a28baf023bbffd6c054a16f5bc5c5748d12804562f` |

This is a new launch-instruction defect, not a mathematical defect or a renewed demand to resolve earlier editorial patches. In particular, earlier Tree exact-size wording and base-case qualifications remain outside this publication-delta verdict. Their unchanged presence does not invalidate the reviewed transfer of the corrected-code status.

## Preserved mathematics and accurate correction claims

Every changed paragraph in all six textual files was read. The relevant evidence is the already completed [corrected-package review](review_batch80_corrected.md) and [corrected placement audit](review_batch80_corrected_placement_8a4e64732.md), together with the actual maintained source bytes. This review does not repeat the original theorem review or unchanged author suites.

The Tree notes correctly say that both codes are checked as exact nonnegative integers before cache lookup or evaluator-state changes. The independent patch was not applied verbatim; the delivered corrected kernel implements an equivalent guard. Five new test groups cover 303 parameter scenarios; the corrected replay schedule has 17 stages, or 20 with symbolic checks. The two old receipt changes are source-hash changes. The corrected archive's manuscript and PDF were unchanged at delivery; the assembled report PDF is rebuilt in the present publication update. These are different artifacts and the text distinguishes them.

The reset notes accurately describe exact Boolean duration options, exact natural initial counters, and supplied markings with exact known string places and natural values. This is a narrow public-boundary repair, not a comprehensive validation of arbitrary caller-supplied net/transition structures. The new correction suite's 64 rejected calls, nine schema hashes, 388 stored legal firings and 72 weighted overlaps agree with the previous review. The documented optimized runs concern the explicit new guards; they do not certify all historical assertion-based programs under `python -O`.

The sparse notes accurately require immutable exact tuple terms, exact integer indices and coefficients, nonzero coefficients, sorted variable indices and distinct sorted monomials. Negative parameter indices, repeated power indices, and zero/constant polynomials remain valid. The stated 24 malformed categories and 2,700 exact expression comparisons on 300 pairs agree with the correction review. The baseline false-zero example and the limited meaning of the `noncanonical_examples_accepted=3` diagnostic are appropriately described. The optional source-fixture regeneration explains the distinct stage totals. The earlier natural-domain witness projections and congruence reduction remain separately attributed and are not presented as new universal arithmetic bounds.

The claims that the earlier patches should not be reapplied are also checked literally, without executing corrected source: the old Tree and reset patches fail on the already repaired files, while the old sparse patch applies and adds a second `Poly.__post_init__` definition. This verifies the new warning rather than proposing any further API change.

The corrected source files still equal their bytes at placement `8a4e647326e8c92f53e222c10e9107b40918a1ff`. Package-prefix inventories contain 53 Tree, 54 reset and 38 sparse files. Total assembled report counts are respectively 298, 174 and 218 files. The new provenance text correctly distinguishes original placement from the later corrected-file replacements and additions, and continues to disclose flattened-layout limitations.

## Exact occurrence preservation and PDF limits

The checker compares ordered **literal occurrences**, preserving duplicates. It consumes every occurrence of each declared theorem-style environment and `proof`, every supported display environment and bracket display, every label, and every mathematical macro-definition line. The brace-display scanner excludes TeX row-spacing commands such as `\\[4pt]`.

| Report | Formal/proof occurrences | Display environments | Bracket displays | Labels | Macro-definition lines |
|---|---:|---:|---:|---:|---:|
| Tree memoir | 1,054 | 602 | 538 | 1,550 | 137 |
| Quadratic orthant | 166 | 135 | 126 | 307 | 67 |
| Signal/sparse | 89 | 95 | 83 | 252 | 36 |

Every listed occurrence remains byte-identical in the same order. These are source occurrence counts, not counts of distinct mathematical results, and they do not replace the reading of changed prose. In particular, new explanatory inline formulas are covered by that bounded prose read rather than an assertion that every inline-math occurrence was unchanged.

The pinned PDFs have 608, 169 and 120 pages and their extracted text contains the new corrected-code-edition discussion. This is a basic page/text check only. No PDF rebuild, visual layout audit, historical Windows runtime replication, or confirmation of the publication author's build logs was performed. The new reports' claims about their own reruns and visual/build quality remain attributed records; this audit does not relabel them as independently rerun here.

## Reproduction and scope

With Python 3, Git, `patch`, and the Poppler tools `pdfinfo` and `pdftotext`:

```sh
python review_batch80_correction_publication_86267b8a3.py \
  --repo /path/to/Proofs \
  --expect review_batch80_correction_publication_86267b8a3.json
```

The patch defaults to the sibling `batch80_historical_stager_launch.patch`; `--patch PATH` overrides its location while retaining the exact pin. `--output PATH` writes a deterministic receipt, and saved-receipt equality is recursively type-sensitive. All four artifacts are portable and have no fixed `/tmp` dependency. A fresh replay from outside the repository matched the saved receipt.

The result is bounded to these three publication updates. It introduces no arithmetic construction, no changed zero-set theorem, no fixed-arity or uniqueness claim, and no new universality assertion. Earlier mathematical and API reviews remain the evidence for the underlying reports.
