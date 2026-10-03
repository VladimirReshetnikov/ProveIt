# Replaying frozen reviews after archive placement

The [materializer](reviewed_report_archive_replay.py) restores all23 computational ZIPs from the fixed historical revision **55d248dc504cff215684773123b3b03a8b8ebbe3** into an external cache, preserving their original `docs/incoming` filenames. The [stable receipt](reviewed_report_archive_replay.json) pins every archive by byte length, SHA256 and Git blob identity: **60,110,941 bytes** altogether. It distinguishes12 archives covered by the named bounded intake reviews from11 additional relocated packages. Copying the latter is not a scientific review.

No old review source, note, receipt or dependency is changed. No ZIP is extracted, imported or executed. The helper uses `git show` on the exact full commit and literal path, verifies the bytes, and creates only cache files, the explicit current-source link below, and an optional receipt outside the repository. It does not run the large Grill review or any historical builder.

## Materialize and reuse a cache

Run from any directory, using absolute paths:

```sh
replay_repo=/absolute/path/Proofs
replay_wip="$replay_repo/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue"
replay_cache=/tmp/reviewed-report-cache

python3 "$replay_wip/reviewed_report_archive_replay.py" \
  --repo-root "$replay_repo" \
  --output-root "$replay_cache" \
  --expect "$replay_wip/reviewed_report_archive_replay.json"
```

`--repo-root` must name the actual Git worktree root and the historical commit must be available locally. No fetch or network operation is performed. The output cache must be outside the repository and must not contain it. Existing archive bytes are accepted only if identical. Differing files, symlink archive/receipt paths, symlink write-path ancestors and conflicting source bridges are rejected. Files are created exclusively rather than replaced. Use a private cache without concurrent path mutation.

The helper also creates exactly this link:

    cache-root/Computability -> repository-root/Computability

An existing link is accepted only if it resolves to that precise current directory; another link, file or ordinary directory at the bridge path is rejected. The helper never writes through it. This link lets old mixed-root verifiers see cached archives and current research files through the same `--repo` argument. Each frozen verifier still checks its own source, archive and member pins. The bridge does not override any pin failure.

The materializer supports normal and optimized Python equally; checks use explicit exceptions. Repeating the command, or using `python3 -O`, yields the same receipt and leaves existing archive bytes and modification times unchanged. Receipt fields contain no cache/repository absolute paths and no created-versus-reused counters. `--output /external/path/receipt.json` optionally writes that stable receipt, also refusing to replace differing existing bytes. `--expect` is checked with recursive type-exact equality before cache writes.

## Existing frozen command interfaces

The names of the older command-line arguments differ. In these examples, keep the source and `--expect` receipt in the original WIP directory:

```sh
# Archive-directory interface; this particular full Grill intake is expensive.
python3 "$replay_wip/review_incoming_matrix_grill.py" \
  --incoming "$replay_cache/docs/incoming" \
  --expect "$replay_wip/review_incoming_matrix_grill.json"

# Archive-only repository-shaped interfaces.
python3 "$replay_wip/review_parallel_particle_reports.py" \
  --repo-root "$replay_cache" \
  --expect "$replay_wip/review_parallel_particle_reports.json"

python3 "$replay_wip/review_binary_planar_four_particle31.py" \
  --repo-root "$replay_cache" \
  --expect "$replay_wip/review_binary_planar_four_particle31.json"

python3 "$replay_wip/group_directed_semigroup193.py" \
  --repo-root "$replay_cache" \
  --expect "$replay_wip/group_directed_semigroup193.json"

# Both archives and current WIP pins: uses the checked Computability link.
python3 "$replay_wip/review_incoming_negative_index_fibers.py" \
  --repo "$replay_cache" \
  --expect "$replay_wip/review_incoming_negative_index_fibers.json"

# Separate current-source and archive-directory arguments.
python3 "$replay_wip/review_incoming_counterexample_heights.py" \
  --root "$replay_wip" \
  --incoming "$replay_cache/docs/incoming" \
  --expect "$replay_wip/review_incoming_counterexample_heights.json"
```

An archive-directory option called `--archive-root`, where supported by another wrapper, likewise receives `cache-root/docs/incoming`; it is not synonymous with the repository-shaped `--repo-root`. None of the six specifically inspected frozen commands above exposes `--archive-root`, so that flag must not be added to them. The compatibility layer changes paths, not the old CLI schemas.

The193-generator and signed-index commands above were freshly replayed against the materialized cache and their original saved receipts: both passed. The other examples document the inspected interfaces; this task did not rerun their scientific checks. In particular the large matrix/Grill intake was not repeated merely to restore archive access.

## Relocation inventory

Permanent report locations below refer to the placement tree; they are reading locations, not byte-for-byte replacement inputs for ZIP-pinned reviews. Delivered manifests, duplicate context files, superseded editions and large regenerable data were not all staged at permanent locations. Repacking those directories would not reproduce the authenticated original archives.

The first11 retired archives were placed or superseded by

* **49dfa8fd6c7d178f4b4537e1c87a57831c3a5201**, the four mass/shuttle packages;
* **2f58ab4e92dea865e0b25a43925970cf92e9e324**, Grill/native/index/height/matrix packages.

They were merged by **da879508944d2c170378200bac0e7c6e5d51e2be**. The remaining12 archives were retired by

* **bca6383e99506fb6cfba6da55a78e6b3c7211274**, the six five-particle series packages;
* **7d2b1b2459cd9500a159ca36b4eadf7a183aae78**, the six compact-clock/parallel packages.

Their combined placement head is **9cad538807bf89c6693a9555f671a1f80c21cd31**. These full revisions are provenance only; the original bytes for every replay come from the single historical revision named at the top. The helper verifies that its23 literal ZIP paths exactly match that revision's `docs/incoming` ZIP inventory.

| ZIP basename | Report | Status in this replay inventory | Permanent report/source |
| --- | --- | --- | --- |
| `Two_Parallel_Conservative_Involutions_Package.zip` |26|Reviewed intake|Five-particle, `26-parallel-involutions-`|
| `Sparse_Parallel_Particle_Evaluation_Package.zip` |27|Reviewed intake|Five-particle, `27-sparse-parallel-`|
| `Canonical_Parallel_Quartic_Certificates_Package.zip` |28|Reviewed intake|Five-particle, `28-parallel-quartic-`|
| `Canonical_Histories_and_Infinite_Fibers_Package.zip` |22|Reviewed intake|Signal-machine Part VIII, `23-canonical-fibers-`|
| `Entire_Native_Witness_Fiber_Package.zip` |25|Reviewed intake|Fixed-universal Part III, `07-native-fiber-`|
| `Failure_of_Positive_Index_Restoration_Package.zip` |33|Reviewed intake|Fixed-universal Part IV, `10-index-restore-`|
| `Fixed_Universal_Grill_Polynomial_Package.zip` |23 original|Reviewed intake|Superseded; no separate permanent copy|
| `Fixed_Universal_Grill_Polynomial_Package (1).zip` |23 revision1|Reviewed intake|Fixed-universal Part I, `11-grill-poly-`|
| `Native_Grill_Exact_Degree_Laws_Package.zip` |24|Reviewed intake|Fixed-universal Part II, `14-degree-laws-`|
| `Universal_Matrix_Semigroup_and_Diophantine_Certificates_Package.zip` |32|Reviewed intake|Group-theoretic Part V, `08-matrix-semigroup-`|
| `Binary_Planar_Four_Particle_Shuttle_Package.zip` |31|Reviewed intake|Signal-machine Part VII, `21-planar-shuttle-`|
| `Counterexample_Height_Expansions_and_Rotation_Discrepancy_Package.zip` |34|Reviewed intake|Fixed-universal Part IV, `05-signed19-heights-`|
| `Timed_Four_Mass_Quartic_Certificates.zip` |Timed addendum|Relocation only|Signal-machine Part VI, `18-timed-quartics-`|
| `Dimension_Independent_Particle_Thresholds_Package.zip` |29|Relocation only|Signal-machine Part VII, `19-mass-four-zd-`|
| `Sparse_Orbit_Geometry_and_Exact_Counting_Package.zip` |30|Relocation only|Signal-machine Part VII, `20-orbit-geometry-`|
| `five-particle-binary-portable.zip` |14|Relocation only|Five-particle, source14|
| `Reversible_Binary_Five_Particle_Package.zip` |15|Relocation only|Five-particle, base article/source15|
| `Literal_Universal_Reversible_Source_Package.zip` |16|Relocation only|Five-particle, source16|
| `Reversible_Startup_Optimization_Package.zip` |17|Relocation only|Five-particle, source17|
| `Cellular_Clock_Domination_Package.zip` |18|Relocation only|Five-particle, source18|
| `Exact_Lazy_Reversible_CA_Evaluator_Package.zip` |19|Relocation only|Five-particle, source19|
| `Event_Budgeted_Quartic_Certificates_Package.zip` |20|Relocation only|Five-particle, `20-event-budget-`|
| `Unbounded_Compact_Clean_Clocks_Package.zip` |21|Relocation only|Signal-machine Part VIII, `22-clean-clocks-`|

The permanent directories are [five-particle binary automata](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/five-particle-binary-automata/README.md), [signal-machine collision certificates](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/README.md), [fixed universal polynomials](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/README.md), and [group-theoretic substrates](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates/README.md). Exact source-reference paths accompany every inventory record in the receipt. “Reviewed intake” refers only to the scope of the corresponding frozen bounded reviews, not a blanket certification of every article, theorem, code file or numerical claim in that archive.

## Verification boundary

Author checks exercised a fresh external cache, normal and optimized exact receipt replay, repeated idempotence with byte/mtime checks, and eight refusals: repository-contained output, cache-root symlink, archive-parent symlink, differing archive bytes, a different source bridge, receipt-parent symlink, receipt-leaf symlink and differing receipt bytes. Existing sentinels remained unchanged. All23 reconstructed files matched their exact historical byte/hash/size pins.

This packet establishes archive availability and faithful relocation instructions. It neither changes the mathematical frontier nor reopens the scientific scope of the frozen reports. The current-source bridge intentionally exposes the current pinned research files; it does not create a historical checkout or guarantee that arbitrary future source changes will satisfy old pins.
