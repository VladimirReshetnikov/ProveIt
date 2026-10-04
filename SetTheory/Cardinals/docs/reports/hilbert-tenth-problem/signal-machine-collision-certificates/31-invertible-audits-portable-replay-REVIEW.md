# Independent review: portable fixed-word invertibility replay

Review date: 2026-10-04 UTC

## Verdict

**Accepted for the documented, release-only purpose, with explicit trust and isolation limitations.** No remaining blocking defect was found in the final inspected adapter or test harness. Two harness defects found during review were fixed and independently regression-tested before this verdict: unsafe work-root alias handling, and optimized Python disabling assertion-based test checks.

This verdict is about authenticating and replaying the unchanged independent exact-arithmetic checker. It is not a new validation of every mathematical claim in the proof, and it is not certification of an operating-system or network sandbox.

## Files to which this verdict applies

All SHA-256 values below identify exact bytes. The adapter was unchanged during review; the harness was amended in response to findings.

| File | SHA-256 |
| --- | --- |
| `replay.py` | `55f9af05403c943440f5aeb4aef1c5fe7f0e4b4d4f61309cee2c78c1c7420f72` |
| `PINNED_INPUTS.json` | `2833e4e52431a495f3923ab6852484c749c550b7e4bab89949ff8a5c1b4d515f` |
| `test_replay.py` | `8f388b0943f5c69c98999a175bf3ca901ed182999b9d5f6cd939add8eea19749` |
| `README.md` | `d6a963fadeaba8f73ef0400da1b8b70a58fbf9f091525a5d83307b2088585c7d` |
| Reviewer `independent_affine_checks.py` | `173eb6d22f7b69dd8a96f444fc422c841e2045b07b3ac9dd74a90d3654e66b92` |
| Expected `independent_affine_evidence.json` | `3a6d31b564f70ccb5173c8997a9e69f2389ee9fc8867ccbcefb112457a1643cb` |

The externally supplied release hash of the adapter is a necessary trust anchor. Its internal constants cannot authenticate a maliciously replaced adapter itself.

## What was inspected and established

1. **Complete inventory authentication.** The pinned manifest covers 10 science files plus its root and two subdirectories, and 9 audit files plus its root. The pins file itself is authenticated before JSON interpretation. `authenticate` rejects entries outside the pinned file/directory sets, missing entries, wrong types, symbolic links, hard-linked files, and mismatched byte lengths or SHA-256 digests. Extra empty directories are not ignored. File modes and timestamps are intentionally not fixed to packaging-time values, allowing relocation and read-only extraction.

2. **Explicit, disjoint paths.** Required command-line paths are canonical absolute spellings. Existing path components are checked for symbolic links. Science/audit overlap, output overlap with either input or the adapter directory, existing outputs, duplicate input filesystem identities, and output ancestry aliasing protected directories are rejected. These checks defend ordinary accidental aliasing on the documented POSIX filesystem model; they are not a guarantee against adversarial mount or concurrent-path replacement.

3. **Narrow scientific execution.** The adapter reads the science and audit trees as data. It retains the authenticated reviewer checker in memory, creates a fresh external directory, writes a single-link byte-identical checker copy there, and invokes trusted Python with `-I -S -B`. The checker source was inspected: it imports standard-library modules, performs reviewer-authored exact `Fraction` identities and interval-endpoint checks, reads its own bytes for a digest, and writes its evidence JSON next to the copy. It does not import the science checker, load source rules, run dependency code, invoke a simulator, or execute a stored schedule. The adapter and test harness themselves are, of course, executed release infrastructure; the scientific payload is only the unchanged reviewer checker.

4. **Exact output comparison.** The adapter requires zero exit status, empty stderr, exact path-dependent stdout, an exact initial output inventory, unchanged copied-checker bytes, and evidence bytes identical to the frozen expected file. It does not weaken evidence checking through JSON normalization or numeric tolerance. The old audit stdout receipt contains a different destination path and is correctly not claimed to be byte-identical to new stdout.

5. **Preservation checks.** After the checker process ends, even on process failure or timeout, the adapter reauthenticates both full trees and checks their recorded device, inode, mode, link count, size, and nanosecond modification time. It also rereads and rechecks the pins file. The successful receipt is written only after the remaining output checks. Reads can change access times; atime is deliberately excluded. The claim is not about ownership, ACLs, extended attributes, or change-and-restore activity between observations.

## Findings resolved during review

### R1. Test harness could create work inside an aliased input

The original harness used lexical `Path` comparisons for its work-root safety checks. With copied inputs, a symlink named `alias-to-science` pointing at the copied science root let `--work-root alias-to-science/new-work` pass the harness checks. The harness created `science/new-work`; its subsequent adapter invocation rejected the symlinked output ancestor. Thus the adapter failed safely, but the harness had already changed its input copy.

This was reproduced only on newly made review fixtures. Neither original frozen tree was used as a mutation target. The initial probe's final diagnostic assertion expected the adapter to complain about the extra inventory entry; the actual first rejection was the linked output ancestor. That expectation mismatch did not invalidate the observed directory creation. The initial probe run therefore failed as a probe script and is not presented as a passing final validation.

**Resolution:** the final harness preserves raw path spelling until validation, rejects noncanonical or linked components before creating work, and checks work ancestry against directory device/inode identities from protected trees. An independent replay of the former hazardous case now rejects before any work directory appears and preserves the copied science snapshot exactly.

### R2. Optimized Python could disable test verdicts

The harness uses Python assertions for test expectations. Without a guard, `-O`/`-OO` removes those checks and can permit a misleading `passed: true` report. This was identified by source inspection; it was not necessary to execute an intentionally broken adapter.

**Resolution:** the final harness explicitly raises when `sys.flags.optimize` is nonzero, before parsing paths or doing filesystem work. The independent `-O` probe rejected and created no work directory. The parent release suite also includes this regression case.

## Validation evidence

### Parent-run release suite

The supplied `PARENT_TEST_RESULTS.json` is a byte-for-byte copy of the parent's final 27-case receipt. Its adapter, pins, and harness hashes match the inspected final files. It reports:

- Three successful executions: original roots; read-only relocated science/audit roots; and complete read-only relocation of adapter plus science/audit roots
- Guard rejections for changed pins, science, checker, and expected evidence; extra or missing inventory; symlink, hardlink, and special-file inputs; noncanonical paths; overlaps; reused output; and linked output ancestry
- Two harness self-guard regressions: linked work parent and optimized Python
- Original science/audit snapshots unchanged, and read-only relocated adapter/input snapshots unchanged

This reviewer inspected that receipt and final test source; the parent performed the full suite execution. It is not represented as a second independent execution of all 27 cases.

### Independently executed supplemental probes

`PROBE_RESULTS.json` records nine further adapter rejection cases, all passing without newly created output:

1. Missing pinned directory and its contents
2. Directory substituted for a pinned file
3. File substituted for a pinned directory
4. Symlink substituted for a nested pinned directory
5. Symlinked pins file
6. Hard-linked pins file
7. Ordinary file as output parent
8. Dangling output symlink
9. Missing output parent

It also records independent successful regression checks for the two resolved harness issues. `FROZEN_PRESERVATION.json` contains identical before/after snapshots of the original science and audit trees for this final supplemental run. The release tree was also unchanged during that run.

The supplemental probes do not execute the scientific checker: each adapter invocation is a pre-execution rejection case. No science/author program, dependency program, simulator, or stored schedule was executed by this reviewer. The parent suite's successful replays execute only the pinned reviewer checker copy.

## Residual limitations and unforced branches

- **No OS/network sandbox.** `-I -S -B`, a sanitized environment, a fresh cwd, and read-only input permissions are useful Python/runtime hygiene. They do not install an OS sandbox, deny network access, or prevent a process from accessing all resources available to its user. Trusted Python, its standard library, the kernel, and a quiescent filesystem remain requirements.
- **No adversarial concurrent mutation or mount test.** Before/after snapshots cannot exclude a change-and-restore race. Parent-directory traversal and path-based checker execution are not a transactional capability boundary. Bind-mount manipulation was not performed, and the documented disclaimer is necessary.
- **Error branches after payload execution were not fault-injected.** The 30-second timeout, checker failure, unexpected stderr/stdout/inventory, copied-checker mutation, and produced-evidence mismatch handling were inspected but not independently forced. Doing so by modifying the pinned checker would break the authorized exact-byte payload boundary. The negative evidence test checks a corrupted expected input; it is not a forced test of an altered checker-produced output.
- **Fresh output is single use.** A failure after output creation can leave partial files. This is correctly documented; a user must choose a new output path for a retry.
- **Portability is POSIX Python 3, not every operating system.** `O_NOFOLLOW` is required. Exact evidence generation remains dependent on the trusted interpreter/standard-library behavior; mismatches fail closed instead of being normalized away.
- **Scientific scope remains finite and explicit.** Reproducing exact arithmetic evidence and authenticating the prose do not mechanically prove the general theorem or compiler composition. Those still rely on the accompanying mathematical proof and human review.

No remaining limitation contradicts the final README's stated scope. Stronger isolation or a hostile-filesystem threat model would require a separately designed execution boundary and separate authorization.

## Review artifacts

- `REVIEW.md`: this portable written review
- `PROBE_RESULTS.json`: independent final supplemental outcomes
- `FROZEN_PRESERVATION.json`: final independent before/after preservation snapshots
- `PARENT_TEST_RESULTS.json`: copied final 27-case parent receipt
- `review_probes.py`: environment-specific source of the supplemental diagnostic runner; its hard-coded original paths are historical run inputs, not requirements of the portable release

Local `probes/` and `probes-final/` directories are inert diagnostic fixtures, including deliberately malformed inputs. They are not release inputs and should not be packaged as part of the review deliverable.
