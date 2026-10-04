# Portable replay of the independent fixed-word invertibility audit

This directory is a release adapter. It does not change the scientific proof or the independent checker. Only the authenticated, reviewer-owned `independent_affine_checks.py` is executed. The author checker, source rules, copied positive-compiler proof, and all other science files are read exclusively as inert bytes.

## Portable layout and invocation

The three input directories can be relocated anywhere and need not have fixed names. A convenient layout is:

    package/science/   complete frozen fixed-word-invertibility61 packet
    package/audit/     complete frozen independent audit packet
    package/replay/    this directory

Use Python 3 on a POSIX system with `O_NOFOLLOW`. No third-party package is required. Supply canonical absolute paths, without symbolic links, `..`, `.` components, repeated separators, or trailing separators. The output's parent must exist; the output itself must not exist. It must be outside all three input directories.

    python3 -I -S -B /absolute/package/replay/replay.py \
      --science-root /absolute/package/science \
      --audit-root /absolute/package/audit \
      --pins /absolute/package/replay/PINNED_INPUTS.json \
      --output-root /absolute/fresh-replay-output

First authenticate this adapter against the release's externally supplied hashes. Its hard-coded SHA-256 pin authenticates `PINNED_INPUTS.json`; that file authenticates every science/audit file and the complete directory inventories, including empty or extra directories. File modes and modification times may differ after extraction, and read-only inputs are supported. Their actual values at replay entry must remain unchanged through the run.

The fixed trust anchors are:

* Science manifest: `715bbbc817188a1a4d90ea7ad673fe4c69a9df105e202828c1835ae308e6f7eb`
* Scientific audit manifest: `dbbc49723fad5b5ab34cd8dab1b8824d66d22b50e384d948e1de0576b7e16aef`
* Unchanged independent checker: `173eb6d22f7b69dd8a96f444fc422c841e2045b07b3ac9dd74a90d3654e66b92`
* Deterministic evidence JSON: `3a6d31b564f70ccb5173c8997a9e69f2389ee9fc8867ccbcefb112457a1643cb`
* Complete input pins file: `2833e4e52431a495f3923ab6852484c749c550b7e4bab89949ff8a5c1b4d515f`

## What a successful replay establishes

1. The supplied science and audit roots exactly match the complete pinned byte inventories. Missing, extra, corrupted, linked, or special-file inputs are rejected before creating output.
2. The input roots are disjoint. Lexical aliases, symbolic links in root paths or their ancestors, hard-linked files, duplicate filesystem identities, output overlap and reused output directories are rejected. Existing directory identities are also checked against output ancestry.
3. The authenticated checker is copied byte-for-byte into a newly created output directory, then run there with isolated Python (`-I -S -B`), a minimal environment, no stdin and a 30-second timeout.
4. The resulting `independent_affine_evidence.json` must equal the frozen expected file **byte for byte**, and the copied checker must still equal its pinned input bytes. No tolerances, normalization, JSON reserialization or ignored fields are used for that comparison.
5. The checker's stdout contains its destination path. Its bytes are therefore compared with the exact expected stdout for this new path; they are not claimed to equal the old path-bearing `execution_receipt.txt`. Stderr must be empty.
6. Complete input inventories, bytes, modes, modification times and relevant filesystem metadata are rechecked. The adapter writes `replay_receipt.json` only after successful checks.

A successful output directory contains the unchanged checker copy, deterministic evidence JSON, `execution_stdout.txt` and `replay_receipt.json`. A rejected run after output creation may leave diagnostic partial output. Do not reuse that directory: inspect it and choose another fresh output path.

The replay verifies the finite exact arithmetic receipt. The generic mathematical theorem, all-chamber sufficiency/necessity, and compiler composition still rely on the accompanying human-readable proofs and review. This is not a proof-assistant certificate.

## Replaying the release tests

The test harness creates new fixture copies, changes only those copies, and invokes the adapter. It never modifies original science/audit inputs and never executes author code. Run it without Python optimization, because its test expectations use assertions.

    python3 -I -S -B /absolute/package/replay/test_replay.py \
      --science-root /absolute/package/science \
      --audit-root /absolute/package/audit \
      --adapter-root /absolute/package/replay \
      --work-root /absolute/fresh-test-work

Tests cover ordinary execution, read-only relocated inputs, complete read-only relocation of adapter plus inputs, bad pins, changed science/checker/evidence, extra/missing files and directories, symlink/hardlink/special-file rejection, aliases, overlap and nonfresh output. The harness records complete case results in its external `TEST_RESULTS.json`. The release includes a frozen copy of the actual test receipt, bound to the tested adapter and harness hashes.

## Precise isolation limitations

This adapter is **not an operating-system or network sandbox**. It does not install seccomp, namespaces, containers, a read-only mount or a network firewall. It does not claim to withstand a compromised Python interpreter/standard library, malicious kernel, hostile concurrent filesystem replacement or adversarial mount manipulation. Use trusted Python and a quiescent filesystem; stronger isolation must be supplied externally if required.

`-I -S -B` prevents ambient Python path/site customization and bytecode writes; the minimal subprocess environment removes inherited customization variables. Integrity checks and link/overlap guards are intended to reject wrong inputs and accidental aliasing. Before/after metadata checks detect persistent mutation but are not a transactional filesystem lock and cannot prove the absence of a change-and-restore race. Access times are intentionally excluded because ordinary reading may update them. Read-only relocation tests set files to 0444 and directories to 0555; they are permission tests, not a sandbox claim.

No author scientific executable, upstream compiler, physical simulator or stored schedule is run by this release. The source and audit packages remain byte-identical to their previously frozen versions.
