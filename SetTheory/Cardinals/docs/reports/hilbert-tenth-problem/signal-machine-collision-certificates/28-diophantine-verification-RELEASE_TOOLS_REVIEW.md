# Report58 release tools: independent review

**Result: PASS for the exact revised scripts below.** The initial guard defects were reported before author changes and were reproduced only in disposable fixtures. The revised versions pass 65 independent adversarial checks and the 38-case built-in suite.

## Exact reviewed inputs

- `build_report.py`: `568c6e9edb68317d859e978f5f7fc697b4fb7ec56621b4babd72b8a49ff1ff3c`
- `release.py`: `ffbf26de30fa86314dc7b0811c924565d2ce410cd0fd797b44f14e3434f9f0b7`
- `test_release.py`: `d38f127ec95c3e1f538d5ba7023527a5a49ad3dca6c612e4259b299212d78165`
- Manuscript: `cc1ffd8ce344dcf45d89d40d4ceadff8eb2decc513c595bdf7b4462465864e89`
- PDF: `af5c8fcda60078976735473b16c027963ce68ee4e1ca58b2581a143fd79b837e`
- Companion review evidence: `c9593201afbeb3f1822c39d444785e620aaa221112db19fe73f006390fca8f1e`

## Results

1. Canonical fresh external outputs and receipt paths are enforced. Existing outputs, relative/dot/dot-dot/double-slash/trailing-slash aliases, symlink paths, dangling links, hard links, FIFOs, and release overlap are refused in the tested cases. Source symlinks, hard links, and FIFOs are rejected before TeX runs.
2. All three programs require isolated Python startup, disabled site imports and bytecode writes, and no optimization. Missing flags and both optimization levels are refused.
3. The manifest catches added, removed, changed, and type-replaced files and directories, including empty directories; unsafe entries and noncanonical manifests are rejected. Sealing now requires regular-file prerequisite entries.
4. ZIP output has sorted file and directory entries, fixed timestamps and Unix modes, and ZIP_STORED compression. Two archives remain byte-identical after source timestamp changes. A fresh extraction passes full inventory verification and retains empty directories.
5. Three clean PDF rebuilds reproduce the exact packaged PDF and all 19 page PNGs. An observed build starts with an empty format directory and all three compilation passes load its freshly generated format (SHA-256 `1a80e73aa37d747fc843542303cf00e142579dbbdd89d72af995f4f83e84d841`). Hostile parent PATH, HOME, TeX, and date variables do not affect the result. Subprocesses use the minimal environment, absolute installed executable paths, and disabled shell escape/font generation.
6. The final compilation has no overfull, underfull, undefined-reference, or undefined-citation warnings. Its one warning states that epstopdf shell escape is disabled, which is expected.
7. All 202 recorded system TeX/font-map inputs and all six executable entries were independently rehashed without a mismatch. The documented provenance excludes dynamic libraries and a complete OS image.
8. The full 33-file science inventory and 11-file root independent-audit inventory remain byte-identical. No scientific, author, emitter, upstream, saved-program, physical-simulator, trajectory-replay, or Lean code was executed.

## Defects found and resolved

The initial test tool accepted a dot-dot receipt alias into its own fixture release and wrote the receipt after reporting preservation. It also accepted a double-slash path and optimized startup. The initial release tool lacked invocation-flag enforcement and allowed a required receipt to be a directory. All six failing expected-refusal variants now refuse correctly. The companion JSON records both the superseded script hashes and the final tested hashes.

## Scope and limits

This is approval of the exact release/build tool versions, not a seal of the still-assembling parent package. Tests ran in isolated fixture trees. The final actual package must still be sealed, verified, archived, and extracted/reverified by the producer. Manifest integrity relies on the external release digest; receipt semantics and mathematical claims are not authenticated by these filesystem guards.

The checks reject static unsafe paths but are not designed as a race-hardened sandbox against concurrent filesystem replacement. Cross-installation TeX/Poppler reproducibility and complete operating-system provenance are not claimed. The separate manuscript reviewer owns visual and mathematical approval.
