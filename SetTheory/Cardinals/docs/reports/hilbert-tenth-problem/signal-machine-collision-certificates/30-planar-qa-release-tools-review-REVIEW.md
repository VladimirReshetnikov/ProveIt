# Independent review of the Report60 release and build tools

## Decision and binding

PASS for the final tool and manuscript checkpoint identified by `SOURCE_BINDING.json`, under the precise boundaries below. This review covers only `tools/release60.py` and `tools/build_report60.py`; it does not reopen the mathematical audit or execute scientific programs.

- Release tool SHA-256: `e25ada2779961601bae0288be90c732816f5d676637258db60aa152d1d4a8ad9`
- Build tool SHA-256: `7c0f8e9ba4a29f0be1b0d119c9ec3bfdbce17a55f1643c5ab6ccffd5e8e795ec`
- Standalone TeX SHA-256: `cf3c8355ed7603e314864e49ac665264962d78466f30a88151cbe5292c37faab`
- Reproduced 28-page PDF SHA-256: `94c0415bd31b9f588c579ffe5c63ac217c957e2568830e842292429c0f555a92`
- Preflight dependency-lock SHA-256: `e17fae69b920a561de81fd06b53eba171ac9aaf557d8bbf6bf2e64a41a226ca3`

## Method

The complete tool source was inspected before execution. Adverse tests run on fresh `copy2` copies; originals are not edited. Every command is invoked through `/usr/bin/python3 -I -S -B`, except deliberate interpreter-mode refusal tests. Snapshots bind every regular source file by SHA-256, byte length, mode, and nanosecond mtime. Generated outputs are outside each copied source root.

The build tool invokes only trusted installed TeX/Kpathsea/Poppler utilities by fixed absolute path. TeX is generated from a fresh format in a fresh private temporary tree, its environment is replaced, shell escape is disabled by both command-line and environment, and file access is restricted by TeX's paranoid policies. Scientific author programs, checker source bytes, collision schedules, physical simulators, and Lean sources remain inert throughout this tool review. The portable replay has a separate independent source review and is not rerun here.

## Findings and corrections

The initial version accepted additional empty directories inside a frozen scientific root. A copied-fixture probe demonstrated that defect. The final implementation rejects every extra empty directory and unexpected scientific/audit/dependency tree. The final builder also authenticates all 137 frozen source files, uses stable no-follow single-link reads, rejects symlink tool paths, verifies standalone TeX against the authenticated modular flattening, checks a pre-pinned dependency inventory before execution and the observed TeX input set afterward, and validates every rendered page's numbering and PNG structure/CRC. Malformed top-level manifest JSON now produces an explicit refusal.

## Tests

The final matrix contains 104 subprocess tests: 97 required refusals and 7 positive cases. Every required refusal returned exit status 2 with an explicit refusal message; there were zero unexpected outcomes. Two additional final full builds passed. Exact hashes and source snapshots are recorded alongside this report. Coverage includes missing, changed and extra files/directories; malformed authenticated metadata; symlinks and hardlinks; FIFOs; symlinked tool or root paths; unsafe/aliased/existing/inside-root outputs; missing isolation flags; optimized Python; incomplete or malformed manuscript inputs; standalone-source disagreement; lock-file changes; invalid render DPI; manifest digest/schema errors; deterministic archives; exact extracted inventories and byte-identical re-archiving.

Clean and deliberately hostile environments are compared using fresh builds. Hostile settings provide fake binaries, a poisoned Python sitecustomize, a poisoned TeX class and format, and altered PATH, PYTHONHOME/PYTHONPATH, TeX roots, HOME, timezone, shell/file-access settings, and source date. Both builds reproduced the expected packaged PDF exactly. Every PNG page, text output, dependency JSON and build receipt matched byte for byte; poison markers remained absent. All 28 PNGs decoded successfully, and two complete contact sheets were visually inspected without gross clipping or render failure. The final compiler log has no overfull boxes, unresolved references or rerun warning; its shell-escape-disabled notice and four underfull paragraph notices are not presented as zero-warning output.

The deterministic archive tests produced two identical 1,079,805-byte ZIPs over the 231-entry pre-assembly copied checkpoint, verified every entry's bytes and canonical metadata, extracted the archive, successfully verified its independently pinned manifest, and produced an identical ZIP from the extraction. Those checkpoint archive hashes are test evidence, not the final delivered archive digest. The final release seal is necessarily generated after this review payload is included and should be verified separately.

All 137 original frozen scientific/audit/dependency files match the pre-review snapshot in bytes, file modes and nanosecond mtimes. All copied fixture source files were preserved by the tool invocations. The separate portable replay review binds replay.py SHA-256 `7a537eeaf0e26d3c720527343f2a0cd1321d3d3486046ee947ef3b5d76b9b71e`; this review checked that the packaged copy has those exact bytes but did not rerun its independent checkers.

## Precise boundaries

- Authenticity requires a separately trusted final manifest digest and reviewed tool hashes. Hashes published only inside the same untrusted archive are not an external trust anchor.
- The dependency lock covers six executable names and 269 resolved recorded TeX/font-map input files. It does not lock dynamic libraries, Python itself, kernel/hardware, or the loader environment before the interpreter starts. It is not a fully hermetic container image.
- Canonical paths, no-follow file reads, single-link restrictions and pre/post checks defend the tested static aliases and ordinary changes. The tools do not claim an OS security sandbox or protection from a hostile same-privilege process swapping ancestors, mounts, or installed toolchain files concurrently.
- Source preservation covers bytes, file modes and nanosecond mtimes. Reads can alter atimes. ZIP entries intentionally use fixed timestamps and regular-file mode 0644; extraction does not promise to reproduce original source mtimes/modes.
- Build log bytes can contain fresh temporary paths. Reproducibility claims apply to the explicitly compared PDF/text/dependency/receipt/page outputs and normalized ZIP, not every incidental log byte.
- The extraction test validates the exact archive produced by the reviewed packager. It is not a generic safe-extraction service for arbitrary third-party ZIPs.
- This review establishes release/build behavior and evidence-byte consistency, not physical execution, a formal Lean certificate, mathematical completeness, or behavior on an untested platform/toolchain.
