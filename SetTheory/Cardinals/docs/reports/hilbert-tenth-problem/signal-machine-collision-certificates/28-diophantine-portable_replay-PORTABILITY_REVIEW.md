# Report58 portable replay review

## Verdict and scope

The reviewed adapter passes the focused portability review for a trusted local POSIX execution environment, with immutable/quiet inputs during the run and a trusted Python interpreter and standard library. The baseline replay reproduced all four frozen scientific receipt files and the arithmetic stdout exactly, while preserving the copied input bytes and recorded metadata. No author program, saved upstream program, or Lean code was executed in this review.

Reviewed adapter: `replay_report58.py`

SHA-256: `a5327ea281be120f99a1b31cb27a568f07a4dc498b96b701177f2ecee7786911`

This review is tied to those adapter bytes. It reviews the wrapper's faithful execution, authentication and portability behavior; it does not independently prove the mathematical statements in the frozen checkers or any external theorem dependency.

## Evidence

`PORTABILITY_REVIEW_EVIDENCE.json` records this review's actual baseline execution, independent source-preservation comparison, exact-byte comparisons, path-facade checks, and double-leading-slash regression result. All executable tests used fresh copies under `/tmp`; the two frozen source trees were only read.

Baseline command used isolated Python with `-I -S -B`, explicit relocated packet/audit paths, and a nonexistent external output directory. Results:

- Exit code 0, a PASS receipt, and empty stderr
- Byte-identical `exact-source-receipt.json`, `POWER_DAG_RECEIPT.json`, `arithmetic-receipt.json`, and `full-positive-witnesses.json`
- Arithmetic stdout byte-identical to frozen `arithmetic-run.stdout.json`
- Independent before/after equality for file/directory types, modes, sizes, mtime, ctime, device, inode, link count, owner/group, and every file's SHA-256
- No `__pycache__` directory created anywhere in the copied input/output test tree
- The adapter itself remained byte-identical during execution
- Sixteen direct path-facade mapping/guard checks passed

The parent task owns the broader adversarial rejection suite. This review does not substitute its focused checks for that suite.

## Faithful execution and exact outputs

The adapter authenticates the entire 33-file packet and 11-file independent audit against embedded SHA-256 inventories, including the independent checker files and expected receipts. It also checks the exact directory inventory. The staged copies are reauthenticated before execution, and both originals and staged copies are authenticated and metadata-compared after execution.

The three pinned checker files were inspected. Their top-level execution consists of standard-library imports, path constants and function/class definitions; their actual scientific work and I/O are behind callable functions or the main guard. Executing those definitions with a non-main module name therefore does not perform an unnoticed initial read or write through the frozen physical paths.

Each checker is compiled from its exact authenticated source bytes with `dont_inherit=True, optimize=0`. No textual or AST rewriting occurs. The wrapper then replaces `ROOT`, `OUT`, and `Path` in the checker's global namespace. These cover the actual path operations in these exact frozen files. The special POWER dispatch reproduces its original main guard: call `audit`, serialize with `json.dumps(..., indent=2) + '\n'`, write its receipt, and `print(text)`.

The worker requires unoptimized isolated Python, no site initialization, and bytecode writes disabled. The parent also refuses invocations without these flags. Pin checks and wrapper authorization checks use explicit exceptions rather than assertions, while the scientific assertions remain enabled in the explicitly unoptimized compilation. The child receives a fresh environment and has no packet/audit directory added to its import path.

The worker checks the exact four-file output inventory, compares each regenerated receipt directly with its authenticated expected bytes, and checks the arithmetic stdout. The parent independently rechecks the four receipts before writing PASS. Exact-source and POWER stdout are captured for inspection; unlike arithmetic stdout, no separate frozen stdout artifact exists for them in the supplied audit inventory.

## Logical-path facade

The original frozen absolute names remain in generated scientific receipts. The actual reads use authenticated relocated staging files, and writes use the fresh results directory. This preserves exact receipt text while allowing the input trees to be relocated.

The facade does not offer arbitrary filesystem operations. Packet/audit reads are restricted to authenticated inventory entries; writes are restricted to the four named audit results; the only permitted glob is the frozen packet evidence DAG glob. Unknown roots, sibling prefix tricks, unknown packet files, writes to packet or checker files, writes to the inherited physical source, dot-dot paths/children, absolute children, and other glob operations were directly tested and rejected.

The old physical-source path maps to the pinned `sources/INDEPENDENT_AUDIT.md` copy in the packet. Consequently, the frozen checker's inherited-copy equality test becomes equality against that authenticated copy. It does **not** independently reopen or revalidate the historical external physical-source tree. The packet SHA-256 authentication supplies identity of the frozen copy; portability documentation must retain this qualification.

## Corrected path defect

The first inspected draft accepted POSIX paths with exactly two leading slashes. `pathlib` preserves that spelling, although Linux normally resolves it like a single leading slash. Because input/output disjointness was lexical, this could bypass containment rejection and cause output creation inside an input tree before the later preservation checks refused the replay.

The current reviewed version explicitly rejects paths starting with `//`. A regression invocation using a double-slash output path inside a fresh packet copy returned exit code 2 with `paths must be explicit canonical absolute paths`; no nested output directory was created. The initial defect was reported from static review and was already corrected before the attempted dynamic reproduction.

The current exact-directory-inventory check also prevents an otherwise byte-correct source tree with an additional empty directory from authenticating.

## Security boundaries and residual limitations

1. This is an authenticated deterministic replay wrapper, not an OS sandbox. Python `-I -S -B` provides import/startup/bytecode isolation; it does not deny arbitrary filesystem access, networking, processes, or syscalls. The facade is safe here because the exact trusted checker sources were reviewed and hash-pinned. Read-only staged modes are not a security boundary against code with the same owner privileges, which could chmod them.
2. Path validation and later filesystem operations are not one atomic operation. Initial symlinks and ordinary malformed/overlapping paths are rejected, and before/after snapshots detect changes that persist, but no guarantee is established against a hostile same-UID process racing path substitutions. A privileged bind mount can alias directories despite lexical disjointness. Such concurrent/privileged adversaries are outside the reviewed operating assumptions.
3. Interpreter, standard-library, kernel and filesystem behavior are trusted. The recorded adapter hash identifies the version used; it is not an external signature or independent trust anchor for an untrusted replacement adapter.
4. Preservation excludes access time, which may change when input files are read. It also does not claim to cover ACLs, extended attributes, creation time, open handles, or all kernel/filesystem metadata. The receipt accurately enumerates the metadata it does cover.
5. A positive run establishes byte equality and checked metadata at the recorded before/after checkpoints. It is not proof that no unobserved transient access or hostile mutation ever occurred. For the reviewed pinned code there is no code path intentionally writing the original sources.
6. A successful replay must be judged by successful process termination and the completed PASS receipt, not merely the existence of an output directory or a receipt-looking filename. Failed output directories are deliberately retained and cannot be reused.
7. The wrapper intentionally supports POSIX absolute paths and assumes an interpreter capable of running the frozen checker syntax/library features. Cross-platform or cross-version runs must pass the same exact-receipt checks; this review's actual test used the available local interpreter only.

Subject to these explicitly bounded claims, no remaining deterministic path-facade, assertion-disablement, scientific-byte transformation, receipt-equality, or source-preservation defect was found in the reviewed version.
