# Portability and execution boundary

All default replay commands are standard-library Python programs. The outer verifier pins all payload files before invoking any command, sanitizes Python path/optimization variables, and runs inside a disposable copy. It intentionally uses `-B`, not `-I`, because the Rocq checker imports its sibling `validation_guard.py`.

| Owned replay | Local dependencies | Writes in temporary copy |
|---|---|---|
| Lean source audit | `lean/snapshot`, import patch, audit JSON | none |
| Lean four profiling/canonical scripts | `lean/latest/KSource215Data.lean`, sibling helpers | profiling JSON |
| Lean CFG minimization | previous CFG helper and source | minimization JSON |
| Rocq three checkers | sibling `prototype.py`, `compare_flat_cfg.py`, `validation_guard.py`; pinned Cert215Offsets/Prog215/DagPerm | CFG/certificate JSON and three generated `.v` drafts |
| Candidate interfaces | `candidates/INPUTS.json`, `candidates/inputs` | none by default |
| CM transport | two pinned TM tables and certificate | recomputed certificate/result JSON |
| Runtime profile | `runtime/inputs`, `runtime/latest`, input hashes | profile JSON |
| Window verification | four pinned native tables, census JSON and 40 `.bits` certificates | verification JSON |
| Enumeration | input pins, EnumPerm source and common-NIP proofs | none; stdout compared with archived JSON |
| GC-ZC intake | exact received ZIP | finite audit JSON; never executes received code |

Optional negative suites use `subprocess` to launch only their owned checkers in further isolated temporary copies. They mutate copied data, never the original inputs. Their recorded diagnostics include temporary paths and need not match byte-for-byte across machines. The outer verifier does not compare those path-dependent diagnostics.

Historical Python files under source snapshots and `new_intake/.../text/hybrid215/verify_composition.py` are **evidence-only** and are not in the execution allowlist. They may depend on historical checkout paths. Likewise `window_reduction/prepare.py` is a historical input-copy helper with workspace-relative provenance paths, not a portable replay step: use the already pinned bundled inputs. `reach.cpp` is the source of the old producer; no compiled executable is bundled or needed. Archives of historical build objects were omitted. The reports and metadata may retain original workspace paths for provenance; the replay does not rely on them.

No incoming ZIP module is imported, no archive executable is run, no shell command or package manager is invoked, and no network access is used by the outer replay. A generic external file integrity check cannot certify semantic correctness. The missing formal soundness and endpoint gates remain those stated in the report.

The final report QA receipt preserves hashes of all 11 reviewed page renders. The rendered PNGs and TeX auxiliary files are not bundled; the final PDF, TeX source, build helper, QA summary and receipt are included.
