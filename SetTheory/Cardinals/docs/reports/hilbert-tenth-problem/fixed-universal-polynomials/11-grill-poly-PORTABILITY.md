# Portability transformations and scope

No pre-existing source directory was modified. `PROVENANCE.json` separately records every retained original file's byte size, SHA-256, and Git-blob SHA-1 before packaging, together with its delivered path, byte size, SHA-256, and transformation list. Source identities use logical labels `arithmetic/`, `input-research/`, `input-audit/`, and `circuit-audit/` rather than private authoring paths.

## Frozen evidence transformations

T1 replaces private absolute authoring-directory prefixes with `source://<logical-label>` references. A historical private virtual-environment interpreter path becomes `python3`. This is a presentation/route change; equations, numeric receipts, and scientific data remain untouched. Such a source is expressly **not byte-identical** to its original. Its original hash is retained, and its delivered hash is separately verifiable.

T2 appends `.txt` to every retained original `.py` filename. Upstream Python and the original local code remain inert source evidence. Byte-identical means identical content, independently of the inert-extension rename. Historical manifests and hyperlinks may still name original `.py` files; their inert delivered mapping is in the provenance table.

Unmodified original bytes include the full DAG, literal table, little-endian program array, recoder receipt, native kernel, primary PDFs, and most frozen theorem sources. Exact original-byte identity is individually recorded; it is never inferred merely from a familiar filename.

Resource-only truncated prototype DAGs/receipts, obsolete input probe outputs, interpreter caches and temporary build products are omitted. Named native small-case fixtures are retained because component checks use them.

## Executable local-code transformations

Only the explicitly local generators and independent checkers are executable under `replay_code/`. No upstream module is imported, executed, evaluated as code, or granted an executable `.py` name. The literal-table reviewer uses `ast.parse` and `ast.literal_eval` only to inspect a static literal from inert upstream text.

T3 changes local filesystem lookup routes to module-relative sibling paths. The runner stages a self-contained copy outside the package, so regenerated outputs never overwrite delivered evidence.

T4 normalizes Python source with the standard-library AST printer and replaces every `assert condition[, message]` by an explicit `if not condition: raise RuntimeError(message)` statement. The supplied message is preserved; statements without a message identify the original line. These checks run under normal and optimized Python alike. This transformation changes code bytes, not accepted invariants or arithmetic schedules. The executable inventory is scanned to reject remaining Assert nodes.

T5 adapts the independent exact-source checker's original absolute dependency-pin loop. Original file hashes and Git-blob hashes are checked against the frozen provenance mapping; corresponding delivered bytes are independently hashed against their delivered commitments. This avoids pretending that sanitation preserved an original file hash. The mathematical exact-row/coefficient audit is unchanged. The inventory/provenance chain is checked before any scientific code runs.

The literal generator is run before the independent literal reviewer. It must reproduce the exact original literal-table hash. Its temporary source manifest then correctly identifies the portable local builder and delivered source bytes. After full DAG re-emission, the regenerated manifest is compared to the frozen scientific manifest after removing only `resources`, `snapshots`, and `extra.source_modules`. The latter records the actual adapted local generator hashes, which the whole-DAG checker verifies. All gate rows, constant recipes, coordinate roles, residual operands, finalizer, ledger, dimensions, and substantive metadata must match exactly.

All original code, original-byte provenance, local adaptations, and invariant tests are visible for review. Resource ceilings and timings are operational checks rather than claims about mathematical completeness or optimality. SHA-256 integrity and finite numerical tests do not replace the source-parametric mathematical proof or its named premises.

The staged copy of the independent outer-interface receipt replaces only its `source_sha256` field with the adapted checker hash before replay. The checker still requires exact equality of every scientific receipt field. This staging-only change is not made to frozen evidence.
