# Independent portable replay review plan

This review concerns release transport and exact reproduction, not a new scientific proof. Original scientific and audit files are treated as immutable, inert inputs except for the explicitly authorized byte-identical independent checker. No author checker, simulator, constructor or saved schedule may execute.

## Acceptance requirements

1. Explicit complete inventories authenticate all science and independent-audit file bytes, including each package's manifest/checksum files and both dependency proofs. Reject omitted, extra and nonregular objects rather than relying only on self-excluding embedded manifests.
2. Only the exact independent checker `a945491e115e5f96dfc11e3d6e714ef367ecc0daddfce425d8310cb5949f4fec` may be compiled as packet code. Use `optimize=0` even under optimized outer Python. No transform of its bytes or source statements.
3. A narrowly scoped pathlib-import facade redirects its original absolute science root, checker self-read, current snapshot read and permitted evidence writes. Unmapped paths/operations should fail closed. The facade must not globally modify pathlib or installed dependencies.
4. Original frozen-before/frozen-after records remain authenticated inert historical evidence; they must not be overwritten, used to rewrite transported metadata, or misrepresented as actual relocated state. The checker may compare a fresh, explicitly identified transport snapshot instead.
5. Reproduced mathematical evidence, complete 44-rule evidence and stdout compare byte-for-byte with authenticated originals. The actual relocated science/audit metadata and contents compare before/after, including modes and nanosecond mtimes; content and object inventories remain exact.
6. Output is fresh, separate and cannot overlap or alias protected inputs. Symlink components, unexpected special files, and path escape routes receive explicit handling. Failed authentication must precede checker execution.
7. Evidence includes fresh relocated success, negative tamper cases, optimized-Python behavior and original-input preservation. Tests execute only inspected fresh adapter/tests and the authorized checker.
8. Document trusted Python/SymPy/runtime and quiescent-filesystem assumptions. This is not an OS or network sandbox, an adversarial/concurrent-filesystem defense, or proof of physical evolution.

## Current inspected input facts

- Science inventory: 14 regular files, 2 internal directories, root (17 objects total)
- Independent audit inventory: 9 regular files, 1 internal directory, root (11 objects total)
- Independent checker: 10,752 bytes, 157 named checks, SymPy 1.14.0 in authenticated output
- Expected science proof hash: `502e90e091eabc0a6c8eb6092e73f4407ae84f143d337be8a4a633a3f85a7c47`
- Original evidence snapshot pair is byte-identical, 3,517 bytes each
- Original snapshots describe original filesystem metadata and must not silently become the relocated-input snapshot
