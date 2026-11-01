# Bounded streaming compiled-header inventory

`inventory.py` follows imports in compiled Lean object headers using one
persistent Lean reader. It resolves each module by the first root containing
its top-level namespace, records object and companion identities, and checks
the observations again after traversal. Missing search roots are recorded and
must remain absent. A configurable module cap produces an explicit partial
result and remaining frontier; the current implementation does not resume a
partial traversal.

For module-system objects, `stream_imports.lean` reads main, server and private
parts **together in that order** with `Lean.readModuleDataParts`, so references
into earlier compacted regions remain valid. It reads IR separately. Non-module
objects with unexpected server/private parts are rejected. The control fixture
`make_shared_fixture.lean` saves the same data across three compacted regions
and verifies shared pointer identity after ordered loading.

Each selected artifact is SHA-256 hashed at baseline and at final checking;
its path and file metadata are also checked around header reads. The hash-read
rate limiter bounds explicit hashing reads and does not itself bound I/O from
Lean's memory maps. Run surveys at idle I/O priority when another proof build
is active. The checks cannot rule out a transient mutation that is restored
between observations.

This inventory concerns **compiled-header reachability and observed object
identities**. It does not prove that objects were built from particular source,
trace actual runtime or dynamic-library loads, authenticate package-transitive
source, or establish Lean/toolchain correctness. A capped survey is not a
complete closure. The [eight-module measurement](../../reviews/compiled-header-inventory-benchmark/README.md)
is explicitly partial; no broader traversal was started while the project
rebuild was running.

Run the real-Lean controls with `PYTHONDONTWRITEBYTECODE=1 python3 test_inventory.py`.
