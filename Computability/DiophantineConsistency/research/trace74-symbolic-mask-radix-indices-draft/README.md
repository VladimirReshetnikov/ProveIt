# Combined radix/index isolation draft

This uncompiled source applies the checked fixed-indices theorem at base `2^67` while keeping support `S` symbolic and retaining its bound. It tests whether fixing the radix and indices together triggers the previously observed resource cost before concrete support or `lowNat` is introduced. The earlier timeouts had empty logs, so no cause is inferred.

The [independent source review](../../reviews/trace74-radix-indices-draft-independent/README.md) found no mathematical blocker and did not run Lean. A pinned provider-compatible runner and a separate guarded Lean check are required. Even acceptance would not establish the concrete support specialization, high bound, full symbolic mask cover, model cast, graph guard or an iPRA endpoint.
