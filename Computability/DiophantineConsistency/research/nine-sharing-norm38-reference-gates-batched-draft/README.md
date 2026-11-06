# Source-only plan for 60 reference gate equations

This packet records the original source-only plan. The subsequent [guarded
build](../nine-sharing-norm38-reference-gates-batched-check/README.md) compiled
all 60 equations and their universal assembly; its independently audited
terminal evidence and limitations are documented there.

`generate.py` reads the pinned successfully built `NormAssignment38.gates` and concrete reference source. It checks that targets are exactly 21–80 and that each reference `let` uses exactly the same two predecessor indices and arithmetic operation as the corresponding gate. It emits twelve source-only modules, each with five proposed `rfl` reference-gate equalities, and a thirteenth proposed conjunction assembly for the universal 60-gate reference-equation theorem. Each group imports only the checked concrete reference-base module. The 4,096 recursion bound reflects the earlier checked U-edge experience; 4,000,000 heartbeats remain unchanged.

This is a planned factoring, not a Lean proof. Definitional equality at every node, group resource use, concrete forall/conjunction elaboration and assembly imports remain unchecked. The theorem would supply the gate-reference premise for the checked generic topological induction; it would not on its own prove initial static/reference agreement, source/seed equivalence, fixed-port casts or an iPRA endpoint. No Lean runner or object is included. The generator has not been independently reviewed.

Generate using `python3 -I -S -B generate.py` only in an isolated copy if preserving these frozen outputs; the script writes its generated files. Generator SHA-256 `a38102ed3a86932ca3e37084d1ab3044d73206608492af82026860f7b705a7b3`, manifest `e51de4382ec1c4b247dc15b408924e60b8923e8e36f36d01b2a9d370c27e94c8`, result `44f38afaf7c1d2968118529813ae3fa7d2232e922721eef7ca18f8affd471266`.
