# Held trace75 direct-BFS carry client

`Trace75BFSCarry.lean` proves a model theorem from a positive trace75
zero with exact natural ports `p0=betaNat`,
`p1=DirectBFSSymbolicKernel.paramKernel rho`, `p2=lowNat`, and
`p3=betaNat+highNat`. It adapts the existing direct-BFS carry proof to the
freshly replayed `Trace75FixedCongruence`. The result is the same-N indexed carry
input, not yet a machine-halt, iPRA, or literal PDF/file equivalence. The
symbolic BFS kernel still needs a formal binding to the retained external
coefficient payload.

The held `run.py` selects only the fresh 1,977-object replay union followed
by the captured package root, pins that replay and actual outer receipt,
and checks the entire union and 80 captured outside objects before and after
the candidate proof and header read. It checks BFS-captured object and
companion hashes for both extra direct-provider subtrees:
`DirectBFSBandCarry` (46 project objects) and `ActualTemporalBand` (9).
It also pins the source and exact expected single axiom report, guards the
temporary output root against shadowing, and records the compiled object's
serialized direct imports. The captured read-only preflight at
`observations/preflight-attempt01/` passes, and 13 actual-function negative
and positive controls are recorded in `observations/policy-attempt01/`.

After independent prelaunch review, one run passed at
`observations/attempt01/result.json` (SHA-256
`7704d80833c17b04cf345e269213121f4bbf41537b62262921f7177f21dd4bc7`),
producing `/tmp/trace75-bfs-carry-fcp4lu0b/Trace75BFSCarry.olean` SHA-256
`d4dc1034131198fd5965e9a23585f81c1182c39ba8b217fb550036acb7b9545e`.
The `observations/outer-attempt01/terminal.json` receipt (SHA-256
`c12da16e2196705490b6b5c54bf1c626eb8bda5446772018974d2e88a7c84631`)
records actual child exit 0 and stable inputs/wrapper; the supervising tool
session also exited 0. Independent post-run review passed in
`reviews/trace75-bfs-carry-result-independent/README.md` (SHA-256
`2f4047e8bef0827fb50fa1c734fbf28b45b3e3543c5cdb9090dba762b5a17d68`).

Historical unrebuilt-source provenance,
full package/dynamic ancestry and external file binding are not established
by the fresh replay or this preflight.
