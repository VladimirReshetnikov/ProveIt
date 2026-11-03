# Held trace75 direct-BFS carry client

`Trace75BFSCarry.lean` proposes a model theorem from a positive trace75
zero with exact natural ports `p0=betaNat`,
`p1=DirectBFSSymbolicKernel.paramKernel rho`, `p2=lowNat`, and
`p3=betaNat+highNat`. It adapts the existing direct-BFS carry proof to the
freshly replayed `Trace75FixedCongruence`; no proof is claimed until its
separate Lean check passes. The intended result is the same-N indexed carry
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
No candidate Lean proof has been run.

**The runner and outer wrapper remain held pending independent prelaunch
review and coordinated release.** Historical unrebuilt-source provenance,
full package/dynamic ancestry and external file binding are not established
by the fresh replay or this preflight.
