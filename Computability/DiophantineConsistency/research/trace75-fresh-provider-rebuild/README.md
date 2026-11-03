# Held trace75 fresh-provider replay

`run.py` is a proposed guarded 14-stage replay from the independently
reviewed fresh-provider plan. **Do not launch an attempt until independent
static review and coordinated release.** It is designed to create a fresh
non-clobbering union from the 1,931-object coherent BFS baseline, select
the fresh `ModelRatioBounds` and `ArithmeticNegativeNorms`, add 40
trace-specific unchanged or generic-helper objects, and rebuild the 14
affected trace75 clients in captured dependency order. It intends to
recheck source, provider and companion hashes around each stage and capture
the actual selected serialized closure of the rebuilt trace75 endpoint and
`DirectBFSBandCarry`. It does not build a trace75/BFS carry join or an iPRA
endpoint.

The read-only `--preflight-only` run at `observations/preflight-attempt01/`
returned 0 and recorded 1,931 base objects, 80 outside objects, 40 trace
supplements, and 14 stages. It used runner SHA-256
`c04420db28f8dd6a2b3675725c089fe4be0b74579d60c8ce932230a1493c03c1`.
An earlier uncaptured preflight stopped before any union or Lean execution
because the outside-baseline hash literal was mistyped; it was corrected
before this captured preflight. The current code is a proposal: the
preflight does not establish that a 14-stage replay or its final closure
will pass. The historical source/object and outside/package/dynamic
provenance limitations must remain explicit even if such a replay passes.
