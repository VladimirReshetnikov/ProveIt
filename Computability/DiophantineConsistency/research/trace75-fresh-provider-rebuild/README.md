# Held trace75 fresh-provider replay

`run.py` is the historical first proposal for a guarded 14-stage replay
from the independently reviewed fresh-provider plan. It was designed to create a fresh
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
preflight alone did not establish that a 14-stage replay or its final closure
would pass. The historical source/object and outside/package/dynamic
provenance limitations must remain explicit even if such a replay passes.

## Reviewed replay

`run-v2.py` (SHA-256
`9aaffde57346464f11a963ff4960592c871cd88c3eef8badd5652f6515fca67b`)
adds copied-source and producer-snapshot/log rechecks, re-resolves all 80
outside names under the actual union/package/core path at every stage, rejects
dangling shadows, and requires each stage's complete output to match its
pinned successful historical log exactly. Thus missing, duplicate, new or
changed axiom reports are rejected along with warnings and errors. The
captured read-only `observations/preflight-attempt02/` passes without creating
a union or launching Lean. `test-policy.py` exercises 14 positive/negative
controls on actual runner functions; `observations/policy-attempt01/`
records PASS. These controls do not replace review or a replay.

The separately pinned `run-outer.py` (SHA-256
`0ed48c144b4cccc026bd4967d1e410889f8379a522999f66bcf21279aff06d1d`)
captured the runner's actual exit, before/after inputs and its own hash
without overwriting an existing attempt. After independent prelaunch review,
the single `observations/attempt01/` run passed all 14 stages and its
selected serialized closure. The fresh union is
`/tmp/trace75-fresh-rebuild-yn60cw_0/lib`; result SHA-256
`b74858343a05be6710e0666abb86189aea375ebd4d494411fee00d31e9f31e1a`.
The outer `observations/outer-attempt01/terminal.json` records actual exit 0,
stable inputs and wrapper, and has SHA-256
`4c310be9b2ee9aa32378f27869c87e7bbbd8af2512f3b6391d02518e3dcbc7af`.
The supervising tool session itself also returned exit 0.

The selected project closure has 248 objects and 28 outside objects;
`Trace75FixedCongruence` has 208 project ancestors and `DirectBFSBandCarry`
has 46. The selected fresh `ModelRatioBounds` and
`ArithmeticNegativeNorms` hashes are `8ba17e0b…` and `33cf4704…`,
respectively. The replay also checks the BandCarry subtree's selected
object and companion hashes against its BFS producer capture. This removes
the prior two old-object selections from this rebuilt selected closure; it
does not by itself establish full historical source/object provenance for
unrebuilt dependencies or outside/package/dynamic ancestry, nor does it
prove a trace75/BFS carry join or iPRA equivalence. Independent post-run
review passed in
`reviews/trace75-fresh-provider-replay-independent/README.md` (SHA-256
`b346fc8c90a68f9c1a05c2b0e4a1fc446dd28e05dc900775d8e7f39597bcf391`).
All 14 newly built objects are byte-identical to their earlier versions;
the replay records this execution and does not establish unique provenance
for those bytes.
