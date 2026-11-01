# Author-produced 73-module fixed-snapshot repair plan

`manifest.json` was produced by the captured `prepare.py` after both fixed endpoint peers passed; `replay.py` is the captured repair driver. It is a project-origin plan, not a Lean proof. Both historical shared-source providers are authenticated against their copied driver/state and the matching frozen packet manifest and `sources/` contents; no live workspace source is used as proof input. The exact physical project-origin graph and source fixed point were independently compared with the output-only-path variant in `../ipra-frozen-repair-plan-v2-verification/`.

A separate author/independent Lean replay must rebuild the 73 dirty modules, match outputs/logs/direct inputs and inspect the endpoint axiom reports. The 848 ancestor is author-only and package-transitive/dynamic ancestry remains inherited. Later workspace source changes require a separate current-source rebase.
