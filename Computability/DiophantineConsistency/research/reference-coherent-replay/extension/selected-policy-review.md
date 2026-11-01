# Source review of the selected-consistency policy

An independent reviewer inspected the proposed wrapper, task policy, freezer
constant, toy report declarations and `test_policy.py`. The reviewer found no
binding mismatch in their six ordered report names or the two newly included
draft import edges. This was source review only: no Lean build, real-parent
source audit or end-to-end toy execution was performed.

The following source hashes were observed after that review:

| File | SHA-256 |
| --- | --- |
| `plan.py` | `007828b8f92298dd8b47413d54d0298198f40d4396417631251f97d06cb7c996` |
| `extension/freeze.py` | `49ecd7b286a6fd3351ab215c60093205765e4506d96f84cdbeec0dd12c3e09e9` |
| `extension/task-policy.json` | `87a32e728b6d19a5c764f83c3be5003a8f9a1bc57515abd08644b5d83bf1fb42` |
| `extension/test_policy.py` | `9ef30c9bdf42146429595ccd22b793670b9a684fc373b872ea2ed4e5e640e60a` |
| `extension/test_full_chain.py` | `bb95a7795c20ff633bd9261dbea178188fb66706d82c4925254dc0dded18ecf1` |
| draft `IPRAReferenceReplayChecks.lean` | `da5e8c40c9e89cec3264affd62e73082d3d960fba22eed756bf8f2a90b05851a` |

The planner's seven controls, the extension's nine selection/observation
controls, the Git-backed freezer control and two policy consistency tests
exited successfully. The earlier replay plans and static audit remain
historical observations of different source hashes; none authenticates this
revision or proves the endpoint.
