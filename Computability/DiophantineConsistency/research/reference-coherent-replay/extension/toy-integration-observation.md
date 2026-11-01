# Observed paired-extension toy controls

The final-source end-to-end toy was run at `nice -n 19`, idle I/O priority,
with a 240-second limit. Actual terminal session **64510 exited 0** and
printed:

```text
PASS: actual observed toy parent, freezer, preparation and paired extension; no AQ29 proof
```

The same source was independently inspected and rerun at low priority. The
reviewer's actual session **20107 exited 0** with the same output. The review
confirmed that the test constructs an isolated temporary Git workspace,
runs a paired toy parent and the actual copied planner, freezer, preparer and
both extension builders, records the actual parent and freezer exits, and
checks the six exact report names. The reviewer observed all eleven tool and
source identities below unchanged before and after that run. The primary
observation also checked the first eight identities before and after.

| Source | SHA-256 |
| --- | --- |
| `plan.py` | `007828b8f92298dd8b47413d54d0298198f40d4396417631251f97d06cb7c996` |
| `extension/freeze.py` | `49ecd7b286a6fd3351ab215c60093205765e4506d96f84cdbeec0dd12c3e09e9` |
| `extension/prepare.py` | `4720f7a2989e4fcf883dd50fd81711a82c5dacfbf526665763cd7c06e7892964` |
| `extension/rebuild.py` | `069aa3f87638e5ea571e30ab8ae12af0ab9d23d38e00b0c6c3935a9228bdf35f` |
| `extension/compare.py` | `7e355f2ecfe464b6828aab85ea324cea519bc0e989f3b6dba81bd50c4abe7a34` |
| `extension/run_pair.py` | `ab51a8b295adc0419610671e5e39775a538d45858151bf8b575bdfa6dfc6a8f7` |
| `extension/task-policy.json` | `87a32e728b6d19a5c764f83c3be5003a8f9a1bc57515abd08644b5d83bf1fb42` |
| `extension/test_full_chain.py` | `bb95a7795c20ff633bd9261dbea178188fb66706d82c4925254dc0dded18ecf1` |
| parent `fresh-project-closure/rebuild.py` | `8170bd401b1821666fffc2a55f8dd908e473d32c71797661a5acd85a32d0dc56` |
| parent `fresh-project-closure/compare.py` | `530def48c58dc38ce8a293a5c9912762b2ad101e63faf7cb0763f71a7ac9a3a5` |
| parent `fresh-project-closure/run_pair.py` | `518e6131c17e3567e723fc1a12cf22a7349334d2b6dd544d0b9c2a0a0e8e1fa6` |

The separate [adversarial toy observation](toy-adversarial-observation.md)
records its own mutation controls. Both tests delete their temporary
workspaces on completion, so their internal logs are not retained.

The tests use tiny toy theorems and a synthetic empty Foundation provider.
They do not authenticate the real parent, prove Foundation/package provenance,
or elaborate or verify the AQ29 endpoint. Dynamic-load and transient-mutation
limits remain those of the underlying guarded workflow.
