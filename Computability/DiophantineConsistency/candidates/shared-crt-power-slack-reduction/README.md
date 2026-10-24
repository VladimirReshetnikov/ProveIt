# Both redundant lower-bound slacks removed

The final literal direct quartics combine fixed `W=n+k`, deletion of
the now-derived `A>=2` and `B>=2` slacks/rows, and the literal beta bound
`H=E+F`. [PROOF.md](PROOF.md) proves both directions and all early
positivity hypotheses. Frozen earlier candidates remain unchanged.

| Variant | Natural variables | Degree | Terms | Height |
|---|---:|---:|---:|---:|
| `affine/` | **3,328** | **4** | **15,289** | 127,299,660 |
| `retained/` | **5,739** | **4** | **16,230** | **1,552** |

Reproduce from the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_shared_crt_power_slack_reduction.py --check
python3 -B Computability/DiophantineConsistency/candidates/shared-crt-power-slack-reduction/check.py
python3 -O -B Computability/DiophantineConsistency/tools/build_shared_crt_power_slack_reduction.py --check
python3 -O -B Computability/DiophantineConsistency/candidates/shared-crt-power-slack-reduction/check.py
```

`SOURCE_PINS.json` lists exact complete source edits. The inherited
numerical C222/refutation meaning is the parent's named ordinary
argument. No native tuple, new Lean theorem or internal object-ZFC
derivation is asserted. Lean formalization remains paused.
