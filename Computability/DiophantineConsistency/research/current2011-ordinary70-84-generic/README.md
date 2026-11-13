# Generic 70/84 versus 67/94 ring zero equivalence

`OrdinarySphere7084Generic.zero_iff94` proves that the 70/84 value is zero exactly when `Carrier94Value.value94` is zero at the same positive coordinates and positive beta, over any commutative strictly ordered ring satisfying the explicit `FreshCarrierSpheres.Facts` (discreteness, a mod-four homomorphism and the two named norm exclusions). This is a generic ring theorem; it does not by itself identify the JSON graph, prove an IΣ₁-model bridge or produce an iPRA endpoint.

The nonzero auxiliary norm makes `U²≥1`; a sphere zero forces `U²=1`, `H=0` and `P*Q*W=1`. Because `H=0` makes the auxiliary coefficient a square, the checked mod-four norm exclusion gives `U≠−1`; the known `P,Q≠−1` facts then force all four factors to `+1`. The reverse direction extracts the ordinary strong factor `+1` using the separately checked 71/60 mod-four exclusion and then all remaining unit factors.

Attempt01 passed: actual outer session 75341 and Lean both exited 0, with no warnings or `sorryAx`, the expected `[propext, Classical.choice, Quot.sound]` report, 340 stable guard slots and no stop. The object `/tmp/current2011-ordinary70-84-generic-check01/OrdinarySphere7084Generic.olean` has SHA-256 `2e7f9a5e8041cee171653527db578adf1fcb426a3890b0415d13439f3436a0cd`. Child receipt and actual outer observation are retained separately. The guard uses Lean `-M2800`, one worker, nice 19, idle I/O, a 120-second bound, sampled 3.5-GiB process-group RSS stop and 10-GiB available-host-memory stop. Its direct-provider pins inherit the transitive base and do not constitute a full dynamic load trace.

| Artifact | SHA-256 |
| --- | --- |
| `OrdinarySphere7084Generic.lean` | `9ad402c654e1d5589d36bf1f6fd23142d20d8a14d8f4d3b553ec9607e4eb3e68` |
| `check01.py` | `e673c13234095dd1033b0ce9d2c24a1cc2b9886b8b0e501b8e3ce1512570dbea` |
| `attempt01/result.json` | `fcbb8f05f31075b399b090d133e44813786d87e3c461bc31e139a3caacc2c0e3` |
| `attempt01/compile.log` | `ac9701dd7c90cc2d9f5006066928a13eabb9f222220131922dacbc0c3c7c2a93` |
| `attempt01/outer-observation.json` | `d6d8a347cf5217ec8d3201db33c0376eff71165b4585599afdb3ead5a5921b87` |
