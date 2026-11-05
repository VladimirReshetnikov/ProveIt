# Literal 71/60 evaluator

`OrdinarySphere7160Literal.lean` defines all 71 rows as an integer-leaf arithmetic expression and proves `eval_expression` over every commutative ring. Its local auxiliary and value definitions have the same bodies as those in the separately checked generic ring proof. `audit_rows.py` compares the complete Lean row list, variable order and port aliases with the corrected candidate JSON; `row-audit.txt` records the successful external check. This external parser is not a Lean theorem about JSON file semantics.

Attempt04 passed: actual outer session 70915 exit 0, Lean exit 0, one `[propext]` axiom report, 251 stable guard slots and no stop. The object `/tmp/current2011-ordinary71-60-literal-check04/OrdinarySphere7160Literal.olean` has SHA-256 `b4386569a433cc7a0e2033368a9167081bb5e6e50ee8fd867df1938c01ed4e60`. Its child receipt and actual outer observation are retained separately. The bounded guard uses Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled group-RSS stop at 3.5 GiB and host-memory stop at 10 GiB.

Attempt01 loaded the generic and endpoint providers together and failed at the interpreter memory limit. Attempt02 used a lighter import but kept a global ring-normalization tactic and also hit that limit. Attempt03 replaced that tactic with local associative simplification; Lean reached the evaluator proof but rejected an unnecessary namespace open. Attempt04 removes that open. All failed sources, logs and outer observations are retained. The direct-provider guard and inherited base do not amount to an independent transitive rebuild or dynamic load trace. This packet alone is an evaluator theorem, not an iPRA endpoint or degree proof.

| Artifact | SHA-256 |
| --- | --- |
| `OrdinarySphere7160Literal.lean` | `554fa13261dcb4f9535764871b4833d0b6182fab9503bfa27b3bc5f88d64d84a` |
| `check04.py` | `cbe8017ae44b334407f2d5ca61c2c556a83fbc1a655b07343122d5dfaeefdd09` |
| `audit_rows.py` | `6925db7e1b835238e0cfc51406c7077870f49cc3ceae8f59a1eea15d1f2a808d` |
| `row-audit.txt` | `8820a305cd28c47d9fe1eeab2f953677493dda3eb5113261cad8b208f6a2c55c` |
| `attempt04/result.json` | `055028339fc050116ec50c065bc47a4d993fb69c0c591dec2527fa45464d4e68` |
| `attempt04/outer-observation.json` | `68b8843f7e21311cbcd136449fbc296b2922c42c110fffd9aa25df4a0a1ec92d` |
