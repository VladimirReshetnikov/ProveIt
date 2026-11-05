# Literal 70/84 evaluator

`OrdinarySphere7084Literal.lean` defines all 70 rows as an integer-leaf expression and proves `eval_expression` over every commutative ring. Its local auxiliary and value definitions have the same bodies as those in the separately checked generic ring proof. `audit_rows.py` compares the complete Lean row list, variable order and port aliases with the candidate JSON; `row-audit.txt` records the external check. This parser is not a Lean theorem about JSON file semantics.

Attempt01 passed: actual outer session 28929 exit 0, Lean exit 0, one `[propext]` axiom report, 251 stable guard slots and no stop. The object `/tmp/current2011-ordinary70-84-literal-check01/OrdinarySphere7084Literal.olean` has SHA-256 `69aea03a50aeb2f6d10a445c5664438771fe668174e45ac456ded02716b50720`. Its child receipt and actual outer observation are retained separately. The guard uses Lean `-M2800`, one worker, nice 19, idle I/O, 120 seconds, sampled process-group RSS stop at 3.5 GiB and available-host-memory stop at 10 GiB. Direct provider pins inherit the transitive base and are not a complete dynamic-load trace or independent rebuild. This is an evaluator theorem, not an iPRA endpoint or degree proof.

| Artifact | SHA-256 |
| --- | --- |
| `OrdinarySphere7084Literal.lean` | `e498fa16e97284c4d048460769d758d4f5b354e2cd9faa616c1857f84897e8ec` |
| `check01.py` | `48241135b66cb72422ad5a462efbe4cab6007ba57e8388848dacfc5115639a40` |
| `audit_rows.py` | `df1f45cf58fb15d5153dbcb7eaedfbda150c661dacc64ffd106306eddd37d152` |
| `row-audit.txt` | `d4fdd6676226fa931ebc4c00c0c0fdeb743e807e1b015d4da32ce5eebd6d637a` |
| `attempt01/result.json` | `ccbd3ba0713022aaf04e1cbb26b3329742d699faa9fa7e9b303cb01acf62b44d` |
| `attempt01/outer-observation.json` | `99425c1647dd635c26e3ffa5b77745af4247544f8b3feb94c51796562453a180` |
