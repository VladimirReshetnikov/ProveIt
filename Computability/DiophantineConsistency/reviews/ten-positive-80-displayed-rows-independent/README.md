# Independent review: explicit 80-row Lean binding

`TenPositive80DisplayedRows.output_eq` states, for **arbitrary integer ports** `p : Fin 4 → ℤ`, the exact Lean expression equality

```text
output_by_rows p = (TenPositive80Graph.graph p).output.
```

The left side is built as an `Expr (Fin 10)` from ten explicit variables `a`–`j` at slots 0–9, four explicit constants `p 0`–`p 3`, and precisely 80 sequential arithmetic-register definitions, returning r80. Its proof is `by rfl` and the accepted author report lists `[propext]`; the theorem itself is **unshifted** and does not mention any fixed coefficient tuple, external files, or iPRA derivability. The separately checked iPRA endpoint uses `positiveShift` on the graph output; equality under that construction or a combined endpoint would require the corresponding Lean composition.

`check.py` independently verifies the accepted `observations/attempt01` source/copy, runner, output and log hashes; source has no `sorry` or `admit`, the log has no diagnostics or `sorryAx`, and the expected axiom report is present. It independently resolves the first `Direct80Graph.olean` on the recorded `LEAN_PATH` and compares its hash to the explicitly selected/pinned direct object. That object is `/tmp/tenpositive-80graph-d2v79zbc/Direct80Graph.olean`, SHA `95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4`; the graph object selected in the fresh 127-stage union has the **same bytes**. `Direct80Graph` was not itself one of the 127 rebuilt modules, so this byte comparison does not supply its full historical source-object ancestry. The accepted displayed-rows object is SHA `aeafe96a70f42a594e30adaf5397289b5155c98c6d481fcdf4e8bffc30956eff`.

The checker separately parses all ten Lean variable declarations, four port declarations and 80 register operations, comparing them to the original-kernel candidate JSON in order, including every operand and the r80 output. It runs the previously independent decimal-display checker, which separately compares all JSON rows to `Direct80Graph.lean` source and the displayed TeX/PDF row text and externally reconstructs the four retained original payloads. This is **external text and byte evidence**: neither `output_eq` nor those checkers is a Lean parser/file-semantics theorem for JSON, TeX, PDF, or compressed coefficient bytes. In particular, this packet does not prove that the printed coefficient recipes equal the Lean symbolic `fixedPorts`, bind the retained root 14-variable PDF, or identify the different direct-BFS K0.

No independent Lean replay was performed. The runner places its explicitly hash-pinned graph directory first on `LEAN_PATH` and rechecks that graph/source after the run; the audit independently checks its current first resolution. Full transitive project/source-object, package and dynamic provenance remain inherited.
