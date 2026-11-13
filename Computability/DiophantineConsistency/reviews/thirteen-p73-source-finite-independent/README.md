# Independent source and finite review of package 73's endpoint

On 2026-11-04 the read-only [`audit.py`](audit.py) produced the captured
[`receipt.json`](receipt.json). The pinned package 73 JSON is present. The
script independently constructs its Lean let-chain and matches the marked
block in `P73Graph.lean`; all 92 gates and all 13 witnesses and four ports
are live and topologically ordered. It also checks the witness indices, port
indices, and graph's selected output row. The gate count is 51 multiplications,
24 additions and 17 subtractions. The upstream generator was also rerun in
check mode and exited 0.

The script independently evaluates the whole JSON graph as a univariate
polynomial over F₁₀₀₀₀₀₃ with witness `j` set to `(j+1)t` and the ports to
5, 6, 7, 8. The residual degrees are 15, 13, 14, 13 and the output has degree
30 with nonzero leading coefficient 6797. This is one specialization; it
does **not** prove a general exact degree for the actual fixed ports. The
package's own finite symbolic certificate is a separate argument.

Source inspection shows `P73Halt.halts` maps positive zeros at the symbolic
compact44 ports to machine halting, and `P73Converse.converse` constructs a
positive zero from a halt. `IPRAPositive73.positiveBridge` combines them,
then applies the existing native, standard and equality-only iPRA adapters.
The author-side [endpoint record](../../research/thirteen-p73-endpoint/README.md)
reports successful serial builds. This review did not run Lean, locate a
complete retained build receipt, independently replay those theorems, or
authenticate full project, package, dynamic and search-path ancestry. It
therefore cannot upgrade the author report to a paired or source-current
proof. JSON-to-Lean graph transcription is checked externally; the symbolic
ports' connection to external coefficient bytes and PDF semantics remains
separate.

Reproduce the deterministic checks from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/thirteen-p73-source-finite-independent/audit.py
```

SHA-256: `audit.py`
`dc5d1bd254fb6405bb315af42b844efc04d8cd770fac6fe29aa024b1abc8be85`;
`receipt.json` `3d988e8027dc416b9e11b1abf936ed4f16ee1efd7d5827235a0e03a2fc13d343`.
The earlier, narrower receipt is retained as `receipt-v1.json`.
