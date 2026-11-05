# Independent review of the 78-operation graph and endpoint receipts

On 2026-11-04 the read-only [`audit.py`](audit.py) produced the captured
[`receipt.json`](receipt.json). It checks that the 79 parent uses
`first_radicand` only for `first_product+1` and the first residual; the 78
graph deletes that gate, subtracts `first_product` directly in `A0`, and
changes only the final output subtraction from 1 to 2. The other 76 rows,
ports, witnesses and output name agree. Thus `A78=A79+1` and
`output78=output79+2*A79`; outputs are not generally equal. There are 42
multiplications, 20 additions and 16 subtractions.

Full univariate evaluation of the actual 78-row graph over F₁₀₀₀₀₀₃, with
witness `j` set to `(j+1)t` and ports 5, 6, 7, 8, gives residual degrees
22, 34, 22, 23, 2 and output degree 68. Its nonzero leading coefficient
193218 matches the claimed symbolic leading form on this ray. This is one
specialization, not a general exact-degree proof for the fixed ports. The
candidate's builder and Lean generator separately reran and reported `PASS`;
the builder's general symbolic certificate uses algebraically rewritten
residuals and the pinned parent verifier's four identities.

The audit rechecks the retained zero-exit binding and positive-zero
equivalence replay receipts, their exact axiom reports, direct inputs and
output hashes. It also checks the endpoint's recorded exit, exact four
reports and direct input/output hashes, including that the endpoint imported
the same existence object produced by the replay. Source inspection confirms
that the endpoint composes `positive_zero_iff` with the 79 bridge and applies
the native, standard and equality-only adapters for the symbolic compact44
ports. The existence theorem uses a separate actual-zero split to obtain
`A78=1` before applying the output-difference identity. The graph-split
packet originally reported an author success and recorded hashes without a
guarded replay. A later [guarded replay](../../research/fourteen-p64-qcube78-graphsplit-replay/README.md)
exited 0 and produced the same object; it inherits the same transitive
provider limitations.

No Lean process was run for this review. The checks use captured temporary
providers, and their full transitive project, package, dynamic-library and
search-path ancestry remains inherited. JSON-to-Lean, payload, TeX/PDF
binding and global minimality remain separate.

Reproduce the retained-evidence checks while the temporary objects exist:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube78-graph-endpoint-independent/audit.py
```

SHA-256: `audit.py`
`31d5f2e47ae5bd34f37ae15b3b75b03788295666dd7e738c3451642bd7be48fc`;
`receipt.json` `b748a7aed9a5b8c3fff61cbb9fa2f28352b549a57b97ff7bf5bffc19e14a5ffe`.
