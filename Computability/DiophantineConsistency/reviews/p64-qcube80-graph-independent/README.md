# Independent audit of the 80-operation graph

On 2026-11-04 the read-only [`audit.py`](audit.py) produced the captured
[`receipt.json`](receipt.json). It checks pinned graph and ring-binding
receipt hashes, confirms the two graphs differ structurally only by removal
of `ell_plus_rho` and replacement of `first_unscaled = ell_plus_rho+s` by
`first_unscaled = ell+r0`, and checks the only occurrences of `rho` and
`r0`. Thus substitution `r0=rho+s` identifies all unchanged rows as well
as the changed carrier, using associativity. The 80 rows contain 42
multiplications, 22 additions and 16 subtractions.

The script independently evaluates the actual 80-row graph using full
univariate polynomial arithmetic over F₁₀₀₀₀₀₃, with witness `j` set to
`(j+1)t` and the four ports to 5, 6, 7, 8. The five residual degrees are
12, 34, 22, 23, 2; the output degree is 68, and its leading coefficient is
193218, equal to the claimed symbolic leading form evaluated on that ray.
This nonzero result corroborates the degree calculation but is **one
specialization**, not by itself a general leading-form or exact-degree
proof for the chosen fixed ports. The candidate builder's separate symbolic
check uses algebraically rewritten residuals and the pinned parent verifier's
four identities.

The audit also checks that the retained ring-binding replay reports exit 0
and precisely six expected `[propext]` reports. The Lean source states
equality of each residual and the output under coordinate `9 ↦ v 9 + v 7`
for all commutative rings. Its source and captured receipt are hash-pinned;
this audit does not rerun Lean or authenticate the transitive provider
ancestry. Neither this ring theorem nor the graph audit proves that every
positive 80 zero has a positive 81 preimage, an iPRA endpoint, or any
JSON/PDF semantics.

Separately, the candidate's own finite builder and Lean generator were
rerun read-only and reported `PASS`; this packet does not claim a new Lean
build. Reproduce its deterministic checks from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube80-graph-independent/audit.py
```

The SHA-256 of `audit.py` is
`da2f5a3e972b5bd9add8d3d2f257496a43fcfe8f8aeca89097e9a6903ba061a5`;
the receipt SHA-256 is
`fb301fb71c1dcbfa72cdfe0c40e04f0c59043d99580ebb8ce6c95f112b9af8c2`.
