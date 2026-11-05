# Independent audit of the 79-operation graph

On 2026-11-04 the read-only [`audit.py`](audit.py) produced the captured
[`receipt.json`](receipt.json). It checks pinned graph and ring-binding
receipt hashes, confirms that the 80-operation parent uses `r0` only in
`first_unscaled = ell+r0`, and that the new graph uses `t` only in
`first_unscaled_square = t*t`. All other 78 rows, ports and output are
identical. Consequently substitution `t=ell+r0` identifies the affected
square and every subsequent row. The new graph has 42 multiplications,
21 additions and 16 subtractions.

The script independently evaluates the actual 79-row graph using full
univariate polynomial arithmetic over F₁₀₀₀₀₀₃, with witness `j` set to
`(j+1)t` and the four ports to 5, 6, 7, 8. Here the indeterminate `t` in
the ray description is independent of the graph's witness name. The five
residual degrees are 22, 34, 22, 23, 2; the output degree is 68, and its
leading coefficient is 193218, equal to the claimed symbolic leading form
evaluated on that ray. This nonzero result corroborates the degree
calculation but is **one specialization**, not by itself a general
leading-form or exact-degree proof for the chosen fixed ports. The separate
candidate builder uses algebraically rewritten residuals and the pinned
parent verifier's four identities.

The audit also checks that the retained ring-binding replay reports exit 0
and precisely six expected `[propext]` reports. The Lean source states
equality of each residual and the output when coordinate 9 is updated to
`ell p v + v 9`, for all commutative rings. Its source and captured receipt
are hash-pinned; the current object hashes also matched the receipt. This
audit does not rerun Lean or authenticate the transitive provider ancestry.
Neither this ring theorem nor the graph audit proves that every positive 79
zero has a positive 80 preimage, an iPRA endpoint, or any JSON/PDF semantics.

Separately, the candidate's finite builder and Lean generator were rerun
read-only and reported `PASS`; this packet does not claim a new Lean build.
Reproduce its deterministic checks from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube79-graph-independent/audit.py
```

The SHA-256 of `audit.py` is
`5764a315c8e9f9329a21bd07e675c8be1fa61735b27e4e785acabdcaa4bd7c3c`;
the receipt SHA-256 is
`bf826ea29bf5be97a61798f7f4a8ed43a5e863894cb0493387fe5809ff06fe41`.
