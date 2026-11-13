# Independent review of the conditional fixed-port transformation

Reviewed [`p64-qcube76-fixed-port-boundary`](../../research/p64-qcube76-fixed-port-boundary/README.md)
against the pinned 77 and 76 graph JSON, its Python source and result receipt.
No algebra, sign, positivity or scope error was found. For positive `d<F`
and `q−1 ∣ d*(K0+w+1)`, the stated quotient is nonnegative and makes the
transport difference zero; the gap and hence rank are unchanged. The strict
guard violation follows from `alpha≤q−2` and `d≥1`. Unchanged ports and all
other witnesses then leave all five residuals and the output unchanged.

The separately analyzed [`d=1` construction](../../research/p64-qcube76-boundary-obstruction/README.md)
is the special case `F≥2`, `q−1 ∣ K0+w+1`; the two formulas for the added
`z` agree because `q=1+(q−1)`. The generalized derivation preserves transport
even without assuming it is zero, whereas the separate packet is stated for
old tuples with zero transport.

Reran the author's `python3 -I -S -B .../check.py` with exit 0. It reproduced
the exact polynomial identities and all 600 recorded modular comparisons,
and matched `result.json`. This is a read-only source and artifact review, not
a fresh Lean proof, an actual graph zero, or an independent rebuild of the
pinned polynomial verifier. The fixed-port result is conditional on an old
zero satisfying its extra hypotheses; it does not disprove fixed-port
existence equivalence or settle the fixed current ports.

Reviewed hashes:

| Artifact | SHA-256 |
| --- | --- |
| author `README.md` | `2a330394515c39c9d5298757d5a719bc2e92e8af9f524b8441cf2980d439d002` |
| author `check.py` | `92624e74a0ce197a8581d508f6d7da8c2d81ea6738e6d0b52ea1a0e94d85ec08` |
| author `result.json` | `e1cc842df1ddfcaa229d26098c1238112171e3a1d5726c85096dad088a691053` |
