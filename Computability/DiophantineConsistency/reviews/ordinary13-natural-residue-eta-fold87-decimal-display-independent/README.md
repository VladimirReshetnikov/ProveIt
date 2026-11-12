# Independent review of the compact folded 13/87 base-10 display

All 87 TeX and extracted PDF rows match the pinned, independently reviewed folded graph, including the eta/rank-offset operations. All 13 input names are distinct. The 87-row version displays its q-scaled `argW` explicitly. The 15,086-digit base-10 seed and fixed-port recipe match the independently authenticated compact P72/P115 construction. The four-page PDF includes the standard-integer-only zero-map notice, distinguishes the current-2011 tuple and reports no overfull boxes. Both deterministic receipts reproduce.

The graph's exact degree 60 and provenance are inherited from its pointwise-equal parent. This review compares source and extracted display bytes; it does not prove formal PDF semantics, a Lean model transfer or an iPRA endpoint.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-natural-residue-eta-fold87-decimal-display-independent/check.py | cmp - reviews/ordinary13-natural-residue-eta-fold87-decimal-display-independent/result.json
python3 -I -S -B research/ordinary13-natural-residue-eta-fold87-decimal-display/verify_display.py | cmp - research/ordinary13-natural-residue-eta-fold87-decimal-display/render-result.json
```
