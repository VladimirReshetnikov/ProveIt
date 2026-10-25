# Natural quartics from canonical CRT signs

All coordinates independently range over N={0,1,2,...}. Each equation is the
sum of the squares of the complete quadratic rows in its `equation.json`.

| Endpoint | Variables | Rows | Degree | Collected terms | Height |
|---|---:|---:|---:|---:|---:|
| natural206 | 206 | 158 | 4 | 8,210 | 130,686,376 |
| balanced207 | 207 | 159 | 4 | 5,278 | 69,238,087 |
| sparse208 | 208 | 160 | 4 | 5,198 | 65,866,712 |

Relative to the retained ordinary C222/ZF/ZFC calibration, each has a natural
zero exactly when ZFC has a finite syntactic refutation. Therefore its
no-natural-zero sentence is provably equivalent in ZFC to Con(ZFC). This is
neither a consistency proof nor a newly kernel-checked logical endpoint.

The new source factors the common square out of the Horn disjunction before
quadratization. Twenty-eight old gates become fourteen natural product gates.
Soundness restores old squares pointwise. Completeness chooses CRT lifts in
the order b>c, Sp>S, then a sufficiently large: every new product is natural
and the original semantic Pell anchor still dominates all seed indices.
The local source polynomial itself is unchanged. See `PROOF.md` and the
article section `report_section.tex` for the full unbounded domain argument.

`dimension206`, `projected207` and `projected208` retain the pre-row-basis controls. The raw
source has310 coordinates/262 rows. Every selected endpoint includes full
literal residuals (TeX and plain text), coordinate names, complete expanded
quartic coefficients and exact restoration or inverse-row certificates.

## Offline verification

```
python verify.py --rebuild
python -O verify.py --rebuild
```

Python's standard library suffices. The verifier independently checks the
entire source delta, each contraction restoration, all coefficients, inverse
row operations, printed TeX parsed back to polynomials, corruption controls,
the complete pinned inherited closure, and byte-identical rebuilt artifacts.
Finite checks are not presented as a proof of the unbounded arithmetic.

`inherited/` is the unchanged frozen round19 natural packet, including all
prior ordinary proofs, source bindings and compiler dependencies. No repository
file was edited. The independent external audit is retained under `review/`.
