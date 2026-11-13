# Conditional fixed-port boundary for the 76 transport proposal

This packet gives an exact algebraic transformation that **would** produce a
76-graph zero violating the proposed reverse-positivity bound at the same four
ports, provided an old 77 zero with additional properties exists. No such old
zero is constructed or asserted here, and this does not disprove the
existence equivalence of the two graphs.

Let a positive 77 tuple have `q=beta*J+1`, write
`C=q−F−alpha`, and suppose `C>0`. Choose a positive integer `d<F` with

```
(q−1) | d*(K0+w+1).
```

Define the nonnegative integer `h=d*(K0+w+1)/(q−1)` and change only

```
F' = F−d,
C' = C+q*d,
z' = z+d*(K0+w)+h.
```

Keep all four ports and every other witness unchanged. Every new witness is
positive. The old gap and transport expressions are preserved:

```
(q−1)*(q−F)+alpha = q*(q−F')−C',
Lt'−Lt = d*(K0+w+1)−h*(q−1) = 0.
```

Thus `R` and all five residuals, and hence the complete graph output, agree
under this mapping. Moreover,

```
C'−(q−F') = d*(q−1)−alpha > 0.
```

The strict inequality follows from positive `F`, `C`, and `alpha`: they imply
`alpha≤q−2`, while `d≥1`. Hence a 77 zero satisfying the extra divisibility
and `d<F` hypotheses would give a 76 zero for the *same fixed ports* where
recovering `alpha'=q−F'−C'` yields a negative value. The simple special case
`d=1` requires `F≥2` and `(q−1)|(K0+w+1)`. This rules out the direct
same-witness inverse under those hypotheses; even such a pair of zeros would
not by itself refute zero-existence equivalence, since a different 77 witness
could exist.

[`check.py`](check.py) verifies the gap, transport-difference and guard
identities in an exact sparse polynomial ring. It also performs 600
reproducible modular graph comparisons with positive natural inputs, fixed
ports, `d=1`, and the divisibility enforced. These are finite algebra checks,
not actual graph-zero examples or a Lean proof. The script pins both graphs
and the polynomial verifier; [`result.json`](result.json) records its exit-0
observation. Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76-fixed-port-boundary/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `92624e74a0ce197a8581d508f6d7da8c2d81ea6738e6d0b52ea1a0e94d85ec08` |
| `result.json` | `e1cc842df1ddfcaa229d26098c1238112171e3a1d5726c85096dad088a691053` |
