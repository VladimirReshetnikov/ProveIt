# Compact44 finite support and defect reconstruction

This is an external finite arithmetic check. It does **not** prove that the
model-level mask is the actual graph port, that the graph's no-carry premise
holds, or that an iPRA derivation exists. The proposed model argument below is
not yet implemented or verified in Lean.

The checker pins the coefficient builder, its binding JSON, the ordered 943-row
JSON, and the retained compressed `MC` and `beta` files. It independently reads
the builder's three literal tuple constants, reconstructs the 41 copy/anchor
positions from the binding, and checks all 8807 radix-2^67 digits of the
retained `MC`. The builder's pinned `recipe()` constructs `E` as the **keys** of
its coefficient dictionary: selector rows, the 41 copies/anchors, and explicit
dummies 1063 and 1064. In particular both dummies have coefficient value zero;
using only nonzero coefficient positions would be wrong. Builder equation
`MC=B-1-sum(1<<(67*e) for e in E if e!=1)-(2<<(67*1063))`
is independently checked here against the retained bytes, not taken as a
model theorem. The ordered table's row 1 is the forbidden selector.

Write `R(w,n) = sum_{j<n} 2^(w*j)` and `q=2^67`. The exact disjoint support is

```
E = [0,942] ∪ [983,992] ∪ [1003,1011] ∪ [1013,1031]
    ∪ {1063,1064,1095,2195,3296},           |E| = 986.
S = R(1,943) + 2^983 R(1,10) + 2^1003 R(1,9) + 2^1013 R(1,19)
    + 2^1063 + 2^1064 + 2^1095 + 2^2195 + 2^3296.
D = sum_{e∈E, e≠1} q^e + 2 q^1063
  = 1 + q^2 R(67,941) + q^983 R(67,10) + q^1003 R(67,9)
    + q^1013 R(67,19) + 3 q^1063 + q^1064 + q^1095 + q^2195 + q^3296.
MC + D = beta = q^8807 − 1.
```

Thus position 1 is in the support but contributes zero to `D`, while position
1063 contributes three. For every integer `j` in `[0,8806]`, defining `δ(j)`
to be zero at 1, three at 1063, and the `j`th bit of `S` otherwise, the
checked identity is `digit_q(MC,j) + δ(j) = q−1`.

A possible model proof would show the same finite `S`-bit identities, define
the defect digit function, and use `ArithmeticPackingBlocks.blocks_add`,
`blocks_unique`, and `blocks_const_rep` to derive `W+D=beta` for the
`CompactStructuredMask.maskDigit` block `W`; cancellation against an
independently established model equality `MC+D=beta` then gives `W=MC`.
Alternatively `bsum_add` requires the relevant Σ₁-function instances. These
are proof obligations, not consequences of Python's finite calculation. A
separate bridge must bind the concrete fixed graph port to the retained MC
recipe in the intended model, and internal provability requires additional
formalization.

Run from the repository root:

```
python3 -I -S Computability/DiophantineConsistency/reviews/compact44-support-defect-independent-audit/audit.py
python3 -O -I -S Computability/DiophantineConsistency/reviews/compact44-support-defect-independent-audit/audit.py
```

Both actual commands exited 0 and reported `PASS_COMPACT44_SUPPORT_DEFECT_FINITE`,
986 support positions, 8807 digit checks, and four rejected negative controls:
retaining position 1 in the defect, giving 1063 only weight 1, omitting 1064,
and omitting copy position 1013. The checker uses explicit `need` checks rather
than `assert`, so optimized mode performs the same checks. Inputs are rehashed
at the end; this is an external point-in-time file check, not a continuous
integrity guarantee. See `reviews/compact44-selector-recipe-independent-audit`
(commit `26ff813576`) for the broader K/MC/MF and phase checks; none imply the
model binding claimed as an open obligation here.
