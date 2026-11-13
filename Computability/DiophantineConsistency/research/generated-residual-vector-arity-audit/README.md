# Bounded residual-vector arity audit

An independent source review identified that three generated definitions used
`Fin 17` for vectors containing 13, 11 and 8 entries. Their generators and
sources were corrected, and dependent source pins and deterministic receipts
were updated. This audit checks those corrected sources alongside the AQ26 and
QM36/37/38 residual sources requested in the review.

The check reads each listed residual definition and its single `![...]`
vector, then compares the declared vector arity, the number of entries and an
explicit expected value. Its receipt records source hashes. This is a bounded
textual check only; it does not elaborate Lean, prove any theorem, identify
all errors or authenticate compiled providers.

```
python3 -I -S -B research/generated-residual-vector-arity-audit/check.py | cmp - research/generated-residual-vector-arity-audit/receipt.json
```
