# Independent review of further low-mask specialization failures

`check.py` rechecks all five retained author receipts and diagnostics: two isolated fixed-radix attempts and three displayed-low iPRA client attempts. Each had nonzero Lean exit under `-M3000` and a kernel excessive-memory diagnostic; the second isolated attempt additionally reported maximum recursion depth. Source files, recorded input pins and logs are rehashed. Failed isolated axiom reports mention `formula_to_digits`, and failed client reports mention `low_eq`; these are unresolved declarations, not accepted proofs.

The separately audited variable-radix generic identity remains accepted. These five attempts do not establish a fixed-radix low-mask equality, a displayed-low iPRA client, or external PDF/file semantics. This review executes no Lean and makes no claim about later unreviewed attempts.
