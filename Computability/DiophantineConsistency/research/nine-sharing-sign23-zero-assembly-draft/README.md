# Sign23 forward/reverse zero bridge: source-only draft

The generator drafts forward and reverse Lean clients from the pinned sign23
AST. The forward enumeration covers 15 old rows, discharges Delta with the
natural lift and transfers 14 other rows. The reverse enumeration covers all
14 new rows and uses old-coordinate recovery and the corresponding transfers.
No beta-port representation premise is needed for this substitution.

Matching source copies passed a guarded build and [independent terminal audit](../../reviews/nine-sharing-sign23-zero-assembly-terminal-independent/README.md).
This establishes the two pointwise directions over symbolic ports in IΣ₁
models. Same-input existential composition, direct expression, Lean/JSON
binding, degree theorem and iPRA endpoint remain separate.
