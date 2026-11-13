# Sign21 forward/reverse zero bridge: source-only draft

The generator drafts forward and reverse Lean clients from the pinned sign21
AST. The forward enumeration covers 13 old rows, discharges normalized-S
with the natural lift and transfers the 12 retained rows. The reverse
enumeration covers 12 new rows and uses old-coordinate recovery and those
transfers. No beta-port representation premise is needed for this substitution.

Matching source copies passed a guarded build and [independent terminal audit](../../reviews/nine-sharing-sign21-zero-assembly-terminal-independent/README.md).
This establishes both pointwise directions over symbolic ports in IΣ₁ models.
Same-input existence, direct expression, Lean/JSON binding, degree theorem and
iPRA endpoint remain separate.
