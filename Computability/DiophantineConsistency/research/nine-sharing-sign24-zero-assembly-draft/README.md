# Sign24 forward/reverse zero bridge: source-only draft

`generate.py` drafts two Lean clients using the 15 transferred row names of
the pinned sign24 AST. The forward client enumerates old q3 and the 15
retained rows, discharges q3 with the lift and transfers each other row from
new zero. The reverse client recovers the old valuation from its drop,
enumerates all 15 new rows, and transfers each from old zero. Both retain the
explicit beta-port representation hypothesis in the IΣ₁ model.

Matching source copies have passed a guarded build with captured outer exit
and an independent terminal review at
`reviews/nine-sharing-sign24-zero-assembly-terminal-independent/`. This
checks both pointwise directions under the displayed beta representation
hypothesis. Same-input existential composition, current-port specialization,
source-byte binding and the iPRA endpoint remain separate.
