# Sign21-to-sign22 normalized-S bridge: source-only draft

`generate.py` emits Fin22 `SharingSeed21Degree14.lean` from the pinned,
independently audited external sign21 AST. `check_syntax.py` parses the
expressions back to that AST and confirms residual syntactic degree at most
seven. This is not a Lean degree theorem, external-byte binding, or Lean
elaboration result. The generator retains the inherited 4,000,000-heartbeat
option.

`SharingSign21Squares.lean` proposes generic square decomposition.
`Sign21Coordinate.lean` proposes to insert the natural product
`(v6+1)*v17*(v17+2)` at old coordinate 21, prove the old S row zero,
recover the coordinate from old zero and prove lift after drop. No beta-port
representation premise is needed. Matching syntax/squares source copies passed
a guarded build and independent terminal audit at
`reviews/nine-sharing-sign21-seed-squares-terminal-independent/`; coordinate
source remains uncompiled.

Guarded syntax/squares and coordinate checks, independent reviews, the 12
remaining residual transfers and zero assembly, same-input/direct-expression
composition and an eventual iPRA endpoint are separate obligations. This packet
claims none of those Lean results.
