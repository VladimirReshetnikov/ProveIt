# Sign22-to-sign23 kY bridge: source-only draft

`generate.py` emits the Fin23 `SharingSeed22Dodecic.lean` syntax from the
pinned independently audited external sign22 AST. `check_syntax.py` parses the
expressions back to that AST, confirms coordinate bounds and residual
syntactic degree at most six, and records `syntax-result.json`. This is not a
Lean degree theorem or a proof of external coefficient-byte binding. The
generator retains the inherited 4,000,000-heartbeat option.

`SharingSign22Squares.lean` proposes generic square decomposition.
`Sign22Coordinate.lean` proposes inserting the natural product
`((v11+1)+(v12+1))*v15` at old coordinate 17, proving the old kY row zero,
recovering the coordinate from old seed zero and proving lift after drop. No
beta-port representation premise is needed for this substitution. Matching
syntax/squares source copies passed a guarded build and independent terminal
audit at `reviews/nine-sharing-sign22-seed-squares-terminal-independent/`;
the coordinate source remains uncompiled.

Further work requires guarded syntax/squares and coordinate checks,
independent review, all 13 remaining residual transfers, forward/reverse zero
assembly, same-input/direct-expression composition, and transport of the
checked sign23 iPRA endpoint. No sign22 model bridge, iPRA endpoint, Lean
degree theorem or external-file binding is claimed here.
