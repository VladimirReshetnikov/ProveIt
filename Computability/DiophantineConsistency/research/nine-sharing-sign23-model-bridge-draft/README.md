# Sign23-to-sign24 Delta bridge: source-only draft

`generate.py` emits `SharingSeed23Octic.lean` from the pinned, independently
audited external sign23 AST; `check_syntax.py` parses the emitted residuals
back to that AST. The author checker passed and its output is
`syntax-result.json`. The generated syntax retains the 4,000,000-heartbeat
option from the preceding generator. These source checks are not a Lean degree
theorem, a proof of external port-byte binding, or an elaboration result.

`SharingSign23Squares.lean` proposes the generic square decomposition.
`Sign23Coordinate.lean` proposes to insert the natural polynomial
`(v16+v15)^2 + 4*(v16+v15)+3` in old coordinate 18, prove the deleted
Delta residual, recover that coordinate from an old seed zero, and prove lift
after drop. Unlike the q3 substitution, this coordinate lift has no beta-port
representation premise. Matching syntax and square-decomposition source
copies passed a guarded build and independent terminal audit at
`reviews/nine-sharing-sign23-seed-squares-terminal-independent/`. The
original coordinate proposal failed; a numeral-rewrite retry subsequently
passed an independent terminal audit at
`reviews/nine-sharing-sign23-coordinate-retry01-terminal-independent/`.
The transfer proposals remain uncompiled.

`generate_transfers.py` drafts evaluation identities for all 14 retained
rows; `check_transfers.py` parses both sets of displayed expressions and
checks their row offsets using the preceding author's parser. That author
check is not Lean elaboration or a model proof.

Further work requires guarded coordinate and transfer checks, independent
reviews, a forward and
reverse zero assembly, same-input and current-port existence equivalence,
and composition with an eventual sign24 iPRA endpoint. The current packet
does not assert any of those Lean theorems or an iPRA endpoint.
