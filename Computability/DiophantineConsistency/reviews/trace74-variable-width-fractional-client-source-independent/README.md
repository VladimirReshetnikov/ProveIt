# Independent source review: fractional linked-index client

The reviewed source has SHA-256
`a91d587c418b9423c6d535052eafc1703c2152905d5094d467b7fc527a65874c`.
The arithmetic derivation is correct: from `n+n/4<r`, discreteness gives
`n+n/4+1≤r`; the model division identity `n=4(n/4)+n%4` and bound
`n%4<4` then imply `5n<4r`. The proof carries these inequalities into the
difference ring and transfers the conclusion back.

The graph theorem applies that implication to the supplied first and main
ordinate indices for the same fixed-symbolic positive graph zero. It keeps
the explicit conditions `n≥4` and `8n≤67·8807`. The existential client
uses the existing linked pair with `n≥7`, odd `r≥11`, `n+3<r<2n`, both
ordinates and the first-index residue; its fractional conclusion is an
implication whose antecedent is `8n≤67·8807` for that very same `n`.

The source does not establish this first-index upper bound, rule out all
zeros, prove the reverse guard, or provide an iPRA endpoint. This review
checks source-level reasoning and imported theorem interfaces only; it is
not an independent Lean replay or a transitive provider/package audit.
