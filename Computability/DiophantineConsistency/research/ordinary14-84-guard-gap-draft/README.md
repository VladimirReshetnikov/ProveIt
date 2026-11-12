# Conditional 84 guard gap — source-only draft

This **unelaborated source proposal** evaluates the 84 guard in the model
difference ring and derives `F+alpha<q` from that graph's own zero. It assumes
explicit natural representations of both beta and K ports and positive F and
w. Since `q=1+J*beta` is positive, `X=q*w` is positive and `X+K` is positive.
The guard equality then makes `(q−F−alpha)*(X+K)=F+(J*beta)*h` positive;
the first factor is positive and the ordered embedding transfers the strict
gap to the natural model. The subtractions in that argument are signed
ring subtractions, not unchecked natural subtraction.

This is a step toward a natural rank representation, not such a representation
itself: casting `q−F` and `q²−1` requires additional model lemmas, as do rank
windows, Pell indices and the carrier gamma comparison. Explicit port casts,
all draft imports, tactics and arbitrary-model coercions remain uncompiled.
There is no provider-chain, iPRA endpoint or external file/PDF claim.

The checker compares 200 integer graph guard evaluations with the displayed
formula, exhaustively checks bounded positive-F/positive-X guard-zero cases,
and replays draft source receipts. This is neither a Lean run nor an
arbitrary-model proof.

Independent source review is recorded in
`../../reviews/ordinary14-84-guard-gap-draft-independent/`.
