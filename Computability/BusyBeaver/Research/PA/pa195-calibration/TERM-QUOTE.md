# Single term-closing code: shapes and standard quotations

`PA194TermQuote.lean` connects the single primitive-recursive `closeCode` of
`PA194TermRecursion.lean` to two external descriptions of arithmetic terms.
The arguments `first` and `second` are explicit certified primitive-recursive
pair projections, with the certificate hypotheses displayed in the statements;
`PRA_has_stackProjections` establishes their existence.

* `modelShape` applies in **every candidate-PRA model**, with no IΣ₁
  hypothesis. For any externally finite `Shape M`, it proves that `closeCode`
  produces its recursively closed value. All the fields of that shape and the
  label and binder depth may be arbitrary model elements, including
  nonstandard elements. The result covers function nodes of arity 0, 1 or 2.
* `quote` assumes the arithmetic reduct also satisfies **IΣ₁**. For any
  externally standard Foundation arithmetic term `t` with standard label `a`
  and depth `d`, it proves that applying `closeCode` to the Foundation quote
  of `t` gives the Foundation quote of `closeDepthRew a d t`. It uses all four
  arithmetic function symbols (the language has no unary function symbol).
  The quote on both sides is interpreted in the model.

The first theorem does not by itself cover model-internal terms of nonstandard
structural depth. The second theorem does not establish `closeCode`'s agreement
with an internal rewrite on arbitrary nonstandard typed syntax. Neither theorem
proves a formula-closing theorem or a machine/PA consistency equivalence.

Run `check-term-quote.sh` with the audited `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` paths set. The checker rebuilds the local prerequisite
chain and rejects `sorryAx`; the two theorem axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.
