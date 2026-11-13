# Model halt to a positive free-J zero, conditional on four port bindings

`halt_positive_zero_of_ports` proves in an arbitrary model of `IΣ₁` that a
model-internal halt of the 215-state machine gives a valuation of the actual
95-operation free-J literal with all twelve coordinates positive and with
`InternalZero (literal p) v`. The theorem explicitly assumes the following
four difference-ring equalities for the graph's integer port tuple `p`:

```
ι(rep 590069 N) · p₀ = ι(2^(590069 N) − 1),
p₁ = ι(K),  p₂ = ι(low),  p₃ = ι(high + (2^590069 − 1)).
```

Here `N` is the constructed halt length, and `K`, `low`, and `high` are the
specified compact symbolic model coefficients; coercions are as stated in the
Lean source. These are **assumptions**. In particular this theorem does not
itself prove that any fixed displayed integer tuple satisfies them.

The proof uses the same halt-derived packing word, rank, outer seed, shifted
transport and positive adaptive correction throughout. It constructs the
corrected positive graph valuation, whose slot 10 is
`Δi+(y−auxw)`, proves `auxw≤y` from the same auxiliary norm, binds the graph
rank under the stated port hypotheses, and applies the checked conditional
model-data-to-graph-zero theorem. The graph is the free-J 95-operation
12-variable expression, not the 14-variable equation in `equation.pdf`.

This is a model-theoretic implication conditional on port bindings. It does not
by itself identify the literal with the delivered circuit or PDF, discharge
fixed-port calibration, establish the converse consistency direction, or prove
in Lean that a syntactic iPRA proof exists. The statements about arbitrary
`IΣ₁` models are not being presented as an internal iPRA derivation.

The bounded replay in the neighboring
[namespaced client rebuild](../free-j-namespaced-client-rebuild/README.md)
compiled the final source with exit 0 and no warnings or `sorryAx`. Source
SHA-256 was
`74a760f5503e0845b7e34a38c458dc69d1f1d612f5c36ea24e18b054841e301f`;
object `/tmp/free-j-halt-model-zero-author-q7bmr12g/FreeJHaltModelZero.olean`
had SHA-256
`c2b93b157ebfaacbeca58b6145ade24e86233e38b3a66c489375d359d1cb50b9`.
It is a single-author check, not an independent replay. Lean reports
`propext`, `Classical.choice`, and `Quot.sound` as metatheoretic dependencies.
