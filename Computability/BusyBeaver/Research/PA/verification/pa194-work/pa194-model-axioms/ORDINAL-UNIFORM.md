# Uniform ordinal-induction statement graph

`PA194FixedSyntaxQuote` defines, by recursion over any **fixed standard typed** relational-source formula, a closed arithmetic Σ₁ graph that denotes its quotation in every covered model. It builds quotations using the internal constructor graphs; it does not introduce the formula's enormous Gödel code as a numeral.

`PA194OrdinalUniform.ordinalInductionGraph` composes five such fixed template graphs with the existing statement-from-property graph. Its checked `ordinalInductionGraph_defined` theorem uses one fixed parameter-free Σ₁ arithmetic formula across all models of the stated candidate PRA and IΣ₁ assumptions. Its property-code argument ranges over the whole model, including nonstandard elements. For an internally valid arity-one property, the previously checked `ordinalInductionCode_scoped` shows that the resulting statement has zero bound variables. For a standard typed property, `ordinalInductionCode_quote` identifies the statement with the Foundation ordinal induction statement exactly.

This is a syntax constructor, not an internal proof of ordinal induction, a PA-to-source proof-code translation, an iPRA theorem, or a PA194 consistency equivalence.

The checker recompiles the two new sources into one fresh output, with the stated prior replay artifacts as dependencies:

```
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-ordinal-uniform.sh "$REPO" /dev/shm/pa194-ordinal-fixed-replay /dev/shm/pa194-ordinal-induction-code-replay /dev/shm/pa194-ordinal-statement-replay /dev/shm/pa194-ordinal-uniform-replay
```

Choose a fresh output path for each replay. The passing log is `/tmp/pa194-ordinal-uniform-replay.log`. Source and immediate fixed-base hashes are checked before and after compilation; remaining transitive dependencies are prebuilt and are not recompiled by this add-on checker.
