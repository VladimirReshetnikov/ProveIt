# Explicit dual quantifier wrappers for the PA194 recursion

`PA194DualForallCode.lean` provides a primitive-recursive binary code that,
given a source variable label and a pair of positive/negative formula codes,
constructs the pair of a universal positive formula and an existential
negative formula. It uses candidate-PRA-certified pair projections and a
supplied binary code `close` for closing the named variable. The numeric
wrapper equation holds in every candidate-PRA model for arbitrary, including
nonstandard, values. Identification with Foundation's named `qqAll` and
`qqExs` constructors is separately proved only under IΣ₁.

`PA194DualQuantRecursion.lean` instantiates the paired source recursion's
universal branch with that wrapper and proves its exact numeric equation in
every candidate-PRA model. With the decoder and projection certificates, all
the source tags now have fixed primitive-recursive syntax combinators except
for the single supplied `close` operation. Existing dual-recursion theorems
apply directly to this instantiation.

This package leaves `close` as a parameter. The separate
[canonical-closer bridge](PA194CanonicalDualForall.md) supplies a fixed code,
proves its agreement with Foundation's internal traversal, and establishes
the universal-branch equation when the recursively translated bodies are
well formed. The separate [source-output proof](PA194SourceOutputWF.md)
establishes that well-formedness for every internal source code, and the
[polarity proof](PA194SourcePolarity.md) identifies the negative output as the
internal syntactic negation of the positive output. These packages do not
establish positive/negative semantic duality for nonstandard formulas, the connection of the
zero alias to this truth code and the represented proof compiler, the encoding
and proof translation to Foundation's relational source, PA calibration,
machine internalization, or either consistency implication.
`PA194ZeroAlias.lean` separately proves the alias's logical equivalence in PA
for truth chosen as `0=0`.
Rebuild the full chain with the pinned overlays:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check-dual-quant-recursion.sh
```
