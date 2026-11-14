# PA194 semantic interpretation checks

For the standard source `Named.imp .truth (.mem 0 0)`,
`PA194Logic.Relational.relationalCode z` equals `NativeCalculus.wn 0` for every
reserved z: the source atom `.mem 0 0` has numeric code 1, the implicit consequent
of `wn`. The pinned PA196 native total decoder has `decode 0 = .truth` and
`decode (wn 0) = .neg .truth`. Over Unit with the everywhere-true relation and
ordinary equality, the source evaluates true but that decoded target evaluates
false. `decoded_translation_false_any` strengthens the target half to every
relation and valuation.

The Unit relation is not irreflexive. Under any irreflexive relation, the source
formula is also false, so `collision_example_agrees_irreflexive` proves this one
example agrees; it is not a general soundness theorem. The native decoder used in
the example is pinned PA196 syntax and uses the opposite universal-quantifier
pairing order from `PA194Logic.wal`. Therefore these facts concern exactly this
named encoding composed with that native decoder and do not establish a
counterexample to an independently defined PA194 total numeric semantics.
They also say nothing about nonstandard codes, semantic correctness of all other
formulas, proof transport, physical-machine simulation or consistency implications.

Over the two-element type Bool, let the binary relation be empty (hence
irreflexive), use ordinary equality, and assign source labels 0 and 1 distinct
values. `source_equality_false` proves source `.eq 0 1` false, while
`named_neighborhood_true` proves the explicit named formula expressing both
forward and backward observational neighborhood equivalence true. Label 2 is used
for the neighborhood quantifier, distinct from 0 and 1.

`encode194` is a named encoder that uses the actual PA194 `wal` argument order;
`target_encoding_agrees` proves the numeric code of the named neighborhood formula
is exactly `PA194Logic.Relational.relationalCode 2 (.eq 0 1)`. This is a semantic
counterexample for this explicit named reading of the translated equality. It does
not assert that `encode194` is injective, define a total numeric decoder, or prove
a counterexample to any independently established PA194 numeric semantics. In
particular, the PA196 native decoder has the opposite quantifier-field convention
and is not used as a PA194 decoder here.

The Bool/empty-relation structure is nonextensional: the two distinct elements have
identical relation profiles, so it is excluded by the standard extensional
set-membership interpretation. To validate this named equality interpretation one
needs source equality to agree with the observational equivalence used by the
neighborhood formula, e.g. through a suitable extensionality theorem or quotient
interpretation. This condition alone does not establish full translation soundness:
capture/freshness, other constructors, proof transport and the actual numeric
semantics remain separate obligations. The replay uses a retained overlay, not an
empty-overlay build.

With fresh binder label `z` distinct from source labels `a` and `b`,
`PA194SemanticNeighborhoodExact` proves the explicit named neighborhood
formula holds exactly when their assigned values have identical incoming and
outgoing relation profiles. Consequently, its agreement with source equality
is equivalent to equality agreeing with that observational equivalence on
the assigned values. This is a standard named-semantics result; it neither
constructs a total PA194 decoder nor proves extensionality or full soundness.

Assuming an explicit named extensionality formula, `PA194SemanticExtensionalModel`
proves ordinary equality agrees with this named neighborhood equality when the
binder is fresh. It also characterizes that named formula by incoming
extensionality of the relation. This is a standard semantic lemma for one atom,
not a target-calculus derivation or an internal PA proof compiler.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-semantic-audit/check.sh --out DIR` with a matching retained overlay to replay the three modules. This is a suffix replay, not an empty-overlay build.
