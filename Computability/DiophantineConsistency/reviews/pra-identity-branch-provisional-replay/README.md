# Negative pi identity branch on a provisional parent

`PRAWitnessNegExistential` transfers the existing formula-negation growth
bound to an existential over an arbitrary selected input index. It uses the
`IΣ₁` estimate only on the source side of witness transfer; candidate-PRA
models are not assumed to satisfy `IΣ₁`.

`actualIdentityBranch_eq` checks by definitional equality that the identity
formula is the literal first disjunct of Foundation's derivation pi core, for
arbitrary set theories with a `Δ₁` instance. `wb_neg_actualIdentityBranch`
proves its negation has monotone witness bounds in every candidate-PRA model.
This is one disjunct, not the whole core. Both modules' axiom checks report
only `propext`, `Classical.choice`, and `Quot.sound`.

Run from the repository root:

```
python3 Computability/DiophantineConsistency/reviews/pra-identity-branch-provisional-replay/replay.py
```

The script rebuilds both modules and checks, guarding 219 declared current
project sources and 215 inherited project objects. The parent
`/tmp/pra-setshift-coherent/lib` is partially inherited; source/object
correspondence for its full project closure and external Foundation, ZFCinPA
and package ancestry are not fully authenticated. The upstream witness chain
emitted an unused-section-instance linter warning in `PRAWitnessSetTerms`.

The independent same-parent replay `/tmp/pra-identity-branch-independent-224i5vnq`
passed and matched all four source/object/full-log rows. Its state and logs
are frozen in `independent-evidence/`; the inherited-parent scope is unchanged.
