# Independent source review: natural-80 J positivity

The [source draft](../../research/ordinary14-natural80-jpos-model-draft/README.md) proposes a mathematically sound conditional proof that an 80-graph zero has positive J when symbolic port 1 is represented by a strictly positive model element `κ`. Its displayed statement has no positive-beta or positive-gamma premise. Both receipts reproduce; no Lean elaboration or iPRA derivation is established.

The independent checker compares all 80 literal Lean graph rows to the pinned JSON, verifies the selected guard and output fields and the relevant factor-product shape, and checks the `J=0` guard identity exactly as a sparse commutative-ring polynomial. Since `b=J*beta=0` at `J=0` regardless of the signed beta port, that guard becomes

```
−(n_F+n_alpha+1)*(n_w+1+κ)−n_F.
```

All named coordinates are nonnegative model elements, and the explicit hypothesis `κ>0` plus model discreteness gives `κ>=1`; hence the guard is at most −2. The output's five-factor product then cannot equal one: if the product of the other four factors were nonnegative, the result would be nonpositive; if negative, discreteness would make its negation at least one, so its product with the negated guard would be at least two. This argument does not inspect gamma or require any positivity or residue property of the other four factors. Natural-model nonzero/positive equivalence then gives `J>0`.

The source statement explicitly requires an `ORingStructure` satisfying `IΣ₁`, `(p 1 : DiffRing V)=ι κ`, `κ>0`, and the 80 `InternalZero`. The selected symbolic K0 must separately supply that representation and positivity. The proposed `simp`, ring evaluation, order embedding, discreteness, `nlinarith` and model instances are unelaborated; the cited `#print axioms` command has not run. This review does not establish provider coherence, physical coefficient/PDF binding, or an iPRA proof-existence claim.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural80-jpos-model-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural80-jpos-model-independent/result.json
```
