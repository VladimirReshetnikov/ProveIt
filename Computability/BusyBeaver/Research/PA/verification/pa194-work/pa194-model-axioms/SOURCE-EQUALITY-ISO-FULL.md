# Full-source closed equality-to-isomorphism proof

`PA194SourceEqualityIsoFull.sourceProof` is a typed proof in the adjunctive full-separation source theory of `∀a b c, domain(b) → domain(c) → b=a → c=a → orderIso(b,c)`. It universally closes the checked open standard derivation and discharges equality and reflexivity using the existing source axiom suppliers.

It is a model-level proof under candidate PRA plus arithmetic IΣ₁. The standard quotation identity connecting this exact formula to `SourceFacts.ei` remains to be proved; this is not yet a native iPRA or machine theorem. The checker rebuilds its source against the repository-replayed closed derivation and pins direct prebuilt objects; transitive imports remain prebuilt.

```
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-source-equality-iso-full.sh "$PWD" /dev/shm/pa194-source-equality-iso-full-repo
```

All three printed axiom reports omit `sorryAx`.
