# Typed separation-schema quotation

For every typed relational-source semiproposition `p : Semiproposition language 1` and every modeled arithmetic M satisfying PRA and IΣ₁, `fullyClosedSeparation_quote` proves the exact equality

```
fullyClosedSeparation (⌜p⌝ : M) = (⌜(separationFormula p).univCl⌝ : M)
```

Here `separationFormula` is the repository's explicit typed membership/equality separation proposition. No alpha-equivalence or parameter restriction is assumed. The proof establishes the open-root quotation, exact agreement of numeric binding with the typed `Rew.fix` at arbitrary typed depth, the order of iterated closures using Foundation's `allClosure_fixitr`, and equality between the numeric free-index bound and the cast of the typed formula's `fvSup`. Thus this result handles each standard typed property in any such model; it does not by itself prove the reverse decoding of all standard numeric property codes or a native iPRA derivation.

Run from the repository root, with a fresh final output path:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-typed-schema.sh "$PWD" \
  /dev/shm/pa194-fully-closed-replay \
  /dev/shm/pa194-typed-schema-replay
```

Five source modules and a ten-declaration axiom audit are rebuilt in one output. The checker pins these sources and selected imported objects, including the closed-separation object, `PA194SourceSeparation.olean`, and Foundation's `InductionSchemeDelta1.olean`, before and after the replay; it rejects `sorryAx`. Other staged overlays and Foundation dependencies are prebuilt. Successful log: `/tmp/pa194-typed-schema-replay.log`.
