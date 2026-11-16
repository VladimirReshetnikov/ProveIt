# Zero-name uniqueness in the guarded source

`PA194UniqZeroField.uZero` proves the exact `NameFacts.uZero` field for the full source theory, with no assumed `NameFacts`, `TermFacts`, fixed-arithmetic-axiom suppliers or induction-supplier hypothesis. It holds uniformly in candidate PRA models whose arithmetic reduct satisfies classical IΣ₁, including nonstandard models. It does not by itself give a native iPRA theorem.

The six source modules in this audit build the typed source proof, discharge its explicit equality assumptions using the full source theory, and use the independently replayed exact quote and identity-packet translation of `uniq zeroT` to obtain the guarded singleton. The source proof uses the separately replayed `PA194EqualZero.unique` matrix, which in turn relates two zero representatives by constructing an actual empty isomorphism; the source theory need not identify all empty representatives. The two universal quantifiers are domain guarded.

From the repository root, with a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-uzero-field.sh "$PWD" /dev/shm/pa194-uzero-field-repo-NEW
```

The checker builds all six modules and an eight-declaration axiom audit in one output, rejects `sorryAx`, and retains the independently source-replayed matrix and syntax/translation overlays along with the other object overlays enumerated in the checker, including prebuilt Foundation. This does not recompile the entire dependency closure. The other naming fields, four remaining fixed arithmetic suppliers, arbitrary internal induction, native iPRA transfer and physical scheduler synchronization remain separate obligations.
