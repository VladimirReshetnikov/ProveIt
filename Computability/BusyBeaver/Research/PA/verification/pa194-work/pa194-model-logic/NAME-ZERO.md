# Zero-name existence in the guarded source

`PA194NameZeroField.eZero` proves the exact `NameFacts.eZero` field for the full source theory: the guarded source calculus derives the translation of the PAeq formula saying that zero has a name. The proof makes no `NameFacts`, `TermFacts`, remaining fixed-arithmetic-axiom or induction-supplier assumption.

The staged sources show the whole chain. `PA194NameZeroSource` constructs a Foundation natural-deduction proof of the translated formula, conditional on source equality, empty-set existence and order-isomorphism reflexivity. `PA194NameZeroContext`, `PA194NameZeroSourceOnly`, and `PA194NameZeroProvable` supply and discharge those premises in the full source theory. `PA194NameZeroQuote` proves that the typed PAeq sentence quotes to the actual numeric `exName zeroT` code, and `PA194NameZeroTranslate` proves its exact canonical identity-packet translation equals the quoted typed source formula. The last module turns that proof into the guarded singleton sequent.

From the repository root, use a fresh output directory:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-ezero.sh "$PWD" /dev/shm/pa194-ezero-repo-NEW-new
```

The checker source-builds all seven modules and a nine-report audit in a single output, and rejects `sorryAx`. The retained object overlays and prebuilt Foundation/package objects are enumerated in the checker; this is not an audit of the entire transitive source closure. The theorem is uniform over candidate PRA models whose arithmetic reduct satisfies classical IΣ₁; it is not an object-level native iPRA derivation. The other naming fields, the four remaining fixed axiom suppliers, arbitrary internal induction and physical scheduler synchronization remain separate obligations.
