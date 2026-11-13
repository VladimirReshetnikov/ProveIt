# Exact transport-restricted equivalence

`Absorb88Restricted.positive_zero_iff` proves that for every natural port tuple with `beta>0`, in every indicated IΣ₁ model, the actual 89 graph has a positive zero if and only if the actual 88 graph has a positive zero that additionally satisfies `(F+alpha)*(K0+w)+F < q*(K0+w)`. The reverse implication is the previously checked conditional selection/inverse proof; for the forward implication the 89 graph's transport theorem supplies the bound and the checked 89-to-88 map preserves it.

This is not an equivalence for arbitrary positive 88 zeros: the extra inequality is part of the existential statement. In particular the conditional full-zero symmetry obstruction rules out simply proving that all 88 zeros obey it under the documented fixed-port hypothesis. This result alone does not give an unrestricted 88 iPRA equivalence.

`run-restricted.py` passed in guarded author session 24085, exit 0. Its exact source snapshot, selected predecessor objects, resource samples and output are under `observations/restricted-attempt01/`. It inherits the previously documented linter suppressions and selected-provider, package-transitive, dynamic and historical source/object ancestry limitations; no independent Lean replay is claimed.

The independent source-and-receipt review passed in `reviews/ordinary12-absorb88-restricted-independent/`; it did not independently replay Lean.
