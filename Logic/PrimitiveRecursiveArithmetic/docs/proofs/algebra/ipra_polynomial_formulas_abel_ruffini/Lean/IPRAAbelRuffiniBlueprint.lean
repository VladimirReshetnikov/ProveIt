import PolynomialFormulas.Basic
import PolynomialFormulas.Cubic
import PolynomialFormulas.Quartic
import PolynomialFormulas.AbelRuffini
import PolynomialFormulas.GenericAbelRuffini
import ConciseIPRA.NativeBiInterpretation

/-!
# iPRA Abel--Ruffini blueprint

This file is an interface blueprint, not the completed object-theory proof.
It deliberately contains no `axiom` and no `sorry`.  The opaque declarations
below mark implementation boundaries for the primitive-recursive coding layer;
target theorems are recorded in comments rather than postulated.

Suggested destination in ProveIt:

  Logic/PrimitiveRecursiveArithmetic/Applications/AbelRuffini/

See `../chapters/11_lean_plan.tex` for the dependency graph and proof plan.
-/

#check LeanProofs.PolynomialFormulas.quadratic_formula_factorization
#check LeanProofs.PolynomialFormulas.cubic_factorization
#check LeanProofs.PolynomialFormulas.quartic_factorization
#check LeanProofs.PolynomialFormulas.no_universal_radical_formula_of_degree_gt_four
#check LeanProofs.PolynomialFormulas.GenericAbelRuffini.every_root_not_solvableByRad
#check LeanProofs.ConciseIPRA.native_iff_pra
#check LeanProofs.ConciseIPRA.pra_iff_native

namespace LeanProofs.ConciseIPRA.Applications.AbelRuffini

/-- All object-language datatypes are ultimately natural-number codes. -/
abbrev Code := Nat
abbrev QCode := Code
abbrev ExprCode := Code
abbrev ProofCode := Code
abbrev GroupCode := Code
abbrev TowerCode := Code

/-- Proof-carrying input for one of the four positive formula checkers. -/
structure LowDegreeWitness (n : Fin 5) where
  coeffs : List QCode
  data : ExprCode
  derivation : ProofCode

/-- The following opaque constants are implementation slots, not assumptions
about their correctness.  Each is to be replaced by a total primitive-
recursive definition in the modules listed in the report. -/
opaque factorCheck : List QCode → List ExprCode → Bool
opaque lowCheck : (n : Fin 5) → LowDegreeWitness n → Bool
opaque lowRoots : (n : Fin 5) → LowDegreeWitness n → List ExprCode
opaque towerCheck : TowerCode → Bool
opaque splittingGroup : TowerCode → GroupCode
opaque solvableB : GroupCode → Bool
opaque genericQuintic : Code
opaque genericQuinticGroup : GroupCode
opaque S5Code : GroupCode
opaque RadicalSplit : Code → TowerCode → Prop
opaque UniversalRadicalFormula : Nat → Code → Prop

/-!
Target certificate theorems, to be proved after the definitions above are
implemented:

```
theorem lowCheck_sound {n} {w : LowDegreeWitness n} :
    lowCheck n w = true →
      factorCheck w.coeffs (lowRoots n w) = true

theorem towerCheck_implies_solvable {t} :
    towerCheck t = true → solvableB (splittingGroup t) = true

theorem genericQuintic_galCode :
    genericQuinticGroup = S5Code

theorem S5_not_solvableB :
    solvableB S5Code = false

theorem no_generic_radical_split :
    ∀ t, RadicalSplit genericQuintic t → False
```

The final object-theory modules should define closed formulas
`lowDegreeSentence`, `abelRuffini5Sentence`, and `abelRuffiniAllSentence`, then
prove them with ProveIt's actual sequent notation:

```
theorem pra_lowDegree_factorization (n : Fin 5) :
    ([] ⊢[PRAAx] lowDegreeSentence n)

theorem pra_abelRuffini_degree_five :
    ([] ⊢[PRAAx] abelRuffini5Sentence)

theorem pra_abelRuffini_degree_ge_five :
    ([] ⊢[PRAAx] abelRuffiniAllSentence)
```

The native endpoint is then obtained from
`LeanProofs.ConciseIPRA.pra_iff_native` or `native_iff_pra`; no field theory
belongs in that final bridge file.
-/

end LeanProofs.ConciseIPRA.Applications.AbelRuffini
