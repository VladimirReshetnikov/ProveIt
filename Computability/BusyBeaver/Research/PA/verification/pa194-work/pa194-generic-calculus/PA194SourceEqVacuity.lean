import PA194SourceDiagonalPreservation

/-!
# Equality vacuity under the translation into arithmetic

`translated x` is the arithmetic formula that the numerical code `x` denotes, and
`PA194SourceLineSoundness.good x` says that arithmetic proves it, inside a candidate-PRA
model whose arithmetic reduct satisfies `𝗜𝚺₁`.

The gate of the PA196 calculus contains the equality vacuity
`Δ_c(a, b) = E(a, b) → U(c, E(a, b))` under the guard `c ≠ a`, `c ≠ b`. This file proves

```lean
lemma eq_vacuity (a b c : M) (ha : c ≠ a) (hb : c ≠ b) :
    Provable 𝗣𝗔 (translated (impSource (eqSource a b) (allSource c (eqSource a b))))
```

for all elements `a b c` of the model. The proof is the one of
`PA194SourceDiagonalPreservation.diagonal`: the translation of `E(a, b)` is the equation of
the two free variables with the indices `a` and `b`, renaming the variable `c` leaves it
unchanged when `c` is neither of them, so closing `c` does nothing and the generalization
is a generalization over a variable that does not occur.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace PA194SourceEqVacuity
open PA194SourceFreshClose PA194SourceHead5Preservation PA194SourceHead1Syntax
open PA194SourceDiagonalPreservation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194ReplacementOpening
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194SourceHead5Preservation
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Renaming a label that is not one of the two labels of an equality atom leaves its
translation unchanged. -/
lemma eq_fixed (a b c : M) (ha : c ≠ a) (hb : c ≠ b) :
    renameFormula replaceGraph replaceMap replaceGraph_correct (pair c (c+1))
      (translated (eqSource a b)) = translated (eqSource a b) := by
  rw [equality_code, rename_eq]
  simp [ha, hb]

/-- Arithmetic proves the translation of `E(a, b) → U(c, E(a, b))` when `c ≠ a` and
`c ≠ b`. -/
lemma eq_vacuity (a b c : M) (ha : c ≠ a) (hb : c ≠ b) :
    Provable (𝗣𝗔 : ArithmeticTheory)
      (translated (impSource (eqSource a b) (allSource c (eqSource a b)))) := by
  have hnz := imp_nonzero_right (eqSource a b) (allSource c (eqSource a b))
    (allSource_nonzero c (eqSource a b))
  rw [imp_code (eqSource a b) (allSource c (eqSource a b)) hnz, universal_code c (eqSource a b)]
  let P : Bootstrapping.Formula M ℒₒᵣ :=
    ⟨translated (eqSource a b), (fixed_all_wf (eqSource a b)).1⟩
  let Q : Bootstrapping.Semiformula M ℒₒᵣ 1 := ⟨PA194InternalFormulaClose.close c 0 P.val, by
    simpa using PA194InternalFormulaClose.close_wellformed c 0 P.val P.isSemiformula⟩
  change Provable (𝗣𝗔 : ArithmeticTheory) ((P 🡒 ∀⁰ Q).val)
  have hclose : Q.val = P.val :=
    formula_close_of_fixed c (c+1) 0 P.val (ne_of_lt (lt_add_one c)) P.isSemiformula
      (eq_fixed a b c ha hb)
  have hfree : Q.free = P.shift := unbound_free P Q hclose
  apply (tprovable_iff_provable).mp
  apply Nonempty.intro
  apply TProof.generalizeAux
  rw [hfree]
  exact C_id

#print axioms eq_fixed
#print axioms eq_vacuity
end models
end PA194SourceEqVacuity
