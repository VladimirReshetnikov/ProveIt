module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeFormulaValidity
@[expose] public section
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCode_quote {n : Nat} (param : V) (p : ArithmeticSemiformula Nat n) :
    formulaCode param (⌜p⌝ : V)=⌜Presentation.formula p⌝ := by
  induction p with
  | verum => exact formulaCode_verum param
  | falsum => exact formulaCode_falsum param
  | @rel n k r ts =>
    rw [FFL.FirstOrder.Semiformula.quote_rel,formulaCode_rel _ _ _ _ (codeIn_rel_quote (V:=V) (L:=ℒₒᵣ) r) (by simp)]
    exact atom_quote param r ts
  | @nrel n k r ts =>
    rw [FFL.FirstOrder.Semiformula.quote_nrel,formulaCode_nrel _ _ _ _ (codeIn_rel_quote (V:=V) (L:=ℒₒᵣ) r) (by simp),atom_quote]
    change neg Presentation.language (⌜Presentation.atom r ts⌝ : V)=⌜∼Presentation.atom r ts⌝
    simp [FFL.FirstOrder.Semiformula.quote_def]
  | and p q ihp ihq =>
    change formulaCode param (qqAnd ⌜p⌝ ⌜q⌝)=qqAnd ⌜Presentation.formula p⌝ ⌜Presentation.formula q⌝
    rw [formulaCode_and _ _ _ (by simp [FFL.FirstOrder.Semiformula.quote_def]) (by simp [FFL.FirstOrder.Semiformula.quote_def]),ihp,ihq]
  | or p q ihp ihq =>
    change formulaCode param (qqOr ⌜p⌝ ⌜q⌝)=qqOr ⌜Presentation.formula p⌝ ⌜Presentation.formula q⌝
    rw [formulaCode_or _ _ _ (by simp [FFL.FirstOrder.Semiformula.quote_def]) (by simp [FFL.FirstOrder.Semiformula.quote_def]),ihp,ihq]
  | all p ih =>
    change formulaCode param (qqAll ⌜p⌝)=qqAll ⌜Presentation.formula p⌝
    rw [formulaCode_all _ _ (by simp [FFL.FirstOrder.Semiformula.quote_def]),ih]
  | exs p ih =>
    change formulaCode param (qqExs ⌜p⌝)=qqExs ⌜Presentation.formula p⌝
    rw [formulaCode_exs _ _ (by simp [FFL.FirstOrder.Semiformula.quote_def]),ih]

#print axioms formulaCode_quote
end M6.PA.FoundationPAeqCode

