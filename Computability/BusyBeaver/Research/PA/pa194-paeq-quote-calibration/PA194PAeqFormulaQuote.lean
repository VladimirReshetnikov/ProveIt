import PA194PAeqAtomQuote
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCode_quote {n : Nat} (param : V) (p : ArithmeticSemiformula Nat n) :
    formulaCode param (⌜p⌝ : V)=⌜PA194PAeq.formula p⌝ := by
  induction p with
  | verum => exact formulaCode_verum param
  | falsum => exact formulaCode_falsum param
  | @rel n k r ts =>
    rw [LO.FirstOrder.Semiformula.quote_rel,formulaCode_rel _ _ _ _ (codeIn_rel_quote (V:=V) (L:=ℒₒᵣ) r) (by simp)]
    exact atom_quote param r ts
  | @nrel n k r ts =>
    rw [LO.FirstOrder.Semiformula.quote_nrel,formulaCode_nrel _ _ _ _ (codeIn_rel_quote (V:=V) (L:=ℒₒᵣ) r) (by simp),atom_quote]
    change neg PA194PAeq.language (⌜PA194PAeq.atom r ts⌝ : V)=⌜∼PA194PAeq.atom r ts⌝
    simp [LO.FirstOrder.Semiformula.quote_def]
  | and p q ihp ihq =>
    change formulaCode param (qqAnd ⌜p⌝ ⌜q⌝)=qqAnd ⌜PA194PAeq.formula p⌝ ⌜PA194PAeq.formula q⌝
    rw [formulaCode_and _ _ _ (by simp [LO.FirstOrder.Semiformula.quote_def]) (by simp [LO.FirstOrder.Semiformula.quote_def]),ihp,ihq]
  | or p q ihp ihq =>
    change formulaCode param (qqOr ⌜p⌝ ⌜q⌝)=qqOr ⌜PA194PAeq.formula p⌝ ⌜PA194PAeq.formula q⌝
    rw [formulaCode_or _ _ _ (by simp [LO.FirstOrder.Semiformula.quote_def]) (by simp [LO.FirstOrder.Semiformula.quote_def]),ihp,ihq]
  | all p ih =>
    change formulaCode param (qqAll ⌜p⌝)=qqAll ⌜PA194PAeq.formula p⌝
    rw [formulaCode_all _ _ (by simp [LO.FirstOrder.Semiformula.quote_def]),ih]
  | exs p ih =>
    change formulaCode param (qqExs ⌜p⌝)=qqExs ⌜PA194PAeq.formula p⌝
    rw [formulaCode_exs _ _ (by simp [LO.FirstOrder.Semiformula.quote_def]),ih]

#print axioms formulaCode_quote
end PA194PAeqTermBlueprint

