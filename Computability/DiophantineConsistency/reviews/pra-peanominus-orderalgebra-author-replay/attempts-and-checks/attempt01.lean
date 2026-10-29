import DiophantineConsistency.PRAPeanoMinusOrderBasic

/-! Remaining order axioms for Foundation PA-minus in candidate PRA. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPeanoMinusOrderAlgebra
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddition PRAAdditionZeroLeft
  PRAAdditionSuccLeft PRAAdditionCommutativity PRAMultiplication PRAQOrder
  PRAPeanoMinusBasic PRAPeanoMinusAddAssoc PRAPeanoMinusDistributivity PRAPeanoMinusMulComm
  PRAPeanoMinusOrderBasic

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
private def succ (x : M) : M := Structure.func (L := language) Code.succ (fun _ => x)
private theorem addAssoc (x y z : M) : (x+y)+z = x+(y+z) := modelAddAssoc x y z
private theorem addComm (x y : M) : x+y = y+x := PRAAdditionCommutativity.modelAddComm x y
private theorem zeroAdd (x : M) : (0 : M)+x = x := modelZeroLeft x
private theorem addSucc (x y : M) : x+succ y = succ (x+y) := modelAddSucc x y
private theorem succAdd (x y : M) : succ x+y = succ (x+y) := modelSuccLeft x y
private theorem mulComm (x y : M) : x*y = y*x := modelMulComm x y
private theorem mulSucc (x y : M) : x*succ y = x*y+x := modelMulSucc x y
private theorem distri (x y z : M) : x*(y+z) = x*y+x*z := modelDistri x y z

theorem modelLtTrans (x y z : M) (hxy : x < y) (hyz : y < z) : x < z := by
  obtain ⟨a,ha⟩ := (ltWitness x y).mp hxy
  obtain ⟨b,hb⟩ := (ltWitness y z).mp hyz
  change x + succ a = y at ha
  change y + succ b = z at hb
  apply (ltWitness x z).mpr
  refine ⟨a + succ b, ?_⟩
  change x + succ (a + succ b) = z
  rw [←succAdd, ←addAssoc, ha, hb]

theorem modelAddLtAdd (x y z : M) (hxy : x < y) : x+z < y+z := by
  obtain ⟨a,ha⟩ := (ltWitness x y).mp hxy
  change x + succ a = y at ha
  apply (ltWitness (x+z) (y+z)).mpr
  refine ⟨a, ?_⟩
  change (x+z)+succ a = y+z
  rw [addAssoc, addComm z (succ a), ←addAssoc, ha]

theorem modelMulLtMul (x y z : M) (hxy : x < y) (hz : (0 : M) < z) : x*z < y*z := by
  obtain ⟨a,ha⟩ := (ltWitness x y).mp hxy
  obtain ⟨b,hb⟩ := (ltWitness 0 z).mp hz
  change x + succ a = y at ha
  change (0 : M) + succ b = z at hb
  rw [zeroAdd] at hb
  apply (ltWitness (x*z) (y*z)).mpr
  refine ⟨(succ a)*b + a, ?_⟩
  change x*z + succ (succ a*b+a) = y*z
  calc
    x*z + succ (succ a*b+a) = x*z + succ a*z := by
      rw [←hb, mulSucc, addSucc]
    _ = (x+succ a)*z := by
      rw [mulComm (x+succ a) z, distri, mulComm z x, mulComm z (succ a)]
    _ = y*z := by rw [ha]

theorem modelMappedLtTrans : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.ltTrans := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.ltTrans]
  exact modelLtTrans

theorem modelMappedAddLtAdd : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.addLtAdd := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.addLtAdd]
  exact modelAddLtAdd

theorem modelMappedMulLtMul : M↓[language] ⊧ Semiformula.lMap embedding PeanoMinus.Axiom.mulLtMul := by
  apply mapped_of_standard
  simp [PeanoMinus.Axiom.mulLtMul]
  exact modelMulLtMul

end models

theorem PRA_proves_ltTrans : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.ltTrans := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedLtTrans

theorem PRA_proves_addLtAdd : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.addLtAdd := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedAddLtAdd

theorem PRA_proves_mulLtMul : PRA ⊢ Semiformula.lMap embedding PeanoMinus.Axiom.mulLtMul := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelMappedMulLtMul

end DiophantineConsistency.PRAPeanoMinusOrderAlgebra
