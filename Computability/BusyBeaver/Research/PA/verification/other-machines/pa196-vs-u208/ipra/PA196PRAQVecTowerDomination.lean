import PA196PRAQVecTowerResultGraph
import PA196PRAQVecTowerMonotone

/-! Candidate PRA proves that the concrete arithmetic tower graph is
bounded by its candidate-PRA term. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA196PRAQVecTowerDomination
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessTransfer
  PA196PAQVecSeqTrace PA196PRAQVecTower PA196PRAQVecTowerResultGraph
  PA196PASubstitutionTowerGraph PA196PRAQVecTowerMonotone

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

theorem towerGraph_candidate (t x : M) (h : towerGraph.val.Evalb ![t,x]) :
    t = tower (x+2) (4*x+1) := by
  have hres : boundBlueprint.resultDef.val.Evalb ![t,x+2,4*x+1] := by
    simpa [towerGraph, numeral_eq_natCast] using h
  exact resultGraph_eq t (x+2) (4*x+1) hres
end models

theorem PRA_proves_tower_domination : PRA ⊢ dominates towerGraph.val towerTerm := by
  apply dominates_of_val
  intro M _ _ _ _ t e h
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  have he : (t :> e) = ![t,e 0] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard,he] at h
  have ht := towerGraph_candidate t (e 0) h
  have hv := towerTerm_val e
  rw [Semiformula.eval_lMap,PRAModelIOpenPairing.reduct_eq_standard]
  simp [Semiformula.Operator.val, Semiformula.Operator.LE.sentence_eq, Semiformula.Operator.Eq.sentence_eq, ht, hv]

#print axioms towerGraph_candidate
#print axioms PRA_proves_tower_domination
end PA196PRAQVecTowerDomination
