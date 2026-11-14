import PA194SubstInverse
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace PA194SubstMatrix
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
variable {V : Type} [Nonempty V] [Structure language V] [Structure.Eq language V]
  [V↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := V)
local instance : Zero V := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One V := ⟨F oneCode Fin.elim0⟩
local instance : Add V := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul V := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT V := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]


theorem matrix_witness {m n w b x y k : V}
    (hb : IsSemiformula L m b) (hw : IsSemitermVec L m n w) (hshift : shift L b=b)
    (hbody : subst L w b=qqOr x (qqOr y (qqAll k))) :
    ∃ a s q : V,
      b=qqOr a (qqOr s (qqAll q)) ∧
      IsSemiformula L m a ∧ IsSemiformula L m s ∧
      IsSemiformula L (m+1) q ∧ shift L q=q ∧
      subst L (qVec L w) q=k := by
  obtain ⟨a,d,rfl,ha,hd,_,hrest⟩ := PA194SubstInverse.subst_or_inverse hb hw hbody
  obtain ⟨s,e,rfl,hs,he,_,hlast⟩ := PA194SubstInverse.subst_or_inverse hd hw hrest
  obtain ⟨q,rfl,hq,hqbody⟩ := PA194SubstInverse.subst_all_inverse he hw hlast
  refine ⟨a,s,q,rfl,ha,hs,hq,?_,hqbody⟩
  simp only [shift_or ha.isUFormula hd.isUFormula,
    shift_or hs.isUFormula he.isUFormula,shift_all hq.isUFormula,
    qqOr_inj,qqAll_inj] at hshift
  exact hshift.2.2

#print axioms matrix_witness
end PA194SubstMatrix
