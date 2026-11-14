import PA194AllInversion
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace PA194SubstInverse
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

theorem subst_all_inverse {m n w b k : V} (hb : IsSemiformula L m b)
    (hw : IsSemitermVec L m n w) (he : subst L w b=qqAll k) :
    ∃ q, b=qqAll q ∧ IsSemiformula L (m+1) q ∧ subst L (qVec L w) q=k := by
  rcases IsSemiformula.case_iff.mp hb with
    ⟨a,r,ts,hr,ht,rfl⟩ | ⟨a,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · rw [substs_rel hr ht.isUTerm] at he
    simp [qqRel,qqAll] at he
  · rw [substs_nrel hr ht.isUTerm] at he
    simp [qqNRel,qqAll] at he
  · rw [substs_verum] at he
    simp [qqVerum,qqAll] at he
  · rw [substs_falsum] at he
    simp [qqFalsum,qqAll] at he
  · rw [Bootstrapping.substs_and hp.isUFormula hq.isUFormula] at he
    simp [qqAnd,qqAll] at he
  · rw [Bootstrapping.substs_or hp.isUFormula hq.isUFormula] at he
    simp [qqOr,qqAll] at he
  · exact ⟨p,rfl,hp,by simpa [substs_all hp.isUFormula] using he⟩
  · rw [substs_ex hp.isUFormula] at he
    simp [qqExs,qqAll] at he
theorem subst_or_inverse {m n w b s t : V} (hb : IsSemiformula L m b)
    (hw : IsSemitermVec L m n w) (he : subst L w b=qqOr s t) :
    ∃ p q, b=qqOr p q ∧ IsSemiformula L m p ∧ IsSemiformula L m q ∧
      subst L w p=s ∧ subst L w q=t := by
  rcases IsSemiformula.case_iff.mp hb with
    ⟨a,r,ts,hr,ht,rfl⟩ | ⟨a,r,ts,hr,ht,rfl⟩ | rfl | rfl |
    ⟨p,q,hp,hq,rfl⟩ | ⟨p,q,hp,hq,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,hp,rfl⟩
  · rw [substs_rel hr ht.isUTerm] at he
    simp [qqRel,qqOr] at he
  · rw [substs_nrel hr ht.isUTerm] at he
    simp [qqNRel,qqOr] at he
  · rw [substs_verum] at he
    simp [qqVerum,qqOr] at he
  · rw [substs_falsum] at he
    simp [qqFalsum,qqOr] at he
  · rw [Bootstrapping.substs_and hp.isUFormula hq.isUFormula] at he
    simp [qqAnd,qqOr] at he
  · have h : subst L w p=s ∧ subst L w q=t := by
      simpa [Bootstrapping.substs_or hp.isUFormula hq.isUFormula] using he
    exact ⟨p,q,rfl,hp,hq,h⟩
  · rw [substs_all hp.isUFormula] at he
    simp [qqAll,qqOr] at he
  · rw [substs_ex hp.isUFormula] at he
    simp [qqExs,qqOr] at he

#print axioms subst_all_inverse
#print axioms subst_or_inverse
end PA194SubstInverse

