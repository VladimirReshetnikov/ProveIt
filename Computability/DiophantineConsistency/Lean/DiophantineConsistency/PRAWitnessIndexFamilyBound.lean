import DiophantineConsistency.PRAWitnessFold
import DiophantineConsistency.StrictSigmaOneInduction
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessIndexFamilyBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAWitnessFold StrictSigmaOneInduction
section
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- Lift any local bound `p + 1` to a common fold bound for all `p < k`. -/
theorem modelIndexFamilyBound (φ : ArithmeticSemisentence 2)
    (hlocal : ∀ x p : M, (Semiformula.lMap embedding φ).Eval ![x,p] Empty.elim →
      (Semiformula.lMap embedding (bnd φ)).Eval ![x,p,p+1] Empty.elim)
    (k p x : M) (hp : Structure.rel (L := language) Language.ORing.Rel.lt ![p,k])
    (hx : (Semiformula.lMap embedding φ).Eval ![x,p] Empty.elim) :
    (Semiformula.lMap embedding (bnd φ)).Eval
      ![x,p,Structure.func (L := language) (foldCode Code.succ) ![k]] Empty.elim := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hlocal := hlocal x p hx
  have hfold := modelIndexSuccBound p k hp
  have hbound : p+1 ≤ Structure.func (L := language) (foldCode Code.succ) ![k] := by
    apply le_of_not_gt
    change ¬ Structure.rel (L := language) Language.ORing.Rel.lt
      ![Structure.func (L := language) (foldCode Code.succ) ![k],
        Structure.func (L := language) addCode ![p,Structure.func (L := language) oneCode Fin.elim0]]
    rw [modelAddOne]
    exact hfold
  simp only [Semiformula.eval_lMap] at hlocal ⊢
  rw [reduct_eq_standard] at hlocal ⊢
  have h := eval_bnd_mono φ ![x,p] Empty.elim hbound (by simpa [Fin.snoc] using hlocal)
  simpa [Fin.snoc] using h
end
end DiophantineConsistency.PRAWitnessIndexFamilyBound
