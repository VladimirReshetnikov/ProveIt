import PA194CloseVariable
/-! Explicit protected-prefix free-label renaming, including its model-uniform
lift equations and injectivity. This does not transform derivation codes. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 3000000
namespace PA194LiftRename
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
  PRABooleanOps PRAQOrder PA194CloseVariable

/-- Inputs are protected-prefix length, source label, and variable index. -/
def renameCode : Code 3 :=
  selectAmong (bin ltBitCode (.proj 2) (.proj 0)) (.proj 2)
    (selectAmong (bin equalityCode (.proj 2) (bin addCode (.proj 1) (.proj 0))) (.proj 0)
      (.comp Code.succ (.cons (.proj 2) (.nil 3))))
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def rename (k a x : M) : M :=
  if x < k then x else if x = a+k then k else x+1

theorem modelCode (k a x : M) : F renameCode ![k,a,x] = rename k a x := by
  rw [renameCode,modelChooseLess]
  simp only [modelProjection]
  change (if x < k then x else _) = _
  unfold rename
  split
  · rfl
  · rw [modelChooseEqual,modelProjection,modelBin,modelProjection,modelProjection]
    change (if x = a+k then k else _) = _
    split
    · rfl
    · rw [modelComposition]
      have h : (fun i : Fin 1 => F (getCode (.cons (.proj 2) (.nil 3)) i) ![k,a,x]) = fun _ => x := by
        funext i
        exact Fin.cases (modelProjection 2 _) (fun j => Fin.elim0 j) i
      rw [h,←modelAddOne]
      rfl

theorem rename_zero (a x : M) : rename 0 a x = if a = x then 0 else x+1 := by
  simp [rename,eq_comm]

theorem rename_lift_zero (k a : M) : rename (k+1) a 0 = 0 := by
  simp [rename]

theorem rename_lift_succ (k a x : M) : rename (k+1) a (x+1) = rename k a x + 1 := by
  simp only [rename]
  have hlt : x+1 < k+1 ↔ x < k := by simp
  have heq : x+1 = a+(k+1) ↔ x = a+k := by
    constructor
    · intro h
      exact add_right_cancel (by simpa [add_assoc] using h : x+1 = (a+k)+1)
    · intro h
      simpa [h,add_assoc]
  simp only [hlt,heq]
  split <;> (try split) <;> simp_all

theorem rename_injective (k a : M) : Function.Injective (rename k a) := by
  intro x y h
  by_cases hx : x < k
  · by_cases hy : y < k
    · simpa [rename,hx,hy] using h
    · by_cases ey : y = a+k
      · simp [rename,hx,hy,ey] at h
        exact False.elim ((ne_of_lt hx) h)
      · have hky : k < y+1 := lt_of_le_of_lt (le_of_not_gt hy) (lt_add_one y)
        have hxy : x < y+1 := lt_trans hx hky
        simp [rename,hx,hy,ey] at h
        exact False.elim ((ne_of_lt hxy) h)
  · by_cases hy : y < k
    · by_cases ex : x = a+k
      · simp [rename,hx,hy,ex] at h
        exact False.elim ((ne_of_lt hy) h.symm)
      · have hkx : k < x+1 := lt_of_le_of_lt (le_of_not_gt hx) (lt_add_one x)
        have hyx : y < x+1 := lt_trans hy hkx
        simp [rename,hx,hy,ex] at h
        exact False.elim ((ne_of_lt hyx) h.symm)
    · by_cases ex : x = a+k
      · by_cases ey : y = a+k
        · exact ex.trans ey.symm
        · have hky : k < y+1 := lt_of_le_of_lt (le_of_not_gt hy) (lt_add_one y)
          simp [rename,hx,hy,ex,ey] at h
          exact False.elim ((ne_of_lt hky) h)
      · by_cases ey : y = a+k
        · have hkx : k < x+1 := lt_of_le_of_lt (le_of_not_gt hx) (lt_add_one x)
          simp [rename,hx,hy,ex,ey] at h
          exact False.elim ((ne_of_lt hkx) h.symm)
        · simp [rename,hx,hy,ex,ey] at h
          exact h

#print axioms rename_injective
#print axioms modelCode
#print axioms rename_zero
#print axioms rename_lift_zero
#print axioms rename_lift_succ
end models
end PA194LiftRename
