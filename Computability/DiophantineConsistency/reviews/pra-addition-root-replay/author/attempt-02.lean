import DiophantineConsistency.PRAAddOne

/-! The addition zero and successor equations in the candidate PRA theory. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAAddition
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelAddExpand (x y : M) :
    Structure.func (L := language) addCode ![x,y] =
      Structure.func (L := language) addCore ![y,x] := by
  have h := modelComposition (M := M) addCore
    (.cons (.proj 1) (.cons (.proj 0) (.nil 2))) ![x,y]
  have harg : (fun i => Structure.func (L := language)
      (getCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2))) i) ![x,y]) = ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection (M := M) 1 _
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      exact modelProjection (M := M) 0 _
  change Structure.func (L := language) addCode ![x,y] = _ at h
  rw [harg] at h
  exact h

theorem modelAddZero (x : M) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) (Code.zero 0) Fin.elim0] = x := by
  rw [modelAddExpand]
  have h := modelBase (M := M) (Code.proj (0 : Fin 1))
    (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))) ![x]
  rw [modelProjection] at h
  have hv : Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) ![x] =
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, x] := rfl
  rw [hv] at h
  exact h

theorem modelAddSucc (x y : M) :
    Structure.func (L := language) addCode
      ![x, Structure.func (L := language) Code.succ (fun _ => y)] =
    Structure.func (L := language) Code.succ
      (fun _ => Structure.func (L := language) addCode ![x,y]) := by
  rw [modelAddExpand, modelAddExpand]
  have hs := modelStep (M := M) (Code.proj (0 : Fin 1))
    (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))) ![y,x]
  have hg := modelComposition (M := M) Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3))
    ![y, Structure.func (L := language) addCore ![y,x], x]
  have hgArg : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.proj (1 : Fin 3)) (.nil 3)) i)
      ![y, Structure.func (L := language) addCore ![y,x], x]) =
      fun _ => Structure.func (L := language) addCore ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact modelProjection (M := M) 1 _
  rw [hgArg] at hg
  change Structure.func (L := language) addCore
      ![Structure.func (L := language) Code.succ (fun _ => y), x] =
    Structure.func (L := language) (Code.comp Code.succ (.cons (.proj (1 : Fin 3)) (.nil 3)))
      ![y, Structure.func (L := language) addCore ![y,x], x] at hs
  exact hs.trans hg

end models
end DiophantineConsistency.PRAAddition
