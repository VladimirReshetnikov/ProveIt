import DiophantineConsistency.PRAExhaustion

/-! Candidate PRA derivations of truncated-subtraction recursion. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRASubtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion

def subZeroSentence : Sentence language :=
  equalClosure (n := 1)
    (applyCode subCode ![.bvar 0, applyCode (.zero 0) Fin.elim0]) (.bvar 0)

def subSuccSentence : Sentence language :=
  equalClosure (n := 2)
    (applyCode subCode ![.bvar 0, applyCode Code.succ (fun _ => .bvar 1)])
    (applyCode predCode (fun _ => applyCode subCode ![.bvar 0, .bvar 1]))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSubExpand (x y : M) :
    Structure.func (L := language) subCode ![x,y] =
      Structure.func (L := language) subCore ![y,x] := by
  have h := modelComposition (M := M) subCore
    (.cons (.proj 1) (.cons (.proj 0) (.nil 2))) ![x,y]
  have harg : (fun i => Structure.func (L := language)
      (getCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2))) i) ![x,y]) = ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection (M := M) 1 _
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      exact modelProjection (M := M) 0 _
  change Structure.func (L := language) subCode ![x,y] = _ at h
  rw [harg] at h
  exact h

theorem modelSubZero (x : M) :
    Structure.func (L := language) subCode
      ![x, Structure.func (L := language) (Code.zero 0) Fin.elim0] = x := by
  rw [modelSubExpand]
  have h := modelBase (M := M) (Code.proj (0 : Fin 1))
    (Code.comp predCode (.cons (.proj (1 : Fin 3)) (.nil 3))) ![x]
  have hv : Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0) ![x] =
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0, x] := rfl
  rw [hv, modelProjection] at h
  exact h

theorem modelSubSucc (x y : M) :
    Structure.func (L := language) subCode
      ![x, Structure.func (L := language) Code.succ (fun _ => y)] =
    Structure.func (L := language) predCode
      (fun _ => Structure.func (L := language) subCode ![x,y]) := by
  rw [modelSubExpand, modelSubExpand]
  have hs := modelStep (M := M) (Code.proj (0 : Fin 1))
    (Code.comp predCode (.cons (.proj (1 : Fin 3)) (.nil 3))) ![y,x]
  have hg := modelComposition (M := M) predCode (.cons (.proj (1 : Fin 3)) (.nil 3))
    ![y, Structure.func (L := language) subCore ![y,x], x]
  have hgArg : (fun i : Fin 1 => Structure.func (L := language)
      (getCode (.cons (.proj (1 : Fin 3)) (.nil 3)) i)
      ![y, Structure.func (L := language) subCore ![y,x], x]) =
      fun _ => Structure.func (L := language) subCore ![y,x] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    exact modelProjection (M := M) 1 _
  rw [hgArg] at hg
  change Structure.func (L := language) subCore
      ![Structure.func (L := language) Code.succ (fun _ => y), x] =
    Structure.func (L := language) (Code.comp predCode (.cons (.proj (1 : Fin 3)) (.nil 3)))
      ![y, Structure.func (L := language) subCore ![y,x], x] at hs
  exact hs.trans hg

end models
end DiophantineConsistency.PRASubtraction
