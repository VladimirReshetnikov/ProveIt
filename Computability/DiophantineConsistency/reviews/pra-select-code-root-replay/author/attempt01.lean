import DiophantineConsistency.PRACharacteristicBit

/-! Primitive-recursive selection with theory-verified defining equations. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRASelectCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABooleanOps

/-- `selectCode b yes no` returns `no` at zero and `yes` at any successor. -/
def selectCode : Code 3 := .prec (.proj (1 : Fin 2)) (.proj (2 : Fin 4))

def selectAmong {n : ℕ} (test yes no : Code n) : Code n :=
  .comp selectCode (.cons test (.cons yes (.cons no (.nil n))))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSelectZero (a b : M) :
    Structure.func (L := language) selectCode
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0,a,b] = b := by
  have h := modelBase (M := M) (.proj (1 : Fin 2)) (.proj (2 : Fin 4)) ![a,b]
  rw [modelProjection] at h
  exact h

theorem modelSelectSucc (x a b : M) :
    Structure.func (L := language) selectCode
      ![Structure.func (L := language) Code.succ (fun _ => x), a,b] = a := by
  have h := modelStep (M := M) (.proj (1 : Fin 2)) (.proj (2 : Fin 4)) ![x,a,b]
  rw [modelProjection] at h
  exact h

theorem modelSelectAmong {n : ℕ} (test yes no : Code n) (e : Fin n → M) :
    Structure.func (L := language) (selectAmong test yes no) e =
      Structure.func (L := language) selectCode
        ![Structure.func (L := language) test e, Structure.func (L := language) yes e,
          Structure.func (L := language) no e] := by
  rw [selectAmong, modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  exact Fin.cases rfl (fun l => Fin.elim0 l) k

theorem modelSelectOne (a b : M) :
    Structure.func (L := language) selectCode
      ![Structure.func (L := language) oneCode Fin.elim0,a,b] = a := by
  rw [modelOneSuccZero]
  exact modelSelectSucc _ _ _

end models
end DiophantineConsistency.PRASelectCode
