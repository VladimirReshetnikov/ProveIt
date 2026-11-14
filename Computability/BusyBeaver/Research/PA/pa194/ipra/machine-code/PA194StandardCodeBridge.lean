import TableDispatch
import DiophantineConsistency.PRAMultiplication
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194StandardCodeBridge
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open TableDispatch

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)

def CodeAgrees {n : Nat} (c : Code n) : Prop :=
  ∀ v : Fin n → Nat, F c (fun i => modelNumeral M (v i)) =
    modelNumeral M (F c v)
def CodesAgree {n m : Nat} (cs : Codes n m) : Prop :=
  ∀ i, CodeAgrees (M := M) (getCode cs i)

theorem modelStandardCode {n : Nat} (c : Code n) : CodeAgrees (M := M) c := by
  apply Code.rec (motive_1 := fun _ c => CodeAgrees (M := M) c)
    (motive_2 := fun _ _ cs => CodesAgree (M := M) cs) ?_ ?_ ?_ ?_ ?_ ?_ ?_ c
  · intro n v
    rw [PRAMultiplication.modelZero, PRAMultiplication.modelZero (M := Nat)]
    rfl
  · intro v
    have hv : v = fun _ => v 0 := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    conv_lhs => rw [hv]
    change F Code.succ (fun _ => modelNumeral M (v 0)) =
      modelNumeral M (v 0 + 1)
    rfl
  · intro n i v
    rw [modelProjection, modelProjection (M := Nat)]
  · intro m n f g hf hg v
    rw [modelComposition, modelComposition (M := Nat)]
    have he : (fun i => F (getCode g i) (fun i => modelNumeral M (v i))) =
        (fun i => modelNumeral M (F (getCode g i) v)) := by
      funext i
      exact hg i v
    rw [he]
    exact hf _
  · intro n f g hf hg v
    let xs : Fin n → Nat := fun i => v i.succ
    have h (k : Nat) : F (Code.prec f g) (Fin.cases (modelNumeral M k) (fun i => modelNumeral M (xs i))) =
        modelNumeral M (F (Code.prec f g) (Fin.cases k xs)) := by
      induction k with
      | zero =>
        rw [show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl]
        rw [modelBase]
        have hN := modelBase (M := Nat) f g xs
        change F (Code.prec f g) (Fin.cases 0 xs) = F f xs at hN
        rw [hN]
        exact hf xs
      | succ k ih =>
        rw [show modelNumeral M (k+1) = F Code.succ (fun _ => modelNumeral M k) from rfl]
        have hM := modelStep (M := M) f g (Fin.cases (modelNumeral M k) (fun i => modelNumeral M (xs i)))
        have hN := modelStep (M := Nat) f g (Fin.cases k xs)
        simp only [Fin.cases_zero, Fin.cases_succ] at hM hN
        change F (Code.prec f g) _ = _ at hM
        change F (Code.prec f g) (Fin.cases (k+1) xs) = _ at hN
        rw [hM,hN,ih]
        have := hg (Fin.cases k (Fin.cases (F (Code.prec f g) (Fin.cases k xs)) xs))
        have he : (fun i => modelNumeral M (Fin.cases k
            (Fin.cases (F (Code.prec f g) (Fin.cases k xs)) xs) i)) =
            Fin.cases (modelNumeral M k) (Fin.cases
              (modelNumeral M (F (Code.prec f g) (Fin.cases k xs)))
              (fun i => modelNumeral M (xs i))) := by
          funext i
          refine Fin.cases rfl (fun j => ?_) i
          exact Fin.cases rfl (fun j => rfl) j
        rw [he] at this
        exact this
    have hv : Fin.cases (v 0) xs = v := by
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    have hvM : Fin.cases (modelNumeral M (v 0)) (fun i => modelNumeral M (xs i)) = (fun i => modelNumeral M (v i)) := by
      funext i
      exact Fin.cases rfl (fun j => rfl) i
    simpa only [hv, hvM] using h (v 0)
  · intro n i
    exact Fin.elim0 i
  · intro n m head tail hh ht i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hh
    · exact ht j
#print axioms modelStandardCode
end models
end PA194StandardCodeBridge
