import DiophantineConsistency.PRAHistoryPairCode
import DiophantineConsistency.PRAIsZero

/-! Explicit primitive-recursive parity and half codes for a binary tape.

Their standard evaluations are `n % 2` and `n / 2`. Their zero and successor
equations also hold in every model of the candidate PRA. These model equations
are not themselves displayed syntactic PRA derivations, and this module does
not yet construct a PA195 transition code or a machine-specific reduction. -/
set_option autoImplicit false
namespace BinaryTapeCodes
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRAIsZero

open List.Vector

def parityStep : Code 2 := .comp isZeroCode (.cons (.proj 1) (.nil 2))
def parityCode : Code 1 := .prec (.zero 0) parityStep
def parityOnIndex : Code 2 := .comp parityCode (.cons (.proj 0) (.nil 2))
def halfStep : Code 2 := bin addCode (.proj 1) parityOnIndex
def halfCode : Code 1 := .prec (.zero 0) halfStep

theorem parityEval_zero : eval parityCode (0 ::ᵥ nil) = 0 := rfl

theorem parityEval_succ (n : Nat) : eval parityCode ((n+1) ::ᵥ nil) =
    if eval parityCode (n ::ᵥ nil) = 0 then 1 else 0 := by
  change eval isZeroCode (eval parityCode (n ::ᵥ nil) ::ᵥ nil) = _
  cases eval parityCode (n ::ᵥ nil) <;> rfl

theorem halfEval_zero : eval halfCode (0 ::ᵥ nil) = 0 := rfl

theorem halfEval_succ (n : Nat) : eval halfCode ((n+1) ::ᵥ nil) =
    eval halfCode (n ::ᵥ nil) + eval parityCode (n ::ᵥ nil) := by
  change eval addCode (eval halfCode (n ::ᵥ nil) ::ᵥ eval parityCode (n ::ᵥ nil) ::ᵥ nil) = _
  exact eval_addCode _ _

theorem parityEval (n : Nat) : eval parityCode (n ::ᵥ nil) = n % 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [parityEval_succ, ih]
    split <;> omega

theorem halfEval (n : Nat) : eval halfCode (n ::ᵥ nil) = n / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [halfEval_succ, ih, parityEval]
    omega

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelParityZero : Structure.func (L := language) (M := M) parityCode
    (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (Code.zero 0) parityStep (Fin.elim0 : Fin 0 → M)
  simpa [parityCode, Matrix.fun_eq_vec_one, PRAMultiplication.modelZero] using h

theorem modelParitySucc (i : M) : Structure.func (L := language) parityCode
    (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
    Structure.func (L := language) isZeroCode
      (fun _ => Structure.func (L := language) parityCode (fun _ => i)) := by
  have h := modelStep (M := M) (Code.zero 0) parityStep (fun _ : Fin 1 => i)
  have hy : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hy] at h
  have hs : Fin.cases (Structure.func (L := language) Code.succ (fun _ => i))
      (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => Structure.func (L := language) Code.succ (fun _ => i)) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  change Structure.func (L := language) parityCode
    (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
    Structure.func (L := language) parityStep
      (Fin.cases i (Fin.cases (Structure.func (L := language) parityCode (fun _ => i)) (Fin.elim0 : Fin 0 → M))) at h
  rw [h, parityStep, modelComposition]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => Fin.elim0 k) j
  change Structure.func (L := language) (Code.proj 1)
      (Fin.cases i (Fin.cases (Structure.func (L := language) parityCode (fun _ => i)) (Fin.elim0 : Fin 0 → M))) = _
  rw [modelProjection]
  rfl

theorem modelHalfZero : Structure.func (L := language) (M := M) halfCode
    (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0) =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelBase (M := M) (Code.zero 0) halfStep (Fin.elim0 : Fin 0 → M)
  simpa [halfCode, Matrix.fun_eq_vec_one, PRAMultiplication.modelZero] using h

theorem modelHalfSucc (i : M) : Structure.func (L := language) halfCode
    (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
    Structure.func (L := language) addCode
      ![Structure.func (L := language) halfCode (fun _ => i),
        Structure.func (L := language) parityCode (fun _ => i)] := by
  have h := modelStep (M := M) (Code.zero 0) halfStep (fun _ : Fin 1 => i)
  have hy : (fun _ : Fin 0 => i) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hy] at h
  have hs : Fin.cases (Structure.func (L := language) Code.succ (fun _ => i))
      (Fin.elim0 : Fin 0 → M) = (fun _ : Fin 1 => Structure.func (L := language) Code.succ (fun _ => i)) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  change Structure.func (L := language) halfCode
    (fun _ => Structure.func (L := language) Code.succ (fun _ => i)) =
    Structure.func (L := language) halfStep
      (Fin.cases i (Fin.cases (Structure.func (L := language) halfCode (fun _ => i)) (Fin.elim0 : Fin 0 → M))) at h
  rw [h, halfStep, modelBin, modelProjection, parityOnIndex, modelComposition]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · refine Fin.cases ?_ (fun l => Fin.elim0 l) k
    change Structure.func (L := language) parityCode
      (fun j => Structure.func (L := language) (getCode (.cons (.proj 0) (.nil 2)) j)
        (Fin.cases i (Fin.cases (Structure.func (L := language) halfCode (fun _ => i)) (Fin.elim0 : Fin 0 → M)))) =
      Structure.func (L := language) parityCode (fun _ => i)
    congr 1
    funext j
    refine Fin.cases ?_ (fun l => Fin.elim0 l) j
    change Structure.func (L := language) (Code.proj 0)
      (Fin.cases i (Fin.cases (Structure.func (L := language) halfCode (fun _ => i)) (Fin.elim0 : Fin 0 → M))) = _
    rw [modelProjection]
    rfl

end models
#print axioms parityEval
#print axioms halfEval
#print axioms parityEval_succ
#print axioms halfEval_succ
#print axioms modelParityZero
#print axioms modelParitySucc
#print axioms modelHalfZero
#print axioms modelHalfSucc
end BinaryTapeCodes
