import DiophantineConsistency.PRAPositivePackedNormal
import DiophantineConsistency.PRABoundedFormula
import DiophantineConsistency.PRATermCompilation
/-! Compile a bounded existential normal matrix with inputs [w,x,params] to
one PR predicate whose inputs are [x,w,params]. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAPositiveCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRATermCompilation PRABoundedFormula
  PRAPositivePackedNormal PRABoundedCharacteristic

def swapTerms {n : ℕ} : Fin ((1+n)+1) → TermN (n+2) :=
  Fin.cases (#1) (Fin.append ![#0] (fun j : Fin n => .bvar j.succ.succ))

def swapCode {n : ℕ} (c : Code ((1+n)+1)) : Code (n+2) :=
  compileTerm (.func c swapTerms)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSwapCode {n : ℕ} (c : Code ((1+n)+1)) (x y : M) (v : Fin n → M) :
    Structure.func (L := language) (swapCode c) (Fin.cases x (Fin.cases y v)) =
      Structure.func (L := language) c (Fin.cases y (Fin.append ![x] v)) := by
  rw [swapCode, modelCompile, Semiterm.val_func]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · induction j using Fin.addCases with
    | left j =>
      refine Fin.cases ?_ (fun k => Fin.elim0 k) j
      simp [swapTerms, Fin.append_left]
    | right j =>
      simp [swapTerms, Fin.append_right]
end models

theorem positive_has_code (φ : ArithmeticSemiformula ℕ 1) (hφ : ParsonsBasePositive.Positive φ) :
    ∃ pred : Code ((Semiformula.lMap embedding φ).fvSup + 2),
      ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
        [M↓[language] ⊧* PRA], ∀ (x : M) (e : ℕ → M),
          (Semiformula.lMap embedding φ).Eval ![x] e ↔
            ∃ y : M, Structure.func (L := language) pred
              (Fin.cases x (Fin.cases y (fun i : Fin (Semiformula.lMap embedding φ).fvSup => e i.val))) =
              Structure.func (L := language) oneCode Fin.elim0 := by
  obtain ⟨C,hC,htruth⟩ := exists_packed_normal φ hφ
  obtain ⟨c,_,_,hc⟩ := PRA_proves_boundedBooleanCharacteristic C hC
  refine ⟨swapCode c, ?_⟩
  intro M _ _ _ _ x e
  rw [htruth M x e]
  apply exists_congr
  intro y
  rw [modelSwapCode]
  have hcm := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hc
  exact ((oneCorrectSentence_iff c C).mp hcm _).symm
end DiophantineConsistency.PRAPositiveCode
