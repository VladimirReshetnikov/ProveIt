import DiophantineConsistency.PRAStageCodedChi
set_option autoImplicit false
namespace DiophantineConsistency.PRAStagePredicateExtension
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PRAStageCodedChi

/-- Extend a predicate code by ignoring extra trailing parameters. -/
def extendPredicate {m n : ℕ} (h : m ≤ n) (pred : Code (m+3)) : Code (n+3) :=
  .comp pred (pack (m+3) (fun i => .proj ⟨i.val, by have := i.isLt; omega⟩))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelExtendPredicate {m n : ℕ} (h : m ≤ n) (pred : Code (m+3)) (e : Fin (n+3) → M) :
    Structure.func (L := language) (extendPredicate h pred) e =
      Structure.func (L := language) pred (fun i => e ⟨i.val, by have := i.isLt; omega⟩) := by
  rw [extendPredicate, modelComposition]
  congr 1
  funext i
  simp only [getCode_pack]
  exact modelProjection _ _

theorem modelExtendedChi {m n : ℕ} (h : m ≤ n) (pred : Code (m+3)) (e : ℕ → M)
    (q w y x y₀ z c v : M) :
    (chiMatrix (extendPredicate h pred)).Eval ![q,w,y,x,y₀,z,c,v] e ↔
      (chiMatrix pred).Eval ![q,w,y,x,y₀,z,c,v] e := by
  rw [modelChiMatrix, modelChiMatrix]
  dsimp only
  have hp (a b : M) :
      Structure.func (L := language) (extendPredicate h pred)
        (Fin.cases a (Fin.cases b (Fin.cases c (fun i : Fin n => e i.val)))) =
      Structure.func (L := language) pred
        (Fin.cases a (Fin.cases b (Fin.cases c (fun i : Fin m => e i.val)))) := by
    rw [modelExtendPredicate]
    congr 1
    funext i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    refine Fin.cases rfl (fun i => ?_) i
    rfl
  simp only [hp]
end models
end DiophantineConsistency.PRAStagePredicateExtension
