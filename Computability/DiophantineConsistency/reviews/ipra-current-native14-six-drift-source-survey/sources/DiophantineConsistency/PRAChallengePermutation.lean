import DiophantineConsistency.PRATermCompilation
import DiophantineConsistency.PRAAddOne
set_option autoImplicit false
namespace DiophantineConsistency.PRAChallengePermutation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation

/-- Map an index in `[parameters, x, y, w]` to the same value's index
in `[x, y, w, parameters]`. -/
def reorderedIndex (n : ℕ) (i : Fin (n+3)) : Fin (n+3) :=
  if h : i.val < n then ⟨i.val+3, by omega⟩ else ⟨i.val-n, by omega⟩

/-- Reorder a code's arguments without coding tuples into natural numbers. -/
def challengeFirst {n : ℕ} (q : Code (n+3)) : Code (n+3) :=
  .comp q (pack (n+3) (fun i => .proj (reorderedIndex n i)))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelChallengeFirst {n : ℕ} (q : Code (n+3)) (e : Fin (n+3) → M) :
    Structure.func (L := language) (challengeFirst q) e =
      Structure.func (L := language) q (fun i => e (reorderedIndex n i)) := by
  rw [challengeFirst, modelComposition]
  congr 1
  funext i
  simp only [getCode_pack]
  exact modelProjection _ _

theorem reorderedIndex_parameter (n : ℕ) (i : Fin n) :
    reorderedIndex n (Fin.castAdd 3 i) = (Fin.natAdd 3 i).cast (by omega) := by
  apply Fin.ext
  simp [reorderedIndex, i.isLt]

theorem reorderedIndex_challenge (n : ℕ) (j : Fin 3) :
    reorderedIndex n (Fin.natAdd n j) = (j.castAdd n).cast (Nat.add_comm 3 n) := by
  apply Fin.ext
  simp [reorderedIndex]

/-- Explicit parameter and challenge vectors have the intended ordering. -/
theorem modelChallengeFirst_vector {n : ℕ} (q : Code (n+3))
    (x y w : M) (params : Fin n → M) :
    Structure.func (L := language) (challengeFirst q)
      (fun i => if h : i.val < 3 then (![x,y,w] : Fin 3 → M) ⟨i.val,h⟩
        else params ⟨i.val-3, by omega⟩) =
    Structure.func (L := language) q
      (fun i => if h : i.val < n then params ⟨i.val,h⟩
        else (![x,y,w] : Fin 3 → M) ⟨i.val-n, by omega⟩) := by
  rw [modelChallengeFirst]
  congr 1
  funext i
  by_cases hi : i.val < n
  · simp [reorderedIndex, hi]
  · have hn : n ≤ i.val := by omega
    have h3 : i.val-n < 3 := by have := i.isLt; omega
    simp [reorderedIndex, hi, h3]
end models
end DiophantineConsistency.PRAChallengePermutation
