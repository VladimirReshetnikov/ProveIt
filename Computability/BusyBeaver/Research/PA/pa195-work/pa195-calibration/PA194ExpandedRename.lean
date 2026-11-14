import PA194GenericRenameAxiom
/-! Parameterized injective free-label maps closed under eigenvariable lifting
and source-shift precomposition; includes their internal PA-axiom invariance. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
namespace PA194ExpandedRename
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode

open PA194GenericRenameBase
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
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def expandedGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “y x p. ∃ k, !pi₁Def k p ∧ ∃ rest, !pi₂Def rest p ∧
    ∃ a, !pi₁Def a rest ∧ ∃ rest', !pi₂Def rest' rest ∧
    ∃ d, !pi₁Def d rest' ∧ ∃ e, !pi₂Def e rest' ∧
      (x < k → y = x) ∧
      (¬ x < k → ((¬ e = 0 ∧ x = a + k → y = k) ∧
        (¬ (¬ e = 0 ∧ x = a + k) → y = x + d)))”

noncomputable def ren (k a s e x : M) : M :=
  if x < k then x else if e ≠ 0 ∧ x = a+k then k else x+s

lemma lift_zero (k a s e : M) : ren (k+1) a s e 0 = 0 := by
  simp [ren]

lemma lift_succ (k a s e x : M) : ren (k+1) a s e (x+1) = ren k a s e x + 1 := by
  simp only [ren]
  have hlt : x+1 < k+1 ↔ x < k := by simp
  have heq : x+1 = a+(k+1) ↔ x = a+k := by
    constructor
    · intro h
      exact add_right_cancel (by simpa [add_assoc] using h : x+1 = (a+k)+1)
    · intro h
      simpa [h,add_assoc]
  simp only [hlt,heq]
  split <;> (try split) <;> simp_all [add_assoc,add_comm,add_left_comm]

lemma shift_positive_prefix (k a s e x : M) :
    ren (k+1) a s e (x+1) = ren k a s e x+1 := lift_succ k a s e x

lemma shift_zero_exception_succ (a s e x : M) :
    ren 0 (a+1) s e (x+1) = ren 0 a (s+1) e x := by
  simp only [ren, not_lt_zero, if_false, zero_add, add_zero]
  have heq : x+1 = a+1 ↔ x = a := by
    constructor
    · exact add_right_cancel
    · intro h; simpa [h]
  simp only [heq]
  split <;> simp_all [add_assoc,add_comm,add_left_comm]

lemma shift_zero_exception_zero (s e x : M) :
    ren 0 0 s e (x+1) = ren 0 0 (s+1) 0 x := by
  simp [ren, add_assoc, add_comm, add_left_comm]

lemma shift_zero_disabled (a s x : M) :
    ren 0 a s 0 (x+1) = ren 0 0 (s+1) 0 x := by
  simp [ren, add_assoc, add_comm, add_left_comm]

lemma original_map (a x : M) : ren 0 a 1 1 x = PA194LiftRename.rename 0 a x := by
  simp [ren, PA194LiftRename.rename]

lemma ren_injective (k a d e : M) (hd : 0 < d) : Function.Injective (ren k a d e) := by
  intro x y h
  by_cases hx : x < k
  · by_cases hy : y < k
    · simpa [ren,hx,hy] using h
    · by_cases ey : e ≠ 0 ∧ y = a+k
      · rw [ren,ren,if_pos hx,if_neg hy,if_pos ey] at h
        exact False.elim ((ne_of_lt hx) h)
      · have hky : k < y+d := lt_of_le_of_lt (le_of_not_gt hy) (lt_add_of_pos_right y hd)
        have hxy : x < y+d := lt_trans hx hky
        rw [ren,ren,if_pos hx,if_neg hy,if_neg ey] at h
        exact False.elim ((ne_of_lt hxy) h)
  · by_cases hy : y < k
    · by_cases ex : e ≠ 0 ∧ x = a+k
      · rw [ren,ren,if_neg hx,if_pos ex,if_pos hy] at h
        exact False.elim ((ne_of_lt hy) h.symm)
      · have hkx : k < x+d := lt_of_le_of_lt (le_of_not_gt hx) (lt_add_of_pos_right x hd)
        have hyx : y < x+d := lt_trans hy hkx
        rw [ren,ren,if_neg hx,if_neg ex,if_pos hy] at h
        exact False.elim ((ne_of_lt hyx) h.symm)
    · by_cases ex : e ≠ 0 ∧ x = a+k
      · by_cases ey : e ≠ 0 ∧ y = a+k
        · exact ex.2.trans ey.2.symm
        · have hky : k < y+d := lt_of_le_of_lt (le_of_not_gt hy) (lt_add_of_pos_right y hd)
          rw [ren,ren,if_neg hx,if_pos ex,if_neg hy,if_neg ey] at h
          exact False.elim ((ne_of_lt hky) h)
      · by_cases ey : e ≠ 0 ∧ y = a+k
        · have hkx : k < x+d := lt_of_le_of_lt (le_of_not_gt hx) (lt_add_of_pos_right x hd)
          rw [ren,ren,if_neg hx,if_neg ex,if_neg hy,if_pos ey] at h
          exact False.elim ((ne_of_lt hkx) h.symm)
        · rw [ren,ren,if_neg hx,if_neg ex,if_neg hy,if_neg ey] at h
          exact add_right_cancel h

#print axioms ren_injective
noncomputable def packedRen (p x : M) : M :=
  ren (π₁ p) (π₁ (π₂ p)) (π₁ (π₂ (π₂ p))) (π₂ (π₂ (π₂ p))) x

lemma expandedGraph_correct (v : Fin 3 → M) :
    (M ⊧/v expandedGraph.val) ↔ v 0 = packedRen (v 2) (v 1) := by
  simp [expandedGraph, packedRen, ren]
  split_ifs <;> simp_all <;> tauto

lemma expanded_pa_axiom_fixed (k a d e p : M) (hp : p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class) :
    PA194GenericRenameAxiom.renameFormula expandedGraph packedRen expandedGraph_correct
      (pair k (pair a (pair d e))) p = p :=
  PA194GenericRenameAxiom.pa_axiom_fixed expandedGraph packedRen expandedGraph_correct _ p hp

#print axioms expanded_pa_axiom_fixed
#print axioms lift_succ
#print axioms shift_zero_exception_succ
#print axioms shift_zero_exception_zero
#print axioms shift_zero_disabled
end models
end PA194ExpandedRename
