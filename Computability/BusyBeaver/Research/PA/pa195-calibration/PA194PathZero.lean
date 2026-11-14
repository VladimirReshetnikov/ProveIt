import PA195PathBound
import DiophantineConsistency.PRAOpenInduction

/-! A model-length path through exact PA195 decoder children, represented by
an explicitly supplied primitive-recursive function code. Existence and
correctness of a path-extraction code from the occurrence predicate are not
assumed to follow automatically and remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
namespace PA195PathBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

/-- Every decoder child is at most the parent, including code zero. -/
theorem decoded_fields_le (n : M) : first (n / 4) ≤ n ∧ second (n / 4) ≤ n := by
  exact ⟨le_trans (projections_spec (n / 4)).1 (div_le n 4),
    le_trans (projections_spec (n / 4)).2.1 (div_le n 4)⟩

/-- For any fixed code representing a sequence of decoder nodes, and any
possibly nonstandard model-length, every node reached via positive-code
Cantor children is bounded by its root. -/
theorem safe_decoder_path_bounded (f : Code 2) (seed limit : M)
    (hstep : ∀ i < limit, (pathValue f seed (i+1) = first (pathValue f seed i / 4) ∨
       pathValue f seed (i+1) = second (pathValue f seed i / 4))) :
    ∀ i ≤ limit, pathValue f seed i ≤ pathValue f seed 0 := by
  let root : M := pathValue f seed 0
  let e : ℕ → M := fun i => if i = 0 then seed else if i = 1 then root else limit
  have hi : ∀ i : M, (pathBody f).Eval ![i] e := by
    apply modelOpenInduction (M := M) (pathBody f) (pathBody_open f) e
    · apply (pathBody_eval f _ e).mpr
      right
      simp only [e, if_pos, if_false, reduceCtorEq]
      change ¬root < pathValue f seed (0 : M)
      exact not_lt_of_ge (le_refl _)
    · intro i hprev
      apply (pathBody_eval f _ e).mpr
      rw [show Structure.func (L := language) Code.succ (fun _ => i) = i+1 from (modelAddOne i).symm]
      by_cases hl : i+1 ≤ limit
      · right
        have hlt : i < limit := lt_iff_succ_le.mpr hl
        have hprev' : pathValue f seed i ≤ root := by
          have h := (pathBody_eval f i e).mp hprev
          simp only [e, if_pos, if_false, reduceCtorEq] at h
          rcases h with h | h
          · exact False.elim (not_lt_of_ge (le_trans (by simp : i ≤ i+1) hl) h)
          · exact le_of_not_gt h
        rcases hstep i hlt with hs | hs
        · have hfield := (decoded_fields_le (pathValue f seed i)).1
          simp only [e, if_pos, if_false, reduceCtorEq]
          rw [hs]
          exact not_lt_of_ge (le_trans hfield hprev')
        · have hfield := (decoded_fields_le (pathValue f seed i)).2
          simp only [e, if_pos, if_false, reduceCtorEq]
          rw [hs]
          exact not_lt_of_ge (le_trans hfield hprev')
      · left
        simp only [e, if_false, reduceCtorEq]
        exact lt_of_not_ge hl
  intro i hlim
  have h := (pathBody_eval f i e).mp (hi i)
  simp only [e, if_pos, if_false, reduceCtorEq] at h
  rcases h with h | h
  · exact False.elim (not_lt_of_ge hlim h)
  · exact le_of_not_gt h

/-- Every occurrence admitted by a model-length child path is below its root. -/
theorem safe_path_occurs_lt (f : Code 2) (seed limit v : M)
    (hstep : ∀ i < limit, (pathValue f seed (i+1) = first (pathValue f seed i / 4) ∨
       pathValue f seed (i+1) = second (pathValue f seed i / 4)))
    (hocc : PathOccurs f seed limit v) : v < pathValue f seed 0 := by
  obtain ⟨i, hlim, hp, hv | hv⟩ := hocc
  · rw [hv]
    exact lt_of_lt_of_le (PA195DecodedFields.decoded_fields_lt (pathValue f seed i) hp).1
      (safe_decoder_path_bounded f seed limit hstep i hlim)
  · rw [hv]
    exact lt_of_lt_of_le (PA195DecodedFields.decoded_fields_lt (pathValue f seed i) hp).2
      (safe_decoder_path_bounded f seed limit hstep i hlim)

/-- A code cannot occur as a field in any such model-length decoder path. -/
theorem safe_path_self_fresh (f : Code 2) (seed limit : M)
    (hstep : ∀ i < limit, (pathValue f seed (i+1) = first (pathValue f seed i / 4) ∨
       pathValue f seed (i+1) = second (pathValue f seed i / 4))) :
    ¬PathOccurs f seed limit (pathValue f seed 0) := by
  intro hocc
  exact _root_.lt_irrefl _ (safe_path_occurs_lt f seed limit _ hstep hocc)

end models
#print axioms safe_path_self_fresh
#print axioms safe_path_occurs_lt
#print axioms safe_decoder_path_bounded
end PA195PathBound
