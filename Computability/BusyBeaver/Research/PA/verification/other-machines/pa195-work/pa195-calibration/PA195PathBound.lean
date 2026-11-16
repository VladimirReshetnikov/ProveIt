import PA195DecodedFields
import DiophantineConsistency.PRAOpenInduction

/-! A model-length path through exact PA195 decoder children, represented by
an explicitly supplied primitive-recursive function code. Existence and
correctness of a path-extraction code from the occurrence predicate are not
assumed to follow automatically and remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA195PathBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAOpenInduction

def pathBody (f : Code 2) : Semiformula language ℕ 1 :=
  (Semiformula.rel Language.ORing.Rel.lt ![&2,#0]) ⋎
    ∼(Semiformula.rel Language.ORing.Rel.lt ![&1,.func f ![&0,#0]])

theorem pathBody_open (f : Code 2) : (pathBody f).Open := by
  simp [pathBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen

def pathValue (f : Code 2) (s i : M) : M := Structure.func (L := language) f ![s,i]

omit [Nonempty M] [Structure.Eq language M] in
theorem pathBody_eval (f : Code 2) (i : M) (e : ℕ → M) :
    (pathBody f).Eval ![i] e ↔ e 2 < i ∨ ¬ e 1 < pathValue f (e 0) i := by
  simp [pathBody, pathValue, Semiformula.eval_rel, Semiterm.val_func]
  change (e 2 < i ∨ ¬ e 1 < pathValue f (e 0) i) ↔ _
  simp [pathValue]

/-- For any fixed code representing a sequence of decoder nodes, and any
possibly nonstandard model-length, every node reached via positive-code
Cantor children is bounded by its root. -/
theorem decoder_path_bounded (f : Code 2) (seed limit : M)
    (hstep : ∀ i < limit, 0 < pathValue f seed i ∧
      (pathValue f seed (i+1) = first (pathValue f seed i / 4) ∨
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
        obtain ⟨hp, hs | hs⟩ := hstep i hlt
        · have hfield := (PA195DecodedFields.decoded_fields_lt (pathValue f seed i) hp).1
          simp only [e, if_pos, if_false, reduceCtorEq]
          rw [hs]
          exact not_lt_of_ge (le_trans (le_of_lt hfield) hprev')
        · have hfield := (PA195DecodedFields.decoded_fields_lt (pathValue f seed i) hp).2
          simp only [e, if_pos, if_false, reduceCtorEq]
          rw [hs]
          exact not_lt_of_ge (le_trans (le_of_lt hfield) hprev')
      · left
        simp only [e, if_false, reduceCtorEq]
        exact lt_of_not_ge hl
  intro i hlim
  have h := (pathBody_eval f i e).mp (hi i)
  simp only [e, if_pos, if_false, reduceCtorEq] at h
  rcases h with h | h
  · exact False.elim (not_lt_of_ge hlim h)
  · exact le_of_not_gt h

/-- Over-approximation of names encountered in the decoded tree: a field of
any positive node along the supplied path counts as an occurrence. This is
not yet the actual numeric decoder's occurrence predicate. -/
def PathOccurs (f : Code 2) (seed limit v : M) : Prop :=
  ∃ i, i ≤ limit ∧ 0 < pathValue f seed i ∧
    (v = first (pathValue f seed i / 4) ∨ v = second (pathValue f seed i / 4))

/-- Every occurrence admitted by a model-length child path is below its root. -/
theorem path_occurs_lt (f : Code 2) (seed limit v : M)
    (hstep : ∀ i < limit, 0 < pathValue f seed i ∧
      (pathValue f seed (i+1) = first (pathValue f seed i / 4) ∨
       pathValue f seed (i+1) = second (pathValue f seed i / 4)))
    (hocc : PathOccurs f seed limit v) : v < pathValue f seed 0 := by
  obtain ⟨i, hlim, hp, hv | hv⟩ := hocc
  · rw [hv]
    exact lt_of_lt_of_le (PA195DecodedFields.decoded_fields_lt (pathValue f seed i) hp).1
      (decoder_path_bounded f seed limit hstep i hlim)
  · rw [hv]
    exact lt_of_lt_of_le (PA195DecodedFields.decoded_fields_lt (pathValue f seed i) hp).2
      (decoder_path_bounded f seed limit hstep i hlim)

/-- A code cannot occur as a field in any such model-length decoder path. -/
theorem path_self_fresh (f : Code 2) (seed limit : M)
    (hstep : ∀ i < limit, 0 < pathValue f seed i ∧
      (pathValue f seed (i+1) = first (pathValue f seed i / 4) ∨
       pathValue f seed (i+1) = second (pathValue f seed i / 4))) :
    ¬PathOccurs f seed limit (pathValue f seed 0) := by
  intro hocc
  exact _root_.lt_irrefl _ (path_occurs_lt f seed limit _ hstep hocc)

end models
#print axioms path_self_fresh
#print axioms path_occurs_lt
#print axioms decoder_path_bounded
end PA195PathBound
