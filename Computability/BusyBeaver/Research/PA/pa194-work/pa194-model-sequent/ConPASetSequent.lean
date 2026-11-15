import ConPASequent

/-!
# Sequents indexed by finite sets, inside a model of `𝗜𝚺₁`

Foundation's internal derivations carry their sequents as hereditarily finite sets of formula
codes. This file connects such a set `s` to the list sequents of `ConPASequent`.

A translation is a `𝚺₁` function `tr e p` of a parameter `e` and a code `p`. For a set `s`,

* `setList e s` is the list of `tr e p` for the members `p` of `s` (largest member first),
  defined by primitive recursion on a bound, so it is one `𝚺₁` function of `e` and `s`;
* `sseq e s a = seq (setList e s) a`, and `Pr (sseq e s a)` is the sequent `tr e [s] ⊢ a`.

The set `s` is an element of the model, so it may have a nonstandard number of members.

* `sseq_mem`: `tr e [s] ⊢ tr e p` for `p ∈ s`;
* `sseq_cut`: if `tr e' [s'] ⊢ tr e p` for every `p ∈ s`, then
  `(tr e [s] ⊢ a) → (tr e' [s'] ⊢ a)` is a theorem; the parameters may differ, which is the
  form needed when a rule changes the variable assignment;
* `sseq_mono`: the case `s ⊆ s'` with the same parameter;
* `sseq_insert_iff`: `tr e [insert p s] ⊢ a` exactly when `tr e [s] ⊢ imp (tr e p) a`.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace ConPA.Sequent
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

section model
attribute [local instance] Classical.propDecidable
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

variable (V) in
/-- A `𝚺₁` translation `tr e p` of codes, with a parameter. -/
structure Tr where
  tr : V → V → V
  trDef : 𝚺₁.Semisentence 3
  tr_defined : 𝚺₁-Function₂ tr via trDef

attribute [instance] Tr.tr_defined

variable (C : Calc V) (T : Tr V)

instance tr_definable : 𝚺₁-Function₂ T.tr := T.tr_defined.to_definable

instance tr_definable' (Γ m) : Γ-[m + 1]-Function₂ T.tr := (tr_definable T).of_sigmaOne

/-! ## The list of translated members -/

namespace Enum

def blueprint (trDef : 𝚺₁.Semisentence 3) : PR.Blueprint 2 where
  zero := .mkSigma “y e s. y = 0”
  succ := .mkSigma “y ih n e s.
    (n ∈ s ∧ ∃ m, !trDef m e n ∧ !adjoinDef y m ih) ∨ (¬n ∈ s ∧ y = ih)”

def construction : PR.Construction V (blueprint T.trDef) where
  zero := fun _ ↦ 0
  succ := fun v n ih ↦ if n ∈ v 1 then T.tr (v 0) n ∷ ih else ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by
    by_cases h : v 2 ∈ v 4 <;> simp [blueprint, h]

end Enum

/-- The list of `tr e p` for the members `p < n` of `s`, largest member first. -/
def enumL (e s n : V) : V := (Enum.construction T).result ![e, s] n

@[simp] lemma enumL_zero (e s : V) : enumL T e s 0 = 0 := by simp [enumL, Enum.construction]

lemma enumL_succ (e s n : V) :
    enumL T e s (n + 1) = if n ∈ s then T.tr e n ∷ enumL T e s n else enumL T e s n := by
  simp [enumL, Enum.construction]

def enumLDef (trDef : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 4 :=
  (Enum.blueprint trDef).resultDef |>.rew (Rew.subst ![#0, #3, #1, #2])

instance enumL_defined : 𝚺₁-Function₃ (enumL T) via enumLDef T.trDef := .mk
  fun v ↦ by simp [(Enum.construction T).result_defined_iff, enumLDef]; rfl

instance enumL_definable : 𝚺₁-Function₃ (enumL T) := (enumL_defined T).to_definable

instance enumL_definable' (Γ m) : Γ-[m + 1]-Function₃ (enumL T) :=
  (enumL_definable T).of_sigmaOne

/-- Every entry of the list translates a member below the bound. -/
lemma enumL_sound (e s n : V) :
    ∀ i < len (enumL T e s n), ∃ p < n, p ∈ s ∧ (enumL T e s n).[i] = T.tr e p := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro i hi; simp at hi
  case succ n ih =>
    intro i hi
    rw [enumL_succ] at hi ⊢
    by_cases hn : n ∈ s
    · rw [if_pos hn] at hi ⊢
      rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
      · exact ⟨n, lt_add_one n, hn, by simp⟩
      · have hj : j < len (enumL T e s n) := by simpa using hi
        obtain ⟨p, hp, hps, he⟩ := ih j hj
        exact ⟨p, lt_trans hp (lt_add_one n), hps, by simpa using he⟩
    · rw [if_neg hn] at hi ⊢
      obtain ⟨p, hp, hps, he⟩ := ih i hi
      exact ⟨p, lt_trans hp (lt_add_one n), hps, he⟩

/-- Every member below the bound has its translation in the list. -/
lemma enumL_complete (e s n : V) :
    ∀ p < n, p ∈ s → ∃ i < len (enumL T e s n), (enumL T e s n).[i] = T.tr e p := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro p hp; simp at hp
  case succ n ih =>
    intro p hp hps
    rw [enumL_succ]
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hp) with (hlt | rfl)
    · obtain ⟨i, hi, he⟩ := ih p hlt hps
      by_cases hn : n ∈ s
      · rw [if_pos hn]
        exact ⟨i + 1, by simpa using hi, by simpa using he⟩
      · rw [if_neg hn]
        exact ⟨i, hi, he⟩
    · rw [if_pos hps]
      exact ⟨0, by simp, by simp⟩

/-- The list of translations of the members of `s`. -/
def setList (e s : V) : V := enumL T e s s

lemma setList_sound (e s : V) :
    ∀ i < len (setList T e s), ∃ p ∈ s, (setList T e s).[i] = T.tr e p := by
  intro i hi
  obtain ⟨p, _, hps, he⟩ := enumL_sound T e s s i hi
  exact ⟨p, hps, he⟩

lemma setList_complete (e s : V) {p : V} (hp : p ∈ s) :
    ∃ i < len (setList T e s), (setList T e s).[i] = T.tr e p :=
  enumL_complete T e s s p (lt_of_mem hp) hp

@[simp] lemma setList_empty (e : V) : setList T e 0 = 0 := by simp [setList]

/-! ## Set sequents -/

/-- `sseq e s a`: the implication chain of the translated members of `s`, ending in `a`. -/
def sseq (e s a : V) : V := seq C (setList T e s) a

@[simp] lemma sseq_empty (e a : V) : sseq C T e 0 a = a := by simp [sseq]

theorem sseq_weaken {a : V} (ha : C.Pr a) (e s : V) : C.Pr (sseq C T e s a) :=
  seq_weaken C ha _

theorem sseq_mp {e s a b : V} (ha : C.Pr (sseq C T e s a))
    (hab : C.Pr (sseq C T e s (C.imp a b))) : C.Pr (sseq C T e s b) :=
  seq_mp C ha hab

/-- The translation of a member is derivable. -/
theorem sseq_mem (e : V) {s p : V} (hp : p ∈ s) : C.Pr (sseq C T e s (T.tr e p)) := by
  obtain ⟨i, hi, h⟩ := setList_complete T e s hp
  rw [sseq, ← h]
  exact seq_proj C _ i hi

/-- Cut between set sequents, possibly with different parameters. -/
theorem sseq_cut (e s e' s' a : V) (h : ∀ p ∈ s, C.Pr (sseq C T e' s' (T.tr e p))) :
    C.Pr (C.imp (sseq C T e s a) (sseq C T e' s' a)) :=
  seq_cut C _ _ a (fun i hi => by
    obtain ⟨p, hp, h'⟩ := setList_sound T e s i hi
    rw [h']
    exact h p hp)

theorem sseq_cut_rule {e s e' s' a : V} (ha : C.Pr (sseq C T e s a))
    (h : ∀ p ∈ s, C.Pr (sseq C T e' s' (T.tr e p))) : C.Pr (sseq C T e' s' a) :=
  C.mp ha (sseq_cut C T e s e' s' a h)

/-- Monotonicity in the set. -/
theorem sseq_mono (e s s' a : V) (h : ∀ p ∈ s, p ∈ s') :
    C.Pr (C.imp (sseq C T e s a) (sseq C T e s' a)) :=
  sseq_cut C T e s e s' a (fun p hp => sseq_mem C T e (h p hp))

/-- `tr e [insert p s] ⊢ a` exactly when `tr e [s] ⊢ imp (tr e p) a`. -/
theorem sseq_insert_iff (e p s a : V) :
    C.Pr (sseq C T e (insert p s) a) ↔ C.Pr (sseq C T e s (C.imp (T.tr e p) a)) := by
  constructor
  · intro h
    refine (seq_adjoin_iff C (T.tr e p) (setList T e s) a).mp ?_
    refine seq_cut_rule C h ?_
    intro i hi
    obtain ⟨q, hq, hq'⟩ := setList_sound T e (insert p s) i hi
    rw [hq']
    rcases mem_bitInsert_iff.mp hq with (rfl | hqs)
    · simpa using seq_k C (setList T e s) (T.tr e q)
    · exact seq_up C (sseq_mem C T e hqs) (T.tr e p)
  · intro h
    have h1 := (seq_adjoin_iff C (T.tr e p) (setList T e s) a).mpr h
    refine seq_cut_rule C h1 ?_
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
    · simpa [sseq] using sseq_mem C T e (mem_insert p s)
    · have hj : j < len (setList T e s) := by simpa using hi
      obtain ⟨q, hq, hq'⟩ := setList_sound T e s j hj
      have hmem : q ∈ insert p s := mem_bitInsert_iff.mpr (Or.inr hq)
      have := sseq_mem C T e hmem
      simpa [sseq, hq'] using this

#print axioms enumL_sound
#print axioms enumL_complete
#print axioms sseq_mem
#print axioms sseq_cut
#print axioms sseq_mono
#print axioms sseq_insert_iff
end model
end ConPA.Sequent
