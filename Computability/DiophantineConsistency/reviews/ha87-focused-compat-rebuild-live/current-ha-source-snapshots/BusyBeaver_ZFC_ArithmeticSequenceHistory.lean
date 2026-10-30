import Foundation.FirstOrder.Arithmetic.HFS.PRF

set_option autoImplicit false
set_option Elab.async false

/-! A represented append-history for a supplied represented step. The graph
formula is fixed independently of the ambient arithmetic model. Foundation's
existing primitive-recursion construction supplies the iteration itself. -/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSequenceHistory

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic

def zeroDef : 𝚺₁.Semisentence 1 := .mkSigma “s. !mkSeq₁Def s 0”

def succDef (stepDef : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 3 := .mkSigma
  “s previous index. ∃ value, !stepDef value previous (index + 1) ∧
    !seqConsDef s previous value”

def blueprint (stepDef : 𝚺₁.Semisentence 3) : PR.Blueprint 0 where
  zero := zeroDef
  succ := succDef stepDef

/-- These graph formulas depend on syntax alone, not on a chosen model or
its semantic presentation of the step function. -/
def historyDef (stepDef : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 2 :=
  (blueprint stepDef).resultDef

def historyDeltaDef (stepDef : 𝚺₁.Semisentence 3) : 𝚫₁.Semisentence 2 :=
  (blueprint stepDef).resultDeltaDef

def valueDef (stepDef : 𝚺₁.Semisentence 3) : 𝚺₁.Semisentence 2 := .mkSigma
  “r code. ∃ s, !(historyDef stepDef) s code ∧ !znthDef r s code”

def valueDeltaDef (stepDef : 𝚺₁.Semisentence 3) : 𝚫₁.Semisentence 2 :=
  (valueDef stepDef).graphDelta

variable (stepDef : 𝚺₁.Semisentence 3)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (step : V → V → V) [hstep : 𝚺₁-Function₂[V] step via stepDef]

noncomputable def construction : PR.Construction V (blueprint stepDef) where
  zero _ := seqCons ∅ 0
  succ _ index previous := seqCons previous (step previous (index + 1))
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

noncomputable def history (code : V) : V :=
  (construction stepDef step).result ![] code

instance history_defined : 𝚺₁-Function₁[V] (history stepDef step) via historyDef stepDef :=
  .mk fun e => by
    have he : (fun i : Fin 0 => e i.succ.succ) = ![] := Subsingleton.elim _ _
    have h := (construction stepDef step).result_defined.df e
    change (blueprint stepDef).resultDef.val.Evalb e ↔
      e 0 = (construction stepDef step).result (fun i : Fin 0 => e i.succ.succ) (e 1) at h
    rw [he] at h
    exact h

instance history_defined_delta :
    𝚫₁-Function₁[V] (history stepDef step) via historyDeltaDef stepDef :=
  (history_defined stepDef step).graph_delta

instance history_definable : 𝚺₁-Function₁[V] (history stepDef step) :=
  (history_defined stepDef step).to_definable

@[simp] theorem history_zero : history stepDef step (0 : V) = seqCons ∅ 0 := by
  simp [history, construction]

@[simp] theorem history_succ (code : V) : history stepDef step (code + 1) =
    seqCons (history stepDef step code) (step (history stepDef step code) (code + 1)) := by
  simp [history, PR.Construction.result_succ, construction]

/-- Definable induction covers all internal indices, not merely Nat indices. -/
theorem history_seq (code : V) : Seq (history stepDef step code) := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ code ih =>
    rw [history_succ]
    exact ih.seqCons _

theorem history_length (code : V) : lh (history stepDef step code) = code + 1 := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ code ih =>
    rw [history_succ, (history_seq stepDef step code).lh_seqCons, ih]

theorem index_lt_length (code : V) : code < lh (history stepDef step code) := by
  rw [history_length]
  simp

noncomputable def value (code : V) : V := znth (history stepDef step code) code

instance value_defined : 𝚺₁-Function₁[V] (value stepDef step) via valueDef stepDef :=
  .mk fun e => by simp [valueDef, value]

instance value_defined_delta :
    𝚫₁-Function₁[V] (value stepDef step) via valueDeltaDef stepDef :=
  (value_defined stepDef step).graph_delta

instance value_definable : 𝚺₁-Function₁[V] (value stepDef step) :=
  (value_defined stepDef step).to_definable

include step hstep in
theorem history_total (code : V) :
    ∃! s, (historyDef stepDef).val.Evalb ![s, code] := by
  have hgraph (s : V) : (historyDef stepDef).val.Evalb ![s, code] ↔
      s = history stepDef step code := (history_defined stepDef step).df ![s, code]
  exact ⟨history stepDef step code, (hgraph _).mpr rfl, fun s hs => (hgraph s).mp hs⟩

include step hstep in
theorem value_total (code : V) :
    ∃! r, (valueDef stepDef).val.Evalb ![r, code] := by
  have hgraph (r : V) : (valueDef stepDef).val.Evalb ![r, code] ↔
      r = value stepDef step code := (value_defined stepDef step).df ![r, code]
  exact ⟨value stepDef step code, (hgraph _).mpr rfl, fun r hr => (hgraph r).mp hr⟩

theorem value_mem (code : V) : ⟪code, value stepDef step code⟫ ∈ history stepDef step code :=
  (history_seq stepDef step code).znth (index_lt_length stepDef step code)

theorem value_lt_history (code : V) : value stepDef step code < history stepDef step code :=
  lt_of_mem_rng (value_mem stepDef step code)

@[simp] theorem value_zero : value stepDef step (0 : V) = 0 := by
  rw [value, history_zero]
  simpa only [lh_empty] using
    ((seq_empty (V := V)).seqCons (0 : V)).znth_eq_of_mem (Seq.mem_seqCons (∅ : V) 0)

/-- The new entry is exactly the supplied step applied to the preceding
complete history and the new index. No row-specific premise occurs here. -/
theorem value_succ (code : V) : value stepDef step (code + 1) =
    step (history stepDef step code) (code + 1) := by
  rw [value, history_succ]
  simpa only [history_length] using
    ((history_seq stepDef step code).seqCons
      (step (history stepDef step code) (code + 1))).znth_eq_of_mem
        (Seq.mem_seqCons (history stepDef step code)
          (step (history stepDef step code) (code + 1)))

theorem history_lookup_le (code : V) :
    ∀ i ≤ code, znth (history stepDef step code) i = value stepDef step i := by
  induction code using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro i hi
    have hi0 : i = 0 := le_antisymm hi (by simp)
    subst i
    rfl
  case succ code ih =>
    intro i hi
    by_cases he : i = code + 1
    · subst i; rfl
    have hilt : i < code + 1 := lt_of_le_of_ne hi he
    have hile : i ≤ code := lt_succ_iff_le.mp hilt
    rw [history_succ]
    have hs := history_seq stepDef step code
    have hm := Seq.subset_seqCons (history stepDef step code)
      (step (history stepDef step code) (code + 1))
      (hs.znth (by simpa only [history_length] using hilt))
    rw [(hs.seqCons _).znth_eq_of_mem hm]
    exact ih i hile

/-- Complete lookup semantics, including every index outside the history. -/
theorem history_lookup (code i : V) : znth (history stepDef step code) i =
    if i ≤ code then value stepDef step i else 0 := by
  classical
  by_cases hi : i ≤ code
  · simp only [hi, if_pos]
    exact history_lookup_le stepDef step code i hi
  · simp only [hi, if_false]
    apply znth_prop_not
    right
    rw [history_length]
    exact lt_iff_succ_le.mp (lt_of_not_ge hi)

end SetTheory.BusyBeaver.ZFC.ArithmeticSequenceHistory
