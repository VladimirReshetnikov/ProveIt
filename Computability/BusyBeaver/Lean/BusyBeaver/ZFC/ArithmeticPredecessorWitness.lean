import Foundation.FirstOrder.Arithmetic.IOpen.Basic
import ConciseIPRA.GuardedWitness
import ConciseIPRA.Semantics

/-! The guarded predecessor proof also used in ordinary iPRA is interpreted
here using only the two predecessor laws of the existing IOpen model. The
predicate on the witness is an arbitrary parameter of that interpretation. -/

set_option autoImplicit false

namespace SetTheory.BusyBeaver.ZFC.ArithmeticPredecessorWitness

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LeanProofs.ConciseIPRA
open scoped Fm LO.FirstOrder.Arithmetic

private inductive Symbol : ℕ → Type
  | zero : Symbol 0
  | one : Symbol 0
  | input : Symbol 0
  | add : Symbol 2
  | sub : Symbol 2
  | observes : Symbol 1

private def language : Language := ⟨Symbol, fun _ => Empty⟩

private abbrev Term (n : ℕ) := ClosedSemiterm language n

private instance : Syn Term where
  var := .bvar
  subst σ t := Rew.subst σ t
  subst_var σ i := Rew.subst_bvar σ i
  subst_id t := by simp
  subst_subst σ τ t := by
    change Rew.subst τ (Rew.subst σ t) = Rew.subst (fun i => Rew.subst τ (σ i)) t
    rw [← Rew.comp_app, Rew.subst_comp_subst]
    rfl

private def zero {n : ℕ} : Term n := .func Symbol.zero Fin.elim0
private def one {n : ℕ} : Term n := .func Symbol.one Fin.elim0
private def input {n : ℕ} : Term n := .func Symbol.input Fin.elim0
private def add {n : ℕ} (a b : Term n) : Term n := .func Symbol.add ![a, b]
private def sub {n : ℕ} (a b : Term n) : Term n := .func Symbol.sub ![a, b]
private def observes {n : ℕ} (a : Term n) : Term n := .func Symbol.observes ![a]

private def witness : Term 0 := sub input one
private def guard : Fm Term 0 := (input ≐ zero) ⟶ .bot
private def row : Fm Term 1 :=
  (sub (Syn.var 0) input ≐ zero) ⋏ (input ≐ add (Syn.var 0) one)
private def body : Fm Term 1 := observes (Syn.var 0) ≐ zero

private def recover : Fm Term 0 := .all (row ⟶ guard.shift ⋏ (Syn.var 0 ≐ Syn.shift witness))
private def supply : Fm Term 0 := guard ⟶ row.subst (Syn.inst witness)
private def noAxioms : Theory Term := fun _ _ => False

private theorem normalization : [recover, supply] ⊢[noAxioms]
    Fm.iff (.ex (row ⋏ body)) (guard ⋏ body.subst (Syn.inst witness)) := by
  refine Prf.guardedWitness row body guard witness ?_ ?_
  · have h : [recover, supply] ⊢[noAxioms] recover := Prf.hyp0
    exact .impE (Prf.allOpen h).wk Prf.hyp0
  · have h : [guard, recover, supply] ⊢[noAxioms] supply := .hyp (by simp)
    exact .impE h Prf.hyp0

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

lemma pred_add_one (u : V) (hu : u ≠ 0) : u - 1 + 1 = u := by
  have hpos : 0 < u := lt_of_le_of_ne (Arithmetic.zero_le u) (Ne.symm hu)
  exact tsub_add_cancel_of_le (by simpa using lt_iff_succ_le.mp hpos)

lemma pred_le (u : V) : u - 1 ≤ u := tsub_le_self

@[reducible] private noncomputable def structureFor (u : V) (Q : V → Prop) : Structure language V where
  func := by
    classical
    intro k f v
    cases f with
    | zero => exact 0
    | one => exact 1
    | input => exact u
    | add => exact v 0 + v 1
    | sub => exact v 0 - v 1
    | observes => exact if Q (v 0) then 0 else 1
  rel _ r := r.elim

private noncomputable def model (u : V) (Q : V → Prop) : TermModel Term V := by
  letI := structureFor u Q
  exact ⟨fun t e => t.valb e, fun _ _ => rfl, fun σ t _ => Semiterm.val_substs σ t⟩

/-- The successor code row in any IOpen model, at the same bounded witness
and with the original arbitrary predicate on the predecessor. -/
theorem predecessor_witness (u : V) (Q : V → Prop) :
    (∃ x, x ≤ u ∧ u = x + 1 ∧ Q x) ↔ u ≠ 0 ∧ Q (u - 1) := by
  classical
  let M := model u Q
  let e : Fin 0 → V := Fin.elim0
  have readRow (v : Fin 1 → V) : M.Holds row v ↔ v 0 ≤ u ∧ u = v 0 + 1 := by
    change (v 0 - u = 0 ∧ u = v 0 + 1) ↔ _
    rw [tsub_eq_zero_iff_le]
  have readGuard (v : Fin 0 → V) : M.Holds guard v ↔ u ≠ 0 := Iff.rfl
  have readBody (v : Fin 1 → V) : M.Holds body v ↔ Q (v 0) := by
    change ((if Q (v 0) then 0 else 1) : V) = 0 ↔ _
    by_cases h : Q (v 0) <;> simp [h]
  have readBodyInst : M.Holds (body.subst (Syn.inst witness)) e ↔ Q (u - 1) := by
    rw [M.holds_subst, readBody]
    rfl
  have hRecover : M.Holds recover e := by
    change ∀ x, M.Holds row (Fin.cases x e) →
      M.Holds guard.shift (Fin.cases x e) ∧ x = u - 1
    intro x hx
    have he := ((readRow _).1 hx).2
    rw [Fm.shift, M.holds_subst, readGuard]
    rw [he]
    simp
  have hSupply : M.Holds supply e := by
    change M.Holds guard e → M.Holds (row.subst (Syn.inst witness)) e
    rw [readGuard, M.holds_subst, readRow]
    intro hu
    exact ⟨pred_le u, (pred_add_one u hu).symm⟩
  have h := M.sound (fun ha => False.elim ha) normalization e
    (List.forall_mem_cons.2 ⟨hRecover,
      List.forall_mem_cons.2 ⟨hSupply, by simp⟩⟩)
  let original : Prop := ∃ x, M.Holds row (Fin.cases x e) ∧ M.Holds body (Fin.cases x e)
  let canonical := M.Holds guard e ∧ M.Holds (body.subst (Syn.inst witness)) e
  change (original → canonical) ∧ (canonical → original) at h
  simpa only [original, canonical, readRow, readBody, readGuard, readBodyInst, Fin.cases_zero, and_assoc]
    using Iff.intro h.1 h.2

end SetTheory.BusyBeaver.ZFC.ArithmeticPredecessorWitness
