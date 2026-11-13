module
public import FoundationBridge
public import Foundation.FirstOrder.Arithmetic.HFS.Vec
@[expose] public section
namespace PalomarPA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
/-- Rewriting an explicit closed operator only rewrites its arguments. -/
theorem operator_rewAux (o : Semiformula.Operator ℒₒᵣ k)
 (v : Fin k → Semiterm ℒₒᵣ Empty n) (ω : Rew ℒₒᵣ Empty n Empty m) :
 Semiformula.rewAux ω (o.operator v) = o.operator (fun i => ω (v i)) := by
 unfold Semiformula.Operator.operator Rewriting.emb Rewriting.subst
 simp only [← TransitiveRewriting.comp_app, Rew.emb_eq_id, Rew.comp_id]
 change (Rewriting.app ω) ((Rewriting.app (Rew.subst v)) o.sentence) = _
 rw [← TransitiveRewriting.comp_app]
 congr 2
 apply Rew.ext
 · intro i; simp [Rew.comp_app]
 · intro x; exact Empty.elim x

theorem operator_subst (o : Semiformula.Operator ℒₒᵣ k)
 (v : Fin k → Semiterm ℒₒᵣ Empty n) (w : Fin n → Semiterm ℒₒᵣ Empty m) :
 (o.operator v) ⇜ w = o.operator (fun i => (Rew.subst w) (v i)) :=
 operator_rewAux o v (Rew.subst w)

theorem closed_embSubsts {k m : Nat} (v : Fin k → Semiterm ℒₒᵣ Empty m) :
 Rew.embSubsts v = Rew.subst v := by
 apply Rew.ext
 · intro i; rfl
 · intro x; exact Empty.elim x
theorem closed_subst_identity (p : ArithmeticSemisentence k)
 (v : Fin k → Semiterm ℒₒᵣ Empty k) (hv : ∀ i, v i = .bvar i) : p ⇜ v = p := by
 have he : v = Semiterm.bvar := funext hv
 rw [he]
 simp [Rewriting.subst]
end PalomarPA
