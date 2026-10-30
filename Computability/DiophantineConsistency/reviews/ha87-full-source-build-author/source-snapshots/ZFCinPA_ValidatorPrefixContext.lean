import BusyBeaver.ZFC.ArithmeticCode254
import Foundation.FirstOrder.Arithmetic.HFS.Vec

/-! Shared proofs for internally represented prefixes of coordinate relations.
The relation, prefix iterator, and provability predicate are arbitrary fixed
Sigma1 operations; the supplied rules describe their propositional behavior. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorPrefixContext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
abbrev conj (p q : V) : V := wim (wim p (wim q 1)) 1
private instance conj_sigma1 : 𝚺₁-Function₂[V] conj := by
  unfold conj
  definability
variable (P : V → Prop) [𝚺₁-Predicate[V] P]
variable (atom : V → V → V) [𝚺₁-Function₂[V] atom]
variable (ctx : V → V → V → V) [𝚺₁-Function₃[V] ctx]
variable (zero_rule : ∀ B B', ctx 0 B B' = 0)
variable (succ_rule : ∀ n B B', ctx (n+1) B B' = conj (atom B.[n] B'.[n]) (ctx n B B'))
variable (left_rule : ∀ a b, P (wim (conj a b) a))
variable (right_rule : ∀ a b, P (wim (conj a b) b))
variable (comp_rule : ∀ {a b c}, P (wim a b) → P (wim b c) → P (wim a c))
include succ_rule left_rule right_rule comp_rule in
/-- Every coordinate below the internal prefix length follows from the prefix. -/
lemma projection (n B B' : V) : ∀ i<n, P (wim (ctx n B B') (atom B.[i] B'.[i])) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => intro i hi; simp at hi
  case succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le (lt_succ_iff_le.mp hi) with hit | rfl
    · rw [succ_rule]; exact comp_rule (right_rule _ _) (ih i hit)
    · rw [succ_rule]; exact left_rule _ _
variable (self_rule : ∀ a, P (wim a a))
variable (mono_rule : ∀ a {b c}, P (wim b c) → P (wim (conj a b) (conj a c)))
variable (swap_rule : ∀ a b c, P (wim (conj a (conj b c)) (conj b (conj a c))))
include zero_rule succ_rule self_rule mono_rule swap_rule comp_rule in
/-- Prepending coordinates commutes with the reversed conjunction up to proof. -/
lemma cons_equiv (n B B' x y : V) :
    P (wim (ctx (n+1) (x∷B) (y∷B')) (conj (atom x y) (ctx n B B'))) ∧
    P (wim (conj (atom x y) (ctx n B B')) (ctx (n+1) (x∷B) (y∷B'))) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    constructor <;> simpa only [succ_rule,zero_rule,nth_adjoin_zero] using
      (self_rule (conj (atom x y) (0 : V)))
  case succ n ih =>
    constructor
    · simpa only [succ_rule,nth_adjoin_succ] using
        comp_rule (mono_rule (atom B.[n] B'.[n]) ih.1)
          (swap_rule (atom B.[n] B'.[n]) (atom x y) (ctx n B B'))
    · simpa only [succ_rule,nth_adjoin_succ] using
        comp_rule (swap_rule (atom x y) (atom B.[n] B'.[n]) (ctx n B B'))
          (mono_rule (atom B.[n] B'.[n]) ih.2)

variable (Q : V → V → Prop) [𝚺₁-Relation[V] Q]
variable (zero_rule : ∀ B B', ctx 0 B B' = 0)
variable (succ_rule : ∀ n B B', ctx (n+1) B B' = conj (atom B.[n] B'.[n]) (ctx n B B'))
variable (zero_vac : ∀ z, Q z 0)
variable (atom_vac : ∀ a b z, z ≠ a → z ≠ b → Q z (atom a b))
variable (conj_vac : ∀ {z a b}, Q z a → Q z b → Q z (conj a b))
omit [𝚺₁-Function₂[V] atom] in
include zero_rule succ_rule zero_vac atom_vac conj_vac in
/-- Coordinate avoidance implies vacuity of the entire internal prefix. -/
lemma vac (n B B' z : V) :
    (∀ i<n, z≠B.[i]) → (∀ i<n, z≠B'.[i]) → Q z (ctx n B B') := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro _ _
    simpa only [zero_rule] using zero_vac z
  case succ n ih =>
    intro hB hB'
    rw [succ_rule]
    exact conj_vac (atom_vac _ _ z (hB n (by simp)) (hB' n (by simp)))
      (ih (fun i hi => hB i (lt_succ_iff_le.mpr (le_of_lt hi)))
        (fun i hi => hB' i (lt_succ_iff_le.mpr (le_of_lt hi))))

end LeanProofs.ZFCinPA.ValidatorPrefixContext
