import BusyBeaver.ZFC.ArithmeticCode254
import BusyBeaver.ZFC.Kalmar
import Foundation.FirstOrder.Arithmetic.HFS.Vec
/-! Internal implication-chain context calculus for any represented Sigma1
provability predicate satisfying the classical implicational rules. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorImplicationContext
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCode254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
variable (P : V → Prop)
variable (fold : V → V → V) [𝚺₁-Function₂[V] fold]
variable (nil_rule : ∀ g, fold 0 g = g)
variable (cons_rule : ∀ a G g, fold (a ∷ G) g = wim a (fold G g))
private abbrev D (G : List V) (p : V) := Kalmar.Der wim P G p
private lemma h0 {G : List V} {a : V} : D P (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D P (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma h2 {G : List V} {a b c : V} : D P (c::b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
private lemma ofDer (hc : Kalmar.Classical (wim : V → V → V) 1 P) {p : V} (d : D P [] p) : P p :=
  d.sound hc (fun _ hm => absurd hm List.not_mem_nil)
private lemma ded1 (hc : Kalmar.Classical (wim : V → V → V) 1 P) {a p : V} (d : D P [a] p) : P (wim a p) :=
  ofDer P hc (Kalmar.deduction hc d)
private lemma ded2 (hc : Kalmar.Classical (wim : V → V → V) 1 P) {a b p : V} (d : D P [b,a] p) : P (wim a (wim b p)) :=
  ofDer P hc (Kalmar.deduction hc (Kalmar.deduction hc d))
private lemma ded3 (hc : Kalmar.Classical (wim : V → V → V) 1 P) {a b c p : V} (d : D P [c,b,a] p) : P (wim a (wim b (wim c p))) :=
  ofDer P hc (Kalmar.deduction hc (Kalmar.deduction hc (Kalmar.deduction hc d)))
variable [𝚺₁-Predicate[V] P] (hc : Kalmar.Classical (wim : V → V → V) 1 P)
include nil_rule cons_rule hc in
lemma imps_k (x : V) : ∀ G : V, P (wim x (fold G x)) := by
  intro G
  induction G using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simpa only [nil_rule] using Kalmar.self_imp hc x
  case adjoin a G ih =>
    simp only [cons_rule]
    exact ded1 P hc (.mp (.ax (hc.k (fold G x) a)) (.mp (.ax ih) (h0 P)))
include nil_rule cons_rule hc in
lemma imps_mp (a b : V) : ∀ G : V,
    P (wim (fold G (wim a b)) (wim (fold G a) (fold G b))) := by
  intro G
  induction G using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simpa only [nil_rule] using Kalmar.self_imp hc (wim a b)
  case adjoin c G ih =>
    simp only [cons_rule]
    apply ded3 P hc
    exact .mp (.mp (.ax ih) (.mp (h2 P) (h0 P))) (.mp (h1 P) (h0 P))
include nil_rule cons_rule hc in
lemma imps_ded (a g : V) : ∀ G : V, P (wim (wim a (fold G g)) (fold G (wim a g))) := by
  intro G
  induction G using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simpa only [nil_rule] using Kalmar.self_imp hc (wim a g)
  case adjoin b G ih =>
    simp only [cons_rule]
    apply ded2 P hc
    exact .mp (.ax ih) (Kalmar.deduction hc (.mp (.mp (h2 P) (h0 P)) (h1 P)))
include nil_rule cons_rule hc in
lemma imps_undeduct (a g : V) : ∀ G : V, P (wim (fold G (wim a g)) (wim a (fold G g))) := by
  intro G
  induction G using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simpa only [nil_rule] using Kalmar.self_imp hc (wim a g)
  case adjoin b G ih =>
    simp only [cons_rule]
    apply ded3 P hc
    exact .mp (.mp (.ax ih) (.mp (h2 P) (h0 P))) (h1 P)
include nil_rule cons_rule hc in
lemma hyp : ∀ G : V, ∀ i < len G, P (fold G G.[i]) := by
  intro G
  induction G using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro i hi; simp at hi
  case adjoin c G ih =>
    intro i hi
    rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
    · simpa only [nth_adjoin_zero, cons_rule] using imps_k P fold nil_rule cons_rule hc c G
    · have hj : j < len G := by simpa using hi
      simp only [nth_adjoin_succ, cons_rule]
      exact hc.mp (hc.k _ c) (ih j hj)

include nil_rule cons_rule hc in
lemma sub (G g : V) : ∀ G' : V, (∀ x, x ∈ᵥ G' → x ∈ᵥ G) →
    P (fold G (wim (fold G' g) g)) := by
  have dof {x : V} (h : P x) : P (fold G x) := hc.mp (imps_k P fold nil_rule cons_rule hc x G) h
  have dmp {a b : V} (hab : P (fold G (wim a b))) (ha : P (fold G a)) : P (fold G b) :=
    hc.mp (hc.mp (imps_mp P fold nil_rule cons_rule hc a b G) hab) ha
  intro G'
  induction G' using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; simpa only [nil_rule] using dof (Kalmar.self_imp hc g)
  case adjoin a G' ih =>
    intro hsub
    have ih' := ih (fun x hx ↦ hsub x (memVec_adjoin_iff.mpr (Or.inr hx)))
    have ha : P (fold G a) := by
      obtain ⟨i, hi, heq⟩ := hsub a (by simp)
      rw [heq]
      exact hyp P fold nil_rule cons_rule hc G i hi
    simp only [cons_rule]
    have taut : P (wim (wim (fold G' g) g) (wim a (wim (wim a (fold G' g)) g))) :=
      ded3 P hc (.mp (h2 P) (.mp (h0 P) (h1 P)))
    exact dmp (dmp (dof taut) ih') ha
end LeanProofs.ZFCinPA.ValidatorImplicationContext
