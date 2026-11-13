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
abbrev D (G : List V) (p : V) := Kalmar.Der wim P G p
lemma h0 {G : List V} {a : V} : D P (a::G) a := .cons_head
lemma h1 {G : List V} {a b : V} : D P (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
lemma h2 {G : List V} {a b c : V} : D P (c::b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
private lemma ofDer (hc : Kalmar.Classical (wim : V → V → V) 1 P) {p : V} (d : D P [] p) : P p :=
  d.sound hc (fun _ hm => absurd hm List.not_mem_nil)
lemma ded1 (hc : Kalmar.Classical (wim : V → V → V) 1 P) {a p : V} (d : D P [a] p) : P (wim a p) :=
  ofDer P hc (Kalmar.deduction hc d)
lemma ded2 (hc : Kalmar.Classical (wim : V → V → V) 1 P) {a b p : V} (d : D P [b,a] p) : P (wim a (wim b p)) :=
  ofDer P hc (Kalmar.deduction hc (Kalmar.deduction hc d))
lemma ded3 (hc : Kalmar.Classical (wim : V → V → V) 1 P) {a b c p : V} (d : D P [c,b,a] p) : P (wim a (wim b (wim c p))) :=
  ofDer P hc (Kalmar.deduction hc (Kalmar.deduction hc (Kalmar.deduction hc d)))
section FiniteReasoning
variable (hc : Kalmar.Classical (wim : V → V → V) 1 P)
private abbrev neg (p : V) : V := wim p 1
private abbrev conj (p q : V) : V := neg (wim p (neg q))
include hc in
lemma compose {a b c : V} (hab : P (wim a b)) (hbc : P (wim b c)) : P (wim a c) :=
  ded1 P hc (.mp (.ax hbc) (.mp (.ax hab) (h0 P)))
include hc in
lemma contrapose (a b : V) : P (wim (wim a b) (wim (neg b) (neg a))) :=
  ded3 P hc (.mp (h1 P) (.mp (h2 P) (h0 P)))
include hc in
lemma double_neg_elim (a : V) : P (wim (neg (neg a)) a) := by
  apply ded1 P hc
  have inner : D P [neg (neg a)] (wim (neg a) a) :=
    Kalmar.deduction hc (.mp (.ax (hc.efq a)) (.mp (h1 P) (h0 P)))
  exact .mp (.ax (hc.peirce a 1)) inner
include hc in
lemma double_neg_intro (a : V) : P (wim a (neg (neg a))) :=
  ded2 P hc (.mp (h0 P) (h1 P))
include hc in
lemma conj_left (a b : V) : P (wim (conj a b) a) := by
  apply ded1 P hc
  have hnna : D P [conj a b] (neg (neg a)) := by
    apply Kalmar.deduction hc
    have hm : D P [neg a,conj a b] (wim a (neg b)) := by
      apply Kalmar.deduction hc
      exact .mp (.ax (hc.efq (neg b))) (.mp (h1 P) (h0 P))
    exact .mp (h1 P) hm
  exact .mp (.ax (double_neg_elim P hc a)) hnna
include hc in
lemma conj_right (a b : V) : P (wim (conj a b) b) := by
  apply ded1 P hc
  have hnnb : D P [conj a b] (neg (neg b)) := by
    apply Kalmar.deduction hc
    have hm : D P [neg b,conj a b] (wim a (neg b)) :=
      .mp (.ax (hc.k (neg b) a)) (h0 P)
    exact .mp (h1 P) hm
  exact .mp (.ax (double_neg_elim P hc b)) hnnb
include hc in
lemma conj_intro {a b : V} (ha : P a) (hb : P b) : P (conj a b) :=
  ded1 P hc (.mp (.mp (h0 P) (.ax ha)) (.ax hb))
include hc in
lemma imp_cases (a b c : V) :
    P (wim (wim (neg a) c) (wim (wim b c) (wim (wim a b) c))) := by
  apply ded3 P hc
  have inner : D P [neg c,wim a b,wim b c,wim (neg a) c] c := by
    have na : D P [neg c,wim a b,wim b c,wim (neg a) c] (neg a) :=
      Kalmar.deduction hc
        (.mp (.hyp (a := neg c) (by simp))
          (.mp (.hyp (a := wim b c) (by simp))
            (.mp (.hyp (a := wim a b) (by simp)) (h0 P))))
    exact .mp (.hyp (a := wim (neg a) c) (by simp)) na
  exact .mp (.ax (hc.peirce c 1)) (Kalmar.deduction hc inner)
include hc in
lemma contra_under {h p q : V} (hpq : P (wim h (wim p q))) :
    P (wim h (wim (neg q) (neg p))) :=
  ded3 P hc (.mp (h1 P) (.mp (.mp (.ax hpq) (h2 P)) (h0 P)))
include hc in
lemma imp_under {h p p' q q' : V} (hp : P (wim h (wim p' p)))
    (hq : P (wim h (wim q q'))) : P (wim h (wim (wim p q) (wim p' q'))) :=
  ded3 P hc (.mp (.mp (.ax hq) (h2 P)) (.mp (h1 P) (.mp (.mp (.ax hp) (h2 P)) (h0 P))))
variable (hgen : ∀ i {p}, P p → P (wal i p))
variable (hdist : ∀ i p q, P (wim (wal i (wim p q)) (wim (wal i p) (wal i q))))
variable (himp_ex : ∀ i p q, P (wim (wal i (wim p q))
  (wim (neg (wal i (neg p))) (neg (wal i (neg q))))))
variable (heq_ex : ∀ i j, P (neg (wal i (neg (weq i j)))))
variable (hex_vac : ∀ {i p}, P (wim p (wal i p)) → P (wim (neg (wal i (neg p))) p))
include hc hgen hdist in
private lemma all_mono (i : V) {p q : V} (h : P (wim p q)) :
    P (wim (wal i p) (wal i q)) := hc.mp (hdist i p q) (hgen i h)
include hc hex_vac in
lemma vac_neg {i p : V} (h : P (wim p (wal i p))) :
    P (wim (neg p) (wal i (neg p))) :=
  compose P hc (hc.mp (contrapose P hc _ _) (hex_vac h)) (double_neg_elim P hc _)
include hc hgen hdist hex_vac in
lemma vac_imp {i a b : V} (ha : P (wim a (wal i a))) (hb : P (wim b (wal i b))) :
    P (wim (wim a b) (wal i (wim a b))) := by
  have hna : P (wim (neg a) (wal i (wim a b))) :=
    compose P hc (vac_neg P hc hex_vac ha)
      (all_mono P hc hgen hdist i (ded2 P hc (.mp (.ax (hc.efq b)) (.mp (h1 P) (h0 P)))))
  have hbb : P (wim b (wal i (wim a b))) :=
    compose P hc hb (all_mono P hc hgen hdist i (hc.k b a))
  exact hc.mp (hc.mp (imp_cases P hc a b (wal i (wim a b))) hna) hbb
include hc hgen hdist in
lemma all_under_two (i : V) {h p q : V}
    (hpq : P (wim h (wim p q))) (hh : P (wim h (wal i h)))
    (hp : P (wim p (wal i p))) : P (wim h (wim p (wal i q))) := by
  have hg := compose P hc hh (all_mono P hc hgen hdist i hpq)
  apply ded2 P hc
  exact .mp (.mp (.ax (hdist i p q)) (.mp (.ax hg) (h1 P)))
    (.mp (.ax hp) (h0 P))
include hc hgen hdist himp_ex heq_ex hex_vac in
lemma all_relational (h p q x y : V)
    (hpq : P (wim h (wim (weq x y) (wim p q))))
    (vxh : P (wim h (wal x h))) (vxq : P (wim q (wal x q)))
    (vyh : P (wim h (wal y h))) (vyall : P (wim (wal x p) (wal y (wal x p)))) :
    P (wim h (wim (wal x p) (wal y q))) := by
  have hs : P (wim h (wim p (wim (weq x y) q))) :=
    ded3 P hc (.mp (.mp (.mp (.ax hpq) (h2 P)) (h0 P)) (h1 P))
  have hx := compose P hc vxh (all_mono P hc hgen hdist x hs)
  have hi : P (wim h (wim (wal x p) (wal x (wim (weq x y) q)))) := by
    apply ded2 P hc
    exact .mp (.mp (.ax (hdist x p (wim (weq x y) q)))
      (.mp (.ax hx) (h1 P))) (h0 P)
  have he : P (wim (wal x (wim (weq x y) q)) (neg (wal x (neg q)))) :=
    ded1 P hc (.mp (.mp (.ax (himp_ex x (weq x y) q)) (h0 P)) (.ax (heq_ex x y)))
  have hq : P (wim h (wim (wal x p) q)) := by
    apply ded2 P hc
    exact .mp (.ax (hex_vac vxq))
      (.mp (.ax he) (.mp (.mp (.ax hi) (h1 P)) (h0 P)))
  exact all_under_two P hc hgen hdist y hq vyh vyall
end FiniteReasoning
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
