import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorSeedClosure222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Uniform arbitrary-matrix projections of the actual internal C222 seed.
The existential closure is normalized by finite certificates. No matrix
vacuity or semantic truth premise is supplied. The result is a literal
subset-indexed request, not raw-membership CP/GIC or tagged comprehension.
-/
namespace LeanProofs.ZFCinPA.ValidatorSeedImage222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorSeedWitness222
open ArithmeticSeedTemplates222 (req clos)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)

def subset (a b k : V) : V := wal k (wim (wel k a) (wel k b))
def support (a b k p : V) : V := wal b (wim (wel b k) (ex a p))
def coverage (a b k p : V) : V :=
  wal b (wim (wel b k) (wim (subset a b k) (req b k p)))
def imageBody (a b k p : V) : V :=
  conj (support a b k p) (conj (req b k p) (coverage a b k p))

/-- Project the witness matrix, retaining its input existential. All codes
are arbitrary, including coincident labels and the matrix code zero. -/
theorem closure_support_exists (a b k p : V) :
    CProv (wim (clos a b k p) (support a b k p)) := by
  let U := wal a (wim (subset a b k) (req b k p))
  have inner := compose (not_all_imp_ex_conj a p U).1 (ex_mono a (conj_left p U))
  exact all_mono b (imp_mono (ded1 h0) inner)

/-- The universal right component is eliminated by the actual rho6
certificate. The input label a remains free in the resulting clause;
there is no unrestricted generalization under its membership hypothesis. -/
theorem closure_coverage (a b k p : V) :
    CProv (wim (clos a b k p) (coverage a b k p)) := by
  let U := wal a (wim (subset a b k) (req b k p))
  have inner := compose (not_all_imp_ex_conj a p U).1
    (compose (ex_mono a (conj_right p U))
      (ex_all_elim a (wim (subset a b k) (req b k p))))
  exact all_mono b (imp_mono (ded1 h0) inner)

theorem pair_image (a b k p : V) :
    CProv (wim (conj (clos a b k p) (req b k p)) (imageBody a b k p)) := by
  apply ded1
  have hc : D [conj (clos a b k p) (req b k p)] (clos a b k p) :=
    .mp (.ax (conj_left _ _)) h0
  exact .mp (.mp (.ax (conj_rule _ _))
    (.mp (.ax (closure_support_exists a b k p)) hc))
    (.mp (.mp (.ax (conj_rule _ _)) (.mp (.ax (conj_right _ _)) h0))
      (.mp (.ax (closure_coverage a b k p)) hc))

/-- Preserve exactly the two literal seed gates, with no Vac a c or Vac c c. -/
theorem seed_image (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    CProv (ex c (imageBody a b c c)) :=
  cProv_mp (ex_mono c (pair_image a b c c)) (seed_pair a b c hca hcb)

private abbrev Equivalent (p q : V) := CProv (wim p q) ∧ CProv (wim q p)
private lemma eq_refl (p : V) : Equivalent p p := ⟨ded1 h0, ded1 h0⟩
private lemma eq_imp {p p' q q' : V}
    (hp : Equivalent p p') (hq : Equivalent q q') :
    Equivalent (wim p q) (wim p' q') :=
  ⟨imp_mono hp.2 hq.1, imp_mono hp.1 hq.2⟩
private lemma eq_neg {p q : V} (h : Equivalent p q) : Equivalent (neg p) (neg q) :=
  ⟨contrapose_of h.2, contrapose_of h.1⟩
private lemma eq_all (i : V) {p q : V} (h : Equivalent p q) :
    Equivalent (wal i p) (wal i q) := ⟨all_mono i h.1, all_mono i h.2⟩

/-- Actual finite congruence certificates for the literal request circuit. -/
theorem request_congr (b k p q : V)
    (hpq : CProv (wim p q)) (hqp : CProv (wim q p)) :
    CProv (wim (req b k p) (req b k q)) ∧
      CProv (wim (req b k q) (req b k p)) :=
  eq_all b (eq_imp ⟨hpq,hqp⟩
    (eq_neg (eq_all b (eq_imp ⟨hpq,hqp⟩ (eq_neg (eq_refl (wel b k)))))))

/-- No binder is renamed: k stays fixed while only the matrix changes by
a proved CProv equivalence, even when the original matrix has code k. -/
theorem closure_congr (a b k p q : V)
    (hpq : CProv (wim p q)) (hqp : CProv (wim q p)) :
    CProv (wim (clos a b k p) (clos a b k q)) ∧
      CProv (wim (clos a b k q) (clos a b k p)) :=
  eq_all b (eq_imp (eq_refl (wel b k)) (eq_neg (eq_all a
    (eq_imp ⟨hpq,hqp⟩ (eq_neg (eq_all a
      (eq_imp (eq_refl (subset a b k)) (request_congr b k p q hpq hqp))))))))

/-- Transport the closure and request together along a matrix equivalence. -/
theorem closure_request_congr (a b k p q : V)
    (hpq : CProv (wim p q)) (hqp : CProv (wim q p)) :
    CProv (wim (conj (clos a b k p) (req b k p))
      (conj (clos a b k q) (req b k q))) := by
  apply ded1
  exact .mp (.mp (.ax (conj_rule _ _))
    (.mp (.ax (closure_congr a b k p q hpq hqp).1) (.mp (.ax (conj_left _ _)) h0)))
    (.mp (.ax (request_congr b k p q hpq hqp).1) (.mp (.ax (conj_right _ _)) h0))

def pad (p : V) : V := neg (neg p)

theorem pad_gt_three (p : V) : (3 : V) < pad p := by
  have hc : (1 : V) ≤ ArithmeticCantor.cantor (wim p 1) 1 :=
    (ArithmeticCantor.components_le _ _).2
  have hm := mul_le_mul_of_nonneg_left hc (show (0 : V) ≤ 4 by simp)
  have hp : (4 : V) ≤ pad p := by
    simpa only [pad, neg, wim, tagged, add_zero, mul_one] using hm
  exact lt_of_lt_of_le (by simpa only [three_add_one_eq_four] using (lt_add_one (3 : V))) hp

/-- Every internal matrix, including zero, is admitted at literal roles1/3.
The container label is its double-negation code, without assuming vacuity
at that label or an arbitrary semantic/represented-formula interpretation. -/
theorem matrix_image (p : V) : CProv (ex (pad p) (imageBody 1 3 (pad p) p)) := by
  have hp : CProv (wim (pad p) p) := double_neg_elim p
  have ph : CProv (wim p (pad p)) := double_neg_intro p
  have point := closure_request_congr 1 3 (pad p) (pad p) p hp ph
  exact cProv_mp (ex_mono (pad p) (compose point (pair_image 1 3 (pad p) p)))
    (seed_pair 1 3 (pad p)
      (ne_of_gt (lt_of_le_of_lt (by simp) (pad_gt_three p))) (ne_of_gt (pad_gt_three p)))

theorem matrix_image_witness (p : V) :
    ∃ code : V, ArithmeticHistory222.value code =
      ex (pad p) (imageBody 1 3 (pad p) p) + 1 := matrix_image p

end LeanProofs.ZFCinPA.ValidatorSeedImage222
