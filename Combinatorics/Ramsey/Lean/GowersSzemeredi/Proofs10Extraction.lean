import GowersSzemeredi.Section10
import GowersSzemeredi.ProofInfrastructure

/-!
# Extracting a local difference model in Section 10

This module audits Lemma 10.6 before supplying its companion proof.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Audit model

The live statement does not retain the upper bounds on `rho` used to produce
the regular component in Lemma 10.5.  The following finite model is used below
to test whether the remaining hypotheses alone recover that information.
-/

private def auditQ : Nat := 32 ^ 5
private def auditH : Nat := 4096 * auditQ ^ 2
private def auditL : Nat := 1000 * auditQ * auditH
private def auditCard : Nat := 1 + 2 * auditH + 4 * auditL
private def auditM : Nat := auditCard ^ 2

private def auditProfile (s : ZMod 8) : Nat :=
  if s = 0 then 1
  else if s = 1 then auditH
  else if s = 2 then auditL
  else if s = 3 then auditL
  else if s = 4 then 0
  else if s = 5 then auditH
  else if s = 6 then auditL
  else auditL

private abbrev AuditX := Σ s : ZMod 8, Fin (auditProfile s)

private def auditDomain : MultifunctionDomain 8 AuditX :=
  ⟨fun x => x.1⟩

private def auditPhi (x : AuditX) : ZMod 8 :=
  if x.1 = 5 then 1 else 0

private noncomputable def auditB : Finset (ZMod 8) := {4}

private noncomputable def auditW : Finset AuditX :=
  Finset.univ.filter fun x => x.1 = 1 ∨ x.1 = 5

private def auditX0 : AuditX :=
  ⟨0, ⟨0, by simp [auditProfile]⟩⟩

private abbrev auditAlpha : Real := auditCard / (auditM * 8)
private abbrev auditEta : Real := 1 / auditQ
private abbrev auditRho : Real := 1024 * auditQ
private abbrev auditSigma : Real := 1 / auditM

@[simp] private lemma auditProfile_zero : auditProfile 0 = 1 := by
  decide

@[simp] private lemma auditProfile_one : auditProfile 1 = auditH := by
  decide

@[simp] private lemma auditProfile_two : auditProfile 2 = auditL := by
  decide

@[simp] private lemma auditProfile_three : auditProfile 3 = auditL := by
  decide

@[simp] private lemma auditProfile_four : auditProfile 4 = 0 := by
  decide

@[simp] private lemma auditProfile_five : auditProfile 5 = auditH := by
  decide

@[simp] private lemma auditProfile_six : auditProfile 6 = auditL := by
  decide

@[simp] private lemma auditProfile_seven : auditProfile 7 = auditL := by
  decide

private def auditFibreEquiv (s : ZMod 8) :
    {x : AuditX // x ∈ auditDomain.fibre s} ≃ Fin (auditProfile s) where
  toFun x := by
    have hx' : auditDomain.index x.1 = s := by
      simpa only [MultifunctionDomain.fibre, Finset.mem_filter,
        Finset.mem_univ, true_and] using x.2
    have hx : x.1.1 = s := hx'
    exact Fin.cast (congrArg auditProfile hx) x.1.2
  invFun y := ⟨⟨s, y⟩, by simp [auditDomain, MultifunctionDomain.fibre]⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨t, v⟩, ht⟩
    simp only
    have hts' : auditDomain.index ⟨t, v⟩ = s := by
      simpa only [MultifunctionDomain.fibre, Finset.mem_filter,
        Finset.mem_univ, true_and] using ht
    have hts : t = s := hts'
    subst t
    rfl
  right_inv y := rfl

@[simp] private lemma audit_fibre_card (s : ZMod 8) :
    (auditDomain.fibre s).card = auditProfile s := by
  rw [← Fintype.card_coe]
  simpa using Fintype.card_congr (auditFibreEquiv s)

@[simp] private lemma audit_fibreSize (x : AuditX) :
    auditDomain.fibreSize x = auditProfile x.1 := by
  unfold MultifunctionDomain.fibreSize auditDomain
  exact audit_fibre_card x.1

private lemma audit_card_X : Fintype.card AuditX = auditCard := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have huniv : (Finset.univ : Finset (ZMod 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by
    decide
  rw [huniv]
  decide

private lemma audit_sum_index (f : ZMod 8 → Nat) :
    (∑ x : AuditX, f x.1) = ∑ s : ZMod 8, auditProfile s * f s := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro s _
  simp

private lemma audit_countWhere_eq_sum_ite {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    countWhere P = ∑ x : T, if P x then 1 else 0 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  simp

private lemma audit_differenceWeight_eq_sum_fibre (y : AuditX) :
    domainDifferenceWeight auditDomain auditX0 y =
      ∑ z : AuditX,
        (auditDomain.fibre
          (z.1 + (y.1 - auditX0.1))).card := by
  classical
  unfold domainDifferenceWeight
  rw [audit_countWhere_eq_sum_ite]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  simp only [auditDomain]
  have hcond (w : AuditX) :
      w.1 - z.1 = y.1 - auditX0.1 ↔
        w.1 = z.1 + (y.1 - auditX0.1) := by
    constructor <;> intro h <;> linear_combination h
  simp_rw [hcond]
  unfold MultifunctionDomain.fibre
  rw [Finset.filter_congr_decidable]
  simp

private lemma audit_differenceWeight_formula (y : AuditX) :
    domainDifferenceWeight auditDomain auditX0 y =
      ∑ s : ZMod 8,
        auditProfile s * auditProfile (s + (y.1 - auditX0.1)) := by
  rw [audit_differenceWeight_eq_sum_fibre]
  simp only [audit_fibre_card]
  simpa only using
    audit_sum_index (fun s => auditProfile (s + (y.1 - auditX0.1)))

private lemma audit_mem_W (y : AuditX) :
    y ∈ auditW ↔ y.1 = 1 ∨ y.1 = 5 := by
  simp [auditW]

private lemma audit_W_eq_fibres :
    auditW = auditDomain.fibre 1 ∪ auditDomain.fibre 5 := by
  ext y
  simp only [audit_mem_W, Finset.mem_union, MultifunctionDomain.fibre,
    Finset.mem_filter, Finset.mem_univ, true_and, auditDomain]

private lemma audit_fibres_one_five_disjoint :
    Disjoint (auditDomain.fibre 1) (auditDomain.fibre 5) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy5
  simp only [MultifunctionDomain.fibre, Finset.mem_filter, Finset.mem_univ,
    true_and, auditDomain] at hy1 hy5
  have : (1 : ZMod 8) = 5 := hy1.symm.trans hy5
  exact (by decide : (1 : ZMod 8) ≠ 5) this

@[simp] private lemma audit_card_W : auditW.card = 2 * auditH := by
  rw [audit_W_eq_fibres, Finset.card_union_of_disjoint
    audit_fibres_one_five_disjoint]
  simp [audit_fibre_card]
  omega

private lemma audit_correlation_one_five :
    (∑ s : ZMod 8, auditProfile s * auditProfile (s + (1 - 0))) =
      ∑ s : ZMod 8, auditProfile s * auditProfile (s + (5 - 0)) := by
  have huniv : (Finset.univ : Finset (ZMod 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by
    decide
  rw [huniv]
  decide

private lemma audit_differenceWeight_eq_of_mem_W {y z : AuditX}
    (hy : y ∈ auditW) (hz : z ∈ auditW) :
    domainDifferenceWeight auditDomain auditX0 y =
      domainDifferenceWeight auditDomain auditX0 z := by
  rw [audit_differenceWeight_formula, audit_differenceWeight_formula]
  rcases (audit_mem_W y).mp hy with hy1 | hy5 <;>
    rcases (audit_mem_W z).mp hz with hz1 | hz5
  · rw [hy1, hz1]
  · rw [hy1, hz5]
    exact audit_correlation_one_five
  · rw [hy5, hz1]
    exact audit_correlation_one_five.symm
  · rw [hy5, hz5]

private lemma audit_fibreSize_eq_H {y : AuditX} (hy : y ∈ auditW) :
    auditDomain.fibreSize y = auditH := by
  rw [audit_fibreSize]
  rcases (audit_mem_W y).mp hy with hy1 | hy5
  · rw [hy1]
    exact auditProfile_one
  · rw [hy5]
    exact auditProfile_five

private lemma audit_restrictedWeight_zero (y : AuditX) :
    domainRestrictedDifferenceWeight auditDomain auditB auditX0 y = 0 := by
  unfold domainRestrictedDifferenceWeight
  rw [countWhere_congr (q := fun _ : AuditX × AuditX => False)]
  · exact countWhere_false
  · intro uv
    constructor
    · intro huv
      have hu := huv.2
      simp only [auditB, Finset.mem_singleton] at hu
      change uv.1.1 - auditX0.1 = (4 : ZMod 8) at hu
      have hu' : uv.1.1 = (4 : ZMod 8) := by
        simpa [auditX0] using hu
      have hzero : auditProfile uv.1.1 = 0 := by
        rw [hu']
        exact auditProfile_four
      exact Fin.elim0 (Fin.cast hzero uv.1.2)
    · exact False.elim

@[simp] private lemma audit_proportionateError_zero (y : AuditX) :
    domainProportionateError auditDomain auditPhi auditB auditX0 y = 0 := by
  unfold domainProportionateError
  rw [audit_restrictedWeight_zero]
  simp only [Nat.cast_zero, div_zero]

private lemma audit_totalWeight_formula :
    domainTotalWeight auditDomain auditX0 =
      ∑ t : ZMod 8, auditProfile t *
        (∑ s : ZMod 8, auditProfile s * auditProfile (s + (t - 0))) := by
  unfold domainTotalWeight
  have hpoint (y : AuditX) :
      domainDifferenceWeight auditDomain auditX0 y =
        ∑ s : ZMod 8,
          auditProfile s * auditProfile (s + (y.1 - 0)) := by
    simpa [auditX0] using audit_differenceWeight_formula y
  simp_rw [hpoint]
  simpa only using audit_sum_index (fun t =>
    ∑ s : ZMod 8, auditProfile s * auditProfile (s + (t - 0)))

private lemma audit_totalWeight_lower :
    4 * auditL ^ 3 ≤ domainTotalWeight auditDomain auditX0 := by
  rw [audit_totalWeight_formula]
  have huniv : (Finset.univ : Finset (ZMod 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by
    decide
  rw [huniv]
  decide

private lemma audit_countWhere_coordinate_mem {Y : Type*}
    [Fintype Y] [DecidableEq Y] (A : Finset Y) (i : Fin 4) :
    countWhere (fun q : Fin 4 → Y => q i ∈ A) =
      A.card * Fintype.card Y ^ 3 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  rw [show (Finset.univ.filter (fun q : Fin 4 → Y => q i ∈ A)) =
      Fintype.piFinset (Function.update
        (fun _ : Fin 4 => (Finset.univ : Finset Y)) i A) by
    rw [Fintype.piFinset_update_eq_filter_piFinset_mem
      (fun _ : Fin 4 => (Finset.univ : Finset Y)) i (Finset.subset_univ A)]
    ext
    simp]
  rw [Fintype.card_piFinset, Fintype.prod_eq_prod_compl_mul i]
  rw [show (∏ x ∈ ({i}ᶜ : Finset (Fin 4)),
      #(Function.update (fun _ : Fin 4 => (Finset.univ : Finset Y)) i A x)) =
      ∏ _x ∈ ({i}ᶜ : Finset (Fin 4)), Fintype.card Y by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]]
  have hcard : #({i}ᶜ : Finset (Fin 4)) = 3 := by
    simp [Finset.card_compl]
  simp [hcard, mul_comm]

private lemma audit_countWhere_all_mem {Y : Type*}
    [Fintype Y] [DecidableEq Y] (A : Finset Y) :
    countWhere (fun q : Fin 4 → Y => ∀ i, q i ∈ A) = A.card ^ 4 := by
  classical
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  rw [show (Finset.univ.filter
      (fun q : Fin 4 → Y => ∀ i, q i ∈ A)) =
      Fintype.piFinset (fun _ : Fin 4 => A) by ext; simp]
  exact Fintype.card_piFinset_const A 4

private lemma audit_coordinate_exception_count (i : Fin 4) :
    (∑ q : Fin 4 → AuditX, if (q i).1 = 5 then 1 else 0) =
      auditH * auditCard ^ 3 := by
  rw [← audit_countWhere_eq_sum_ite]
  calc
    countWhere (fun q : Fin 4 → AuditX => (q i).1 = 5) =
        countWhere (fun q : Fin 4 → AuditX =>
          q i ∈ auditDomain.fibre 5) := by
      apply countWhere_congr
      intro q
      simp [MultifunctionDomain.fibre, auditDomain]
    _ = (auditDomain.fibre 5).card * Fintype.card AuditX ^ 3 :=
      audit_countWhere_coordinate_mem (auditDomain.fibre 5) i
    _ = auditH * auditCard ^ 3 := by
      rw [audit_fibre_card, auditProfile_five, audit_card_X]

private lemma audit_hits_exception_count_le :
    countWhere (fun q : Fin 4 → AuditX => ∃ i, (q i).1 = 5) ≤
      4 * auditH * auditCard ^ 3 := by
  rw [audit_countWhere_eq_sum_ite]
  calc
    (∑ q : Fin 4 → AuditX, if ∃ i, (q i).1 = 5 then 1 else 0) ≤
        ∑ q : Fin 4 → AuditX, ∑ i : Fin 4,
          if (q i).1 = 5 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro q _
      by_cases hq : ∃ i, (q i).1 = 5
      · rw [if_pos hq]
        obtain ⟨i, hi⟩ := hq
        have hsingle := Finset.single_le_sum
          (fun j (_hj : j ∈ (Finset.univ : Finset (Fin 4))) =>
            Nat.zero_le (if (q j).1 = 5 then 1 else 0))
          (Finset.mem_univ i)
        simpa [hi] using hsingle
      · rw [if_neg hq]
        exact Nat.zero_le _
    _ = ∑ i : Fin 4, ∑ q : Fin 4 → AuditX,
          if (q i).1 = 5 then 1 else 0 := by rw [Finset.sum_comm]
    _ = ∑ _i : Fin 4, auditH * auditCard ^ 3 := by
      apply Finset.sum_congr rfl
      intro i _
      exact audit_coordinate_exception_count i
    _ = 4 * auditH * auditCard ^ 3 := by simp; ring

private abbrev auditCore (q : Fin 4 → AuditX) : Prop :=
  (q 0).1 = 2 ∧ (q 1).1 = 2 ∧ (q 2).1 = 2 ∧ (q 3).1 = 2

private lemma audit_core_count : countWhere auditCore = auditL ^ 4 := by
  calc
    countWhere auditCore = countWhere (fun q : Fin 4 → AuditX =>
        ∀ i, q i ∈ auditDomain.fibre 2) := by
      apply countWhere_congr
      intro q
      simp [auditCore, MultifunctionDomain.fibre, auditDomain,
        Fin.forall_fin_succ]
    _ = (auditDomain.fibre 2).card ^ 4 :=
      audit_countWhere_all_mem (auditDomain.fibre 2)
    _ = auditL ^ 4 := by
      rw [audit_fibre_card, auditProfile_two]

private lemma audit_core_additive (q : Fin 4 → AuditX) (hq : auditCore q) :
    HasEqualHalfSums (k := 2) (fun i => auditDomain.index (q i)) := by
  rcases hq with ⟨h0, h1, h2, h3⟩
  unfold HasEqualHalfSums
  simp only [auditDomain]
  rw [show (Finset.univ.filter (fun i : Fin 4 => (i : Nat) < 2)) = {0, 1} by decide]
  rw [show (Finset.univ.filter (fun i : Fin 4 => 2 ≤ (i : Nat))) = {2, 3} by decide]
  simp [h0, h1, h2, h3]

private lemma audit_additive_count_lower :
    auditL ^ 4 ≤ domainAdditiveTupleCount auditDomain 2 := by
  rw [← audit_core_count]
  unfold domainAdditiveTupleCount
  apply countWhere_mono
  exact audit_core_additive

private lemma audit_phi_good_without_exception (q : Fin 4 → AuditX)
    (hq : ∀ i, (q i).1 ≠ 5) :
    HasEqualHalfSums (k := 2) (fun i => auditPhi (q i)) := by
  have hphi (i : Fin 4) : auditPhi (q i) = 0 := by
    simp [auditPhi, hq i]
  unfold HasEqualHalfSums
  rw [show (Finset.univ.filter (fun i : Fin 4 => (i : Nat) < 2)) = {0, 1} by decide]
  rw [show (Finset.univ.filter (fun i : Fin 4 => 2 ≤ (i : Nat))) = {2, 3} by decide]
  simp [hphi]

private def auditAdditive (q : Fin 4 → AuditX) : Prop :=
  HasEqualHalfSums (k := 2) (fun i => auditDomain.index (q i))

private def auditPhiRelation (q : Fin 4 → AuditX) : Prop :=
  HasEqualHalfSums (k := 2) (fun i => auditPhi (q i))

private lemma audit_domain_count_eq :
    domainAdditiveTupleCount auditDomain 2 = countWhere auditAdditive := by
  unfold domainAdditiveTupleCount
  apply countWhere_congr
  intro q
  unfold auditAdditive
  constructor <;> intro h <;> exact h

private lemma audit_phi_count_eq :
    domainPhiAdditiveTupleCount auditDomain auditPhi 2 =
      countWhere (fun q => auditAdditive q ∧ auditPhiRelation q) := by
  unfold domainPhiAdditiveTupleCount
  apply countWhere_congr
  intro q
  unfold auditAdditive auditPhiRelation
  constructor <;> intro h <;> exact h

private lemma countWhere_and_partition {T : Type*} [Fintype T]
    (A P : T → Prop) :
    countWhere A = countWhere (fun x => A x ∧ P x) +
      countWhere (fun x => A x ∧ ¬ P x) := by
  classical
  let S : Finset T := Finset.univ.filter A
  have hcard := Finset.card_filter_add_card_filter_not (s := S) P
  have hA : countWhere A = S.card := by
    unfold countWhere
    rw [Finset.filter_congr_decidable]
  have hGood : countWhere (fun x => A x ∧ P x) = (S.filter P).card := by
    unfold countWhere
    rw [Finset.filter_congr_decidable]
    congr 1
    ext x
    simp [S]
  have hBad : countWhere (fun x => A x ∧ ¬ P x) =
      (S.filter (fun x => ¬ P x)).card := by
    unfold countWhere
    rw [Finset.filter_congr_decidable]
    congr 1
    ext x
    simp [S]
  calc
    countWhere A = S.card := hA
    _ = (S.filter P).card + (S.filter (fun x => ¬ P x)).card := hcard.symm
    _ = countWhere (fun x => A x ∧ P x) +
        countWhere (fun x => A x ∧ ¬ P x) := by rw [hGood, hBad]

private lemma audit_additive_partition :
    countWhere auditAdditive =
      countWhere (fun q => auditAdditive q ∧ auditPhiRelation q) +
        countWhere (fun q => auditAdditive q ∧ ¬ auditPhiRelation q) :=
  countWhere_and_partition auditAdditive auditPhiRelation

private lemma audit_bad_count_le :
    countWhere (fun q => auditAdditive q ∧ ¬ auditPhiRelation q) ≤
      4 * auditH * auditCard ^ 3 := by
  calc
    countWhere (fun q => auditAdditive q ∧ ¬ auditPhiRelation q) ≤
        countWhere (fun q : Fin 4 → AuditX => ∃ i, (q i).1 = 5) := by
      apply countWhere_mono
      intro q hq
      by_contra hhit
      have hnone : ∀ i, (q i).1 ≠ 5 := by
        simpa only [not_exists] using hhit
      apply hq.2
      unfold auditPhiRelation
      exact audit_phi_good_without_exception q hnone
    _ ≤ 4 * auditH * auditCard ^ 3 := audit_hits_exception_count_le

private lemma audit_Q_pos : 0 < auditQ := by
  norm_num [auditQ]

private lemma audit_H_pos : 0 < auditH := by
  unfold auditH
  exact Nat.mul_pos (by omega) (pow_pos audit_Q_pos 2)

private lemma audit_card_le_five_L : auditCard ≤ 5 * auditL := by
  have hQ : 1 ≤ auditQ := audit_Q_pos
  have hH : 1 ≤ auditH := audit_H_pos
  have hthree : 3 ≤ 1000 * auditQ := by
    calc
      3 ≤ 1000 := by omega
      _ ≤ 1000 * auditQ := Nat.mul_le_mul_left 1000 hQ
  have hsmall : 1 + 2 * auditH ≤ auditL := by
    calc
      1 + 2 * auditH ≤ 3 * auditH := by omega
      _ ≤ (1000 * auditQ) * auditH :=
        Nat.mul_le_mul_right auditH hthree
      _ = auditL := by simp [auditL, mul_assoc]
  unfold auditCard
  omega

private lemma audit_bad_numeric_nat :
    auditQ * (4 * auditH * auditCard ^ 3) ≤ auditL ^ 4 := by
  have hCpow : auditCard ^ 3 ≤ (5 * auditL) ^ 3 := by
    gcongr
    exact audit_card_le_five_L
  have hcoeff : 500 * auditQ * auditH ≤ auditL := by
    rw [auditL]
    have h := Nat.mul_le_mul_right (auditQ * auditH)
      (show 500 ≤ 1000 by omega)
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  calc
    auditQ * (4 * auditH * auditCard ^ 3) ≤
        auditQ * (4 * auditH * (5 * auditL) ^ 3) := by
      exact Nat.mul_le_mul_left auditQ (Nat.mul_le_mul_left (4 * auditH) hCpow)
    _ = (500 * auditQ * auditH) * auditL ^ 3 := by ring
    _ ≤ auditL * auditL ^ 3 := Nat.mul_le_mul_right (auditL ^ 3) hcoeff
    _ = auditL ^ 4 := by ring

private lemma audit_bad_numeric :
    ((4 * auditH * auditCard ^ 3 : Nat) : Real) ≤
      auditEta * (auditL ^ 4 : Nat) := by
  have hQreal : (0 : Real) < auditQ := by exact_mod_cast audit_Q_pos
  have hcast : ((auditQ * (4 * auditH * auditCard ^ 3) : Nat) : Real) ≤
      ((auditL ^ 4 : Nat) : Real) := by
    exact_mod_cast audit_bad_numeric_nat
  dsimp only [auditEta]
  rw [one_div, inv_mul_eq_div]
  apply (le_div_iff₀ hQreal).2
  simpa only [Nat.cast_mul, mul_comm] using hcast

private lemma audit_approx_hom :
    DomainApproxHomOfOrder auditDomain auditPhi auditEta 2 := by
  have hpartNat := audit_additive_partition
  have hpart : (countWhere auditAdditive : Real) =
      countWhere (fun q => auditAdditive q ∧ auditPhiRelation q) +
        countWhere (fun q => auditAdditive q ∧ ¬ auditPhiRelation q) := by
    exact_mod_cast hpartNat
  have hbad :
      (countWhere (fun q => auditAdditive q ∧ ¬ auditPhiRelation q) : Real) ≤
      (4 * auditH * auditCard ^ 3 : Nat) := by
    exact_mod_cast audit_bad_count_le
  have hcore : (((auditL ^ 4 : Nat) : Real)) ≤ countWhere auditAdditive := by
    rw [← audit_domain_count_eq]
    exact_mod_cast audit_additive_count_lower
  have heta : 0 ≤ auditEta := by
    norm_num [auditEta, auditQ]
  have hbadEta :
      (countWhere (fun q => auditAdditive q ∧ ¬ auditPhiRelation q) : Real) ≤
      auditEta * countWhere auditAdditive := by
    calc
      (countWhere (fun q => auditAdditive q ∧ ¬ auditPhiRelation q) : Real) ≤
          (4 * auditH * auditCard ^ 3 : Nat) := hbad
      _ ≤ auditEta * (auditL ^ 4 : Nat) := audit_bad_numeric
      _ ≤ auditEta * countWhere auditAdditive :=
        mul_le_mul_of_nonneg_left hcore heta
  unfold DomainApproxHomOfOrder
  rw [audit_domain_count_eq, audit_phi_count_eq]
  change (1 - auditEta) * (countWhere auditAdditive : Real) ≤
    (countWhere (fun q => auditAdditive q ∧ auditPhiRelation q) : Real)
  linarith

private lemma audit_L_pos : 0 < auditL := by
  unfold auditL
  exact Nat.mul_pos (Nat.mul_pos (by omega) audit_Q_pos) audit_H_pos

private lemma audit_card_pos : 0 < auditCard := by
  unfold auditCard
  omega

private lemma audit_M_pos : 0 < auditM := by
  rw [auditM]
  exact pow_pos audit_card_pos 2

private lemma audit_alpha_eq :
    auditAlpha = 1 / (8 * (auditCard : Real)) := by
  have hC : (auditCard : Real) ≠ 0 := by exact_mod_cast audit_card_pos.ne'
  dsimp only [auditAlpha]
  rw [auditM]
  push_cast
  field_simp

private lemma audit_sigma_mul_M : auditSigma * auditM = 1 := by
  have hM : (auditM : Real) ≠ 0 := by exact_mod_cast audit_M_pos.ne'
  dsimp only [auditSigma]
  field_simp

private lemma audit_domain_bounds :
    Section10DomainBounds auditDomain auditAlpha auditM := by
  have hC : (0 : Real) < auditCard := by exact_mod_cast audit_card_pos
  have hC1 : (1 : Nat) ≤ auditCard := audit_card_pos
  have hC1R : (1 : Real) ≤ auditCard := by exact_mod_cast hC1
  have hHC : auditH ≤ auditCard := by
    unfold auditCard
    omega
  have hLC : auditL ≤ auditCard := by
    unfold auditCard
    omega
  have hCM : auditCard ≤ auditM := by
    rw [auditM]
    nlinarith
  refine ⟨?_, ?_, audit_M_pos, ?_, ?_⟩
  · rw [audit_alpha_eq]
    positivity
  · rw [audit_alpha_eq]
    apply (div_le_one (by positivity : (0 : Real) < 8 * auditCard)).2
    nlinarith
  · rw [audit_card_X]
    dsimp only [auditAlpha]
    have hM : (auditM : Real) ≠ 0 := by exact_mod_cast audit_M_pos.ne'
    norm_num only [Nat.cast_ofNat, Nat.cast_mul]
    field_simp
  · intro s
    rw [audit_fibre_card]
    have hHM : auditH ≤ auditM := hHC.trans hCM
    have hLM : auditL ≤ auditM := hLC.trans hCM
    unfold auditProfile
    split_ifs <;> omega

private lemma audit_symmetric : IsSymmetricModSet auditB := by
  intro d
  have hneg : -(4 : ZMod 8) = 4 := by decide
  simp only [auditB, Finset.mem_singleton]
  constructor
  · rintro rfl
    exact hneg
  · intro hd
    calc
      d = -(-d) := (neg_neg d).symm
      _ = -4 := congrArg Neg.neg hd
      _ = 4 := hneg

private lemma audit_profile_shift_four (s : ZMod 8) :
    auditProfile (s + 4) = auditProfile s ∨
      (auditProfile (s + 4) = 0 ∧ auditProfile s = 1) ∨
      (auditProfile (s + 4) = 1 ∧ auditProfile s = 0) := by
  fin_cases s <;> decide

private lemma audit_invariant :
    DomainInvariant auditDomain auditB (auditSigma * auditM) := by
  intro s d hd
  simp only [auditB, Finset.mem_singleton] at hd
  subst d
  rw [audit_sigma_mul_M]
  simp only [audit_fibre_card]
  rcases audit_profile_shift_four s with hEq | h01 | h10
  · rw [hEq]
    norm_num
  · rw [h01.1, h01.2]
    norm_num
  · rw [h10.1, h10.2]
    norm_num

private lemma audit_setup :
    Section10Setup auditDomain auditPhi auditB auditAlpha auditM
      auditSigma auditEta := by
  have heta0 : 0 ≤ auditEta := by
    dsimp only [auditEta]
    have hQ : (0 : Real) < auditQ := by exact_mod_cast audit_Q_pos
    positivity
  have heta1 : auditEta ≤ 1 := by
    dsimp only [auditEta]
    apply (div_le_one (by exact_mod_cast audit_Q_pos)).2
    exact_mod_cast audit_Q_pos
  have hsigma : 0 < auditSigma := by
    dsimp only [auditSigma]
    have hM : (0 : Real) < auditM := by exact_mod_cast audit_M_pos
    positivity
  exact ⟨audit_domain_bounds, hsigma, heta0, heta1, audit_symmetric,
    audit_invariant, audit_approx_hom⟩

private lemma audit_fibreSize_x0 : auditDomain.fibreSize auditX0 = 1 := by
  rw [audit_fibreSize]
  exact auditProfile_zero

private lemma audit_anchor_fibre_scale :
    auditAlpha ^ 2 * auditM / 2 = (1 : Real) / 128 := by
  have hC : (auditCard : Real) ≠ 0 := by exact_mod_cast audit_card_pos.ne'
  rw [audit_alpha_eq, auditM]
  push_cast
  field_simp
  ring

private lemma audit_anchor_weight_scale :
    auditAlpha ^ 3 * auditM ^ 3 * (8 : Nat) ^ 2 / 4 =
      (auditCard : Real) ^ 3 / 32 := by
  have hC : (auditCard : Real) ≠ 0 := by exact_mod_cast audit_card_pos.ne'
  rw [audit_alpha_eq, auditM]
  norm_num only [Nat.cast_ofNat, Nat.cast_pow]
  field_simp
  ring

private lemma audit_weightedError_zero :
    domainWeightedError auditDomain auditPhi auditB auditX0 = 0 := by
  unfold domainWeightedError
  simp only [audit_proportionateError_zero, zero_mul, Finset.sum_const_zero]

private lemma audit_anchor_fibre_bound :
    auditAlpha ^ 2 * auditM / 2 ≤ auditDomain.fibreSize auditX0 := by
  rw [audit_fibreSize_x0, audit_anchor_fibre_scale]
  norm_num

private lemma audit_card_le_five_L_real :
    (auditCard : Real) ≤ 5 * auditL := by
  have h := audit_card_le_five_L
  exact_mod_cast h

private lemma audit_card_cube_le :
    (auditCard : Real) ^ 3 ≤ (5 * (auditL : Real)) ^ 3 :=
  pow_le_pow_left₀ (by positivity) audit_card_le_five_L_real 3

private lemma audit_fiveL_cube_div_le :
    (5 * (auditL : Real)) ^ 3 / 32 ≤ 4 * auditL ^ 3 := by
  have hL3 : (0 : Real) ≤ (auditL : Real) ^ 3 := by positivity
  have hcoef : (125 : Real) * auditL ^ 3 ≤ 128 * auditL ^ 3 :=
    mul_le_mul_of_nonneg_right (by norm_num) hL3
  calc
    (5 * (auditL : Real)) ^ 3 / 32 =
        125 * (auditL : Real) ^ 3 / (32 : Real) := by ring
    _ ≤ 128 * (auditL : Real) ^ 3 / (32 : Real) :=
      div_le_div_of_nonneg_right hcoef (by norm_num : (0 : Real) ≤ 32)
    _ = 4 * (auditL : Real) ^ 3 := by ring

private lemma audit_totalWeight_lower_real :
    (4 * auditL ^ 3 : Real) ≤ domainTotalWeight auditDomain auditX0 := by
  have h := audit_totalWeight_lower
  exact_mod_cast h

private lemma audit_anchor_weight_bound :
    auditAlpha ^ 3 * auditM ^ 3 * (8 : Nat) ^ 2 / 4 ≤
      domainTotalWeight auditDomain auditX0 := by
  rw [audit_anchor_weight_scale]
  exact (div_le_div_of_nonneg_right audit_card_cube_le (by norm_num)).trans
    (audit_fiveL_cube_div_le.trans audit_totalWeight_lower_real)

private lemma audit_anchor_error_bound :
    domainWeightedError auditDomain auditPhi auditB auditX0 ≤
      60 * auditEta * domainTotalWeight auditDomain auditX0 := by
  rw [audit_weightedError_zero]
  positivity

private lemma audit_anchor :
    IsSection10Anchor auditDomain auditPhi auditB auditAlpha auditM 8
      auditEta auditX0 :=
  ⟨audit_anchor_fibre_bound, audit_anchor_weight_bound,
    audit_anchor_error_bound⟩

private lemma audit_fibreSaturated :
    auditDomain.FibreSaturated auditW := by
  intro y hy z hzy
  rw [audit_mem_W] at hy ⊢
  change z.1 = y.1 at hzy
  simpa [hzy] using hy

private lemma audit_weight_varies :
    VariesByFactorAtMostTwo auditW
      (fun y => domainDifferenceWeight auditDomain auditX0 y) := by
  intro y hy z hz
  dsimp only
  rw [audit_differenceWeight_eq_of_mem_W hy hz]
  omega

private lemma audit_error_almostEvery :
    AlmostEvery (1 - 5 * auditEta ^ ((1 : Real) / 5)) auditW
      (fun y => domainProportionateError auditDomain auditPhi auditB auditX0 y ≤
        300 * auditEta ^ ((4 : Real) / 5)) := by
  unfold AlmostEvery
  rw [Finset.filter_eq_self.2]
  · have hroot : 0 ≤ auditEta ^ ((1 : Real) / 5) := by positivity
    have hcard : 0 ≤ (auditW.card : Real) := by positivity
    nlinarith
  · intro y hy
    rw [audit_proportionateError_zero]
    positivity

private lemma audit_regular_card_scale :
    auditRho ^ 2 * auditAlpha ^ 2 * auditM * (8 : Nat) / 16 =
      (2 * auditH : Nat) := by
  have hC : (auditCard : Real) ≠ 0 := by
    exact_mod_cast audit_card_pos.ne'
  rw [audit_alpha_eq, auditM]
  norm_num only [Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow]
  dsimp only [auditRho]
  rw [auditH]
  push_cast
  field_simp
  ring

private lemma audit_regular_card_bound :
    auditRho ^ 2 * auditAlpha ^ 2 * auditM * (8 : Nat) / 16 ≤
      auditW.card := by
  rw [audit_regular_card_scale, audit_card_W]

private lemma audit_fibreSize_varies :
    VariesByFactorAtMostTwo auditW auditDomain.fibreSize := by
  intro y hy z hz
  rw [audit_fibreSize_eq_H hy, audit_fibreSize_eq_H hz]
  omega

private lemma audit_regular_fibre_scale :
    auditAlpha ^ 2 * auditM / 16 = (1 : Real) / 1024 := by
  have hC : (auditCard : Real) ≠ 0 := by
    exact_mod_cast audit_card_pos.ne'
  rw [audit_alpha_eq, auditM]
  push_cast
  field_simp
  ring

private lemma audit_regular_fibre_bound (y : AuditX) (hy : y ∈ auditW) :
    auditAlpha ^ 2 * auditM / 16 ≤ auditDomain.fibreSize y := by
  rw [audit_regular_fibre_scale, audit_fibreSize_eq_H hy]
  have hH : (1 : Real) ≤ auditH := by exact_mod_cast audit_H_pos
  linarith

private def auditOne : AuditX :=
  ⟨1, ⟨0, by rw [auditProfile_one]; exact audit_H_pos⟩⟩

private def auditFive : AuditX :=
  ⟨5, ⟨0, by rw [auditProfile_five]; exact audit_H_pos⟩⟩

@[simp] private lemma auditOne_index : auditOne.1 = (1 : ZMod 8) := rfl

@[simp] private lemma auditFive_index : auditFive.1 = (5 : ZMod 8) := rfl

private lemma auditOne_mem : auditOne ∈ auditW := by
  rw [audit_mem_W]
  exact Or.inl rfl

private lemma auditFive_mem : auditFive ∈ auditW := by
  rw [audit_mem_W]
  exact Or.inr rfl

private lemma audit_shift_four : auditDomain.shift auditW 4 = auditW := by
  ext y
  simp only [MultifunctionDomain.shift, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨w, hw, hwy⟩
    rw [audit_mem_W] at hw ⊢
    change y.1 = w.1 + 4 at hwy
    rcases hw with hw | hw
    · right
      calc
        y.1 = w.1 + 4 := hwy
        _ = 1 + 4 := by rw [hw]
        _ = 5 := by decide
    · left
      calc
        y.1 = w.1 + 4 := hwy
        _ = 5 + 4 := by rw [hw]
        _ = 1 := by decide
  · rw [audit_mem_W]
    rintro (hy | hy)
    · refine ⟨auditFive, auditFive_mem, ?_⟩
      change y.1 = auditFive.1 + 4
      rw [hy]
      decide
    · refine ⟨auditOne, auditOne_mem, ?_⟩
      change y.1 = auditOne.1 + 4
      rw [hy]
      decide

private lemma audit_overlap :
    ∀ d, d ∈ auditB →
      (1 - auditEta) * auditW.card ≤
        (auditW ∩ auditDomain.shift auditW d).card := by
  intro d hd
  simp only [auditB, Finset.mem_singleton] at hd
  subst d
  rw [audit_shift_four, Finset.inter_self]
  have heta : 0 ≤ auditEta := by positivity
  have hcard : 0 ≤ (auditW.card : Real) := by positivity
  nlinarith

private lemma audit_regular :
    IsSection10RegularComponent auditDomain auditPhi auditB auditX0
      auditAlpha auditEta auditRho auditM 8 auditW :=
  ⟨audit_fibreSaturated, audit_weight_varies, audit_error_almostEvery,
    audit_regular_card_bound, audit_fibreSize_varies,
    audit_regular_fibre_bound, audit_overlap⟩

private lemma audit_sigma_bound :
    auditSigma ≤ auditEta * auditRho * auditAlpha ^ 2 / 16 := by
  have hQ : (auditQ : Real) ≠ 0 := by exact_mod_cast audit_Q_pos.ne'
  have hC : (auditCard : Real) ≠ 0 := by exact_mod_cast audit_card_pos.ne'
  rw [audit_alpha_eq]
  dsimp only [auditSigma, auditEta, auditRho]
  rw [auditM]
  push_cast
  field_simp
  norm_num

private lemma audit_eta_eq_pow :
    auditEta = ((1 : Real) / 32) ^ 5 := by
  norm_num [auditEta, auditQ]

private lemma audit_eta_root :
    auditEta ^ ((1 : Real) / 5) = (1 : Real) / 32 := by
  rw [audit_eta_eq_pow]
  simpa [show (1 : Real) / 5 = ((5 : Nat) : Real)⁻¹ by norm_num] using
    (Real.pow_rpow_inv_natCast (x := (1 : Real) / 32) (n := 5)
      (by positivity) (by norm_num))

private lemma audit_theta_eq :
    10 * auditEta ^ ((1 : Real) / 5) = (5 : Real) / 16 := by
  rw [audit_eta_root]
  norm_num

private lemma audit_one_sub_theta_pos :
    0 < 1 - 10 * auditEta ^ ((1 : Real) / 5) := by
  rw [audit_theta_eq]
  norm_num

private lemma exists_of_almostEvery_of_pos {Y : Type*} [DecidableEq Y]
    {p : Real} {U : Finset Y} {P : Y → Prop}
    (hp : 0 < p) (hU : U.Nonempty) (hAE : AlmostEvery p U P) :
    ∃ y, y ∈ U ∧ P y := by
  classical
  unfold AlmostEvery at hAE
  have hUcard : 0 < (U.card : Real) := by
    exact_mod_cast Finset.card_pos.mpr hU
  have hfilterCard : 0 < ((U.filter P).card : Real) :=
    (mul_pos hp hUcard).trans_le hAE
  have hfilterCardNat : 0 < (U.filter P).card := by
    exact_mod_cast hfilterCard
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hfilterCardNat
  exact ⟨y, (Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2⟩

private lemma audit_shifted_fibre_card_one {w : AuditX} (hw : w.1 = 1) :
    (auditDomain.fibre (auditDomain.index w + 4)).card = auditH := by
  rw [audit_fibre_card]
  change auditProfile (w.1 + 4) = auditH
  rw [hw]
  exact auditProfile_five

private lemma audit_shifted_fibre_card_five {w : AuditX} (hw : w.1 = 5) :
    (auditDomain.fibre (auditDomain.index w + 4)).card = auditH := by
  rw [audit_fibre_card]
  change auditProfile (w.1 + 4) = auditH
  rw [hw]
  exact auditProfile_one

private lemma audit_difference_at_one {w z : AuditX} (hw : w.1 = 1)
    (hz : z ∈ auditDomain.fibre (auditDomain.index w + 4)) :
    auditPhi z - auditPhi w = 1 := by
  have hzIndex : z.1 = w.1 + 4 := by
    simpa only [MultifunctionDomain.fibre, Finset.mem_filter,
      Finset.mem_univ, true_and, auditDomain] using hz
  have hzFive : z.1 = 5 := by
    calc
      z.1 = w.1 + 4 := hzIndex
      _ = 1 + 4 := by rw [hw]
      _ = 5 := by decide
  have hwNe : w.1 ≠ 5 := by rw [hw]; decide
  unfold auditPhi
  rw [if_pos hzFive, if_neg hwNe]
  decide

private lemma audit_difference_at_five {w z : AuditX} (hw : w.1 = 5)
    (hz : z ∈ auditDomain.fibre (auditDomain.index w + 4)) :
    auditPhi z - auditPhi w = 7 := by
  have hzIndex : z.1 = w.1 + 4 := by
    simpa only [MultifunctionDomain.fibre, Finset.mem_filter,
      Finset.mem_univ, true_and, auditDomain] using hz
  have hzOne : z.1 = 1 := by
    calc
      z.1 = w.1 + 4 := hzIndex
      _ = 5 + 4 := by rw [hw]
      _ = 1 := by decide
  have hzNe : z.1 ≠ 5 := by rw [hzOne]; decide
  unfold auditPhi
  rw [if_neg hzNe, if_pos hw]
  decide

private lemma audit_inner_forces_one (psi : ZMod 8 → ZMod 8) {w : AuditX}
    (hw : w.1 = 1)
    (hinner : AlmostEvery (1 - 10 * auditEta ^ ((1 : Real) / 5))
      (auditDomain.fibre (auditDomain.index w + 4))
      (fun z => auditPhi z - auditPhi w = psi 4)) :
    psi 4 = 1 := by
  have hnonempty :
      (auditDomain.fibre (auditDomain.index w + 4)).Nonempty := by
    apply Finset.card_pos.mp
    rw [audit_shifted_fibre_card_one hw]
    exact audit_H_pos
  obtain ⟨z, hz, hzRelation⟩ := exists_of_almostEvery_of_pos
    audit_one_sub_theta_pos hnonempty hinner
  rw [audit_difference_at_one hw hz] at hzRelation
  exact hzRelation.symm

private lemma audit_inner_forces_five (psi : ZMod 8 → ZMod 8) {w : AuditX}
    (hw : w.1 = 5)
    (hinner : AlmostEvery (1 - 10 * auditEta ^ ((1 : Real) / 5))
      (auditDomain.fibre (auditDomain.index w + 4))
      (fun z => auditPhi z - auditPhi w = psi 4)) :
    psi 4 = 7 := by
  have hnonempty :
      (auditDomain.fibre (auditDomain.index w + 4)).Nonempty := by
    apply Finset.card_pos.mp
    rw [audit_shifted_fibre_card_five hw]
    exact audit_H_pos
  obtain ⟨z, hz, hzRelation⟩ := exists_of_almostEvery_of_pos
    audit_one_sub_theta_pos hnonempty hinner
  rw [audit_difference_at_five hw hz] at hzRelation
  exact hzRelation.symm

private lemma audit_no_local_difference_model :
    ¬ ∃ B' : Finset (ZMod 8), ∃ psi : ZMod 8 → ZMod 8,
      IsSection10LocalDifferenceModel auditDomain auditPhi auditW auditB B' psi
        (10 * auditEta ^ ((1 : Real) / 5)) := by
  classical
  rintro ⟨B', psi, hsubsetB, hlarge, hlocal⟩
  have hlarge' : (11 : Real) / 16 ≤ (B'.card : Real) := by
    rw [audit_theta_eq] at hlarge
    have hBcard : auditB.card = 1 := by simp [auditB]
    rw [hBcard] at hlarge
    norm_num at hlarge ⊢
    linarith
  have hcardPosReal : 0 < (B'.card : Real) := by
    linarith [hlarge']
  have hcardPos : 0 < B'.card := by exact_mod_cast hcardPosReal
  obtain ⟨d, hd⟩ := Finset.card_pos.mp hcardPos
  have hdB := hsubsetB hd
  have hdEq : d = 4 := by simpa [auditB] using hdB
  subst d
  have hfour : (4 : ZMod 8) ∈ B' := hd
  let Good : AuditX → Prop := fun w =>
    AlmostEvery (1 - 10 * auditEta ^ ((1 : Real) / 5))
      (auditDomain.fibre (auditDomain.index w + 4))
      (fun z => auditPhi z - auditPhi w = psi 4)
  have houter :
      AlmostEvery (1 - 10 * auditEta ^ ((1 : Real) / 5)) auditW Good := by
    simpa [Good] using hlocal 4 hfour
  have hgoodCard : (auditW.filter Good).card ≤ auditH := by
    by_cases hpsi : psi 4 = 1
    · calc
        (auditW.filter Good).card ≤ (auditDomain.fibre 1).card := by
          apply Finset.card_le_card
          intro w hwGood
          have hwParts := Finset.mem_filter.mp hwGood
          have hwW := hwParts.1
          have hwInner := hwParts.2
          dsimp only [Good] at hwInner
          rcases (audit_mem_W w).mp hwW with hwOne | hwFive
          · simp only [MultifunctionDomain.fibre, Finset.mem_filter,
              Finset.mem_univ, true_and, auditDomain]
            exact hwOne
          · have hseven := audit_inner_forces_five psi hwFive hwInner
            have hbad : (1 : ZMod 8) = 7 := hpsi.symm.trans hseven
            exact ((by decide : (1 : ZMod 8) ≠ 7) hbad).elim
        _ = auditH := by rw [audit_fibre_card, auditProfile_one]
    · calc
        (auditW.filter Good).card ≤ (auditDomain.fibre 5).card := by
          apply Finset.card_le_card
          intro w hwGood
          have hwParts := Finset.mem_filter.mp hwGood
          have hwW := hwParts.1
          have hwInner := hwParts.2
          dsimp only [Good] at hwInner
          rcases (audit_mem_W w).mp hwW with hwOne | hwFive
          · exact (hpsi (audit_inner_forces_one psi hwOne hwInner)).elim
          · simp only [MultifunctionDomain.fibre, Finset.mem_filter,
              Finset.mem_univ, true_and, auditDomain]
            exact hwFive
        _ = auditH := by rw [audit_fibre_card, auditProfile_five]
  unfold AlmostEvery at houter
  rw [audit_theta_eq, audit_card_W] at houter
  have houterLower :
      (11 : Real) / 8 * auditH ≤ ((auditW.filter Good).card : Real) := by
    calc
      (11 : Real) / 8 * auditH =
          (1 - (5 : Real) / 16) * ((2 * auditH : Nat) : Real) := by
        push_cast
        ring
      _ ≤ ((auditW.filter Good).card : Real) := houter
  have hgoodCardReal : ((auditW.filter Good).card : Real) ≤ auditH := by
    exact_mod_cast hgoodCard
  have hHReal : (0 : Real) < auditH := by exact_mod_cast audit_H_pos
  linarith

/-- The hypotheses in the live, uncorrected statement of Lemma 10.6 have a
finite model in which no asserted local difference model exists. -/
theorem lemma_10_6_counterexample :
    Section10Setup auditDomain auditPhi auditB auditAlpha auditM
        auditSigma auditEta ∧
      IsSection10Anchor auditDomain auditPhi auditB auditAlpha auditM 8
        auditEta auditX0 ∧
      IsSection10RegularComponent auditDomain auditPhi auditB auditX0
        auditAlpha auditEta auditRho auditM 8 auditW ∧
      auditSigma ≤ auditEta * auditRho * auditAlpha ^ 2 / 16 ∧
      ¬ ∃ B' : Finset (ZMod 8), ∃ psi : ZMod 8 → ZMod 8,
        IsSection10LocalDifferenceModel auditDomain auditPhi auditW auditB B' psi
          (10 * auditEta ^ ((1 : Real) / 5)) :=
  ⟨audit_setup, audit_anchor, audit_regular, audit_sigma_bound,
    audit_no_local_difference_model⟩

/-! ## Companion proof for the corrected statement -/

private lemma extraction_almostEvery_bad_card_le {Y : Type*}
    [DecidableEq Y] (a : Real) (U : Finset Y) (P : Y → Prop)
    [DecidablePred P] (hP : AlmostEvery (1 - a) U P) :
    ((U.filter fun y => ¬ P y).card : Real) ≤ a * U.card := by
  classical
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) +
          ((U.filter fun y => ¬ P y).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery at hP
  rw [Finset.filter_congr_decidable] at hP
  linarith

private lemma extraction_bad_card_lt_of_not_almostEvery {Y : Type*}
    [DecidableEq Y] (a : Real) (U : Finset Y) (P : Y → Prop)
    [DecidablePred P] (hP : ¬ AlmostEvery (1 - a) U P) :
    a * U.card < ((U.filter fun y => ¬ P y).card : Real) := by
  classical
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) +
          ((U.filter fun y => ¬ P y).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery at hP
  rw [Finset.filter_congr_decidable] at hP
  push Not at hP
  linarith

private lemma extraction_almostEvery_of_bad_card_le {Y : Type*}
    [DecidableEq Y] (a : Real) (U : Finset Y) (P : Y → Prop)
    [DecidablePred P]
    (hbad : ((U.filter fun y => ¬ P y).card : Real) ≤ a * U.card) :
    AlmostEvery (1 - a) U P := by
  classical
  have hpartNat := Finset.card_filter_add_card_filter_not P (s := U)
  have hpart :
      ((U.filter P).card : Real) +
          ((U.filter fun y => ¬ P y).card : Real) = U.card := by
    exact_mod_cast hpartNat
  unfold AlmostEvery
  rw [Finset.filter_congr_decidable]
  linarith

private lemma extraction_almostEvery_of_nonpos {Y : Type*}
    [DecidableEq Y] (p : Real) (U : Finset Y) (P : Y → Prop)
    (hp : p ≤ 0) : AlmostEvery p U P := by
  classical
  unfold AlmostEvery
  exact (mul_nonpos_of_nonpos_of_nonneg hp (by positivity)).trans (by positivity)

private noncomputable def extractionBadPairs {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (x w : X) (d : ZMod N) : Finset (X × X) :=
  ((D.fibre (D.index x + d)).product
      (D.fibre (D.index w + d))).filter fun yz =>
    phi yz.1 - phi x ≠ phi yz.2 - phi w

private def extractionDirectionGood {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (x w : X) (d : ZMod N) (t : Real) : Prop :=
  AlmostEvery (1 - 35 * t ^ 2)
    ((D.fibre (D.index x + d)).product (D.fibre (D.index w + d)))
    (fun yz => phi yz.1 - phi x = phi yz.2 - phi w)

private lemma extraction_restricted_ite_eq_sum {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (B : Finset (ZMod N)) (x w : X)
    (uv : X × X) :
    (if D.index uv.1 - D.index x = D.index uv.2 - D.index w ∧
        D.index uv.1 - D.index x ∈ B then 1 else 0) =
      ∑ d ∈ B, if D.index uv.1 = D.index x + d ∧
        D.index uv.2 = D.index w + d then 1 else 0 := by
  classical
  by_cases hrel : D.index uv.1 - D.index x =
      D.index uv.2 - D.index w ∧ D.index uv.1 - D.index x ∈ B
  · rw [if_pos hrel]
    let d₀ : ZMod N := D.index uv.1 - D.index x
    have hd₀ : d₀ ∈ B := hrel.2
    rw [Finset.sum_eq_single d₀]
    · have hu : D.index uv.1 = D.index x + d₀ := by
        dsimp only [d₀]
        abel
      have hv : D.index uv.2 = D.index w + d₀ := by
        dsimp only [d₀]
        linear_combination hrel.1.symm
      simp [hu, hv]
    · intro d hd hdne
      rw [if_neg]
      intro huv
      apply hdne
      dsimp only [d₀]
      linear_combination huv.1.symm
    · exact fun hd₀not => (hd₀not hd₀).elim
  · rw [if_neg hrel]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro huv
    apply hrel
    constructor
    · rw [huv.1, huv.2]
      abel
    · have hu : D.index uv.1 - D.index x = d := by
        rw [huv.1]
        abel
      rw [hu]
      exact hd

private lemma extraction_error_ite_eq_sum {N : Nat} {X : Type*}
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (x w : X) (uv : X × X) :
    (if D.index uv.1 - D.index x = D.index uv.2 - D.index w ∧
        D.index uv.1 - D.index x ∈ B ∧
        (phi uv.1 - phi x != phi uv.2 - phi w) = true then 1 else 0) =
      ∑ d ∈ B, if D.index uv.1 = D.index x + d ∧
        D.index uv.2 = D.index w + d ∧
        (phi uv.1 - phi x != phi uv.2 - phi w) = true then 1 else 0 := by
  classical
  by_cases hphi : (phi uv.1 - phi x != phi uv.2 - phi w) = true
  · simp only [hphi, and_true]
    exact extraction_restricted_ite_eq_sum D B x w uv
  · simp [hphi]

private lemma extraction_restrictedWeight_eq_sum {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (x w : X) :
    domainRestrictedDifferenceWeight D B x w =
      ∑ d ∈ B, (D.fibre (D.index x + d)).card *
        (D.fibre (D.index w + d)).card := by
  classical
  unfold domainRestrictedDifferenceWeight
  rw [audit_countWhere_eq_sum_ite]
  simp_rw [extraction_restricted_ite_eq_sum D B x w]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← audit_countWhere_eq_sum_ite]
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  rw [show (Finset.univ.filter fun uv : X × X =>
      D.index uv.1 = D.index x + d ∧ D.index uv.2 = D.index w + d) =
      (D.fibre (D.index x + d)).product
        (D.fibre (D.index w + d)) by
    ext uv
    simp [MultifunctionDomain.fibre]]
  simp

private lemma extraction_errorCount_eq_sum {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N)) (x w : X) :
    domainDifferenceErrorCount D phi B x w =
      ∑ d ∈ B, (extractionBadPairs D phi x w d).card := by
  classical
  unfold domainDifferenceErrorCount
  rw [audit_countWhere_eq_sum_ite]
  simp_rw [extraction_error_ite_eq_sum D phi B x w]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← audit_countWhere_eq_sum_ite]
  unfold countWhere extractionBadPairs
  rw [Finset.filter_congr_decidable]
  congr 1
  ext uv
  simp [MultifunctionDomain.fibre, and_assoc]

private lemma extraction_sigma_le_alpha_sq_div_64 {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N))
    (alpha rho : Real) (M : Nat) (sigma eta : Real)
    (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hrho : rho ≤ alpha ^ 2 / 32)
    (hsigma : sigma ≤ eta * rho * alpha ^ 2 / 16) :
    sigma ≤ alpha ^ 2 / 64 := by
  rcases hsetup with ⟨⟨halpha, halphaOne, _hM, _hcard, _hfibre⟩,
    hsigmaPos, heta, hetaOne, _hsym, _hinv, _happrox⟩
  have hpositive : 0 < eta * rho * alpha ^ 2 / 16 :=
    hsigmaPos.trans_le hsigma
  have hmulPositive : 0 < eta * rho * alpha ^ 2 := by linarith
  have hetaRhoPositive : 0 < eta * rho := by
    rcases (mul_pos_iff.mp hmulPositive) with h | h
    · exact h.1
    · exact (not_lt_of_ge (sq_nonneg alpha) h.2).elim
  have hrhoPositive : 0 < rho := by
    rcases (mul_pos_iff.mp hetaRhoPositive) with h | h
    · exact h.2
    · exact (not_lt_of_ge heta h.1).elim
  have hetaRhoUpper : eta * rho ≤ alpha ^ 2 / 32 := by
    exact (mul_le_of_le_one_left hrhoPositive.le hetaOne).trans hrho
  have halphaSqOne : alpha ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr halphaOne)
      (show 0 ≤ 1 + alpha by linarith)]
  have halphaFourth : alpha ^ 2 * alpha ^ 2 ≤ alpha ^ 2 :=
    mul_le_of_le_one_right (sq_nonneg alpha) halphaSqOne
  calc
    sigma ≤ eta * rho * alpha ^ 2 / 16 := hsigma
    _ ≤ (alpha ^ 2 / 32) * alpha ^ 2 / 16 := by
      gcongr
    _ ≤ alpha ^ 2 / 64 := by
      nlinarith

private lemma extraction_sigmaM_le_anchor_quarter {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N))
    (alpha rho : Real) (M : Nat) (sigma eta : Real) (x : X)
    (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hanchor : IsSection10Anchor D phi B alpha M N eta x)
    (hrho : rho ≤ alpha ^ 2 / 32)
    (hsigma : sigma ≤ eta * rho * alpha ^ 2 / 16) :
    sigma * M ≤ (D.fibreSize x : Real) / 4 := by
  have hs := extraction_sigma_le_alpha_sq_div_64 D phi B alpha rho M
    sigma eta hsetup hrho hsigma
  have hMnonneg : (0 : Real) ≤ M := by positivity
  have hsM : sigma * M ≤ alpha ^ 2 / 64 * M :=
    mul_le_mul_of_nonneg_right hs hMnonneg
  have hx := hanchor.1
  nlinarith

private lemma extraction_sigmaM_le_regular_quarter {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (B : Finset (ZMod N))
    (alpha rho : Real) (M N0 : Nat) (sigma eta : Real) (x w : X)
    (W : Finset X) (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hregular : IsSection10RegularComponent D phi B x alpha eta rho M N0 W)
    (hrho : rho ≤ alpha ^ 2 / 32)
    (hsigma : sigma ≤ eta * rho * alpha ^ 2 / 16)
    (hw : w ∈ W) :
    sigma * M ≤ (D.fibreSize w : Real) / 4 := by
  have hs := extraction_sigma_le_alpha_sq_div_64 D phi B alpha rho M
    sigma eta hsetup hrho hsigma
  have hMnonneg : (0 : Real) ≤ M := by positivity
  have hsM : sigma * M ≤ alpha ^ 2 / 64 * M :=
    mul_le_mul_of_nonneg_right hs hMnonneg
  have hwLower := hregular.2.2.2.2.2.1 w hw
  nlinarith

private lemma extraction_shifted_fibre_bounds {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (sigma : Real) (M : Nat) (u : X)
    (hinvariant : DomainInvariant D B (sigma * M))
    (hquarter : sigma * M ≤ (D.fibreSize u : Real) / 4)
    (d : ZMod N) (hd : d ∈ B) :
    (3 : Real) / 4 * D.fibreSize u ≤
        (D.fibre (D.index u + d)).card ∧
      ((D.fibre (D.index u + d)).card : Real) ≤
        (5 : Real) / 4 * D.fibreSize u := by
  have h := abs_le.mp (hinvariant (D.index u) d hd)
  unfold MultifunctionDomain.fibreSize at hquarter ⊢
  constructor <;> linarith

private lemma extraction_fibre_product_le_four {N : Nat} {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (B : Finset (ZMod N)) (sigma : Real) (M : Nat) (x w : X)
    (hinvariant : DomainInvariant D B (sigma * M))
    (hxQuarter : sigma * M ≤ (D.fibreSize x : Real) / 4)
    (hwQuarter : sigma * M ≤ (D.fibreSize w : Real) / 4)
    (d : ZMod N) (hd : d ∈ B) (e : ZMod N) (he : e ∈ B) :
    ((D.fibre (D.index x + d)).card : Real) *
        (D.fibre (D.index w + d)).card ≤
      4 * (((D.fibre (D.index x + e)).card : Real) *
        (D.fibre (D.index w + e)).card) := by
  have hxd := extraction_shifted_fibre_bounds D B sigma M x hinvariant
    hxQuarter d hd
  have hxe := extraction_shifted_fibre_bounds D B sigma M x hinvariant
    hxQuarter e he
  have hwd := extraction_shifted_fibre_bounds D B sigma M w hinvariant
    hwQuarter d hd
  have hwe := extraction_shifted_fibre_bounds D B sigma M w hinvariant
    hwQuarter e he
  have hxCompare : ((D.fibre (D.index x + d)).card : Real) ≤
      2 * (D.fibre (D.index x + e)).card := by linarith
  have hwCompare : ((D.fibre (D.index w + d)).card : Real) ≤
      2 * (D.fibre (D.index w + e)).card := by linarith
  calc
    ((D.fibre (D.index x + d)).card : Real) *
          (D.fibre (D.index w + d)).card ≤
        (2 * (D.fibre (D.index x + e)).card) *
          (D.fibre (D.index w + d)).card := by gcongr
    _ ≤ (2 * (D.fibre (D.index x + e)).card) *
          (2 * (D.fibre (D.index w + e)).card) := by gcongr
    _ = 4 * (((D.fibre (D.index x + e)).card : Real) *
          (D.fibre (D.index w + e)).card) := by ring

private lemma extraction_direction_good_almostEvery {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (B : Finset (ZMod N)) (alpha rho : Real) (M : Nat)
    (sigma eta t : Real) (x w : X) (W : Finset X)
    (hsetup : Section10Setup D phi B alpha M sigma eta)
    (hanchor : IsSection10Anchor D phi B alpha M N eta x)
    (hregular : IsSection10RegularComponent D phi B x alpha eta rho M N W)
    (hrho : rho ≤ alpha ^ 2 / 32)
    (hsigma : sigma ≤ eta * rho * alpha ^ 2 / 16)
    (ht : 0 < t) (hw : w ∈ W)
    (hwError : domainProportionateError D phi B x w ≤ 300 * t ^ 4) :
    AlmostEvery (1 - 35 * t ^ 2) B
      (fun d => extractionDirectionGood D phi x w d t) := by
  classical
  by_cases hBempty : B = ∅
  · subst B
    unfold AlmostEvery
    simp
  have hBnonempty : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr hBempty
  let P : ZMod N → Real := fun d =>
    ((D.fibre (D.index x + d)).card : Real) *
      (D.fibre (D.index w + d)).card
  let BadD : Finset (ZMod N) :=
    B.filter fun d => ¬ extractionDirectionGood D phi x w d t
  apply extraction_almostEvery_of_bad_card_le
  change (BadD.card : Real) ≤ 35 * t ^ 2 * B.card
  by_contra hBadBound
  have hBadGt : 35 * t ^ 2 * (B.card : Real) < BadD.card :=
    lt_of_not_ge hBadBound
  have hBadPositiveReal : 0 < (BadD.card : Real) := by
    exact (mul_nonneg (by positivity) (by positivity)).trans_lt hBadGt
  have hBadNonempty : BadD.Nonempty := by
    exact Finset.card_pos.mp (by exact_mod_cast hBadPositiveReal)
  obtain ⟨d₀, hd₀B, hd₀min⟩ := B.exists_min_image P hBnonempty
  have hxQuarter := extraction_sigmaM_le_anchor_quarter D phi B alpha rho M
    sigma eta x hsetup hanchor hrho hsigma
  have hwQuarter := extraction_sigmaM_le_regular_quarter D phi B alpha rho M N
    sigma eta x w W hsetup hregular hrho hsigma hw
  have hinvariant := hsetup.2.2.2.2.2.1
  have hprodCompare (d : ZMod N) (hd : d ∈ B) : P d ≤ 4 * P d₀ := by
    exact extraction_fibre_product_le_four D B sigma M x w hinvariant
      hxQuarter hwQuarter d hd d₀ hd₀B
  have hxBasePos : 0 < (D.fibreSize x : Real) := by
    have hM : (0 : Real) < M := by exact_mod_cast hsetup.1.2.2.1
    have halpha := hsetup.1.1
    exact (show 0 < alpha ^ 2 * M / 2 by positivity).trans_le hanchor.1
  have hwBasePos : 0 < (D.fibreSize w : Real) := by
    have hM : (0 : Real) < M := by exact_mod_cast hsetup.1.2.2.1
    have halpha := hsetup.1.1
    exact (show 0 < alpha ^ 2 * M / 16 by positivity).trans_le
      (hregular.2.2.2.2.2.1 w hw)
  have hxd₀ := extraction_shifted_fibre_bounds D B sigma M x hinvariant
    hxQuarter d₀ hd₀B
  have hwd₀ := extraction_shifted_fibre_bounds D B sigma M w hinvariant
    hwQuarter d₀ hd₀B
  have hxd₀Pos : 0 < ((D.fibre (D.index x + d₀)).card : Real) := by
    linarith
  have hwd₀Pos : 0 < ((D.fibre (D.index w + d₀)).card : Real) := by
    linarith
  have hP₀Pos : 0 < P d₀ := by
    dsimp only [P]
    positivity
  have hbEq : (domainRestrictedDifferenceWeight D B x w : Real) =
      ∑ d ∈ B, P d := by
    rw [extraction_restrictedWeight_eq_sum]
    push_cast
    rfl
  have hbUpper : (domainRestrictedDifferenceWeight D B x w : Real) ≤
      4 * (B.card : Real) * P d₀ := by
    rw [hbEq]
    calc
      (∑ d ∈ B, P d) ≤ ∑ _d ∈ B, 4 * P d₀ := by
        apply Finset.sum_le_sum
        intro d hd
        exact hprodCompare d hd
      _ = 4 * (B.card : Real) * P d₀ := by
        simp
        ring
  have hbLower : P d₀ ≤
      (domainRestrictedDifferenceWeight D B x w : Real) := by
    rw [hbEq]
    exact Finset.single_le_sum
      (fun d (_hd : d ∈ B) => by dsimp only [P]; positivity) hd₀B
  have hbPos : 0 < (domainRestrictedDifferenceWeight D B x w : Real) :=
    hP₀Pos.trans_le hbLower
  have hdirBad (d : ZMod N) (hd : d ∈ BadD) :
      35 * t ^ 2 * P d < ((extractionBadPairs D phi x w d).card : Real) := by
    have hdNot := (Finset.mem_filter.mp hd).2
    have hbad := extraction_bad_card_lt_of_not_almostEvery
      (35 * t ^ 2)
      ((D.fibre (D.index x + d)).product (D.fibre (D.index w + d)))
      (fun yz => phi yz.1 - phi x = phi yz.2 - phi w) hdNot
    simpa [extractionDirectionGood, extractionBadPairs, P] using hbad
  have hsumStrict :
      (∑ _d ∈ BadD, 35 * t ^ 2 * P d₀) <
        ∑ d ∈ BadD, ((extractionBadPairs D phi x w d).card : Real) := by
    apply Finset.sum_lt_sum_of_nonempty hBadNonempty
    intro d hd
    calc
      35 * t ^ 2 * P d₀ ≤ 35 * t ^ 2 * P d := by
        gcongr
        exact hd₀min d (Finset.filter_subset _ _ hd)
      _ < ((extractionBadPairs D phi x w d).card : Real) := hdirBad d hd
  have hsumBadLe :
      (∑ d ∈ BadD, ((extractionBadPairs D phi x w d).card : Real)) ≤
        domainDifferenceErrorCount D phi B x w := by
    rw [extraction_errorCount_eq_sum]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro d hdB _hdBad
      positivity
  have hfactorPos : 0 < 35 * t ^ 2 * P d₀ := by positivity
  have hscaled := mul_lt_mul_of_pos_left hBadGt hfactorPos
  have herrorLower :
      1225 * t ^ 4 * (B.card : Real) * P d₀ <
        domainDifferenceErrorCount D phi B x w := by
    calc
      1225 * t ^ 4 * (B.card : Real) * P d₀ =
          (35 * t ^ 2 * P d₀) * (35 * t ^ 2 * B.card) := by ring
      _ < (35 * t ^ 2 * P d₀) * BadD.card := hscaled
      _ = ∑ _d ∈ BadD, 35 * t ^ 2 * P d₀ := by simp; ring
      _ < ∑ d ∈ BadD,
          ((extractionBadPairs D phi x w d).card : Real) := hsumStrict
      _ ≤ domainDifferenceErrorCount D phi B x w := hsumBadLe
  have herrorUpper :
      (domainDifferenceErrorCount D phi B x w : Real) ≤
        300 * t ^ 4 * domainRestrictedDifferenceWeight D B x w := by
    unfold domainProportionateError at hwError
    exact (div_le_iff₀ hbPos).mp hwError
  have hupperFinal :
      (domainDifferenceErrorCount D phi B x w : Real) ≤
        1200 * t ^ 4 * (B.card : Real) * P d₀ := by
    calc
      (domainDifferenceErrorCount D phi B x w : Real) ≤
          300 * t ^ 4 * domainRestrictedDifferenceWeight D B x w := herrorUpper
      _ ≤ 300 * t ^ 4 * (4 * (B.card : Real) * P d₀) := by
        gcongr
      _ = 1200 * t ^ 4 * (B.card : Real) * P d₀ := by ring
  have hBcardPos : (0 : Real) < B.card := by
    exact_mod_cast Finset.card_pos.mpr hBnonempty
  have : 0 < t ^ 4 * (B.card : Real) * P d₀ := by positivity
  nlinarith

private lemma extraction_agreement_card_eq_sum {Y Z L : Type*}
    [DecidableEq Y] [DecidableEq Z] [DecidableEq L]
    (A : Finset Y) (C : Finset Z) (f : Y → L) (g : Z → L) :
    ((A.product C).filter fun yz => f yz.1 = g yz.2).card =
      ∑ z ∈ C, (A.filter fun y => f y = g z).card := by
  classical
  rw [Finset.filter_congr_decidable, Finset.card_filter]
  change (∑ yz ∈ A ×ˢ C, if f yz.1 = g yz.2 then 1 else 0) = _
  rw [Finset.sum_product, Finset.sum_comm]
  simp_rw [Finset.card_filter]

private noncomputable def extractionMode {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (x : X) (d : ZMod N) : ZMod N :=
  Classical.choose (Finite.exists_max fun a : ZMod N =>
    ((D.fibre (D.index x + d)).filter fun y => phi y - phi x = a).card)

private lemma extractionMode_max {N : Nat} [NeZero N] {X : Type*}
    [Fintype X] [DecidableEq X] (D : MultifunctionDomain N X)
    (phi : X → ZMod N) (x : X) (d a : ZMod N) :
    ((D.fibre (D.index x + d)).filter fun y =>
        phi y - phi x = a).card ≤
      ((D.fibre (D.index x + d)).filter fun y =>
        phi y - phi x = extractionMode D phi x d).card :=
  Classical.choose_spec (Finite.exists_max fun a : ZMod N =>
    ((D.fibre (D.index x + d)).filter fun y => phi y - phi x = a).card) a

private lemma extraction_directionGood_gives_mode {N : Nat} [NeZero N]
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : MultifunctionDomain N X) (phi : X → ZMod N)
    (x w : X) (d : ZMod N) (t : Real)
    (ht : 0 < t) (htUpper : t < 1 / 10)
    (hanchorFibre : 0 < ((D.fibre (D.index x + d)).card : Real))
    (hgood : extractionDirectionGood D phi x w d t) :
    AlmostEvery (1 - 10 * t) (D.fibre (D.index w + d))
      (fun z => phi z - phi w = extractionMode D phi x d) := by
  classical
  let A : Finset X := D.fibre (D.index x + d)
  let C : Finset X := D.fibre (D.index w + d)
  let m : ZMod N := extractionMode D phi x d
  let Am : Finset X := A.filter fun y => phi y - phi x = m
  let Cm : Finset X := C.filter fun z => phi z - phi w = m
  let E : Finset (X × X) := (A.product C).filter fun yz =>
    phi yz.1 - phi x = phi yz.2 - phi w
  let Ebad : Finset (X × X) := (A.product C).filter fun yz =>
    phi yz.1 - phi x ≠ phi yz.2 - phi w
  by_cases hCempty : C = ∅
  · unfold AlmostEvery
    simp [C, hCempty]
  have hCpos : (0 : Real) < C.card := by
    exact_mod_cast Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hCempty)
  have hEdgeLower :
      (1 - 35 * t ^ 2) * (A.card : Real) * C.card ≤ E.card := by
    have hgood' := hgood
    unfold extractionDirectionGood AlmostEvery at hgood'
    rw [Finset.filter_congr_decidable] at hgood'
    have hcardProduct : ((A.product C).card : Real) =
        (A.card : Real) * C.card := by
      exact_mod_cast Finset.card_product A C
    calc
      (1 - 35 * t ^ 2) * (A.card : Real) * C.card =
          (1 - 35 * t ^ 2) * ((A.product C).card : Real) := by
        rw [hcardProduct]
        ring
      _ ≤ (E.card : Real) := by simpa only [A, C, E] using hgood'
  have hEdgeUpperNat : E.card ≤ Am.card * C.card := by
    calc
      E.card = ∑ z ∈ C,
          (A.filter fun y => phi y - phi x = phi z - phi w).card := by
        exact extraction_agreement_card_eq_sum A C
          (fun y => phi y - phi x) (fun z => phi z - phi w)
      _ ≤ ∑ _z ∈ C, Am.card := by
        apply Finset.sum_le_sum
        intro z hz
        dsimp only [Am, m, A]
        exact extractionMode_max D phi x d (phi z - phi w)
      _ = Am.card * C.card := by simp [mul_comm]
  have hEdgeUpper : (E.card : Real) ≤ Am.card * C.card := by
    exact_mod_cast hEdgeUpperNat
  have hModeLower :
      (1 - 35 * t ^ 2) * (A.card : Real) ≤ Am.card := by
    apply le_of_mul_le_mul_right _ hCpos
    calc
      (1 - 35 * t ^ 2) * (A.card : Real) * C.card ≤ E.card := hEdgeLower
      _ ≤ (Am.card : Real) * C.card := hEdgeUpper
  have hBadEdgeUpper : (Ebad.card : Real) ≤
      35 * t ^ 2 * (A.card : Real) * C.card := by
    have hbad := extraction_almostEvery_bad_card_le (35 * t ^ 2)
      (A.product C)
      (fun yz => phi yz.1 - phi x = phi yz.2 - phi w) hgood
    simpa [Ebad, Finset.card_product, mul_assoc] using hbad
  have hrectangleSubset : Am.product (C \ Cm) ⊆ Ebad := by
    intro yz hyz
    have hyzParts := Finset.mem_product.mp hyz
    have hyAm := Finset.mem_filter.mp hyzParts.1
    have hzBad := Finset.mem_sdiff.mp hyzParts.2
    have hzC := hzBad.1
    have hzNot := hzBad.2
    have hzNe : phi yz.2 - phi w ≠ m := by
      intro hzEq
      apply hzNot
      exact Finset.mem_filter.mpr ⟨hzC, hzEq⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hyAm.1, hzC⟩,
      fun heq => hzNe (heq ▸ hyAm.2)⟩
  have hrectangle : (Am.card : Real) * (C \ Cm).card ≤ Ebad.card := by
    have hcard := Finset.card_le_card hrectangleSubset
    have hcardReal : ((Am.product (C \ Cm)).card : Real) ≤ Ebad.card := by
      exact_mod_cast hcard
    have hcardProduct : ((Am.product (C \ Cm)).card : Real) =
        (Am.card : Real) * (C \ Cm).card := by
      exact_mod_cast Finset.card_product Am (C \ Cm)
    rw [hcardProduct] at hcardReal
    exact hcardReal
  have hModeBad : (Am.card : Real) * (C \ Cm).card ≤
      35 * t ^ 2 * (A.card : Real) * C.card :=
    hrectangle.trans hBadEdgeUpper
  have hp : 0 < 1 - 35 * t ^ 2 := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htUpper.le)]
  have hmodeTimesBad :
      (1 - 35 * t ^ 2) * (A.card : Real) * (C \ Cm).card ≤
        35 * t ^ 2 * (A.card : Real) * C.card := by
    calc
      (1 - 35 * t ^ 2) * (A.card : Real) * (C \ Cm).card ≤
          (Am.card : Real) * (C \ Cm).card := by gcongr
      _ ≤ 35 * t ^ 2 * (A.card : Real) * C.card := hModeBad
  have hcancelA :
      (1 - 35 * t ^ 2) * ((C \ Cm).card : Real) ≤
        35 * t ^ 2 * C.card := by
    apply le_of_mul_le_mul_left _ hanchorFibre
    calc
      (A.card : Real) * ((1 - 35 * t ^ 2) * (C \ Cm).card) =
          (1 - 35 * t ^ 2) * A.card * (C \ Cm).card := by ring
      _ ≤ 35 * t ^ 2 * A.card * C.card := hmodeTimesBad
      _ = (A.card : Real) * (35 * t ^ 2 * C.card) := by ring
  have htSq : t ^ 2 ≤ t / 10 := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr htUpper.le)]
  have htCube : t ^ 3 ≤ t / 100 := by
    have hmul := mul_le_mul_of_nonneg_left htSq ht.le
    nlinarith
  have hnumeric : 35 * t ^ 2 ≤ 10 * t * (1 - 35 * t ^ 2) := by
    nlinarith
  have htargetBad : ((C \ Cm).card : Real) ≤ 10 * t * C.card := by
    apply le_of_mul_le_mul_left _ hp
    calc
      (1 - 35 * t ^ 2) * ((C \ Cm).card : Real) ≤
          35 * t ^ 2 * C.card := hcancelA
      _ ≤ (10 * t * (1 - 35 * t ^ 2)) * C.card := by gcongr
      _ = (1 - 35 * t ^ 2) * (10 * t * C.card) := by ring
  have hdiff : C \ Cm = C.filter fun z =>
      ¬ (phi z - phi w = extractionMode D phi x d) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    dsimp only [Cm, m]
    simp only [Finset.mem_filter]
    tauto
  apply extraction_almostEvery_of_bad_card_le
  rw [← hdiff]
  simpa only [C] using htargetBad

private lemma extraction_product_filter_card_first {Y Z : Type*}
    [DecidableEq Y] [DecidableEq Z] (U : Finset Y) (V : Finset Z)
    (P : Y → Z → Prop) [DecidableRel P] :
    ((U.product V).filter fun yz : Y × Z => P yz.1 yz.2).card =
      ∑ y ∈ U, (V.filter fun z : Z => P y z).card := by
  classical
  rw [Finset.filter_congr_decidable, Finset.card_filter]
  change (∑ yz ∈ U ×ˢ V, if P yz.1 yz.2 then 1 else 0) = _
  rw [Finset.sum_product]
  simp_rw [Finset.card_filter]

private lemma extraction_product_filter_card_second {Y Z : Type*}
    [DecidableEq Y] [DecidableEq Z] (U : Finset Y) (V : Finset Z)
    (P : Y → Z → Prop) [DecidableRel P] :
    ((U.product V).filter fun yz : Y × Z => P yz.1 yz.2).card =
      ∑ z ∈ V, (U.filter fun y : Y => P y z).card := by
  classical
  rw [Finset.filter_congr_decidable, Finset.card_filter]
  change (∑ yz ∈ U ×ˢ V, if P yz.1 yz.2 then 1 else 0) = _
  rw [Finset.sum_product, Finset.sum_comm]
  simp_rw [Finset.card_filter]

private lemma extraction_select_directions {Y Z : Type*}
    [DecidableEq Y] [DecidableEq Z] (U : Finset Y) (V : Finset Z)
    (Q : Y → Z → Prop) (t : Real) (ht : 0 < t)
    (hrow : ∀ y, y ∈ U →
      AlmostEvery (1 - 35 * t ^ 2) V (Q y)) :
    AlmostEvery (1 - 7 * t) V fun z =>
      AlmostEvery (1 - 5 * t) U fun y => Q y z := by
  classical
  by_cases hUempty : U = ∅
  · subst U
    unfold AlmostEvery
    rw [Finset.filter_eq_self.2]
    · have hVcard : (0 : Real) ≤ V.card := by positivity
      nlinarith
    · intro z hz
      simp
  have hUnonempty : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hUempty
  have hUcardPos : (0 : Real) < U.card := by
    exact_mod_cast Finset.card_pos.mpr hUnonempty
  let BadPair : Finset (Y × Z) :=
    (U.product V).filter fun yz => ¬ Q yz.1 yz.2
  let H : Finset Z := V.filter fun z =>
    ¬ AlmostEvery (1 - 5 * t) U (fun y => Q y z)
  apply extraction_almostEvery_of_bad_card_le
  change (H.card : Real) ≤ 7 * t * V.card
  by_contra hHBound
  have hHGt : 7 * t * (V.card : Real) < H.card := lt_of_not_ge hHBound
  have hHPosReal : 0 < (H.card : Real) := by
    exact (mul_nonneg (by positivity) (by positivity)).trans_lt hHGt
  have hHnonempty : H.Nonempty := by
    exact Finset.card_pos.mp (by exact_mod_cast hHPosReal)
  have hBadRows : BadPair.card =
      ∑ y ∈ U, (V.filter fun z => ¬ Q y z).card := by
    exact extraction_product_filter_card_first U V (fun y z => ¬ Q y z)
  have hBadUpper : (BadPair.card : Real) ≤
      35 * t ^ 2 * (V.card : Real) * U.card := by
    rw [hBadRows]
    push_cast
    calc
      (∑ y ∈ U, ((V.filter fun z => ¬ Q y z).card : Real)) ≤
          ∑ _y ∈ U, 35 * t ^ 2 * V.card := by
        apply Finset.sum_le_sum
        intro y hy
        exact extraction_almostEvery_bad_card_le (35 * t ^ 2) V (Q y)
          (hrow y hy)
      _ = 35 * t ^ 2 * (V.card : Real) * U.card := by
        simp
        ring
  have hcolumnBad (z : Z) (hz : z ∈ H) :
      5 * t * (U.card : Real) <
        ((U.filter fun y => ¬ Q y z).card : Real) := by
    have hzNot := (Finset.mem_filter.mp hz).2
    exact extraction_bad_card_lt_of_not_almostEvery (5 * t) U
      (fun y => Q y z) hzNot
  have hsumColumnsStrict :
      (∑ _z ∈ H, 5 * t * (U.card : Real)) <
        ∑ z ∈ H, ((U.filter fun y => ¬ Q y z).card : Real) := by
    exact Finset.sum_lt_sum_of_nonempty hHnonempty hcolumnBad
  have hBadColumns : BadPair.card =
      ∑ z ∈ V, (U.filter fun y => ¬ Q y z).card := by
    exact extraction_product_filter_card_second U V (fun y z => ¬ Q y z)
  have hsumColumnsLe :
      (∑ z ∈ H, ((U.filter fun y => ¬ Q y z).card : Real)) ≤
        BadPair.card := by
    rw [hBadColumns]
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro z hzV _hzH
      positivity
  have hfactorPos : 0 < 5 * t * (U.card : Real) := by positivity
  have hscaled := mul_lt_mul_of_pos_left hHGt hfactorPos
  have : 35 * t ^ 2 * (V.card : Real) * U.card < BadPair.card := by
    calc
      35 * t ^ 2 * (V.card : Real) * U.card =
          (5 * t * U.card) * (7 * t * V.card) := by ring
      _ < (5 * t * U.card) * H.card := hscaled
      _ = ∑ _z ∈ H, 5 * t * (U.card : Real) := by simp; ring
      _ < ∑ z ∈ H,
          ((U.filter fun y => ¬ Q y z).card : Real) := hsumColumnsStrict
      _ ≤ (BadPair.card : Real) := hsumColumnsLe
  linarith

private lemma extraction_lift_almostEvery {Y : Type*} [DecidableEq Y]
    (W U : Finset Y) (P : Y → Prop) (a b : Real)
    (_ha : 0 ≤ a) (hb : 0 ≤ b) (hUW : U ⊆ W)
    (hU : AlmostEvery (1 - a) W (fun y => y ∈ U))
    (hP : AlmostEvery (1 - b) U P) :
    AlmostEvery (1 - (a + b)) W P := by
  classical
  have hbadU := extraction_almostEvery_bad_card_le a W
    (fun y => y ∈ U) hU
  have hbadP := extraction_almostEvery_bad_card_le b U P hP
  have hsubset : (W.filter fun y => ¬ P y) ⊆
      (W.filter fun y => y ∉ U) ∪ (U.filter fun y => ¬ P y) := by
    intro y hy
    have hyParts := Finset.mem_filter.mp hy
    by_cases hyU : y ∈ U
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyU, hyParts.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyParts.1, hyU⟩)
  have hcardNat : (W.filter fun y => ¬ P y).card ≤
      (W.filter fun y => y ∉ U).card + (U.filter fun y => ¬ P y).card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hcard : ((W.filter fun y => ¬ P y).card : Real) ≤
      ((W.filter fun y => y ∉ U).card : Real) +
        (U.filter fun y => ¬ P y).card := by
    exact_mod_cast hcardNat
  have hUcard : (U.card : Real) ≤ W.card := by
    exact_mod_cast Finset.card_le_card hUW
  apply extraction_almostEvery_of_bad_card_le
  calc
    ((W.filter fun y => ¬ P y).card : Real) ≤
        ((W.filter fun y => y ∉ U).card : Real) +
          (U.filter fun y => ¬ P y).card := hcard
    _ ≤ a * W.card + b * U.card := add_le_add hbadU hbadP
    _ ≤ (a + b) * W.card := by
      have := mul_le_mul_of_nonneg_left hUcard hb
      nlinarith

private lemma extraction_almostEvery_mono {Y : Type*} [DecidableEq Y]
    (p : Real) (U : Finset Y) (P Q : Y → Prop)
    (hP : AlmostEvery p U P) (hPQ : ∀ y, y ∈ U → P y → Q y) :
    AlmostEvery p U Q := by
  classical
  unfold AlmostEvery at hP ⊢
  rw [Finset.filter_congr_decidable] at hP ⊢
  exact hP.trans (by
    exact_mod_cast Finset.card_le_card (fun y hy =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
        hPQ y (Finset.mem_filter.mp hy).1 (Finset.mem_filter.mp hy).2⟩))

/-- **Gowers, Lemma 10.6.**  The proof uses the inherited smallness bound on
`rho` made explicit in the corrected statement. -/
theorem lemma_10_6_holds : lemma_10_6 := by
  classical
  intro N _ X _ _ D phi B alpha rho M sigma eta x W
    hsetup hanchor hregular hrho hsigma
  let t : Real := eta ^ ((1 : Real) / 5)
  have hpositive : 0 < eta * rho * alpha ^ 2 / 16 :=
    hsetup.2.1.trans_le hsigma
  have hmulPositive : 0 < eta * rho * alpha ^ 2 := by linarith
  have hetaRhoPositive : 0 < eta * rho := by
    rcases (mul_pos_iff.mp hmulPositive) with h | h
    · exact h.1
    · exact (not_lt_of_ge (sq_nonneg alpha) h.2).elim
  have heta : 0 ≤ eta := hsetup.2.2.1
  have hetaPos : 0 < eta := by
    rcases (mul_pos_iff.mp hetaRhoPositive) with h | h
    · exact h.1
    · exact (not_lt_of_ge heta h.1).elim
  have ht : 0 < t := by
    dsimp only [t]
    exact Real.rpow_pos_of_pos hetaPos _
  by_cases htLarge : 1 ≤ 10 * t
  · refine ⟨∅, fun _ => 0, ?_⟩
    refine ⟨Finset.empty_subset _, ?_, ?_⟩
    · simp only [Finset.card_empty, Nat.cast_zero]
      have hBcard : (0 : Real) ≤ B.card := by positivity
      dsimp only [t] at htLarge
      nlinarith
    · intro d hd
      simp at hd
  have htUpper : t < 1 / 10 := by nlinarith
  have htFour : eta ^ ((4 : Real) / 5) = t ^ 4 := by
    dsimp only [t]
    have h := Real.rpow_mul_natCast heta ((1 : Real) / 5) 4
    convert h using 1
    norm_num
  let Low : Finset X := W.filter fun w =>
    domainProportionateError D phi B x w ≤ 300 * t ^ 4
  have hLowAE : AlmostEvery (1 - 5 * t) W (fun w => w ∈ Low) := by
    have h := hregular.2.2.1
    rw [htFour] at h
    change AlmostEvery (1 - 5 * t) W
      (fun w => domainProportionateError D phi B x w ≤ 300 * t ^ 4) at h
    exact extraction_almostEvery_mono (1 - 5 * t) W
      (fun w => domainProportionateError D phi B x w ≤ 300 * t ^ 4)
      (fun w => w ∈ Low) h (fun w hwW hwError =>
        Finset.mem_filter.mpr ⟨hwW, hwError⟩)
  have hrows : ∀ w, w ∈ Low →
      AlmostEvery (1 - 35 * t ^ 2) B
        (fun d => extractionDirectionGood D phi x w d t) := by
    intro w hwLow
    have hwParts := Finset.mem_filter.mp hwLow
    exact extraction_direction_good_almostEvery D phi B alpha rho M sigma eta t
      x w W hsetup hanchor hregular hrho hsigma ht hwParts.1 hwParts.2
  have hselected := extraction_select_directions Low B
    (fun w d => extractionDirectionGood D phi x w d t) t ht hrows
  let Selected : ZMod N → Prop := fun d =>
    AlmostEvery (1 - 5 * t) Low fun w =>
      extractionDirectionGood D phi x w d t
  let B' : Finset (ZMod N) := B.filter Selected
  let psi : ZMod N → ZMod N := fun d => extractionMode D phi x d
  have hB'largeSeven : (1 - 7 * t) * B.card ≤ (B'.card : Real) := by
    change AlmostEvery (1 - 7 * t) B Selected at hselected
    unfold AlmostEvery at hselected
    change (1 - 7 * t) * B.card ≤ (B'.card : Real) at hselected
    exact hselected
  have hB'largeTen : (1 - 10 * t) * B.card ≤ (B'.card : Real) := by
    have hBcard : (0 : Real) ≤ B.card := by positivity
    nlinarith
  have hxQuarter := extraction_sigmaM_le_anchor_quarter D phi B alpha rho M
    sigma eta x hsetup hanchor hrho hsigma
  have hinvariant := hsetup.2.2.2.2.2.1
  refine ⟨B', psi, Finset.filter_subset _ _, ?_, ?_⟩
  · simpa only [t] using hB'largeTen
  · intro d hdB'
    have hdParts := Finset.mem_filter.mp hdB'
    have hdB := hdParts.1
    have hdSelected := hdParts.2
    dsimp only [Selected] at hdSelected
    have hdirWbase := extraction_lift_almostEvery W Low
      (fun w => extractionDirectionGood D phi x w d t)
      (5 * t) (5 * t) (by positivity) (by positivity)
      (Finset.filter_subset _ _) hLowAE hdSelected
    have hdirW : AlmostEvery (1 - 10 * t) W
        (fun w => extractionDirectionGood D phi x w d t) := by
      convert hdirWbase using 1
      ring
    have hxd := extraction_shifted_fibre_bounds D B sigma M x hinvariant
      hxQuarter d hdB
    have hxBasePos : 0 < (D.fibreSize x : Real) := by
      have hM : (0 : Real) < M := by exact_mod_cast hsetup.1.2.2.1
      have halpha := hsetup.1.1
      exact (show 0 < alpha ^ 2 * M / 2 by positivity).trans_le hanchor.1
    have hxdPos : 0 < ((D.fibre (D.index x + d)).card : Real) := by
      linarith
    have hlocalT : AlmostEvery (1 - 10 * t) W fun w =>
        AlmostEvery (1 - 10 * t) (D.fibre (D.index w + d)) fun z =>
          phi z - phi w = psi d := by
      apply extraction_almostEvery_mono (1 - 10 * t) W
        (fun w => extractionDirectionGood D phi x w d t)
        (fun w => AlmostEvery (1 - 10 * t) (D.fibre (D.index w + d))
          (fun z => phi z - phi w = psi d)) hdirW
      intro w hwW hwDirection
      simpa only [psi] using extraction_directionGood_gives_mode D phi x w d t
        ht htUpper hxdPos hwDirection
    simpa only [t] using hlocalT

end LeanProofs.GowersSzemeredi
