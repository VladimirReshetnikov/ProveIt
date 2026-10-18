import GowersSzemeredi.Proofs10Extraction

/-! Declarations of `Proofs10Extraction` that the final route does not use (moved here so
that the route keeps only what it uses). -/

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
  right_inv _ := rfl

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

private lemma audit_differenceWeight_eq_sum_fibre (y : AuditX) :
    domainDifferenceWeight auditDomain auditX0 y =
      ∑ z : AuditX,
        (auditDomain.fibre
          (z.1 + (y.1 - auditX0.1))).card := by
  unfold domainDifferenceWeight
  rw [countWhere_eq_sum_ite, Fintype.sum_prod_type]
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

private lemma audit_countWhere_coordinate_mem {Y : Type*}
    [Fintype Y] [DecidableEq Y] (A : Finset Y) (i : Fin 4) :
    countWhere (fun q : Fin 4 → Y => q i ∈ A) =
      A.card * Fintype.card Y ^ 3 := by
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
  unfold countWhere
  rw [Finset.filter_congr_decidable]
  rw [show (Finset.univ.filter
      (fun q : Fin 4 → Y => ∀ i, q i ∈ A)) =
      Fintype.piFinset (fun _ : Fin 4 => A) by ext; simp]
  exact Fintype.card_piFinset_const A 4

private lemma audit_coordinate_exception_count (i : Fin 4) :
    (∑ q : Fin 4 → AuditX, if (q i).1 = 5 then 1 else 0) =
      auditH * auditCard ^ 3 := by
  rw [← countWhere_eq_sum_ite]
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
  rw [countWhere_eq_sum_ite]
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
  exact countWhere_mono audit_core_additive

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
  have hpartNat := countWhere_and_partition auditAdditive auditPhiRelation
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

private lemma audit_invariant :
    DomainInvariant auditDomain auditB (auditSigma * auditM) := by
  intro s d hd
  simp only [auditB, Finset.mem_singleton] at hd
  subst d
  rw [audit_sigma_mul_M]
  simp only [audit_fibre_card]
  rcases (show auditProfile (s + 4) = auditProfile s ∨
      (auditProfile (s + 4) = 0 ∧ auditProfile s = 1) ∨
      (auditProfile (s + 4) = 1 ∧ auditProfile s = 0) by
    fin_cases s <;> decide) with hEq | h01 | h10
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
  have h : 4 * auditL ^ 3 ≤ domainTotalWeight auditDomain auditX0 := by
    rw [audit_totalWeight_formula]
    have huniv : (Finset.univ : Finset (ZMod 8)) = {0, 1, 2, 3, 4, 5, 6, 7} := by
      decide
    rw [huniv]
    decide
  exact_mod_cast h

private lemma audit_anchor_weight_bound :
    auditAlpha ^ 3 * auditM ^ 3 * (8 : Nat) ^ 2 / 4 ≤
      domainTotalWeight auditDomain auditX0 := by
  rw [audit_anchor_weight_scale]
  exact (div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) audit_card_le_five_L_real 3) (by norm_num)).trans
    (audit_fiveL_cube_div_le.trans audit_totalWeight_lower_real)

private lemma audit_anchor_error_bound :
    domainWeightedError auditDomain auditPhi auditB auditX0 ≤
      60 * auditEta * domainTotalWeight auditDomain auditX0 := by
  rw [audit_weightedError_zero]
  positivity

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
    nlinarith
  · intro y _
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
  nlinarith

private lemma audit_regular :
    IsSection10RegularComponent auditDomain auditPhi auditB auditX0
      auditAlpha auditEta auditRho auditM 8 auditW :=
  ⟨audit_fibreSaturated, audit_weight_varies, audit_error_almostEvery,
    (by rw [audit_regular_card_scale, audit_card_W]), audit_fibreSize_varies,
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

private lemma audit_eta_root :
    auditEta ^ ((1 : Real) / 5) = (1 : Real) / 32 := by
  rw [(show auditEta = ((1 : Real) / 32) ^ 5 by norm_num [auditEta, auditQ])]
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
  ⟨audit_setup,
    ⟨audit_anchor_fibre_bound, audit_anchor_weight_bound, audit_anchor_error_bound⟩,
    audit_regular, audit_sigma_bound, audit_no_local_difference_model⟩

end LeanProofs.GowersSzemeredi
