import GowersSzemeredi.Proofs12Amplification

/-!
# The random restriction in Gowers's Lemma 12.5

This file proves the repaired statement of Lemma 12.5.  The proof is written
as a finite weighted average (rather than using measure theory): first one
averages the Riesz weights over their three phase parameters, and then one
uses the Bernoulli weights on `B.powerset` to obtain an actual subset.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Elementary finite Bernoulli averaging -/

private def restrictionWeight {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (S : Finset X) : Real :=
  (∏ x ∈ S, p x) * ∏ x ∈ U \ S, (1 - p x)

private lemma restrictionWeight_nonneg {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (hp0 : ∀ x ∈ U, 0 ≤ p x)
    (hp1 : ∀ x ∈ U, p x ≤ 1) (S : Finset X) (hS : S ⊆ U) :
    0 ≤ restrictionWeight U p S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun x hx ↦ hp0 x (hS hx)
  · exact Finset.prod_nonneg fun x hx ↦
      sub_nonneg.mpr (hp1 x (Finset.mem_sdiff.mp hx).1)

private lemma restrictionWeight_insert {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (a : X) (ha : a ∉ U) (S : Finset X)
    (hS : S ⊆ U) :
    restrictionWeight (insert a U) p (insert a S) =
      p a * restrictionWeight U p S := by
  simp only [restrictionWeight]
  rw [Finset.prod_insert (notMem_mono hS ha)]
  have hdiff : insert a U \ insert a S = U \ S := by
    ext x
    simp only [mem_sdiff, mem_insert]
    aesop
  rw [hdiff]
  ring

private lemma restrictionWeight_not_insert {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (a : X) (ha : a ∉ U) (S : Finset X)
    (hS : S ⊆ U) :
    restrictionWeight (insert a U) p S =
      (1 - p a) * restrictionWeight U p S := by
  simp only [restrictionWeight]
  have haS : a ∉ S := fun h ↦ ha (hS h)
  have hdiff : insert a U \ S = insert a (U \ S) := by
    ext x
    simp only [mem_sdiff, mem_insert]
    aesop
  rw [hdiff, Finset.prod_insert]
  · ring
  · simp [ha]

private lemma restrictionWeight_sum {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) :
    ∑ S ∈ U.powerset, restrictionWeight U p S = 1 := by
  induction U using Finset.induction_on with
  | empty => simp [restrictionWeight]
  | @insert a U ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hleft :
          (∑ S ∈ U.powerset, restrictionWeight (insert a U) p S) =
            (1 - p a) * ∑ S ∈ U.powerset, restrictionWeight U p S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [restrictionWeight_not_insert U p a ha S
          (Finset.mem_powerset.mp hS)]
      have hright :
          (∑ S ∈ U.powerset,
            restrictionWeight (insert a U) p (insert a S)) =
            p a * ∑ S ∈ U.powerset, restrictionWeight U p S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [restrictionWeight_insert U p a ha S
          (Finset.mem_powerset.mp hS)]
      rw [hleft, hright, ih]
      ring

private lemma restrictionWeight_event {X : Type*} [DecidableEq X]
    (U C : Finset X) (p : X → Real) (hC : C ⊆ U) :
    ∑ S ∈ U.powerset, restrictionWeight U p S * (if C ⊆ S then 1 else 0) =
      ∏ x ∈ C, p x := by
  induction U using Finset.induction_on generalizing C with
  | empty =>
      have hC0 : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦
        (Finset.notMem_empty x) (hC hx)
      subst C
      simp [restrictionWeight]
  | @insert a U ha ih =>
      rw [Finset.sum_powerset_insert ha]
      by_cases haC : a ∈ C
      · let C₀ := C.erase a
        have hCeq : C = insert a C₀ := (Finset.insert_erase haC).symm
        have hC₀ : C₀ ⊆ U := by
          intro x hx
          have hxC : x ∈ C := Finset.mem_of_mem_erase hx
          have hxins := hC hxC
          rcases Finset.mem_insert.mp hxins with hxa | hxU
          · subst x
            exact (Finset.notMem_erase a C hx).elim
          · exact hxU
        have haC₀ : a ∉ C₀ := Finset.notMem_erase _ _
        have hfalse (S : Finset X) (hS : S ∈ U.powerset) : ¬ C ⊆ S := by
          intro hCS
          exact ha (Finset.mem_powerset.mp hS (hCS haC))
        have hins (S : Finset X) (hS : S ∈ U.powerset) :
            (C ⊆ insert a S) ↔ C₀ ⊆ S := by
          rw [hCeq, Finset.insert_subset_iff]
          constructor
          · rintro ⟨-, hsub⟩ x hx
            have := hsub hx
            rcases Finset.mem_insert.mp this with hxa | hxS
            · subst x
              exact (haC₀ hx).elim
            · exact hxS
          · intro hsub
            exact ⟨Finset.mem_insert_self _ _, fun x hx ↦
              Finset.mem_insert_of_mem (hsub hx)⟩
        have hleft :
            (∑ S ∈ U.powerset,
              restrictionWeight (insert a U) p S *
                (if C ⊆ S then 1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro S hS
          rw [if_neg (hfalse S hS), mul_zero]
        have hright :
            (∑ S ∈ U.powerset,
              restrictionWeight (insert a U) p (insert a S) *
                (if C ⊆ insert a S then 1 else 0)) =
              p a * ∑ S ∈ U.powerset,
                restrictionWeight U p S *
                  (if C₀ ⊆ S then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          rw [restrictionWeight_insert U p a ha S
            (Finset.mem_powerset.mp hS)]
          simp only [hins S hS]
          ring
        rw [hleft, zero_add, hright]
        rw [ih C₀ hC₀, hCeq,
          Finset.prod_insert haC₀]
      · have hCU : C ⊆ U := by
          intro x hx
          rcases Finset.mem_insert.mp (hC hx) with hxa | hxU
          · subst x
            exact (haC hx).elim
          · exact hxU
        have hevent (S : Finset X) (hS : S ∈ U.powerset) :
            (C ⊆ insert a S) ↔ C ⊆ S := by
          constructor
          · intro hsub x hx
            rcases Finset.mem_insert.mp (hsub hx) with hxa | hxS
            · subst x
              exact (haC hx).elim
            · exact hxS
          · exact fun hsub ↦ hsub.trans (Finset.subset_insert _ _)
        have hleft :
            (∑ S ∈ U.powerset,
              restrictionWeight (insert a U) p S *
                (if C ⊆ S then 1 else 0)) =
              (1 - p a) * ∑ S ∈ U.powerset,
                restrictionWeight U p S * (if C ⊆ S then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          rw [restrictionWeight_not_insert U p a ha S
            (Finset.mem_powerset.mp hS)]
          ring
        have hright :
            (∑ S ∈ U.powerset,
              restrictionWeight (insert a U) p (insert a S) *
                (if C ⊆ insert a S then 1 else 0)) =
              p a * ∑ S ∈ U.powerset,
                restrictionWeight U p S * (if C ⊆ S then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          rw [restrictionWeight_insert U p a ha S
            (Finset.mem_powerset.mp hS)]
          simp only [hevent S hS]
          ring
        rw [hleft, hright, ih C hCU]
        ring

private lemma exists_subset_of_weighted_average {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (hp0 : ∀ x ∈ U, 0 ≤ p x)
    (hp1 : ∀ x ∈ U, p x ≤ 1) (F : Finset X → Real) (A : Real)
    (haverage : A ≤ ∑ S ∈ U.powerset, restrictionWeight U p S * F S) :
    ∃ S ⊆ U, A ≤ F S := by
  by_contra hno
  push Not at hno
  have hex : ∃ T ∈ U.powerset, 0 < restrictionWeight U p T := by
    by_contra hz
    push Not at hz
    have hall : ∀ T ∈ U.powerset, restrictionWeight U p T = 0 := by
      intro T hT
      exact le_antisymm (hz T hT)
        (restrictionWeight_nonneg U p hp0 hp1 T
          (Finset.mem_powerset.mp hT))
    have hsum := restrictionWeight_sum U p
    have hzero :
        (∑ T ∈ U.powerset, restrictionWeight U p T) = 0 := by
      apply Finset.sum_eq_zero
      intro T hT
      exact hall T hT
    rw [hzero] at hsum
    norm_num at hsum
  have hstrict :
      (∑ S ∈ U.powerset, restrictionWeight U p S * F S) <
        ∑ S ∈ U.powerset, restrictionWeight U p S * A := by
    apply Finset.sum_lt_sum
    · intro S hS
      exact mul_le_mul_of_nonneg_left (le_of_lt (hno S (Finset.mem_powerset.mp hS)))
        (restrictionWeight_nonneg U p hp0 hp1 S (Finset.mem_powerset.mp hS))
    · obtain ⟨T, hT, hTpos⟩ := hex
      exact ⟨T, hT,
        mul_lt_mul_of_pos_left (hno T (Finset.mem_powerset.mp hT)) hTpos⟩
  have hright :
      (∑ S ∈ U.powerset, restrictionWeight U p S * A) = A := by
    rw [← Finset.sum_mul]
    rw [restrictionWeight_sum]
    simp
  rw [hright] at hstrict
  exact (haverage.trans_lt hstrict).false

private lemma restrictionWeight_count {X E : Type*} [DecidableEq X]
    [DecidableEq E] (U : Finset X) (p : X → Real) (edges : Finset E)
    (carrier : E → Finset X) (hcarrier : ∀ e ∈ edges, carrier e ⊆ U) :
    (∑ S ∈ U.powerset, restrictionWeight U p S *
        ((edges.filter fun e ↦ carrier e ⊆ S).card : Real)) =
      ∑ e ∈ edges, ∏ x ∈ carrier e, p x := by
  classical
  simp_rw [Finset.cast_card, Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← restrictionWeight_event U (carrier e) p (hcarrier e he)]

private lemma exists_subset_count_score {X E : Type*} [DecidableEq X]
    [DecidableEq E] (U : Finset X) (p : X → Real)
    (hp0 : ∀ x ∈ U, 0 ≤ p x) (hp1 : ∀ x ∈ U, p x ≤ 1)
    (good bad : Finset E) (carrier : E → Finset X)
    (hgood : ∀ e ∈ good, carrier e ⊆ U)
    (hbad : ∀ e ∈ bad, carrier e ⊆ U) (eta A : Real)
    (haverage : A ≤
      eta * (∑ e ∈ good, ∏ x ∈ carrier e, p x) -
        ∑ e ∈ bad, ∏ x ∈ carrier e, p x) :
    ∃ S ⊆ U,
      A ≤ eta * ((good.filter fun e ↦ carrier e ⊆ S).card : Real) -
        ((bad.filter fun e ↦ carrier e ⊆ S).card : Real) := by
  let F : Finset X → Real := fun S ↦
    eta * ((good.filter fun e ↦ carrier e ⊆ S).card : Real) -
      ((bad.filter fun e ↦ carrier e ⊆ S).card : Real)
  apply exists_subset_of_weighted_average U p hp0 hp1 F A
  calc
    A ≤ eta * (∑ e ∈ good, ∏ x ∈ carrier e, p x) -
        ∑ e ∈ bad, ∏ x ∈ carrier e, p x := haverage
    _ = ∑ S ∈ U.powerset, restrictionWeight U p S * F S := by
      rw [← restrictionWeight_count U p good carrier hgood,
        ← restrictionWeight_count U p bad carrier hbad]
      simp only [F]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro S hS
      ring

/-! ## Arrangements as finite hyperedges -/

private abbrev restrictionIndex := Fin 16 × Bool

private def restrictionVertex {N : Nat} (R : DArrangement N 8)
    (j : restrictionIndex) : Pair N :=
  (R.x j.1, R.y j.1 + if j.2 then R.height else 0)

private noncomputable def restrictionCarrier {N : Nat}
    (R : DArrangement N 8) : Finset (Pair N) := by
  classical
  exact Finset.univ.image (restrictionVertex R)

private lemma restrictionCarrier_subset {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (R : DArrangement N 8) (hR : R.IsIn B) :
    restrictionCarrier R ⊆ B := by
  classical
  intro z hz
  rw [restrictionCarrier, Finset.mem_image] at hz
  obtain ⟨j, -, rfl⟩ := hz
  rcases j with ⟨i, b⟩
  cases b
  · simpa [restrictionVertex] using (hR.2 i).1
  · simpa [restrictionVertex] using (hR.2 i).2

private lemma restriction_isIn_iff {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (R : DArrangement N 8) :
    R.IsIn B ↔ IsAdditiveTuple R.x ∧ restrictionCarrier R ⊆ B := by
  constructor
  · intro hR
    exact ⟨hR.1, restrictionCarrier_subset B R hR⟩
  · rintro ⟨hadd, hsub⟩
    refine ⟨hadd, fun i ↦ ⟨?_, ?_⟩⟩
    · apply hsub
      rw [restrictionCarrier, Finset.mem_image]
      exact ⟨(i, false), Finset.mem_univ _, by simp [restrictionVertex]⟩
    · apply hsub
      rw [restrictionCarrier, Finset.mem_image]
      exact ⟨(i, true), Finset.mem_univ _, by simp [restrictionVertex]⟩

private noncomputable def restrictionArrangements {N : Nat} [NeZero N]
    (B : Finset (Pair N)) : Finset (DArrangement N 8) := by
  classical
  exact Finset.univ.filter fun R ↦ R.IsIn B

private noncomputable def respectedRestrictionArrangements {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    Finset (DArrangement N 8) := by
  classical
  exact (restrictionArrangements B).filter fun R ↦ R.IsRespected phi

private noncomputable def restrictionBadArrangements {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    Finset (DArrangement N 8) := by
  classical
  exact restrictionArrangements B \ respectedRestrictionArrangements B phi

private lemma restrictionArrangements_card {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    (restrictionArrangements B).card = arrangementCount 8 B := by
  classical
  rfl

private lemma respectedRestrictionArrangements_card {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    (respectedRestrictionArrangements B phi).card =
      respectedArrangementCount 8 B phi := by
  classical
  unfold respectedRestrictionArrangements restrictionArrangements
  unfold respectedArrangementCount countWhere
  rw [Finset.filter_filter]
  congr 1
  ext R
  simp

private lemma restriction_respected_le_arrangement {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    respectedArrangementCount 8 B phi ≤ arrangementCount 8 B := by
  classical
  rw [← respectedRestrictionArrangements_card,
    ← restrictionArrangements_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

private lemma restriction_good_restrict_card {N : Nat} [NeZero N]
    (B S : Finset (Pair N)) (phi : Pair N → ZMod N) (hSB : S ⊆ B) :
    ((respectedRestrictionArrangements B phi).filter fun R ↦
        restrictionCarrier R ⊆ S).card =
      respectedArrangementCount 8 S phi := by
  classical
  rw [← respectedRestrictionArrangements_card]
  apply congrArg Finset.card
  ext R
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hRB, hcarrier⟩
    have hdata : R.IsIn B ∧ R.IsRespected phi := by
      simpa [respectedRestrictionArrangements, restrictionArrangements] using hRB
    have hRS : R.IsIn S :=
      restriction_isIn_iff S R |>.mpr ⟨hdata.1.1, hcarrier⟩
    simp [respectedRestrictionArrangements, restrictionArrangements, hRS,
      hdata.2]
  · intro hRS
    have hdata : R.IsIn S ∧ R.IsRespected phi := by
      simpa [respectedRestrictionArrangements, restrictionArrangements] using hRS
    have hRB : R.IsIn B := ⟨hdata.1.1, fun i ↦
      ⟨hSB (hdata.1.2 i).1, hSB (hdata.1.2 i).2⟩⟩
    exact ⟨by
      simp [respectedRestrictionArrangements, restrictionArrangements,
        hRB, hdata.2], restrictionCarrier_subset S R hdata.1⟩

private lemma restriction_good_bad_restrict_card {N : Nat} [NeZero N]
    (B S : Finset (Pair N)) (phi : Pair N → ZMod N) (hSB : S ⊆ B) :
    ((respectedRestrictionArrangements B phi).filter fun R ↦
        restrictionCarrier R ⊆ S).card +
      ((restrictionBadArrangements B phi).filter fun R ↦
        restrictionCarrier R ⊆ S).card = arrangementCount 8 S := by
  classical
  let goodS := (respectedRestrictionArrangements B phi).filter fun R ↦
    restrictionCarrier R ⊆ S
  let badS := (restrictionBadArrangements B phi).filter fun R ↦
    restrictionCarrier R ⊆ S
  have hgood : goodS = (restrictionArrangements S).filter fun R ↦
      R.IsRespected phi := by
    ext R
    simp only [goodS, Finset.mem_filter]
    constructor
    · rintro ⟨hRB, hcarrier⟩
      have hdata : R.IsIn B ∧ R.IsRespected phi := by
        simpa [respectedRestrictionArrangements, restrictionArrangements] using hRB
      have hRS : R.IsIn S :=
        restriction_isIn_iff S R |>.mpr ⟨hdata.1.1, hcarrier⟩
      exact ⟨by simpa [restrictionArrangements], hdata.2⟩
    · rintro ⟨hRS, hrespected⟩
      have hIsInS : R.IsIn S := by simpa [restrictionArrangements] using hRS
      have hIsInB : R.IsIn B := ⟨hIsInS.1, fun i ↦
        ⟨hSB (hIsInS.2 i).1, hSB (hIsInS.2 i).2⟩⟩
      exact ⟨by
        simp [respectedRestrictionArrangements, restrictionArrangements,
          hIsInB, hrespected], restrictionCarrier_subset S R hIsInS⟩
  have hbad : badS = (restrictionArrangements S).filter fun R ↦
      ¬R.IsRespected phi := by
    ext R
    simp only [badS, Finset.mem_filter]
    constructor
    · rintro ⟨hRB, hcarrier⟩
      have hbadData := Finset.mem_sdiff.mp hRB
      have hIsInB : R.IsIn B := by
        simpa [restrictionArrangements] using hbadData.1
      have hnotRespected : ¬R.IsRespected phi := by
        intro hrespected
        apply hbadData.2
        simp [respectedRestrictionArrangements, restrictionArrangements,
          hIsInB, hrespected]
      have hRS : R.IsIn S :=
        restriction_isIn_iff S R |>.mpr ⟨hIsInB.1, hcarrier⟩
      exact ⟨by simpa [restrictionArrangements], hnotRespected⟩
    · rintro ⟨hRS, hnotRespected⟩
      have hIsInS : R.IsIn S := by simpa [restrictionArrangements] using hRS
      have hIsInB : R.IsIn B := ⟨hIsInS.1, fun i ↦
        ⟨hSB (hIsInS.2 i).1, hSB (hIsInS.2 i).2⟩⟩
      refine ⟨Finset.mem_sdiff.mpr ⟨by simpa [restrictionArrangements], ?_⟩,
        restrictionCarrier_subset S R hIsInS⟩
      intro hgood
      have : R.IsRespected phi := by
        simpa [respectedRestrictionArrangements, restrictionArrangements,
          hIsInB] using hgood
      exact hnotRespected this
  change goodS.card + badS.card = arrangementCount 8 S
  rw [hgood, hbad]
  rw [Finset.filter_card_add_filter_neg_card_eq_card]
  exact restrictionArrangements_card S

private def restrictionLeft : Finset (Fin 16) :=
  Finset.univ.filter fun i ↦ (i : Nat) < 8

private def restrictionRight : Finset (Fin 16) :=
  Finset.univ.filter fun i ↦ 8 ≤ (i : Nat)

private lemma restriction_zero_mem_left : (0 : Fin 16) ∈ restrictionLeft := by
  simp [restrictionLeft]

private lemma restriction_zero_notMem_right : (0 : Fin 16) ∉ restrictionRight := by
  simp [restrictionRight]

private lemma restriction_additive_ext {N : Nat}
    {x y : Fin 16 → ZMod N} (hx : IsAdditiveTuple (k := 8) x)
    (hy : IsAdditiveTuple (k := 8) y)
    (htail : ∀ i : Fin 15, x i.succ = y i.succ) : x = y := by
  have hoff : ∀ i : Fin 16, i ≠ 0 → x i = y i := by
    intro i hi
    rcases i with ⟨(_ | i), hiBound⟩
    · exact (hi rfl).elim
    · exact htail ⟨i, by omega⟩
  unfold IsAdditiveTuple at hx hy
  change (∑ i ∈ restrictionLeft, x i) = ∑ i ∈ restrictionRight, x i at hx
  change (∑ i ∈ restrictionLeft, y i) = ∑ i ∈ restrictionRight, y i at hy
  have hleft :
      (∑ i ∈ restrictionLeft.erase 0, x i) =
        ∑ i ∈ restrictionLeft.erase 0, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hoff i (Finset.ne_of_mem_erase hi)
  have hright :
      (∑ i ∈ restrictionRight, x i) = ∑ i ∈ restrictionRight, y i := by
    apply Finset.sum_congr rfl
    intro i hi
    apply hoff i
    intro hzero
    subst i
    exact restriction_zero_notMem_right hi
  funext i
  refine Fin.cases ?_ (fun j ↦ htail j) i
  apply add_left_cancel (a := ∑ i ∈ restrictionLeft.erase 0, x i)
  calc
    (∑ i ∈ restrictionLeft.erase 0, x i) + x 0 =
        ∑ i ∈ restrictionLeft, x i :=
      Finset.sum_erase_add _ _ restriction_zero_mem_left
    _ = ∑ i ∈ restrictionRight, x i := hx
    _ = ∑ i ∈ restrictionRight, y i := hright
    _ = ∑ i ∈ restrictionLeft, y i := hy.symm
    _ = (∑ i ∈ restrictionLeft.erase 0, y i) + y 0 := by
      symm
      exact Finset.sum_erase_add _ _ restriction_zero_mem_left
    _ = (∑ i ∈ restrictionLeft.erase 0, x i) + y 0 := by rw [hleft]

private abbrev restrictionTailCode {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :=
  (Fin 15 → ↑B) × ZMod N × ZMod N

private def encodeRestrictionArrangement {N : Nat} [NeZero N]
    (B : Finset (Pair N))
    (R : {R : DArrangement N 8 // R.IsIn B}) : restrictionTailCode B :=
  (fun i ↦ ⟨(R.1.x i.succ, R.1.y i.succ), (R.2.2 i.succ).1⟩,
    R.1.y 0, R.1.height)

private lemma encodeRestrictionArrangement_injective {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    Function.Injective (encodeRestrictionArrangement B) := by
  intro R S hcode
  apply Subtype.ext
  have hfun :
      (fun i : Fin 15 ↦
        (⟨(R.1.x i.succ, R.1.y i.succ), (R.2.2 i.succ).1⟩ : ↑B)) =
        fun i : Fin 15 ↦
          ⟨(S.1.x i.succ, S.1.y i.succ), (S.2.2 i.succ).1⟩ :=
    congrArg Prod.fst hcode
  have hxTail : ∀ i : Fin 15, R.1.x i.succ = S.1.x i.succ := by
    intro i
    exact congrArg (fun f ↦ (f i : Pair N).1) hfun
  have hyTail : ∀ i : Fin 15, R.1.y i.succ = S.1.y i.succ := by
    intro i
    exact congrArg (fun f ↦ (f i : Pair N).2) hfun
  have hx : R.1.x = S.1.x :=
    restriction_additive_ext R.2.1 S.2.1 hxTail
  have hy0 : R.1.y 0 = S.1.y 0 :=
    congrArg (fun c ↦ c.2.1) hcode
  have hy : R.1.y = S.1.y := by
    funext i
    refine Fin.cases hy0 (fun j ↦ hyTail j) i
  have hh : R.1.height = S.1.height :=
    congrArg (fun c ↦ c.2.2) hcode
  exact Prod.ext hx (Prod.ext hy hh)

private lemma arrangementCount_le_card_pow {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    arrangementCount 8 B ≤ B.card ^ 15 * N ^ 2 := by
  classical
  unfold arrangementCount countWhere
  calc
    (Finset.univ.filter fun R : DArrangement N 8 ↦ R.IsIn B).card =
        Fintype.card {R : DArrangement N 8 // R.IsIn B} := by
      rw [Finset.filter_congr_decidable]
      exact (Fintype.card_subtype _).symm
    _ ≤ Fintype.card (restrictionTailCode B) :=
      Fintype.card_le_of_injective (encodeRestrictionArrangement B)
        (encodeRestrictionArrangement_injective B)
    _ = B.card ^ 15 * N ^ 2 := by
      simp only [restrictionTailCode, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, ZMod.card]
      ring

/-! ## The one-stage Riesz weight -/

private abbrev restrictionPhaseTriple (N : Nat) :=
  ZMod N × ZMod N × ZMod N

private def restrictionDigit {N : Nat} (j : Fin 4) : ZMod N :=
  ![0, 0, 1, -1] j

private def restrictionSign {N : Nat} (i : Fin 16) : ZMod N :=
  if i ∈ restrictionLeft then 1 else -1

private def restrictionCanonicalDigit (j : restrictionIndex) : Fin 4 :=
  if ((j.1 : Nat) < 8) = j.2 then 2 else 3

private def restrictionNegativeCanonicalDigit (j : restrictionIndex) : Fin 4 :=
  if ((j.1 : Nat) < 8) = j.2 then 3 else 2

private lemma restrictionDigit_canonical {N : Nat} (j : restrictionIndex) :
    restrictionDigit (N := N) (restrictionCanonicalDigit j) =
      if j.2 then restrictionSign (N := N) j.1 else -restrictionSign j.1 := by
  rcases j with ⟨i, b⟩
  simp only [restrictionCanonicalDigit, restrictionSign, restrictionLeft,
    Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp_all [restrictionDigit]

private lemma restrictionDigit_negativeCanonical {N : Nat}
    (j : restrictionIndex) :
    restrictionDigit (N := N) (restrictionNegativeCanonicalDigit j) =
      -(if j.2 then restrictionSign (N := N) j.1 else
        -restrictionSign j.1) := by
  rcases j with ⟨i, b⟩
  simp only [restrictionNegativeCanonicalDigit, restrictionSign, restrictionLeft,
    Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp_all [restrictionDigit]

private lemma restriction_sum_sign_mul {N : Nat} (x : Fin 16 → ZMod N) :
    (∑ i, restrictionSign (N := N) i * x i) =
      (∑ i ∈ restrictionLeft, x i) - ∑ i ∈ restrictionRight, x i := by
  classical
  have hcomp :
      (Finset.univ.filter fun i : Fin 16 ↦ i ∉ restrictionLeft) =
        restrictionRight := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, restrictionLeft,
      restrictionRight]
    omega
  simp_rw [restrictionSign, ite_mul, one_mul, neg_one_mul]
  rw [Finset.sum_ite]
  change (∑ i ∈ restrictionLeft, x i) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin 16 ↦ i ∉ restrictionLeft),
        -x i) = _
  rw [hcomp, Finset.sum_neg_distrib]
  rw [sub_eq_add_neg]

private lemma restriction_sum_sign {N : Nat} :
    (∑ i : Fin 16, restrictionSign (N := N) i) = 0 := by
  have h := restriction_sum_sign_mul (N := N) (fun _ ↦ 1)
  have hleft : restrictionLeft.card = 8 := by decide
  have hright : restrictionRight.card = 8 := by decide
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, hleft, hright,
    Nat.cast_ofNat, sub_self] using h

private def restrictionRelation {N : Nat} (eps : restrictionIndex → Fin 4)
    (f : Pair N → ZMod N) (R : DArrangement N 8) : ZMod N :=
  ∑ j, restrictionDigit (N := N) (eps j) * f (restrictionVertex R j)

private lemma restrictionRelation_canonical_second {N : Nat}
    (R : DArrangement N 8) :
    restrictionRelation restrictionCanonicalDigit (fun z : Pair N ↦ z.2) R = 0 := by
  classical
  unfold restrictionRelation
  rw [Fintype.sum_prod_type]
  simp only [restrictionDigit_canonical, restrictionVertex]
  have hsign := restriction_sum_sign (N := N)
  calc
    (∑ i : Fin 16, ∑ b : Bool,
        (if b then restrictionSign (N := N) i else -restrictionSign i) *
          (R.y i + if b then R.height else 0)) =
        ∑ i : Fin 16, restrictionSign (N := N) i * R.height := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
      ring
    _ = (∑ i : Fin 16, restrictionSign (N := N) i) * R.height := by
      rw [Finset.sum_mul]
    _ = 0 := by rw [hsign, zero_mul]

private lemma restrictionRelation_canonical_mul {N : Nat}
    (R : DArrangement N 8) (hadd : IsAdditiveTuple R.x) :
    restrictionRelation restrictionCanonicalDigit
        (fun z : Pair N ↦ z.1 * z.2) R = 0 := by
  classical
  unfold restrictionRelation
  rw [Fintype.sum_prod_type]
  simp only [restrictionDigit_canonical, restrictionVertex]
  have hsum :
      (∑ i : Fin 16, restrictionSign (N := N) i * R.x i) = 0 := by
    rw [restriction_sum_sign_mul]
    exact sub_eq_zero.mpr hadd
  calc
    (∑ i : Fin 16, ∑ b : Bool,
        (if b then restrictionSign (N := N) i else -restrictionSign i) *
          (R.x i * (R.y i + if b then R.height else 0))) =
        ∑ i : Fin 16,
          (restrictionSign (N := N) i * R.x i) * R.height := by
      apply Finset.sum_congr rfl
      intro i hi
      simp
      ring
    _ = (∑ i : Fin 16,
        restrictionSign (N := N) i * R.x i) * R.height := by
      rw [Finset.sum_mul]
    _ = 0 := by rw [hsum, zero_mul]

private lemma restrictionRelation_negativeCanonical {N : Nat}
    (f : Pair N → ZMod N) (R : DArrangement N 8) :
    restrictionRelation restrictionNegativeCanonicalDigit f R =
      -restrictionRelation restrictionCanonicalDigit f R := by
  classical
  unfold restrictionRelation
  simp_rw [restrictionDigit_negativeCanonical, restrictionDigit_canonical]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private def restrictionPhaseValue {N : Nat}
    (c : restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (z : Pair N) : ZMod N :=
  c.1 * z.2 + c.2.1 * (z.1 * z.2) + c.2.2 * phi z

private def oneStageRestrictionWeight {N : Nat} [NeZero N]
    (c : restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (z : Pair N) : Real :=
  Complex.normSq (1 + exponential (restrictionPhaseValue c phi z)) / 4

private lemma oneStageRestrictionWeight_nonneg {N : Nat} [NeZero N]
    (c : restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (z : Pair N) : 0 ≤ oneStageRestrictionWeight c phi z := by
  unfold oneStageRestrictionWeight
  exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)

private lemma oneStageRestrictionWeight_le_one {N : Nat} [NeZero N]
    (c : restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (z : Pair N) : oneStageRestrictionWeight c phi z ≤ 1 := by
  have hexp : ‖exponential (restrictionPhaseValue c phi z)‖ = 1 :=
    (ZMod.stdAddChar (N := N)).norm_apply _
  have hn : ‖1 + exponential (restrictionPhaseValue c phi z)‖ ≤ 2 := by
    calc
      ‖1 + exponential (restrictionPhaseValue c phi z)‖ ≤
          ‖(1 : Complex)‖ + ‖exponential (restrictionPhaseValue c phi z)‖ :=
        norm_add_le _ _
      _ = 2 := by rw [norm_one, hexp]; norm_num
  have hn0 : 0 ≤ ‖1 + exponential (restrictionPhaseValue c phi z)‖ := norm_nonneg _
  have hsq : Complex.normSq
      (1 + exponential (restrictionPhaseValue c phi z)) ≤ 4 := by
    rw [← Complex.sq_norm]
    nlinarith
  unfold oneStageRestrictionWeight
  linarith

@[simp] private lemma restriction_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma restriction_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

@[simp] private lemma restriction_exponential_zero {N : Nat} [NeZero N] :
    exponential (0 : ZMod N) = 1 := by
  exact AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))

private lemma oneStageRestrictionWeight_complex {N : Nat} [NeZero N]
    (c : restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (z : Pair N) :
    ((oneStageRestrictionWeight c phi z : Real) : Complex) =
      (4 : Complex)⁻¹ * ∑ j : Fin 4,
        exponential (restrictionDigit (N := N) j *
          restrictionPhaseValue c phi z) := by
  let u := exponential (restrictionPhaseValue c phi z)
  have hsum :
      (∑ j : Fin 4, exponential (restrictionDigit (N := N) j *
        restrictionPhaseValue c phi z)) = 2 + u + star u := by
    rw [Fin.sum_univ_four]
    simp [restrictionDigit, u]
    ring
  unfold oneStageRestrictionWeight
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, hsum]
  rw [div_eq_mul_inv, mul_comm _ (4 : Complex)⁻¹]
  change ((4 : Complex)⁻¹ * ((star (1 + u)) * (1 + u))) =
    (4 : Complex)⁻¹ * (2 + u + star u)
  congr 1
  simp only [star_add, star_one]
  have hu : star u * u = 1 := by
    change star (exponential (restrictionPhaseValue c phi z)) *
      exponential (restrictionPhaseValue c phi z) = 1
    rw [restriction_star_exponential, ← restriction_exponential_add]
    simp
  calc
    (1 + star u) * (1 + u) = 1 + u + star u + star u * u := by ring
    _ = 2 + u + star u := by rw [hu]; ring

private lemma restriction_prod_exponential {N : Nat} [NeZero N]
    {I : Type*} [Fintype I] (f : I → ZMod N) :
    ∏ i, exponential (f i) = exponential (∑ i, f i) := by
  classical
  symm
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, restriction_exponential_add,
        Finset.prod_insert hi, ih]

private lemma restriction_phase_relation {N : Nat}
    (c : restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (R : DArrangement N 8) (eps : restrictionIndex → Fin 4) :
    (∑ j, restrictionDigit (N := N) (eps j) *
      restrictionPhaseValue c phi (restrictionVertex R j)) =
      c.1 * restrictionRelation eps (fun z : Pair N ↦ z.2) R +
        c.2.1 * restrictionRelation eps (fun z : Pair N ↦ z.1 * z.2) R +
        c.2.2 * restrictionRelation eps phi R := by
  unfold restrictionPhaseValue restrictionRelation
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma restriction_product_complex {N : Nat} [NeZero N]
    (c : restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (R : DArrangement N 8) :
    ((∏ j : restrictionIndex,
        oneStageRestrictionWeight c phi (restrictionVertex R j) : Real) : Complex) =
      ((4 : Complex)⁻¹) ^ 32 *
        ∑ eps : restrictionIndex → Fin 4,
          exponential
            (c.1 * restrictionRelation eps (fun z : Pair N ↦ z.2) R +
              c.2.1 * restrictionRelation eps
                (fun z : Pair N ↦ z.1 * z.2) R +
              c.2.2 * restrictionRelation eps phi R) := by
  rw [Complex.ofReal_prod]
  simp_rw [oneStageRestrictionWeight_complex]
  rw [Finset.prod_mul_distrib]
  have hcard : Fintype.card restrictionIndex = 32 := by
    simp [restrictionIndex]
  simp only [Finset.prod_const, Finset.card_univ, hcard]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro eps heps
  rw [restriction_prod_exponential]
  congr 1
  exact restriction_phase_relation c phi R eps

private lemma restriction_sum_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) =
      if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private lemma restriction_expect_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    (𝔼 u : ZMod N, exponential (x * u)) = if x = 0 then 1 else 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  by_cases hx : x = 0
  · rw [if_pos hx]
    have h := Fintype.card_mul_expect
      (fun u : ZMod N ↦ exponential (x * u))
    rw [ZMod.card, restriction_sum_exponential_mul, if_pos hx] at h
    exact (mul_left_cancel₀ (Nat.cast_ne_zero.mpr hN) (by simpa using h))
  · rw [if_neg hx]
    have h := Fintype.card_mul_expect
      (fun u : ZMod N ↦ exponential (x * u))
    rw [ZMod.card, restriction_sum_exponential_mul, if_neg hx] at h
    exact (mul_eq_zero.mp (by simpa using h)).resolve_left
      (Nat.cast_ne_zero.mpr hN)

private lemma restriction_expect_phase {N : Nat} [NeZero N]
    (a b d : ZMod N) :
    (𝔼 c : restrictionPhaseTriple N,
      exponential (c.1 * a + c.2.1 * b + c.2.2 * d)) =
        if a = 0 ∧ b = 0 ∧ d = 0 then 1 else 0 := by
  rw [← Finset.univ_product_univ, Finset.expect_product]
  simp_rw [← Finset.univ_product_univ, Finset.expect_product]
  simp_rw [restriction_exponential_add]
  calc
    (𝔼 r : ZMod N,
      𝔼 s : ZMod N,
        𝔼 t : ZMod N,
          exponential (r * a) * exponential (s * b) * exponential (t * d)) =
        (𝔼 r : ZMod N, exponential (r * a)) *
          (𝔼 s : ZMod N, exponential (s * b)) *
            (𝔼 t : ZMod N, exponential (t * d)) := by
      let A : ZMod N → Complex := fun r ↦ exponential (r * a)
      let B : ZMod N → Complex := fun s ↦ exponential (s * b)
      let D : ZMod N → Complex := fun t ↦ exponential (t * d)
      change (𝔼 r : ZMod N, 𝔼 s : ZMod N, 𝔼 t : ZMod N,
          A r * B s * D t) = (𝔼 r : ZMod N, A r) *
            (𝔼 s : ZMod N, B s) * (𝔼 t : ZMod N, D t)
      have ht (r s : ZMod N) :
          (𝔼 t : ZMod N, A r * B s * D t) =
            A r * B s * (𝔼 t : ZMod N, D t) := by
        exact (Finset.mul_expect Finset.univ D (A r * B s)).symm
      simp_rw [ht]
      have hs (r : ZMod N) :
          (𝔼 s : ZMod N, A r * B s * (𝔼 t : ZMod N, D t)) =
            A r * (𝔼 s : ZMod N, B s) * (𝔼 t : ZMod N, D t) := by
        rw [← Finset.expect_mul]
        rw [← Finset.mul_expect]
      simp_rw [hs]
      rw [← Finset.expect_mul]
      rw [← Finset.expect_mul]
    _ = (if a = 0 then 1 else 0) * (if b = 0 then 1 else 0) *
        (if d = 0 then 1 else 0) := by
      rw [show (𝔼 r : ZMod N, exponential (r * a)) =
          if a = 0 then 1 else 0 by
            simpa [mul_comm] using restriction_expect_exponential_mul a,
        show (𝔼 s : ZMod N, exponential (s * b)) =
          if b = 0 then 1 else 0 by
            simpa [mul_comm] using restriction_expect_exponential_mul b,
        show (𝔼 t : ZMod N, exponential (t * d)) =
          if d = 0 then 1 else 0 by
            simpa [mul_comm] using restriction_expect_exponential_mul d]
    _ = if a = 0 ∧ b = 0 ∧ d = 0 then 1 else 0 := by
      by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hd : d = 0 <;>
        simp [ha, hb, hd]

private noncomputable def restrictionValidRelations {N : Nat}
    (phi : Pair N → ZMod N) (R : DArrangement N 8) :
    Finset (restrictionIndex → Fin 4) := by
  classical
  exact Finset.univ.filter fun eps ↦
    restrictionRelation eps (fun z : Pair N ↦ z.2) R = 0 ∧
      restrictionRelation eps (fun z : Pair N ↦ z.1 * z.2) R = 0 ∧
      restrictionRelation eps phi R = 0

private lemma restriction_oneStage_average {N : Nat} [NeZero N]
    (phi : Pair N → ZMod N) (R : DArrangement N 8) :
    (𝔼 c : restrictionPhaseTriple N,
      ∏ j : restrictionIndex,
        oneStageRestrictionWeight c phi (restrictionVertex R j)) =
      ((4 : Real)⁻¹) ^ 32 * (restrictionValidRelations phi R).card := by
  apply Complex.ofReal_injective
  change Complex.ofRealHom
      (𝔼 c : restrictionPhaseTriple N,
        ∏ j : restrictionIndex,
          oneStageRestrictionWeight c phi (restrictionVertex R j)) =
    Complex.ofRealHom
      (((4 : Real)⁻¹) ^ 32 * (restrictionValidRelations phi R).card)
  rw [map_expect Complex.ofRealHom]
  have hrewrite (c : restrictionPhaseTriple N) :
      Complex.ofRealHom
          (∏ j : restrictionIndex,
            oneStageRestrictionWeight c phi (restrictionVertex R j)) =
        ((4 : Complex)⁻¹) ^ 32 *
          ∑ eps : restrictionIndex → Fin 4,
            exponential
              (c.1 * restrictionRelation eps (fun z : Pair N ↦ z.2) R +
                c.2.1 * restrictionRelation eps
                  (fun z : Pair N ↦ z.1 * z.2) R +
                c.2.2 * restrictionRelation eps phi R) := by
    change ((∏ j : restrictionIndex,
      oneStageRestrictionWeight c phi (restrictionVertex R j) : Real) : Complex) = _
    exact restriction_product_complex c phi R
  simp_rw [hrewrite]
  rw [← Finset.mul_expect]
  rw [Finset.expect_sum_comm]
  simp_rw [restriction_expect_phase]
  unfold restrictionValidRelations
  simp_rw [Finset.cast_card, Finset.sum_filter]
  rw [map_mul, map_pow, map_inv₀, map_ofNat, map_sum]
  apply congrArg (((4 : Complex)⁻¹) ^ 32 * ·)
  apply Finset.sum_congr rfl
  intro eps heps
  by_cases hvalid :
      restrictionRelation eps (fun z : Pair N ↦ z.2) R = 0 ∧
        restrictionRelation eps (fun z : Pair N ↦ z.1 * z.2) R = 0 ∧
        restrictionRelation eps phi R = 0 <;> simp [hvalid]

/-! ## Regular arrangements and the two distinguished relations -/

private lemma restrictionRelation_canonical_phi {N : Nat}
    (phi : Pair N → ZMod N) (R : DArrangement N 8) :
    restrictionRelation restrictionCanonicalDigit phi R =
      ∑ i : Fin 16, restrictionSign (N := N) i *
        (phi (R.x i, R.y i + R.height) - phi (R.x i, R.y i)) := by
  classical
  unfold restrictionRelation
  rw [Fintype.sum_prod_type]
  simp only [restrictionDigit_canonical, restrictionVertex]
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring

private lemma restrictionRelation_canonical_phi_iff {N : Nat}
    (phi : Pair N → ZMod N) (R : DArrangement N 8) :
    restrictionRelation restrictionCanonicalDigit phi R = 0 ↔
      R.IsRespected phi := by
  rw [restrictionRelation_canonical_phi, restriction_sum_sign_mul]
  unfold DArrangement.IsRespected IsAdditiveTuple
  exact sub_eq_zero

private def IsRegularRestriction {N : Nat} (R : DArrangement N 8) : Prop :=
  Function.Injective (restrictionVertex R) ∧
    ∀ eps : restrictionIndex → Fin 4,
      restrictionRelation eps (fun z : Pair N ↦ z.2) R = 0 →
      restrictionRelation eps (fun z : Pair N ↦ z.1 * z.2) R = 0 →
      (∀ j, restrictionDigit (N := N) (eps j) = 0) ∨
        eps = restrictionCanonicalDigit ∨
        eps = restrictionNegativeCanonicalDigit

private noncomputable def restrictionZeroRelations (N : Nat) :
    Finset (restrictionIndex → Fin 4) := by
  classical
  exact Finset.univ.filter fun eps ↦
    ∀ j, restrictionDigit (N := N) (eps j) = 0

@[simp] private lemma restrictionDigit_zero {N : Nat} :
    restrictionDigit (N := N) (0 : Fin 4) = 0 := by rfl

@[simp] private lemma restrictionDigit_one {N : Nat} :
    restrictionDigit (N := N) (1 : Fin 4) = 0 := by rfl

@[simp] private lemma restrictionDigit_two {N : Nat} :
    restrictionDigit (N := N) (2 : Fin 4) = 1 := by rfl

@[simp] private lemma restrictionDigit_three {N : Nat} :
    restrictionDigit (N := N) (3 : Fin 4) = -1 := by rfl

private lemma restrictionDigit_eq_zero_iff (N : Nat) [Fact (1 < N)]
    (d : Fin 4) : restrictionDigit (N := N) d = 0 ↔ (d : Nat) < 2 := by
  fin_cases d <;> norm_num [restrictionDigit]

private def restrictionZeroDigitEquiv (N : Nat) [Fact (1 < N)] :
    {d : Fin 4 // restrictionDigit (N := N) d = 0} ≃ Bool where
  toFun d := d.1 = 1
  invFun b := if b then ⟨1, by simp [restrictionDigit]⟩
    else ⟨0, by simp [restrictionDigit]⟩
  left_inv d := by
    have hdlt : (d.1 : Nat) < 2 :=
      (restrictionDigit_eq_zero_iff N d.1).mp d.2
    apply Subtype.ext
    by_cases hd : (d.1 : Nat) = 1
    · have hdfin : d.1 = (1 : Fin 4) := Fin.ext hd
      simp [hdfin]
    · have hdval : (d.1 : Nat) = 0 := by omega
      have hdfin : d.1 = (0 : Fin 4) := Fin.ext hdval
      simp [hdfin]
  right_inv b := by cases b <;> simp

private lemma restriction_zeroDigit_card (N : Nat) (hN : 3 ≤ N) :
    Fintype.card {d : Fin 4 // restrictionDigit (N := N) d = 0} = 2 := by
  letI : Fact (1 < N) := ⟨by omega⟩
  rw [Fintype.card_congr (restrictionZeroDigitEquiv N)]
  decide

private lemma restrictionZeroRelations_card (N : Nat) (hN : 3 ≤ N) :
    (restrictionZeroRelations N).card = 2 ^ 32 := by
  classical
  letI : Fact (1 < N) := ⟨by omega⟩
  have hdigit := restriction_zeroDigit_card N hN
  have hindex : Fintype.card restrictionIndex = 32 := by
    simp [restrictionIndex]
  unfold restrictionZeroRelations
  calc
    (Finset.univ.filter fun eps : restrictionIndex → Fin 4 ↦
        ∀ j, restrictionDigit (N := N) (eps j) = 0).card =
        Fintype.card {eps : restrictionIndex → Fin 4 //
          ∀ j, restrictionDigit (N := N) (eps j) = 0} := by
      rw [Finset.filter_congr_decidable]
      exact (Fintype.card_subtype _).symm
    _ = Fintype.card
        ((j : restrictionIndex) →
          {d : Fin 4 // restrictionDigit (N := N) d = 0}) :=
      Fintype.card_congr
        (Equiv.subtypePiEquivPi
          (p := fun (_ : restrictionIndex) d ↦
            restrictionDigit (N := N) d = 0))
    _ = 2 ^ 32 := by
      rw [Fintype.card_fun, hdigit, hindex]

private lemma restrictionCanonical_not_zeroRelation (N : Nat) (hN : 3 ≤ N) :
    restrictionCanonicalDigit ∉ restrictionZeroRelations N := by
  classical
  letI : Fact (1 < N) := ⟨by omega⟩
  simp only [restrictionZeroRelations, Finset.mem_filter, Finset.mem_univ, true_and]
  push Not
  refine ⟨((0 : Fin 16), false), ?_⟩
  simp [restrictionDigit_canonical, restrictionSign, restrictionLeft]

private lemma restrictionNegativeCanonical_not_zeroRelation
    (N : Nat) (hN : 3 ≤ N) :
    restrictionNegativeCanonicalDigit ∉ restrictionZeroRelations N := by
  classical
  letI : Fact (1 < N) := ⟨by omega⟩
  simp only [restrictionZeroRelations, Finset.mem_filter, Finset.mem_univ, true_and]
  push Not
  refine ⟨((0 : Fin 16), false), ?_⟩
  simp [restrictionDigit_negativeCanonical, restrictionSign, restrictionLeft]

private lemma restrictionCanonical_ne_negative :
    restrictionCanonicalDigit ≠ restrictionNegativeCanonicalDigit := by
  intro h
  have h0 := congrFun h ((0 : Fin 16), false)
  norm_num [restrictionCanonicalDigit, restrictionNegativeCanonicalDigit] at h0
  omega

private lemma restrictionRelation_zero_of_zeroDigits {N : Nat}
    (eps : restrictionIndex → Fin 4)
    (heps : ∀ j, restrictionDigit (N := N) (eps j) = 0)
    (f : Pair N → ZMod N) (R : DArrangement N 8) :
    restrictionRelation eps f R = 0 := by
  unfold restrictionRelation
  apply Finset.sum_eq_zero
  intro j hj
  rw [heps j, zero_mul]

private lemma restrictionValidRelations_eq_zero_of_regular {N : Nat}
    (hN : 3 ≤ N) (phi : Pair N → ZMod N) (R : DArrangement N 8)
    (hadd : IsAdditiveTuple R.x) (hreg : IsRegularRestriction R)
    (hbad : ¬ R.IsRespected phi) :
    restrictionValidRelations phi R = restrictionZeroRelations N := by
  classical
  ext eps
  simp only [restrictionValidRelations, restrictionZeroRelations,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hy, hxy, hphi⟩
    rcases hreg.2 eps hy hxy with hzero | hcanon | hneg
    · exact hzero
    · subst eps
      exact (hbad (restrictionRelation_canonical_phi_iff phi R |>.mp hphi)).elim
    · subst eps
      have hc : restrictionRelation restrictionCanonicalDigit phi R = 0 := by
        rw [restrictionRelation_negativeCanonical] at hphi
        exact neg_eq_zero.mp hphi
      exact (hbad (restrictionRelation_canonical_phi_iff phi R |>.mp hc)).elim
  · intro hzero
    exact ⟨restrictionRelation_zero_of_zeroDigits eps hzero _ _,
      restrictionRelation_zero_of_zeroDigits eps hzero _ _,
      restrictionRelation_zero_of_zeroDigits eps hzero _ _⟩

private lemma restrictionValidRelations_eq_insert_of_regular {N : Nat}
    (hN : 3 ≤ N) (phi : Pair N → ZMod N) (R : DArrangement N 8)
    (hadd : IsAdditiveTuple R.x) (hreg : IsRegularRestriction R)
    (hgood : R.IsRespected phi) :
    restrictionValidRelations phi R =
      insert restrictionCanonicalDigit
        (insert restrictionNegativeCanonicalDigit (restrictionZeroRelations N)) := by
  classical
  ext eps
  simp only [restrictionValidRelations, restrictionZeroRelations,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨hy, hxy, hphi⟩
    rcases hreg.2 eps hy hxy with hzero | hcanon | hneg
    · exact Or.inr (Or.inr hzero)
    · exact Or.inl hcanon
    · exact Or.inr (Or.inl hneg)
  · rintro (hcanon | hneg | hzero)
    · subst eps
      exact ⟨restrictionRelation_canonical_second R,
        restrictionRelation_canonical_mul R hadd,
        restrictionRelation_canonical_phi_iff phi R |>.mpr hgood⟩
    · subst eps
      rw [restrictionRelation_negativeCanonical,
        restrictionRelation_negativeCanonical,
        restrictionRelation_negativeCanonical]
      simp only [restrictionRelation_canonical_second R,
        restrictionRelation_canonical_mul R hadd,
        restrictionRelation_canonical_phi_iff phi R |>.mpr hgood, neg_zero,
        and_self]
    · exact ⟨restrictionRelation_zero_of_zeroDigits eps hzero _ _,
        restrictionRelation_zero_of_zeroDigits eps hzero _ _,
        restrictionRelation_zero_of_zeroDigits eps hzero _ _⟩

private lemma restrictionValidRelations_card_regular_good {N : Nat}
    (hN : 3 ≤ N) (phi : Pair N → ZMod N) (R : DArrangement N 8)
    (hadd : IsAdditiveTuple R.x) (hreg : IsRegularRestriction R)
    (hgood : R.IsRespected phi) :
    (restrictionValidRelations phi R).card = 2 ^ 32 + 2 := by
  classical
  rw [restrictionValidRelations_eq_insert_of_regular hN phi R hadd hreg hgood]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem
        (restrictionNegativeCanonical_not_zeroRelation N hN),
      restrictionZeroRelations_card N hN]
  · simp only [Finset.mem_insert, not_or]
    exact ⟨restrictionCanonical_ne_negative,
      restrictionCanonical_not_zeroRelation N hN⟩

private lemma restrictionValidRelations_card_regular_bad {N : Nat}
    (hN : 3 ≤ N) (phi : Pair N → ZMod N) (R : DArrangement N 8)
    (hadd : IsAdditiveTuple R.x) (hreg : IsRegularRestriction R)
    (hbad : ¬ R.IsRespected phi) :
    (restrictionValidRelations phi R).card = 2 ^ 32 := by
  rw [restrictionValidRelations_eq_zero_of_regular hN phi R hadd hreg hbad,
    restrictionZeroRelations_card N hN]

private lemma restriction_regular_good_average_base {N : Nat}
    (hN : 3 ≤ N) (phi : Pair N → ZMod N) (R : DArrangement N 8)
    (hadd : IsAdditiveTuple R.x) (hreg : IsRegularRestriction R)
    (hgood : R.IsRespected phi) :
    ((4 : Real)⁻¹) ^ 32 * (restrictionValidRelations phi R).card =
      ((2 : Real)⁻¹) ^ 32 * (1 + ((2 : Real)⁻¹) ^ 31) := by
  rw [restrictionValidRelations_card_regular_good hN phi R hadd hreg hgood]
  norm_num

private lemma restriction_regular_bad_average_base {N : Nat}
    (hN : 3 ≤ N) (phi : Pair N → ZMod N) (R : DArrangement N 8)
    (hadd : IsAdditiveTuple R.x) (hreg : IsRegularRestriction R)
    (hbad : ¬R.IsRespected phi) :
    ((4 : Real)⁻¹) ^ 32 * (restrictionValidRelations phi R).card =
      ((2 : Real)⁻¹) ^ 32 := by
  rw [restrictionValidRelations_card_regular_bad hN phi R hadd hreg hbad]
  norm_num

private lemma restriction_amplification_step :
    (2 : Real) ≤
      (1 + ((2 : Real)⁻¹) ^ 31) ^ ((2 : Nat) ^ 31) := by
  have hbern := one_add_mul_le_pow
    (a := ((2 : Real)⁻¹) ^ 31) (by norm_num :
      (-2 : Real) ≤ ((2 : Real)⁻¹) ^ 31) ((2 : Nat) ^ 31)
  norm_num at hbern ⊢
  exact hbern

private noncomputable def restrictionTarget (alpha eta : Real) : Real :=
  (alpha * eta / 4) ^ ((2 : Nat) ^ 36)

private lemma restrictionTarget_eq (alpha eta : Real) :
    restrictionTarget alpha eta =
      (alpha * eta / 4) ^ ((2 : Nat) ^ 36) := by rfl

attribute [irreducible] restrictionTarget

private lemma restriction_exists_stage_margin (alpha eta : Real)
    (halpha : 0 < alpha) (heta : 0 < eta)
    (halpha_one : alpha ≤ 1) (heta_one : eta ≤ 1) :
    ∃ m : Nat, 0 <
      (((2 : Real)⁻¹) ^ 32) ^ ((2 : Nat) ^ 31 * m) *
          (alpha * eta *
              (1 + ((2 : Real)⁻¹) ^ 31) ^ ((2 : Nat) ^ 31 * m) - 1) -
        eta * restrictionTarget alpha eta := by
  let a := alpha * eta
  have ha : 0 < a := mul_pos halpha heta
  have haone : a ≤ 1 := by
    dsimp [a]
    calc
      alpha * eta ≤ 1 * eta :=
        mul_le_mul_of_nonneg_right halpha_one heta.le
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left heta_one (by norm_num)
      _ = 1 := mul_one _
  obtain ⟨n : Nat, hnupper, hnlower⟩ :=
    exists_nat_pow_near_of_lt_one
      (x := a / 2) (y := (2 : Real)⁻¹)
      (by positivity) (by nlinarith) (by norm_num) (by norm_num)
  let m := n + 1
  let q : Real := ((2 : Real)⁻¹) ^ m
  have hqpos : 0 < q := by positivity
  have hqupper : q < a / 2 := by
    exact hnupper
  have hqlower : a / 4 ≤ q := by
    dsimp [q, m]
    rw [pow_succ]
    norm_num
    nlinarith
  let amp : Real := 1 + ((2 : Real)⁻¹) ^ 31
  let K : Nat := (2 : Nat) ^ 31
  let E : Nat := (2 : Nat) ^ 36
  have hamp : (2 : Real) ≤ amp ^ K := by
    exact restriction_amplification_step
  have hamp_pow : (2 : Real) ^ m ≤ amp ^ (K * m) := by
    calc
      (2 : Real) ^ m ≤ (amp ^ K) ^ m :=
        pow_le_pow_left₀ (by norm_num) hamp m
      _ = amp ^ (K * m) := (pow_mul amp K m).symm
  have hqmul : q * (2 : Real) ^ m = 1 := by
    dsimp [q]
    rw [← mul_pow]
    norm_num
  have htwo : 2 < a * (2 : Real) ^ m := by
    have hmul := mul_lt_mul_of_pos_right hqupper
      (pow_pos (by norm_num : (0 : Real) < 2) m)
    rw [hqmul] at hmul
    nlinarith
  have hfactor : 1 < a * amp ^ (K * m) - 1 := by
    have hamp_a : a * (2 : Real) ^ m ≤ a * amp ^ (K * m) :=
      mul_le_mul_of_nonneg_left hamp_pow ha.le
    nlinarith
  have hpower :
      (((2 : Real)⁻¹) ^ 32) ^ (K * m) = q ^ E := by
    have hKE : 32 * K = E := by decide
    calc
      (((2 : Real)⁻¹) ^ 32) ^ (K * m) =
          ((2 : Real)⁻¹) ^ (32 * (K * m)) :=
        (pow_mul ((2 : Real)⁻¹) 32 (K * m)).symm
      _ = ((2 : Real)⁻¹) ^ (E * m) := by rw [← Nat.mul_assoc, hKE]
      _ = ((2 : Real)⁻¹) ^ (m * E) := by rw [Nat.mul_comm E m]
      _ = q ^ E := by
        dsimp [q]
        rw [pow_mul]
  have htarget : eta * (a / 4) ^ E ≤ q ^ E := by
    calc
      eta * (a / 4) ^ E ≤ 1 * (a / 4) ^ E :=
        mul_le_mul_of_nonneg_right heta_one (pow_nonneg (by positivity) _)
      _ = (a / 4) ^ E := one_mul _
      _ ≤ q ^ E := pow_le_pow_left₀ (by positivity) hqlower E
  have hstrict : q ^ E < q ^ E * (a * amp ^ (K * m) - 1) := by
    have h := mul_lt_mul_of_pos_left hfactor (pow_pos hqpos E)
    rw [mul_one] at h
    exact h
  refine ⟨m, ?_⟩
  unfold restrictionTarget
  change 0 <
    (((2 : Real)⁻¹) ^ 32) ^ (K * m) *
        (a * amp ^ (K * m) - 1) - eta * (a / 4) ^ E
  rw [hpower]
  exact sub_pos.mpr (htarget.trans_lt hstrict)

private lemma restrictionCarrier_prod_of_regular {N : Nat}
    (R : DArrangement N 8) (hreg : IsRegularRestriction R)
    (p : Pair N → Real) :
    (∏ z ∈ restrictionCarrier R, p z) =
      ∏ j : restrictionIndex, p (restrictionVertex R j) := by
  classical
  unfold restrictionCarrier
  rw [Finset.prod_image hreg.1.injOn]

/-! ## Iterating the one-stage restriction -/

private lemma restriction_expect_pi_prod {C : Type*} [Fintype C] [Nonempty C]
    (r : Nat) (f : Fin r → C → Real) :
    (𝔼 g : Fin r → C, ∏ i : Fin r, f i (g i)) =
      ∏ i : Fin r, 𝔼 c : C, f i c := by
  classical
  simp only [Finset.expect_univ, Fintype.card_fun]
  rw [← Fintype.prod_sum]
  simp only [NNRat.smul_def, NNRat.cast_inv, NNRat.cast_natCast,
    Fintype.card_fin, Nat.cast_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp [inv_pow]

/-! The article counts exceptional arrangements over a field.  For the
formal statement we need the following replacement over every `ZMod N`.
The loss is only a square root: averaged over `h`, the kernel of
multiplication by `h` has size `O(N^(3/2))`. -/

private lemma restriction_divisor_small_or_complement_small (n d : Nat)
    (hd : d ∈ n.divisors) : d ≤ n.sqrt ∨ n / d ≤ n.sqrt := by
  by_contra h
  push Not at h
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hdle : n.sqrt + 1 ≤ d := by omega
  have hqle : n.sqrt + 1 ≤ n / d := by omega
  have hmul : (n.sqrt + 1) * (n.sqrt + 1) ≤ d * (n / d) :=
    Nat.mul_le_mul hdle hqle
  have heq : d * (n / d) = n := Nat.mul_div_cancel' hdvd
  rw [heq] at hmul
  exact (Nat.not_le_of_lt (Nat.lt_succ_sqrt n)) hmul

private lemma restriction_card_divisors_le (n : Nat) :
    n.divisors.card ≤ 2 * (n.sqrt + 1) := by
  classical
  let small := n.divisors.filter fun d ↦ d ≤ n.sqrt
  let large := n.divisors.filter fun d ↦ ¬d ≤ n.sqrt
  have hsplit : small.card + large.card = n.divisors.card := by
    exact Finset.filter_card_add_filter_neg_card_eq_card
      (fun d ↦ d ≤ n.sqrt)
  have hsmall : small.card ≤ n.sqrt + 1 := by
    calc
      small.card ≤ (Finset.range (n.sqrt + 1)).card := by
        apply Finset.card_le_card_of_injOn id
        · intro d hd
          change d ∈ small at hd
          rw [Finset.mem_filter] at hd
          exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hd.2)
        · exact fun _ _ _ _ h ↦ h
      _ = n.sqrt + 1 := Finset.card_range _
  have hlarge : large.card ≤ small.card := by
    apply Finset.card_le_card_of_injOn (fun d ↦ n / d)
    · intro d hd
      change d ∈ large at hd
      rcases Finset.mem_filter.mp hd with ⟨hddiv, hdlarge⟩
      change n / d ∈ small
      apply Finset.mem_filter.mpr
      have hcomp := restriction_divisor_small_or_complement_small n d hddiv
      exact ⟨by
        rw [Nat.mem_divisors]
        exact ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hddiv),
          Nat.ne_zero_of_mem_divisors hddiv⟩,
        hcomp.resolve_left hdlarge⟩
    · intro a ha b hb hab
      change a ∈ large at ha
      change b ∈ large at hb
      rcases Finset.mem_filter.mp ha with ⟨hadiv, ha_large⟩
      rcases Finset.mem_filter.mp hb with ⟨hbdiv, hb_large⟩
      exact (Nat.div_eq_iff_eq_of_dvd_dvd
        (Nat.ne_zero_of_mem_divisors hadiv)
        (Nat.dvd_of_mem_divisors hadiv)
        (Nat.dvd_of_mem_divisors hbdiv)).mp hab
  omega

private lemma restriction_sum_gcd_le (n : Nat) (hn : n ≠ 0) :
    (∑ k ∈ Finset.range n, n.gcd k) ≤ 2 * (n.sqrt + 1) * n := by
  have hmaps : ∀ k ∈ Finset.range n, n.gcd k ∈ n.divisors := by
    intro k hk
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn⟩
  calc
    (∑ k ∈ Finset.range n, n.gcd k) =
        ∑ d ∈ n.divisors,
          ∑ k ∈ Finset.range n with n.gcd k = d, n.gcd k := by
      symm
      exact Finset.sum_fiberwise_of_maps_to hmaps _
    _ = ∑ d ∈ n.divisors, d * (n / d).totient := by
      apply Finset.sum_congr rfl
      intro d hd
      have hcard := Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)
      have heq :
          (∑ k ∈ Finset.range n with n.gcd k = d, n.gcd k) =
            ∑ k ∈ Finset.range n with n.gcd k = d, d := by
        apply Finset.sum_congr rfl
        intro k hk
        exact (Finset.mem_filter.mp hk).2
      rw [heq, Finset.sum_const, nsmul_eq_mul, hcard]
      simp [Nat.mul_comm]
    _ ≤ ∑ d ∈ n.divisors, n := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        d * (n / d).totient ≤ d * (n / d) :=
          Nat.mul_le_mul_left d (Nat.totient_le _)
        _ = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    _ = n.divisors.card * n := by simp
    _ ≤ 2 * (n.sqrt + 1) * n :=
      Nat.mul_le_mul_right n (restriction_card_divisors_le n)

private lemma restriction_mulLeft_range {N : Nat} [NeZero N] (h : ZMod N) :
    (AddMonoidHom.mulLeft h).range = AddSubgroup.zmultiples h := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    rw [show x = (x.val : ZMod N) by
      exact (ZMod.natCast_zmod_val x).symm]
    simpa [mul_comm] using
      (AddSubgroup.intCast_mul_mem_zmultiples h (Int.ofNat x.val))
  · intro hz
    rw [AddSubgroup.mem_zmultiples_iff] at hz
    rcases hz with ⟨k, rfl⟩
    refine ⟨(k : ZMod N), ?_⟩
    change h * (k : ZMod N) = k • h
    rw [zsmul_eq_mul]
    exact mul_comm _ _

private lemma restriction_mul_kernel_card {N : Nat} [NeZero N]
    (h : ZMod N) :
    Fintype.card {x : ZMod N // h * x = 0} = N.gcd h.val := by
  let f : ZMod N →+ ZMod N := AddMonoidHom.mulLeft h
  have hrange : Nat.card f.range = addOrderOf h := by
    rw [restriction_mulLeft_range h, Nat.card_zmultiples]
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card (ZMod N) := by
    rw [← AddSubgroup.index_ker f]
    exact f.ker.card_mul_index
  have hord : addOrderOf h = N / N.gcd h.val := by
    calc
      addOrderOf h = addOrderOf (h.val : ZMod N) := by
        rw [ZMod.natCast_zmod_val]
      _ = N / N.gcd h.val := ZMod.addOrderOf_coe h.val (NeZero.ne N)
  have hprod : Nat.card f.ker * (N / N.gcd h.val) = N := by
    rw [← hord, ← hrange]
    simpa using hcard
  have hgpos : 0 < N.gcd h.val :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne N))
  have hdiv : N.gcd h.val ∣ N := Nat.gcd_dvd_left _ _
  have hquotpos : 0 < N / N.gcd h.val :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdiv)
      hgpos
  have heq : N.gcd h.val * (N / N.gcd h.val) = N :=
    Nat.mul_div_cancel' hdiv
  have hker : Nat.card f.ker = N.gcd h.val := by
    exact Nat.eq_of_mul_eq_mul_right hquotpos (hprod.trans heq.symm)
  let e : {x : ZMod N // h * x = 0} ≃ f.ker :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦ by rfl)
  calc
    Fintype.card {x : ZMod N // h * x = 0} = Fintype.card f.ker :=
      Fintype.card_congr e
    _ = N.gcd h.val := by
      simpa [Nat.card_eq_fintype_card] using hker

private lemma restriction_mul_fiber_card_le {N : Nat} [NeZero N]
    (a b : ZMod N) :
    Fintype.card {x : ZMod N // a * x = b} ≤ N.gcd a.val := by
  by_cases hex : ∃ x : ZMod N, a * x = b
  · let x0 := Classical.choose hex
    have hx0 : a * x0 = b := Classical.choose_spec hex
    let enc : {x : ZMod N // a * x = b} →
        {x : ZMod N // a * x = 0} :=
      fun x ↦ ⟨x.1 - x0, by rw [mul_sub, x.2, hx0, sub_self]⟩
    calc
      Fintype.card {x : ZMod N // a * x = b} ≤
          Fintype.card {x : ZMod N // a * x = 0} := by
        apply Fintype.card_le_of_injective enc
        intro x y hxy
        apply Subtype.ext
        have h := congrArg Subtype.val hxy
        dsimp [enc] at h
        exact sub_left_injective h
      _ = N.gcd a.val := restriction_mul_kernel_card a
  · have hempty : IsEmpty {x : ZMod N // a * x = b} :=
      ⟨fun x ↦ hex ⟨x, x.2⟩⟩
    simp only [Fintype.card_eq_zero]
    exact Nat.zero_le _

private lemma restriction_sum_zmod_gcd {N : Nat} [NeZero N] :
    (∑ h : ZMod N, N.gcd h.val) =
      ∑ k ∈ Finset.range N, N.gcd k := by
  cases N with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      calc
        (∑ h : ZMod (n + 1), (n + 1).gcd h.val) =
            ∑ k : Fin (n + 1), (n + 1).gcd k.val := by rfl
        _ = ∑ k ∈ Finset.range (n + 1), (n + 1).gcd k := by
          simpa using (Fin.sum_univ_eq_sum_range
            (fun k : Nat ↦ (n + 1).gcd k) (n + 1))

private lemma restriction_card_le_of_fiber_le {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) (k : Nat)
    (h : ∀ b, Fintype.card {a : A // f a = b} ≤ k) :
    Fintype.card A ≤ Fintype.card B * k := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  calc
    (∑ b : B, Fintype.card {a : A // f a = b}) ≤ ∑ _ : B, k :=
      Finset.sum_le_sum fun b hb ↦ h b
    _ = Fintype.card B * k := by simp

/-! ## Coefficient patterns and exceptional arrangements -/

private def restrictionBottomCoefficient {N : Nat}
    (eps : restrictionIndex → Fin 4) (i : Fin 16) : ZMod N :=
  restrictionDigit (N := N) (eps (i, false))

private def restrictionTopCoefficient {N : Nat}
    (eps : restrictionIndex → Fin 4) (i : Fin 16) : ZMod N :=
  restrictionDigit (N := N) (eps (i, true))

private def restrictionPairCoefficient {N : Nat}
    (eps : restrictionIndex → Fin 4) (i : Fin 16) : ZMod N :=
  restrictionBottomCoefficient eps i + restrictionTopCoefficient eps i

private def restrictionCoefficientDeterminant {N : Nat}
    (eps : restrictionIndex → Fin 4) (i j : Fin 16) : ZMod N :=
  restrictionSign (N := N) i * restrictionTopCoefficient eps j -
    restrictionSign (N := N) j * restrictionTopCoefficient eps i

private lemma restrictionRelation_second_expansion {N : Nat}
    (eps : restrictionIndex → Fin 4) (R : DArrangement N 8) :
    restrictionRelation eps (fun z : Pair N ↦ z.2) R =
      (∑ i : Fin 16, restrictionPairCoefficient eps i * R.y i) +
        R.height * ∑ i : Fin 16, restrictionTopCoefficient eps i := by
  classical
  unfold restrictionRelation restrictionPairCoefficient
    restrictionBottomCoefficient restrictionTopCoefficient
  rw [Fintype.sum_prod_type]
  simp only [restrictionVertex]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring

private lemma restrictionRelation_mul_expansion {N : Nat}
    (eps : restrictionIndex → Fin 4) (R : DArrangement N 8) :
    restrictionRelation eps (fun z : Pair N ↦ z.1 * z.2) R =
      (∑ i : Fin 16,
        restrictionPairCoefficient eps i * (R.x i * R.y i)) +
        R.height * ∑ i : Fin 16,
          restrictionTopCoefficient eps i * R.x i := by
  classical
  unfold restrictionRelation restrictionPairCoefficient
    restrictionBottomCoefficient restrictionTopCoefficient
  rw [Fintype.sum_prod_type]
  simp only [restrictionVertex]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp
  ring

private lemma restrictionSign_cases {N : Nat} (i : Fin 16) :
    restrictionSign (N := N) i = 1 ∨ restrictionSign (N := N) i = -1 := by
  unfold restrictionSign
  split_ifs <;> simp

private lemma restrictionSign_sq {N : Nat} (i : Fin 16) :
    restrictionSign (N := N) i * restrictionSign (N := N) i = 1 := by
  rcases restrictionSign_cases (N := N) i with hi | hi <;> rw [hi] <;> ring

private lemma restrictionDigit_cases {N : Nat} (d : Fin 4) :
    restrictionDigit (N := N) d = 0 ∨
      restrictionDigit (N := N) d = 1 ∨
      restrictionDigit (N := N) d = -1 := by
  fin_cases d <;> simp [restrictionDigit]

private lemma restrictionPairCoefficient_small {N : Nat}
    (eps : restrictionIndex → Fin 4) (i : Fin 16)
    (hi : restrictionPairCoefficient (N := N) eps i ≠ 0) :
    restrictionPairCoefficient (N := N) eps i = 1 ∨
      restrictionPairCoefficient (N := N) eps i = -1 ∨
      restrictionPairCoefficient (N := N) eps i = 2 ∨
      restrictionPairCoefficient (N := N) eps i = -2 := by
  rcases restrictionDigit_cases (N := N) (eps (i, false)) with hb | hb | hb <;>
    rcases restrictionDigit_cases (N := N) (eps (i, true)) with ht | ht | ht <;>
    simp only [restrictionPairCoefficient, restrictionBottomCoefficient,
      restrictionTopCoefficient, hb, ht] at hi ⊢ <;> ring_nf at hi ⊢ <;> aesop

private lemma restrictionCoefficientDeterminant_small {N : Nat}
    (eps : restrictionIndex → Fin 4) (i j : Fin 16)
    (hij : restrictionCoefficientDeterminant (N := N) eps i j ≠ 0) :
    restrictionCoefficientDeterminant (N := N) eps i j = 1 ∨
      restrictionCoefficientDeterminant (N := N) eps i j = -1 ∨
      restrictionCoefficientDeterminant (N := N) eps i j = 2 ∨
      restrictionCoefficientDeterminant (N := N) eps i j = -2 := by
  rcases restrictionSign_cases (N := N) i with hi | hi <;>
    rcases restrictionSign_cases (N := N) j with hj | hj <;>
    rcases restrictionDigit_cases (N := N) (eps (i, true)) with hti | hti | hti <;>
    rcases restrictionDigit_cases (N := N) (eps (j, true)) with htj | htj | htj <;>
    simp only [restrictionCoefficientDeterminant, restrictionTopCoefficient,
      hi, hj, hti, htj] at hij ⊢ <;> ring_nf at hij ⊢ <;> aesop

private lemma restrictionDigit_eq_one_iff (N : Nat) (hN : 3 ≤ N)
    (d : Fin 4) : restrictionDigit (N := N) d = 1 ↔ d = 2 := by
  letI : Fact (1 < N) := ⟨by omega⟩
  letI : Fact (2 < N) := ⟨by omega⟩
  fin_cases d <;>
    simp [restrictionDigit, Fin.ext_iff, ZMod.neg_one_ne_one (n := N)]

private lemma restrictionDigit_eq_neg_one_iff (N : Nat) (hN : 3 ≤ N)
    (d : Fin 4) : restrictionDigit (N := N) d = -1 ↔ d = 3 := by
  letI : Fact (1 < N) := ⟨by omega⟩
  letI : Fact (2 < N) := ⟨by omega⟩
  have hone : (1 : ZMod N) ≠ -1 := (ZMod.neg_one_ne_one (n := N)).symm
  fin_cases d <;> simp [restrictionDigit, Fin.ext_iff, hone]

private lemma restriction_eq_canonical_of_coefficients {N : Nat}
    (hN : 3 ≤ N) (eps : restrictionIndex → Fin 4)
    (hpair : ∀ i, restrictionPairCoefficient (N := N) eps i = 0)
    (htop : ∀ i, restrictionTopCoefficient (N := N) eps i =
      restrictionSign (N := N) i) :
    eps = restrictionCanonicalDigit := by
  funext j
  rcases j with ⟨i, b⟩
  have hp := hpair i
  have ht := htop i
  have hbottom : restrictionBottomCoefficient (N := N) eps i =
      -restrictionSign (N := N) i := by
    unfold restrictionPairCoefficient at hp
    rw [ht] at hp
    exact eq_neg_of_add_eq_zero_left hp
  by_cases hi : (i : Nat) < 8
  · have hs : restrictionSign (N := N) i = 1 := by
      simp [restrictionSign, restrictionLeft, hi]
    cases b with
    | false =>
        rw [hs] at hbottom
        change restrictionDigit (N := N) (eps (i, false)) = -1 at hbottom
        rw [(restrictionDigit_eq_neg_one_iff N hN _).mp hbottom]
        simp [restrictionCanonicalDigit, hi]
    | true =>
        rw [hs] at ht
        change restrictionDigit (N := N) (eps (i, true)) = 1 at ht
        rw [(restrictionDigit_eq_one_iff N hN _).mp ht]
        simp [restrictionCanonicalDigit, hi]
  · have hs : restrictionSign (N := N) i = -1 := by
      simp [restrictionSign, restrictionLeft, hi]
    cases b with
    | false =>
        rw [hs] at hbottom
        have hbottom' : restrictionDigit (N := N) (eps (i, false)) = 1 := by
          simpa only [restrictionBottomCoefficient, neg_neg] using hbottom
        rw [(restrictionDigit_eq_one_iff N hN _).mp hbottom']
        simp [restrictionCanonicalDigit, hi]
    | true =>
        rw [hs] at ht
        change restrictionDigit (N := N) (eps (i, true)) = -1 at ht
        rw [(restrictionDigit_eq_neg_one_iff N hN _).mp ht]
        simp [restrictionCanonicalDigit, hi]

private lemma restriction_eq_negativeCanonical_of_coefficients {N : Nat}
    (hN : 3 ≤ N) (eps : restrictionIndex → Fin 4)
    (hpair : ∀ i, restrictionPairCoefficient (N := N) eps i = 0)
    (htop : ∀ i, restrictionTopCoefficient (N := N) eps i =
      -restrictionSign (N := N) i) :
    eps = restrictionNegativeCanonicalDigit := by
  funext j
  rcases j with ⟨i, b⟩
  have hp := hpair i
  have ht := htop i
  have hbottom : restrictionBottomCoefficient (N := N) eps i =
      restrictionSign (N := N) i := by
    unfold restrictionPairCoefficient at hp
    rw [ht] at hp
    linear_combination hp
  by_cases hi : (i : Nat) < 8
  · have hs : restrictionSign (N := N) i = 1 := by
      simp [restrictionSign, restrictionLeft, hi]
    cases b with
    | false =>
        rw [hs] at hbottom
        change restrictionDigit (N := N) (eps (i, false)) = 1 at hbottom
        rw [(restrictionDigit_eq_one_iff N hN _).mp hbottom]
        simp [restrictionNegativeCanonicalDigit, hi]
    | true =>
        rw [hs] at ht
        have ht' : restrictionDigit (N := N) (eps (i, true)) = -1 := by
          simpa only [restrictionTopCoefficient, neg_one_mul] using ht
        rw [(restrictionDigit_eq_neg_one_iff N hN _).mp ht']
        simp [restrictionNegativeCanonicalDigit, hi]
  · have hs : restrictionSign (N := N) i = -1 := by
      simp [restrictionSign, restrictionLeft, hi]
    cases b with
    | false =>
        rw [hs] at hbottom
        change restrictionDigit (N := N) (eps (i, false)) = -1 at hbottom
        rw [(restrictionDigit_eq_neg_one_iff N hN _).mp hbottom]
        simp [restrictionNegativeCanonicalDigit, hi]
    | true =>
        rw [hs] at ht
        have ht' : restrictionDigit (N := N) (eps (i, true)) = 1 := by
          simpa only [restrictionTopCoefficient, neg_neg] using ht
        rw [(restrictionDigit_eq_one_iff N hN _).mp ht']
        simp [restrictionNegativeCanonicalDigit, hi]

private lemma restriction_coefficient_pattern {N : Nat} (hN : 3 ≤ N)
    (eps : restrictionIndex → Fin 4) :
    (∀ j, restrictionDigit (N := N) (eps j) = 0) ∨
      eps = restrictionCanonicalDigit ∨
      eps = restrictionNegativeCanonicalDigit ∨
      (∃ i, restrictionPairCoefficient (N := N) eps i ≠ 0) ∨
      (∀ i, restrictionPairCoefficient (N := N) eps i = 0) ∧
        ∃ i j, restrictionCoefficientDeterminant (N := N) eps i j ≠ 0 := by
  by_cases hpair_bad : ∃ i, restrictionPairCoefficient (N := N) eps i ≠ 0
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpair_bad)))
  have hpair : ∀ i, restrictionPairCoefficient (N := N) eps i = 0 := by
    push Not at hpair_bad
    exact hpair_bad
  by_cases htop_nonzero : ∃ i, restrictionTopCoefficient (N := N) eps i ≠ 0
  · rcases htop_nonzero with ⟨p, hp⟩
    by_cases hdet_bad :
        ∃ q, restrictionCoefficientDeterminant (N := N) eps p q ≠ 0
    · rcases hdet_bad with ⟨q, hq⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hpair, p, q, hq⟩)))
    have hdet : ∀ q,
        restrictionCoefficientDeterminant (N := N) eps p q = 0 := by
      push Not at hdet_bad
      exact hdet_bad
    have htop_formula : ∀ q,
        restrictionTopCoefficient (N := N) eps q =
          (restrictionSign (N := N) p * restrictionTopCoefficient eps p) *
            restrictionSign (N := N) q := by
      intro q
      have hd := hdet q
      have hs := restrictionSign_sq (N := N) p
      unfold restrictionCoefficientDeterminant at hd
      calc
        restrictionTopCoefficient (N := N) eps q =
            (restrictionSign (N := N) p * restrictionSign (N := N) p) *
              restrictionTopCoefficient eps q := by rw [hs, one_mul]
        _ = restrictionSign (N := N) p *
              (restrictionSign (N := N) p *
                restrictionTopCoefficient eps q) := by ring
        _ = restrictionSign (N := N) p *
              (restrictionSign (N := N) q *
                restrictionTopCoefficient eps p) := by
            rw [sub_eq_zero.mp hd]
        _ = (restrictionSign (N := N) p *
              restrictionTopCoefficient eps p) *
                restrictionSign (N := N) q := by ring
    rcases restrictionDigit_cases (N := N) (eps (p, true)) with htp | htp | htp
    · exact (hp (by simpa [restrictionTopCoefficient] using htp)).elim
    · rcases restrictionSign_cases (N := N) p with hsp | hsp
      · apply Or.inr
        apply Or.inl
        apply restriction_eq_canonical_of_coefficients hN eps hpair
        intro q
        simpa [hsp, restrictionTopCoefficient, htp] using htop_formula q
      · apply Or.inr
        apply Or.inr
        apply Or.inl
        apply restriction_eq_negativeCanonical_of_coefficients hN eps hpair
        intro q
        simpa [hsp, restrictionTopCoefficient, htp] using htop_formula q
    · rcases restrictionSign_cases (N := N) p with hsp | hsp
      · apply Or.inr
        apply Or.inr
        apply Or.inl
        apply restriction_eq_negativeCanonical_of_coefficients hN eps hpair
        intro q
        simpa [hsp, restrictionTopCoefficient, htp] using htop_formula q
      · apply Or.inr
        apply Or.inl
        apply restriction_eq_canonical_of_coefficients hN eps hpair
        intro q
        simpa [hsp, restrictionTopCoefficient, htp] using htop_formula q
  · push Not at htop_nonzero
    apply Or.inl
    intro j
    rcases j with ⟨i, b⟩
    cases b with
    | true =>
        exact htop_nonzero i
    | false =>
        have hp := hpair i
        have ht := htop_nonzero i
        unfold restrictionPairCoefficient at hp
        rw [ht, add_zero] at hp
        exact hp

private lemma restriction_smallCoefficient_fiber_card_le_two {N : Nat}
    [NeZero N] (hN : 3 ≤ N) (c b : ZMod N)
    (hc : c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2) :
    Fintype.card {x : ZMod N // c * x = b} ≤ 2 := by
  rcases hc with rfl | rfl | rfl | rfl
  · have hcard :
        Fintype.card {x : ZMod N // (1 : ZMod N) * x = b} ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      intro x y
      apply Subtype.ext
      simpa using x.2.trans y.2.symm
    omega
  · have hcard :
        Fintype.card {x : ZMod N // (-1 : ZMod N) * x = b} ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      intro x y
      apply Subtype.ext
      have hx : -x.1 = b := by simpa using x.2
      have hy : -y.1 = b := by simpa using y.2
      exact neg_injective (hx.trans hy.symm)
    omega
  · have hval : (2 : ZMod N).val = 2 := ZMod.val_natCast_of_lt
      (lt_of_lt_of_le (by norm_num : 2 < 3) hN)
    have h := restriction_mul_fiber_card_le (2 : ZMod N) b
    rw [hval] at h
    exact h.trans (Nat.gcd_le_right N (by norm_num))
  · let e : {x : ZMod N // (-2 : ZMod N) * x = b} ≃
        {x : ZMod N // (2 : ZMod N) * x = -b} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦ by
        constructor
        · intro hx
          have hx' : -((2 : ZMod N) * x) = b := by
            simpa only [neg_mul] using hx
          have h := congrArg Neg.neg hx'
          simpa using h
        · intro hx
          have h := congrArg Neg.neg hx
          have hx' : -((2 : ZMod N) * x) = b := by simpa using h
          simpa only [neg_mul] using hx')
    rw [Fintype.card_congr e]
    have hval : (2 : ZMod N).val = 2 := ZMod.val_natCast_of_lt
      (lt_of_lt_of_le (by norm_num : 2 < 3) hN)
    have h := restriction_mul_fiber_card_le (2 : ZMod N) (-b)
    rw [hval] at h
    exact h.trans (Nat.gcd_le_right N (by norm_num))

private abbrev restrictionAdditiveXs (N : Nat) :=
  {x : Fin 16 → ZMod N // IsAdditiveTuple (k := 8) x}

private abbrev restrictionXTail (N : Nat) :=
  Fin 15 → ZMod N

private noncomputable instance restrictionAdditiveXsFintype (N : Nat) [NeZero N] :
    Fintype (restrictionAdditiveXs N) := by
  letI : Finite (restrictionAdditiveXs N) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private def restrictionEncodeAdditiveX {N : Nat} :
    restrictionAdditiveXs N → restrictionXTail N :=
  fun x i ↦ x.1 i.succ

private lemma restrictionEncodeAdditiveX_injective {N : Nat} :
    Function.Injective (restrictionEncodeAdditiveX (N := N)) := by
  intro x y hxy
  apply Subtype.ext
  apply restriction_additive_ext x.2 y.2
  intro i
  exact congrFun hxy i

private lemma restrictionAdditiveXs_card_le {N : Nat} [NeZero N] :
    Fintype.card (restrictionAdditiveXs N) ≤ N ^ 15 := by
  calc
    Fintype.card (restrictionAdditiveXs N) ≤
        Fintype.card (restrictionXTail N) :=
      Fintype.card_le_of_injective restrictionEncodeAdditiveX
        restrictionEncodeAdditiveX_injective
    _ = N ^ 15 := by
      simp [restrictionXTail]

private abbrev restrictionYTail (N : Nat) (i : Fin 16) :=
  {j : Fin 16 // j ≠ i} → ZMod N

private abbrev restrictionPairRelationSolutions {N : Nat} [NeZero N]
    (eps : restrictionIndex → Fin 4) :=
  {R : DArrangement N 8 // IsAdditiveTuple R.x ∧
    restrictionRelation eps (fun z : Pair N ↦ z.2) R = 0}

private noncomputable instance restrictionPairRelationSolutionsFintype
    {N : Nat} [NeZero N] (eps : restrictionIndex → Fin 4) :
    Fintype (restrictionPairRelationSolutions (N := N) eps) := by
  letI : Finite (restrictionPairRelationSolutions (N := N) eps) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev restrictionPairRelationBase (N : Nat) (i : Fin 16) :=
  restrictionAdditiveXs N × (restrictionYTail N i × ZMod N)

private def restrictionPairRelationProjection {N : Nat} [NeZero N]
    (eps : restrictionIndex → Fin 4) (i : Fin 16) :
    restrictionPairRelationSolutions (N := N) eps → restrictionPairRelationBase N i :=
  fun R ↦ ⟨⟨R.1.x, R.2.1⟩,
    ⟨fun j ↦ R.1.y j, R.1.height⟩⟩

private lemma restrictionPairRelationSolutions_card_le {N : Nat} [NeZero N]
    (hN : 3 ≤ N) (eps : restrictionIndex → Fin 4) (i : Fin 16)
    (hi : restrictionPairCoefficient (N := N) eps i ≠ 0) :
    Fintype.card (restrictionPairRelationSolutions (N := N) eps) ≤ 2 * N ^ 31 := by
  classical
  let c := restrictionPairCoefficient (N := N) eps i
  have hc := restrictionPairCoefficient_small eps i hi
  let proj := restrictionPairRelationProjection (N := N) eps i
  have hfiber : ∀ b : restrictionPairRelationBase N i,
      Fintype.card {R : restrictionPairRelationSolutions (N := N) eps // proj R = b} ≤ 2 := by
    intro b
    by_cases hex : Nonempty
        {R : restrictionPairRelationSolutions (N := N) eps // proj R = b}
    · let R₀ := Classical.choice hex
      let enc : {R : restrictionPairRelationSolutions (N := N) eps // proj R = b} →
          {v : ZMod N // c * v = 0} := fun R ↦ by
        let A := R.1.1
        let A₀ := R₀.1.1
        have hproj : proj R.1 = proj R₀.1 := R.2.trans R₀.2.symm
        have hyTail :
            (fun j : {j : Fin 16 // j ≠ i} ↦ A.y j) =
              fun j : {j : Fin 16 // j ≠ i} ↦ A₀.y j :=
          congrArg (fun z ↦ z.2.1) hproj
        have hh : A.height = A₀.height :=
          congrArg (fun z ↦ z.2.2) hproj
        have hyoff : ∀ j : Fin 16, j ≠ i → A.y j = A₀.y j := by
          intro j hj
          exact congrFun hyTail ⟨j, hj⟩
        have hsum :
            (∑ j : Fin 16,
                restrictionPairCoefficient (N := N) eps j * A.y j) -
              (∑ j : Fin 16,
                restrictionPairCoefficient (N := N) eps j * A₀.y j) =
              c * (A.y i - A₀.y i) := by
          rw [← Finset.sum_sub_distrib]
          calc
            (∑ j : Fin 16,
                (restrictionPairCoefficient (N := N) eps j * A.y j -
                  restrictionPairCoefficient (N := N) eps j * A₀.y j)) =
                ∑ j : Fin 16,
                  restrictionPairCoefficient (N := N) eps j *
                    (A.y j - A₀.y j) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = restrictionPairCoefficient (N := N) eps i *
                  (A.y i - A₀.y i) := by
              apply Finset.sum_eq_single i
              · intro j hj hji
                rw [hyoff j hji, sub_self, mul_zero]
              · simp
            _ = c * (A.y i - A₀.y i) := rfl
        have hrel := R.1.2.2
        have hrel₀ := R₀.1.2.2
        rw [restrictionRelation_second_expansion] at hrel hrel₀
        have hdiff :
            (∑ j : Fin 16,
                restrictionPairCoefficient (N := N) eps j * A.y j) -
              (∑ j : Fin 16,
                restrictionPairCoefficient (N := N) eps j * A₀.y j) = 0 := by
          calc
            (∑ j : Fin 16,
                restrictionPairCoefficient (N := N) eps j * A.y j) -
                (∑ j : Fin 16,
                  restrictionPairCoefficient (N := N) eps j * A₀.y j) =
              ((∑ j : Fin 16,
                  restrictionPairCoefficient (N := N) eps j * A.y j) +
                  A.height * ∑ j : Fin 16,
                    restrictionTopCoefficient (N := N) eps j) -
                ((∑ j : Fin 16,
                  restrictionPairCoefficient (N := N) eps j * A₀.y j) +
                  A₀.height * ∑ j : Fin 16,
                    restrictionTopCoefficient (N := N) eps j) := by
                rw [hh]
                ring
            _ = 0 := by rw [hrel, hrel₀, sub_self]
        exact ⟨A.y i - A₀.y i, by rw [← hsum, hdiff]⟩
      have henc : Function.Injective enc := by
        intro R S hRS
        have hproj : proj R.1 = proj S.1 := R.2.trans S.2.symm
        have hx : R.1.1.x = S.1.1.x :=
          congrArg (fun z ↦ z.1.1) hproj
        have hyTail :
            (fun j : {j : Fin 16 // j ≠ i} ↦ R.1.1.y j) =
              fun j : {j : Fin 16 // j ≠ i} ↦ S.1.1.y j :=
          congrArg (fun z ↦ z.2.1) hproj
        have hh : R.1.1.height = S.1.1.height :=
          congrArg (fun z ↦ z.2.2) hproj
        have hyi : R.1.1.y i = S.1.1.y i := by
          have hval := congrArg Subtype.val hRS
          dsimp [enc] at hval
          exact sub_left_injective hval
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · exact hx
        · apply Prod.ext
          · funext j
            by_cases hji : j = i
            · subst j
              exact hyi
            · exact congrFun hyTail ⟨j, hji⟩
          · exact hh
      calc
        Fintype.card {R : restrictionPairRelationSolutions (N := N) eps // proj R = b} ≤
            Fintype.card {v : ZMod N // c * v = 0} :=
          Fintype.card_le_of_injective enc henc
        _ ≤ 2 := restriction_smallCoefficient_fiber_card_le_two hN c 0 hc
    · haveI : IsEmpty
          {R : restrictionPairRelationSolutions (N := N) eps // proj R = b} :=
        ⟨fun R ↦ hex ⟨R⟩⟩
      simp
  have htotal := restriction_card_le_of_fiber_le proj 2 hfiber
  have hbase : Fintype.card (restrictionPairRelationBase N i) ≤ N ^ 31 := by
    calc
      Fintype.card (restrictionPairRelationBase N i) =
          Fintype.card (restrictionAdditiveXs N) * (N ^ 15 * N) := by
        simp [restrictionPairRelationBase, restrictionYTail]
      _ ≤ N ^ 15 * (N ^ 15 * N) := by
        gcongr
        exact restrictionAdditiveXs_card_le
      _ = N ^ 31 := by ring
  calc
    Fintype.card (restrictionPairRelationSolutions (N := N) eps) ≤
        Fintype.card (restrictionPairRelationBase N i) * 2 := htotal
    _ ≤ N ^ 31 * 2 := Nat.mul_le_mul_right 2 hbase
    _ = 2 * N ^ 31 := by ring

private lemma restriction_gcd_two_mul_le {N : Nat} [NeZero N]
    (h : ZMod N) :
    N.gcd ((2 : ZMod N) * h).val ≤ 2 * N.gcd h.val := by
  have hval2 : (2 : ZMod N).val = 2 % N := ZMod.val_natCast N 2
  have hmod : ((2 : ZMod N) * h).val ≡ 2 * h.val [MOD N] := by
    rw [ZMod.val_mul, hval2]
    exact (Nat.mod_modEq ((2 % N) * h.val) N).trans
      ((Nat.mod_modEq 2 N).mul_right h.val)
  have heq : N.gcd ((2 : ZMod N) * h).val = N.gcd (2 * h.val) := by
    rw [Nat.gcd_comm N, Nat.gcd_comm N]
    exact Nat.ModEq.gcd_eq hmod
  rw [heq]
  have hdvd : N.gcd (2 * h.val) ∣ N.gcd 2 * N.gcd h.val := by
    have hdvd' := gcd_mul_dvd_mul_gcd (α := Nat) N 2 h.val
    change N.gcd (2 * h.val) ∣ N.gcd 2 * N.gcd h.val at hdvd'
    exact hdvd'
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hle : N.gcd 2 ≤ 2 := Nat.gcd_le_right N (by norm_num)
  exact le_trans (Nat.le_of_dvd (Nat.mul_pos
    (Nat.gcd_pos_of_pos_left 2 hNpos)
    (Nat.gcd_pos_of_pos_left h.val hNpos)) hdvd)
    (Nat.mul_le_mul_right (N.gcd h.val) hle)

private lemma restriction_smallCoefficient_mul_fiber_card_le {N : Nat}
    [NeZero N] (h : ZMod N) (d b : ZMod N)
    (hd : d = 1 ∨ d = -1 ∨ d = 2 ∨ d = -2) :
    Fintype.card {x : ZMod N // (h * d) * x = b} ≤
      2 * N.gcd h.val := by
  rcases hd with rfl | rfl | rfl | rfl
  · simpa using (restriction_mul_fiber_card_le h b).trans
      (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2))
  · let e : {x : ZMod N // (h * (-1 : ZMod N)) * x = b} ≃
        {x : ZMod N // h * x = -b} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦ by
        constructor <;> intro hx
        · have hx' : -(h * x) = b := by simpa using hx
          have hneg := congrArg Neg.neg hx'
          simpa using hneg
        · have hneg := congrArg Neg.neg hx
          have hx' : -(h * x) = b := by simpa using hneg
          simpa using hx')
    rw [Fintype.card_congr e]
    exact (restriction_mul_fiber_card_le h (-b)).trans
      (Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2))
  · have heq : h * (2 : ZMod N) = 2 * h := mul_comm _ _
    rw [heq]
    exact (restriction_mul_fiber_card_le ((2 : ZMod N) * h) b).trans
      (restriction_gcd_two_mul_le h)
  · let a : ZMod N := (2 : ZMod N) * h
    have heq : h * (-2 : ZMod N) = -a := by dsimp [a]; ring
    rw [heq]
    let e : {x : ZMod N // (-a) * x = b} ≃
        {x : ZMod N // a * x = -b} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦ by
        constructor <;> intro hx
        · have hx' : -(a * x) = b := by simpa using hx
          have hneg := congrArg Neg.neg hx'
          simpa using hneg
        · have hneg := congrArg Neg.neg hx
          have hx' : -(a * x) = b := by simpa using hneg
          simpa using hx')
    rw [Fintype.card_congr e]
    exact (restriction_mul_fiber_card_le a (-b)).trans
      (restriction_gcd_two_mul_le h)

private def restrictionDoubleExceptEquiv (i j : Fin 16) (hij : i ≠ j) :
    {q : Fin 16 // q ≠ i ∧ q ≠ j} ≃
      {q : {q : Fin 16 // q ≠ i} // q ≠ ⟨j, hij.symm⟩} where
  toFun q := ⟨⟨q, q.2.1⟩, by
    intro h
    exact q.2.2 (congrArg Subtype.val h)⟩
  invFun q := ⟨q.1.1, q.1.2, by
    intro h
    apply q.2
    apply Subtype.ext
    exact h⟩
  left_inv q := by rfl
  right_inv q := by rfl

private lemma restrictionDoubleExcept_card (i j : Fin 16) (hij : i ≠ j) :
    Fintype.card {q : Fin 16 // q ≠ i ∧ q ≠ j} = 14 := by
  rw [Fintype.card_congr (restrictionDoubleExceptEquiv i j hij)]
  rw [Fintype.card_subtype_compl]
  simp

private lemma restriction_sum_mul_sub_eq_two {N : Nat}
    (f x y : Fin 16 → ZMod N) (i j : Fin 16) (hij : i ≠ j)
    (hoff : ∀ q, q ≠ i → q ≠ j → x q = y q) :
    (∑ q : Fin 16, f q * x q) - (∑ q : Fin 16, f q * y q) =
      f i * (x i - y i) + f j * (x j - y j) := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ q : Fin 16, (f q * x q - f q * y q)) =
        ∑ q : Fin 16, f q * (x q - y q) := by
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ q ∈ ({i, j} : Finset (Fin 16)), f q * (x q - y q) := by
      symm
      apply Finset.sum_subset (by simp)
      intro q hq hqpair
      have hqi : q ≠ i := by
        intro h
        subst q
        exact hqpair (by simp)
      have hqj : q ≠ j := by
        intro h
        subst q
        exact hqpair (by simp)
      rw [hoff q hqi hqj, sub_self, mul_zero]
    _ = f i * (x i - y i) + f j * (x j - y j) := by
      simp [hij]

private abbrev restrictionDetRelationSolutions {N : Nat} [NeZero N]
    (eps : restrictionIndex → Fin 4) :=
  {R : DArrangement N 8 // IsAdditiveTuple R.x ∧
    restrictionRelation eps (fun z : Pair N ↦ z.1 * z.2) R = 0}

private noncomputable instance restrictionDetRelationSolutionsFintype
    {N : Nat} [NeZero N] (eps : restrictionIndex → Fin 4) :
    Fintype (restrictionDetRelationSolutions (N := N) eps) := by
  letI : Finite (restrictionDetRelationSolutions (N := N) eps) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev restrictionDetRelationAtHeight {N : Nat} [NeZero N]
    (eps : restrictionIndex → Fin 4) (h : ZMod N) :=
  {R : restrictionDetRelationSolutions (N := N) eps // R.1.height = h}

private noncomputable instance restrictionDetRelationAtHeightFintype
    {N : Nat} [NeZero N] (eps : restrictionIndex → Fin 4) (h : ZMod N) :
    Fintype (restrictionDetRelationAtHeight eps h) := by
  letI : Finite (restrictionDetRelationAtHeight eps h) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev restrictionDetRelationBase (N : Nat) (i j : Fin 16) :=
  ({q : Fin 16 // q ≠ i ∧ q ≠ j} → ZMod N) × (Fin 16 → ZMod N)

private def restrictionDetRelationProjection {N : Nat} [NeZero N]
    (eps : restrictionIndex → Fin 4) (h : ZMod N) (i j : Fin 16) :
    restrictionDetRelationAtHeight eps h → restrictionDetRelationBase N i j :=
  fun R ↦ ⟨fun q ↦ R.1.1.x q, R.1.1.y⟩

private lemma restrictionDetRelationAtHeight_card_le {N : Nat} [NeZero N]
    (eps : restrictionIndex → Fin 4)
    (hpair : ∀ q, restrictionPairCoefficient (N := N) eps q = 0)
    (h : ZMod N) (i j : Fin 16)
    (hdet : restrictionCoefficientDeterminant (N := N) eps i j ≠ 0) :
    Fintype.card (restrictionDetRelationAtHeight eps h) ≤
      (2 * N.gcd h.val) * N ^ 30 := by
  classical
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hdet (by simp [restrictionCoefficientDeterminant])
  let d := restrictionCoefficientDeterminant (N := N) eps i j
  have hd := restrictionCoefficientDeterminant_small eps i j hdet
  let proj := restrictionDetRelationProjection (N := N) eps h i j
  have hfiber : ∀ b : restrictionDetRelationBase N i j,
      Fintype.card {R : restrictionDetRelationAtHeight eps h // proj R = b} ≤
        2 * N.gcd h.val := by
    intro b
    by_cases hex : Nonempty
        {R : restrictionDetRelationAtHeight eps h // proj R = b}
    · let R₀ := Classical.choice hex
      let enc : {R : restrictionDetRelationAtHeight eps h // proj R = b} →
          {v : ZMod N // (h * d) * v = 0} := fun R ↦ by
        let A := R.1.1.1
        let A₀ := R₀.1.1.1
        have hproj : proj R.1 = proj R₀.1 := R.2.trans R₀.2.symm
        have hxTail :
            (fun q : {q : Fin 16 // q ≠ i ∧ q ≠ j} ↦ A.x q) =
              fun q : {q : Fin 16 // q ≠ i ∧ q ≠ j} ↦ A₀.x q :=
          congrArg Prod.fst hproj
        have hxoff : ∀ q : Fin 16, q ≠ i → q ≠ j → A.x q = A₀.x q := by
          intro q hqi hqj
          exact congrFun hxTail ⟨q, hqi, hqj⟩
        have haddA :
            (∑ q : Fin 16, restrictionSign (N := N) q * A.x q) = 0 := by
          rw [restriction_sum_sign_mul]
          exact sub_eq_zero.mpr R.1.1.2.1
        have haddA₀ :
            (∑ q : Fin 16, restrictionSign (N := N) q * A₀.x q) = 0 := by
          rw [restriction_sum_sign_mul]
          exact sub_eq_zero.mpr R₀.1.1.2.1
        have haddDiff :
            restrictionSign (N := N) i * (A.x i - A₀.x i) +
                restrictionSign (N := N) j * (A.x j - A₀.x j) = 0 := by
          rw [← restriction_sum_mul_sub_eq_two
            (restrictionSign (N := N)) A.x A₀.x i j hij hxoff]
          rw [haddA, haddA₀, sub_self]
        have hrelA := R.1.1.2.2
        have hrelA₀ := R₀.1.1.2.2
        rw [restrictionRelation_mul_expansion] at hrelA hrelA₀
        simp only [hpair, zero_mul, Finset.sum_const_zero, zero_add] at hrelA hrelA₀
        have htopA :
            h * ∑ q : Fin 16,
              restrictionTopCoefficient (N := N) eps q * A.x q = 0 := by
          simpa only [R.1.2] using hrelA
        have htopA₀ :
            h * ∑ q : Fin 16,
              restrictionTopCoefficient (N := N) eps q * A₀.x q = 0 := by
          simpa only [R₀.1.2] using hrelA₀
        have htopDiff :
            h * (restrictionTopCoefficient (N := N) eps i *
                  (A.x i - A₀.x i) +
                restrictionTopCoefficient (N := N) eps j *
                  (A.x j - A₀.x j)) = 0 := by
          rw [← restriction_sum_mul_sub_eq_two
            (restrictionTopCoefficient (N := N) eps) A.x A₀.x i j hij hxoff]
          calc
            h * ((∑ q : Fin 16,
                restrictionTopCoefficient (N := N) eps q * A.x q) -
                ∑ q : Fin 16,
                  restrictionTopCoefficient (N := N) eps q * A₀.x q) =
                h * (∑ q : Fin 16,
                  restrictionTopCoefficient (N := N) eps q * A.x q) -
                  h * ∑ q : Fin 16,
                    restrictionTopCoefficient (N := N) eps q * A₀.x q := by
                  ring
            _ = 0 := by rw [htopA, htopA₀, sub_self]
        have helim :
            d * (A.x j - A₀.x j) =
              restrictionSign (N := N) i *
                (restrictionTopCoefficient (N := N) eps i *
                    (A.x i - A₀.x i) +
                  restrictionTopCoefficient (N := N) eps j *
                    (A.x j - A₀.x j)) := by
          dsimp [d]
          unfold restrictionCoefficientDeterminant
          linear_combination
            -(restrictionTopCoefficient (N := N) eps i) * haddDiff
        refine ⟨A.x j - A₀.x j, ?_⟩
        calc
          (h * d) * (A.x j - A₀.x j) =
              h * (d * (A.x j - A₀.x j)) := by ring
          _ = restrictionSign (N := N) i *
              (h * (restrictionTopCoefficient (N := N) eps i *
                  (A.x i - A₀.x i) +
                restrictionTopCoefficient (N := N) eps j *
                  (A.x j - A₀.x j))) := by rw [helim]; ring
          _ = 0 := by rw [htopDiff, mul_zero]
      have henc : Function.Injective enc := by
        intro R S hRS
        have hproj : proj R.1 = proj S.1 := R.2.trans S.2.symm
        have hxTail :
            (fun q : {q : Fin 16 // q ≠ i ∧ q ≠ j} ↦ R.1.1.1.x q) =
              fun q : {q : Fin 16 // q ≠ i ∧ q ≠ j} ↦ S.1.1.1.x q :=
          congrArg Prod.fst hproj
        have hxoff : ∀ q : Fin 16, q ≠ i → q ≠ j →
            R.1.1.1.x q = S.1.1.1.x q := by
          intro q hqi hqj
          exact congrFun hxTail ⟨q, hqi, hqj⟩
        have hy : R.1.1.1.y = S.1.1.1.y := congrArg Prod.snd hproj
        have hxj : R.1.1.1.x j = S.1.1.1.x j := by
          have hval := congrArg Subtype.val hRS
          dsimp [enc] at hval
          exact sub_left_injective hval
        have haddR :
            (∑ q : Fin 16,
              restrictionSign (N := N) q * R.1.1.1.x q) = 0 := by
          rw [restriction_sum_sign_mul]
          exact sub_eq_zero.mpr R.1.1.2.1
        have haddS :
            (∑ q : Fin 16,
              restrictionSign (N := N) q * S.1.1.1.x q) = 0 := by
          rw [restriction_sum_sign_mul]
          exact sub_eq_zero.mpr S.1.1.2.1
        have haddDiff :
            restrictionSign (N := N) i *
                (R.1.1.1.x i - S.1.1.1.x i) +
              restrictionSign (N := N) j *
                (R.1.1.1.x j - S.1.1.1.x j) = 0 := by
          rw [← restriction_sum_mul_sub_eq_two
            (restrictionSign (N := N)) R.1.1.1.x S.1.1.1.x i j hij hxoff]
          rw [haddR, haddS, sub_self]
        have hxi : R.1.1.1.x i = S.1.1.1.x i := by
          rw [hxj, sub_self, mul_zero, add_zero] at haddDiff
          rcases restrictionSign_cases (N := N) i with hsi | hsi <;>
            rw [hsi] at haddDiff
          · simpa only [one_mul, sub_eq_zero] using haddDiff
          · have : R.1.1.1.x i - S.1.1.1.x i = 0 := by
              simpa only [neg_one_mul, neg_eq_zero] using haddDiff
            exact sub_eq_zero.mp this
        have hx : R.1.1.1.x = S.1.1.1.x := by
          funext q
          by_cases hqi : q = i
          · subst q
            exact hxi
          by_cases hqj : q = j
          · subst q
            exact hxj
          exact hxoff q hqi hqj
        have hh : R.1.1.1.height = S.1.1.1.height :=
          R.1.2.trans S.1.2.symm
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext hx (Prod.ext hy hh)
      calc
        Fintype.card {R : restrictionDetRelationAtHeight eps h // proj R = b} ≤
            Fintype.card {v : ZMod N // (h * d) * v = 0} :=
          Fintype.card_le_of_injective enc henc
        _ ≤ 2 * N.gcd h.val :=
          restriction_smallCoefficient_mul_fiber_card_le h d 0 hd
    · haveI : IsEmpty
          {R : restrictionDetRelationAtHeight eps h // proj R = b} :=
        ⟨fun R ↦ hex ⟨R⟩⟩
      simp
  have htotal := restriction_card_le_of_fiber_le proj (2 * N.gcd h.val) hfiber
  have hbase : Fintype.card (restrictionDetRelationBase N i j) = N ^ 30 := by
    simp only [restrictionDetRelationBase, Fintype.card_prod,
      Fintype.card_fun, Fintype.card_fin, ZMod.card,
      restrictionDoubleExcept_card i j hij]
    ring
  calc
    Fintype.card (restrictionDetRelationAtHeight eps h) ≤
        Fintype.card (restrictionDetRelationBase N i j) *
          (2 * N.gcd h.val) := htotal
    _ = (2 * N.gcd h.val) * N ^ 30 := by rw [hbase]; ring

private lemma restrictionDetRelationSolutions_card_le {N : Nat} [NeZero N]
    (eps : restrictionIndex → Fin 4)
    (hpair : ∀ q, restrictionPairCoefficient (N := N) eps q = 0)
    (i j : Fin 16)
    (hdet : restrictionCoefficientDeterminant (N := N) eps i j ≠ 0) :
    Fintype.card (restrictionDetRelationSolutions (N := N) eps) ≤
      4 * (N.sqrt + 1) * N ^ 31 := by
  classical
  let height : restrictionDetRelationSolutions (N := N) eps → ZMod N :=
    fun R ↦ R.1.height
  have hdecomp :
      Fintype.card (restrictionDetRelationSolutions (N := N) eps) =
        ∑ h : ZMod N, Fintype.card (restrictionDetRelationAtHeight eps h) := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv height),
      Fintype.card_sigma]
  rw [hdecomp]
  calc
    (∑ h : ZMod N, Fintype.card (restrictionDetRelationAtHeight eps h)) ≤
        ∑ h : ZMod N, (2 * N.gcd h.val) * N ^ 30 :=
      Finset.sum_le_sum fun h hh ↦
        restrictionDetRelationAtHeight_card_le eps hpair h i j hdet
    _ = (2 * N ^ 30) * ∑ h : ZMod N, N.gcd h.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ ≤ (2 * N ^ 30) * (2 * (N.sqrt + 1) * N) := by
      gcongr
      rw [restriction_sum_zmod_gcd]
      exact restriction_sum_gcd_le N (NeZero.ne N)
    _ = 4 * (N.sqrt + 1) * N ^ 31 := by ring

private abbrev restrictionCollisionSolutions {N : Nat} [NeZero N]
    (a b : restrictionIndex) :=
  {R : DArrangement N 8 // IsAdditiveTuple R.x ∧
    restrictionVertex R a = restrictionVertex R b}

private noncomputable instance restrictionCollisionSolutionsFintype
    {N : Nat} [NeZero N] (a b : restrictionIndex) :
    Fintype (restrictionCollisionSolutions (N := N) a b) := by
  letI : Finite (restrictionCollisionSolutions (N := N) a b) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private lemma restrictionCollisionSolutions_card_le {N : Nat} [NeZero N]
    (a b : restrictionIndex) (hab : a ≠ b) :
    Fintype.card (restrictionCollisionSolutions (N := N) a b) ≤ N ^ 31 := by
  classical
  by_cases hij : a.1 = b.1
  · have hbool : a.2 ≠ b.2 := by
      intro hb
      exact hab (Prod.ext hij hb)
    let base := restrictionAdditiveXs N × (Fin 16 → ZMod N)
    let proj : restrictionCollisionSolutions (N := N) a b → base :=
      fun R ↦ ⟨⟨R.1.x, R.2.1⟩, R.1.y⟩
    have hinj : Function.Injective proj := by
      intro R S hRS
      have hx : R.1.x = S.1.x := congrArg (fun z ↦ z.1.1) hRS
      have hy : R.1.y = S.1.y := congrArg Prod.snd hRS
      have hcollR := congrArg Prod.snd R.2.2
      have hcollS := congrArg Prod.snd S.2.2
      simp only [restrictionVertex] at hcollR hcollS
      have hhR : R.1.height = 0 := by
        rcases a with ⟨i, ba⟩
        rcases b with ⟨j, bb⟩
        dsimp at hij hbool hcollR ⊢
        subst j
        fin_cases ba <;> fin_cases bb <;> simp_all
      have hhS : S.1.height = 0 := by
        rcases a with ⟨i, ba⟩
        rcases b with ⟨j, bb⟩
        dsimp at hij hbool hcollS ⊢
        subst j
        fin_cases ba <;> fin_cases bb <;> simp_all
      apply Subtype.ext
      exact Prod.ext hx (Prod.ext hy (hhR.trans hhS.symm))
    calc
      Fintype.card (restrictionCollisionSolutions (N := N) a b) ≤
          Fintype.card base := Fintype.card_le_of_injective proj hinj
      _ = Fintype.card (restrictionAdditiveXs N) * N ^ 16 := by
        simp [base]
      _ ≤ N ^ 15 * N ^ 16 := by
        gcongr
        exact restrictionAdditiveXs_card_le
      _ = N ^ 31 := by ring
  · let base := restrictionAdditiveXs N ×
        (restrictionYTail N a.1 × ZMod N)
    let proj : restrictionCollisionSolutions (N := N) a b → base :=
      fun R ↦ ⟨⟨R.1.x, R.2.1⟩,
        ⟨fun q ↦ R.1.y q, R.1.height⟩⟩
    have hinj : Function.Injective proj := by
      intro R S hRS
      have hx : R.1.x = S.1.x := congrArg (fun z ↦ z.1.1) hRS
      have hyTail :
          (fun q : {q : Fin 16 // q ≠ a.1} ↦ R.1.y q) =
            fun q : {q : Fin 16 // q ≠ a.1} ↦ S.1.y q :=
        congrArg (fun z ↦ z.2.1) hRS
      have hh : R.1.height = S.1.height := congrArg (fun z ↦ z.2.2) hRS
      have hyoff : ∀ q : Fin 16, q ≠ a.1 → R.1.y q = S.1.y q := by
        intro q hq
        exact congrFun hyTail ⟨q, hq⟩
      have hyb : R.1.y b.1 = S.1.y b.1 := hyoff b.1 (Ne.symm hij)
      have hcollR := congrArg Prod.snd R.2.2
      have hcollS := congrArg Prod.snd S.2.2
      simp only [restrictionVertex] at hcollR hcollS
      have hya : R.1.y a.1 = S.1.y a.1 := by
        calc
          R.1.y a.1 =
              (R.1.y a.1 + if a.2 then R.1.height else 0) -
                (if a.2 then R.1.height else 0) := by ring
          _ = (R.1.y b.1 + if b.2 then R.1.height else 0) -
                (if a.2 then R.1.height else 0) := by rw [hcollR]
          _ = (S.1.y b.1 + if b.2 then S.1.height else 0) -
                (if a.2 then S.1.height else 0) := by rw [hyb, hh]
          _ = (S.1.y a.1 + if a.2 then S.1.height else 0) -
                (if a.2 then S.1.height else 0) := by rw [hcollS]
          _ = S.1.y a.1 := by ring
      have hy : R.1.y = S.1.y := by
        funext q
        by_cases hq : q = a.1
        · subst q
          exact hya
        · exact hyoff q hq
      apply Subtype.ext
      exact Prod.ext hx (Prod.ext hy hh)
    calc
      Fintype.card (restrictionCollisionSolutions (N := N) a b) ≤
          Fintype.card base := Fintype.card_le_of_injective proj hinj
      _ = Fintype.card (restrictionAdditiveXs N) * (N ^ 15 * N) := by
        simp [base, restrictionYTail]
      _ ≤ N ^ 15 * (N ^ 15 * N) := by
        gcongr
        exact restrictionAdditiveXs_card_le
      _ = N ^ 31 := by ring

private abbrev restrictionIrregularArrangements (N : Nat) [NeZero N] :=
  {R : DArrangement N 8 // IsAdditiveTuple R.x ∧ ¬IsRegularRestriction R}

private noncomputable instance restrictionIrregularArrangementsFintype
    (N : Nat) [NeZero N] : Fintype (restrictionIrregularArrangements N) := by
  letI : Finite (restrictionIrregularArrangements N) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev restrictionCollisionCode (N : Nat) [NeZero N] :=
  Σ a : restrictionIndex,
    Σ b : {b : restrictionIndex // b ≠ a},
      restrictionCollisionSolutions (N := N) a b.1

private abbrev restrictionPairExceptionalCode (N : Nat) [NeZero N] :=
  Σ eps : restrictionIndex → Fin 4,
    Σ i : {i : Fin 16 //
      restrictionPairCoefficient (N := N) eps i ≠ 0},
      restrictionPairRelationSolutions (N := N) eps

private abbrev restrictionDetCoefficientPatterns (N : Nat) :=
  {eps : restrictionIndex → Fin 4 //
    ∀ q, restrictionPairCoefficient (N := N) eps q = 0}

private abbrev restrictionDetExceptionalCode (N : Nat) [NeZero N] :=
  Σ eps : restrictionDetCoefficientPatterns N,
    Σ i : Fin 16, Σ j : {j : Fin 16 //
      restrictionCoefficientDeterminant (N := N) eps.1 i j ≠ 0},
      restrictionDetRelationSolutions (N := N) eps.1

private abbrev restrictionExceptionalCode (N : Nat) [NeZero N] :=
  restrictionCollisionCode N ⊕
    (restrictionPairExceptionalCode N ⊕ restrictionDetExceptionalCode N)

private noncomputable def restrictionIrregularEncode {N : Nat} [NeZero N]
    (hN : 3 ≤ N) :
    restrictionIrregularArrangements N → restrictionExceptionalCode N :=
  fun R ↦ by
    by_cases hinj : Function.Injective (restrictionVertex R.1)
    · have hfail : ¬∀ eps : restrictionIndex → Fin 4,
          restrictionRelation eps (fun z : Pair N ↦ z.2) R.1 = 0 →
          restrictionRelation eps (fun z : Pair N ↦ z.1 * z.2) R.1 = 0 →
          (∀ q, restrictionDigit (N := N) (eps q) = 0) ∨
            eps = restrictionCanonicalDigit ∨
            eps = restrictionNegativeCanonicalDigit := by
        intro hall
        exact R.2.2 ⟨hinj, hall⟩
      push Not at hfail
      let eps := Classical.choose hfail
      have heps := Classical.choose_spec hfail
      have hy := heps.1
      have hxy := heps.2.1
      have hnontrivial : ¬((∀ q,
          restrictionDigit (N := N) (eps q) = 0) ∨
          eps = restrictionCanonicalDigit ∨
          eps = restrictionNegativeCanonicalDigit) := by
        intro htrivial
        rcases htrivial with hzero | hcanon | hnegative
        · rcases heps.2.2.1 with ⟨q, hq⟩
          exact hq (hzero q)
        · exact heps.2.2.2.1 hcanon
        · exact heps.2.2.2.2 hnegative
      by_cases hpair_bad :
          ∃ i, restrictionPairCoefficient (N := N) eps i ≠ 0
      · let i := Classical.choose hpair_bad
        exact Sum.inr (Sum.inl
          ⟨eps, ⟨i, Classical.choose_spec hpair_bad⟩,
            ⟨R.1, R.2.1, hy⟩⟩)
      · have hpair : ∀ q,
            restrictionPairCoefficient (N := N) eps q = 0 := by
          push Not at hpair_bad
          exact hpair_bad
        have hdet_exists : ∃ i j,
            restrictionCoefficientDeterminant (N := N) eps i j ≠ 0 := by
          rcases restriction_coefficient_pattern hN eps with
            hzero | hcanon | hnegative | hpair_witness | hdet
          · exact (hnontrivial (Or.inl hzero)).elim
          · exact (hnontrivial (Or.inr (Or.inl hcanon))).elim
          · exact (hnontrivial (Or.inr (Or.inr hnegative))).elim
          · exact (hpair_bad hpair_witness).elim
          · exact hdet.2
        let i := Classical.choose hdet_exists
        let j := Classical.choose (Classical.choose_spec hdet_exists)
        have hij := Classical.choose_spec (Classical.choose_spec hdet_exists)
        exact Sum.inr (Sum.inr
          ⟨⟨eps, hpair⟩, i, ⟨j, hij⟩, ⟨R.1, R.2.1, hxy⟩⟩)
    · have hcollision := Function.not_injective_iff.mp hinj
      let a := Classical.choose hcollision
      let b := Classical.choose (Classical.choose_spec hcollision)
      have hab := Classical.choose_spec (Classical.choose_spec hcollision)
      exact Sum.inl ⟨a, ⟨b, Ne.symm hab.2⟩, ⟨R.1, R.2.1, hab.1⟩⟩

private def restrictionExceptionalDecode {N : Nat} [NeZero N] :
    restrictionExceptionalCode N → DArrangement N 8
  | Sum.inl ⟨_, _, R⟩ => R.1
  | Sum.inr (Sum.inl ⟨_, _, R⟩) => R.1
  | Sum.inr (Sum.inr ⟨_, _, _, R⟩) => R.1

private lemma restrictionExceptionalDecode_encode {N : Nat} [NeZero N]
    (hN : 3 ≤ N) (R : restrictionIrregularArrangements N) :
    restrictionExceptionalDecode (restrictionIrregularEncode hN R) = R.1 := by
  classical
  unfold restrictionIrregularEncode
  split
  · simp only
    split <;> simp only [restrictionExceptionalDecode]
  · simp only [restrictionExceptionalDecode]

private lemma restrictionIrregularEncode_injective {N : Nat} [NeZero N]
    (hN : 3 ≤ N) : Function.Injective (restrictionIrregularEncode hN) := by
  intro R S hRS
  apply Subtype.ext
  rw [← restrictionExceptionalDecode_encode hN R,
    ← restrictionExceptionalDecode_encode hN S, hRS]

private lemma restrictionCollisionCode_card_le {N : Nat} [NeZero N] :
    Fintype.card (restrictionCollisionCode N) ≤ 32 * 31 * N ^ 31 := by
  classical
  have hindex : Fintype.card restrictionIndex = 32 := by
    simp [restrictionIndex]
  have hexcept (a : restrictionIndex) :
      Fintype.card {b : restrictionIndex // b ≠ a} = 31 := by
    rw [Fintype.card_subtype_compl (fun b : restrictionIndex ↦ b = a)]
    simp [hindex]
  have hinner (a : restrictionIndex) :
      (∑ _b : {b : restrictionIndex // b ≠ a}, N ^ 31) =
        31 * N ^ 31 := by
    simp [hexcept]
  rw [Fintype.card_sigma]
  calc
    (∑ a : restrictionIndex,
        Fintype.card (Σ b : {b : restrictionIndex // b ≠ a},
          restrictionCollisionSolutions (N := N) a b.1)) =
        ∑ a : restrictionIndex,
          ∑ b : {b : restrictionIndex // b ≠ a},
            Fintype.card
              (restrictionCollisionSolutions (N := N) a b.1) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Fintype.card_sigma]
    _ ≤ ∑ a : restrictionIndex,
          ∑ _b : {b : restrictionIndex // b ≠ a}, N ^ 31 := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact restrictionCollisionSolutions_card_le a b.1 (Ne.symm b.2)
    _ = 32 * 31 * N ^ 31 := by
      simp_rw [hinner]
      simp [hindex]
      ring

private lemma restrictionPairExceptionalCode_card_le {N : Nat} [NeZero N]
    (hN : 3 ≤ N) :
    Fintype.card (restrictionPairExceptionalCode N) ≤
      4 ^ 32 * 16 * (2 * N ^ 31) := by
  classical
  have hindex : Fintype.card restrictionIndex = 32 := by
    simp [restrictionIndex]
  rw [Fintype.card_sigma]
  calc
    (∑ eps : restrictionIndex → Fin 4,
        Fintype.card (Σ _i : {i : Fin 16 //
            restrictionPairCoefficient (N := N) eps i ≠ 0},
          restrictionPairRelationSolutions (N := N) eps)) =
        ∑ eps : restrictionIndex → Fin 4,
          ∑ _i : {i : Fin 16 //
            restrictionPairCoefficient (N := N) eps i ≠ 0},
            Fintype.card (restrictionPairRelationSolutions (N := N) eps) := by
      apply Finset.sum_congr rfl
      intro eps heps
      rw [Fintype.card_sigma]
    _ ≤ ∑ _eps : restrictionIndex → Fin 4, 16 * (2 * N ^ 31) := by
      apply Finset.sum_le_sum
      intro eps heps
      calc
        (∑ i : {i : Fin 16 //
              restrictionPairCoefficient (N := N) eps i ≠ 0},
            Fintype.card (restrictionPairRelationSolutions (N := N) eps)) ≤
            ∑ _i : {i : Fin 16 //
              restrictionPairCoefficient (N := N) eps i ≠ 0},
              2 * N ^ 31 := by
          apply Finset.sum_le_sum
          intro i hi
          exact restrictionPairRelationSolutions_card_le hN eps i.1 i.2
        _ = Fintype.card {i : Fin 16 //
              restrictionPairCoefficient (N := N) eps i ≠ 0} *
                (2 * N ^ 31) := by simp
        _ ≤ 16 * (2 * N ^ 31) := by
          gcongr
          simpa using Fintype.card_subtype_le
    _ = 4 ^ 32 * 16 * (2 * N ^ 31) := by
      simp [hindex]
      ring

private lemma restrictionDetExceptionalCode_card_le {N : Nat} [NeZero N] :
    Fintype.card (restrictionDetExceptionalCode N) ≤
      4 ^ 32 * 16 * 16 * (4 * (N.sqrt + 1) * N ^ 31) := by
  classical
  have hindex : Fintype.card restrictionIndex = 32 := by
    simp [restrictionIndex]
  have hpatterns :
      Fintype.card (restrictionDetCoefficientPatterns N) ≤ 4 ^ 32 := by
    calc
      Fintype.card (restrictionDetCoefficientPatterns N) ≤
          Fintype.card (restrictionIndex → Fin 4) :=
        Fintype.card_subtype_le _
      _ = 4 ^ 32 := by simp [hindex]
  rw [Fintype.card_sigma]
  calc
    (∑ eps : restrictionDetCoefficientPatterns N,
        Fintype.card (Σ i : Fin 16,
          Σ _j : {j : Fin 16 //
            restrictionCoefficientDeterminant (N := N) eps.1 i j ≠ 0},
            restrictionDetRelationSolutions (N := N) eps.1)) =
        ∑ eps : restrictionDetCoefficientPatterns N,
          ∑ i : Fin 16,
            ∑ _j : {j : Fin 16 //
              restrictionCoefficientDeterminant (N := N) eps.1 i j ≠ 0},
              Fintype.card
                (restrictionDetRelationSolutions (N := N) eps.1) := by
      apply Finset.sum_congr rfl
      intro eps heps
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Fintype.card_sigma]
    _ ≤ ∑ _eps : restrictionDetCoefficientPatterns N,
          16 * 16 * (4 * (N.sqrt + 1) * N ^ 31) := by
      apply Finset.sum_le_sum
      intro eps heps
      calc
        (∑ i : Fin 16,
            ∑ j : {j : Fin 16 //
              restrictionCoefficientDeterminant (N := N) eps.1 i j ≠ 0},
                Fintype.card
                  (restrictionDetRelationSolutions (N := N) eps.1)) ≤
            ∑ _i : Fin 16,
              16 * (4 * (N.sqrt + 1) * N ^ 31) := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            (∑ j : {j : Fin 16 //
                restrictionCoefficientDeterminant (N := N) eps.1 i j ≠ 0},
                Fintype.card
                  (restrictionDetRelationSolutions (N := N) eps.1)) ≤
                ∑ _j : {j : Fin 16 //
                  restrictionCoefficientDeterminant (N := N) eps.1 i j ≠ 0},
                    4 * (N.sqrt + 1) * N ^ 31 := by
              apply Finset.sum_le_sum
              intro j hj
              exact restrictionDetRelationSolutions_card_le eps.1 eps.2
                i j.1 j.2
            _ = Fintype.card {j : Fin 16 //
                  restrictionCoefficientDeterminant (N := N) eps.1 i j ≠ 0} *
                    (4 * (N.sqrt + 1) * N ^ 31) := by simp
            _ ≤ 16 * (4 * (N.sqrt + 1) * N ^ 31) := by
              gcongr
              simpa using Fintype.card_subtype_le
        _ = 16 * 16 * (4 * (N.sqrt + 1) * N ^ 31) := by simp; ring
    _ = Fintype.card (restrictionDetCoefficientPatterns N) *
          (16 * 16 * (4 * (N.sqrt + 1) * N ^ 31)) := by simp
    _ ≤ 4 ^ 32 * (16 * 16 * (4 * (N.sqrt + 1) * N ^ 31)) := by
      gcongr
    _ = 4 ^ 32 * 16 * 16 * (4 * (N.sqrt + 1) * N ^ 31) := by ring

private def restrictionExceptionalConstant : Nat :=
  32 * 31 + 4 ^ 32 * 16 * 2 + 4 ^ 32 * 16 * 16 * 4

private lemma restrictionIrregularArrangements_card_le {N : Nat} [NeZero N]
    (hN : 3 ≤ N) :
    Fintype.card (restrictionIrregularArrangements N) ≤
      restrictionExceptionalConstant * (N.sqrt + 1) * N ^ 31 := by
  classical
  have hencode :
      Fintype.card (restrictionIrregularArrangements N) ≤
        Fintype.card (restrictionExceptionalCode N) :=
    Fintype.card_le_of_injective (restrictionIrregularEncode hN)
      (restrictionIrregularEncode_injective hN)
  have hcode : Fintype.card (restrictionExceptionalCode N) =
      Fintype.card (restrictionCollisionCode N) +
        (Fintype.card (restrictionPairExceptionalCode N) +
          Fintype.card (restrictionDetExceptionalCode N)) := by
    rw [Fintype.card_sum, Fintype.card_sum]
  rw [hcode] at hencode
  have hcollision := restrictionCollisionCode_card_le (N := N)
  have hpair := restrictionPairExceptionalCode_card_le (N := N) hN
  have hdet := restrictionDetExceptionalCode_card_le (N := N)
  calc
    Fintype.card (restrictionIrregularArrangements N) ≤
        Fintype.card (restrictionCollisionCode N) +
          (Fintype.card (restrictionPairExceptionalCode N) +
            Fintype.card (restrictionDetExceptionalCode N)) := hencode
    _ ≤ (32 * 31) * N ^ 31 +
          ((4 ^ 32 * 16 * 2) * N ^ 31 +
            (4 ^ 32 * 16 * 16 * 4) * (N.sqrt + 1) * N ^ 31) := by
      apply Nat.add_le_add
      · simpa only [Nat.mul_assoc] using hcollision
      · apply Nat.add_le_add
        · calc
            Fintype.card (restrictionPairExceptionalCode N) ≤
                4 ^ 32 * 16 * (2 * N ^ 31) := hpair
            _ = (4 ^ 32 * 16 * 2) * N ^ 31 := by ring
        · calc
            Fintype.card (restrictionDetExceptionalCode N) ≤
                4 ^ 32 * 16 * 16 *
                  (4 * (N.sqrt + 1) * N ^ 31) := hdet
            _ = (4 ^ 32 * 16 * 16 * 4) *
                (N.sqrt + 1) * N ^ 31 := by ring
    _ ≤ (32 * 31) * (N.sqrt + 1) * N ^ 31 +
          ((4 ^ 32 * 16 * 2) * (N.sqrt + 1) * N ^ 31 +
            (4 ^ 32 * 16 * 16 * 4) * (N.sqrt + 1) * N ^ 31) := by
      have hs : 1 ≤ N.sqrt + 1 := by omega
      have hscale (A : Nat) : A * N ^ 31 ≤ A * (N.sqrt + 1) * N ^ 31 := by
        calc
          A * N ^ 31 = A * (1 * N ^ 31) := by ring
          _ ≤ A * ((N.sqrt + 1) * N ^ 31) :=
            Nat.mul_le_mul_left A (Nat.mul_le_mul_right (N ^ 31) hs)
          _ = A * (N.sqrt + 1) * N ^ 31 := by ring
      exact Nat.add_le_add (hscale (32 * 31))
        (Nat.add_le_add (hscale (4 ^ 32 * 16 * 2)) le_rfl)
    _ = restrictionExceptionalConstant * (N.sqrt + 1) * N ^ 31 := by
      unfold restrictionExceptionalConstant
      ring

private lemma restrictionIrregularArrangements_real_small
    (scale delta : Real) (hscale : 0 < scale) (hdelta : 0 < delta) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
      (Fintype.card (restrictionIrregularArrangements N) : Real) ≤
        delta * scale * (N : Real) ^ 32 := by
  let C : Real := restrictionExceptionalConstant
  have hC : 0 ≤ C := by positivity
  have hden : 0 < delta * scale := mul_pos hdelta hscale
  obtain ⟨k : Nat, hk⟩ :=
    exists_nat_gt ((2 * C) / (delta * scale))
  have hkpos : 0 < k := by
    by_contra hkzero
    have hkzero' : k = 0 := Nat.eq_zero_of_not_pos hkzero
    rw [hkzero', Nat.cast_zero] at hk
    exact (not_lt_of_ge (div_nonneg (mul_nonneg (by norm_num) hC)
      hden.le)) hk
  refine ⟨max 3 (k * k), ?_⟩
  intro N hNZ hN
  have hN3 : 3 ≤ N := (le_max_left 3 (k * k)).trans hN
  have hk2 : k * k ≤ N := (le_max_right 3 (k * k)).trans hN
  have hksqrt : k ≤ N.sqrt := Nat.le_sqrt.mpr hk2
  have hsqrtpos : 1 ≤ N.sqrt := (Nat.succ_le_iff.mpr hkpos).trans hksqrt
  have hsqrtN : N.sqrt ≤ N := Nat.sqrt_le_self N
  have hkN : k ≤ N := hksqrt.trans hsqrtN
  have hmul : k * N.sqrt ≤ N :=
    (Nat.mul_le_mul_right N.sqrt hksqrt).trans (Nat.sqrt_le N)
  have hsizeNat : k * (N.sqrt + 1) ≤ 2 * N := by
    calc
      k * (N.sqrt + 1) = k * N.sqrt + k := by ring
      _ ≤ N + N := Nat.add_le_add hmul hkN
      _ = 2 * N := by ring
  have hsizeReal : (k : Real) * (N.sqrt + 1 : Nat) ≤ 2 * (N : Real) := by
    exact_mod_cast hsizeNat
  have hconst : 2 * C < (delta * scale) * (k : Real) := by
    simpa only [mul_comm] using (div_lt_iff₀ hden).mp hk
  have hconst' :
      2 * C * (N.sqrt + 1 : Nat) ≤
        ((delta * scale) * (k : Real)) * (N.sqrt + 1 : Nat) :=
    mul_le_mul_of_nonneg_right hconst.le (by positivity)
  have hsize' :
      (delta * scale) * ((k : Real) * (N.sqrt + 1 : Nat)) ≤
        (delta * scale) * (2 * (N : Real)) :=
    mul_le_mul_of_nonneg_left hsizeReal hden.le
  have hcoefficient :
      C * (N.sqrt + 1 : Nat) ≤
        (delta * scale) * (N : Real) := by
    nlinarith
  have hcardNat := restrictionIrregularArrangements_card_le (N := N) hN3
  have hcardReal₀ :
      (Fintype.card (restrictionIrregularArrangements N) : Real) ≤
        (restrictionExceptionalConstant : Real) * (N.sqrt + 1 : Nat) *
          (N : Real) ^ 31 := by
    exact_mod_cast hcardNat
  have hcardReal :
      (Fintype.card (restrictionIrregularArrangements N) : Real) ≤
        C * (N.sqrt + 1 : Nat) * (N : Real) ^ 31 := by
    exact hcardReal₀
  calc
    (Fintype.card (restrictionIrregularArrangements N) : Real) ≤
        C * (N.sqrt + 1 : Nat) * (N : Real) ^ 31 := hcardReal
    _ ≤ ((delta * scale) * (N : Real)) * (N : Real) ^ 31 := by
      gcongr
    _ = delta * scale * (N : Real) ^ 32 := by ring

private def multiStageRestrictionWeight {N r : Nat} [NeZero N]
    (C : Fin r → restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (z : Pair N) : Real :=
  ∏ i : Fin r, oneStageRestrictionWeight (C i) phi z

private lemma multiStageRestrictionWeight_nonneg {N r : Nat} [NeZero N]
    (C : Fin r → restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (z : Pair N) : 0 ≤ multiStageRestrictionWeight C phi z := by
  exact Finset.prod_nonneg fun i hi ↦ oneStageRestrictionWeight_nonneg _ _ _

private lemma multiStageRestrictionWeight_le_one {N r : Nat} [NeZero N]
    (C : Fin r → restrictionPhaseTriple N) (phi : Pair N → ZMod N)
    (z : Pair N) : multiStageRestrictionWeight C phi z ≤ 1 := by
  unfold multiStageRestrictionWeight
  exact Finset.prod_le_one (fun _ _ ↦ oneStageRestrictionWeight_nonneg _ _ _)
    (fun _ _ ↦ oneStageRestrictionWeight_le_one _ _ _)

private lemma restriction_multiStage_indexed_average {N r : Nat} [NeZero N]
    (phi : Pair N → ZMod N) (R : DArrangement N 8) :
    (𝔼 C : Fin r → restrictionPhaseTriple N,
      ∏ j : restrictionIndex,
        multiStageRestrictionWeight C phi (restrictionVertex R j)) =
      (((4 : Real)⁻¹) ^ 32 *
        (restrictionValidRelations phi R).card) ^ r := by
  classical
  calc
    (𝔼 C : Fin r → restrictionPhaseTriple N,
        ∏ j : restrictionIndex,
          multiStageRestrictionWeight C phi (restrictionVertex R j)) =
        𝔼 C : Fin r → restrictionPhaseTriple N,
          ∏ i : Fin r, ∏ j : restrictionIndex,
            oneStageRestrictionWeight (C i) phi (restrictionVertex R j) := by
      apply Finset.expect_congr rfl
      intro C hC
      simp only [multiStageRestrictionWeight]
      rw [Finset.prod_comm]
    _ = ∏ _i : Fin r,
          𝔼 c : restrictionPhaseTriple N,
            ∏ j : restrictionIndex,
              oneStageRestrictionWeight c phi (restrictionVertex R j) := by
      exact restriction_expect_pi_prod r
        (fun _i c ↦ ∏ j : restrictionIndex,
          oneStageRestrictionWeight c phi (restrictionVertex R j))
    _ = ∏ _i : Fin r,
          (((4 : Real)⁻¹) ^ 32 *
            (restrictionValidRelations phi R).card) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact restriction_oneStage_average phi R
    _ = (((4 : Real)⁻¹) ^ 32 *
          (restrictionValidRelations phi R).card) ^ r := by simp

private noncomputable def restrictionGoodRegular {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    Finset (DArrangement N 8) := by
  classical
  exact (respectedRestrictionArrangements B phi).filter IsRegularRestriction

private noncomputable def restrictionBadRegular {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    Finset (DArrangement N 8) := by
  classical
  exact (restrictionBadArrangements B phi).filter IsRegularRestriction

private lemma restriction_phase_score_average {N r : Nat} [NeZero N]
    (hN : 3 ≤ N) (eta : Real) (B : Finset (Pair N))
    (phi : Pair N → ZMod N) :
    (𝔼 C : Fin r → restrictionPhaseTriple N,
      (
      eta * (∑ R ∈ restrictionGoodRegular B phi,
        ∏ j : restrictionIndex,
          multiStageRestrictionWeight C phi (restrictionVertex R j)) -
      ∑ R ∈ restrictionBadRegular B phi,
        ∏ j : restrictionIndex,
          multiStageRestrictionWeight C phi (restrictionVertex R j))) =
      eta *
          (((2 : Real)⁻¹) ^ 32 *
            (1 + ((2 : Real)⁻¹) ^ 31)) ^ r *
          (restrictionGoodRegular B phi).card -
        (((2 : Real)⁻¹) ^ 32) ^ r *
          (restrictionBadRegular B phi).card := by
  classical
  have hgoodavg :
      (𝔼 C : Fin r → restrictionPhaseTriple N,
        ∑ R ∈ restrictionGoodRegular B phi,
          ∏ j : restrictionIndex,
            multiStageRestrictionWeight C phi (restrictionVertex R j)) =
        (((2 : Real)⁻¹) ^ 32 *
          (1 + ((2 : Real)⁻¹) ^ 31)) ^ r *
            (restrictionGoodRegular B phi).card := by
    rw [Finset.expect_sum_comm]
    calc
      (∑ R ∈ restrictionGoodRegular B phi,
          𝔼 C : Fin r → restrictionPhaseTriple N,
            ∏ j : restrictionIndex,
              multiStageRestrictionWeight C phi (restrictionVertex R j)) =
          ∑ _R ∈ restrictionGoodRegular B phi,
            (((2 : Real)⁻¹) ^ 32 *
              (1 + ((2 : Real)⁻¹) ^ 31)) ^ r := by
        apply Finset.sum_congr rfl
        intro R hR
        rw [restriction_multiStage_indexed_average]
        have hR' := Finset.mem_filter.mp hR
        have hgoodData :
            R ∈ restrictionArrangements B ∧ R.IsRespected phi := by
          simpa [respectedRestrictionArrangements] using hR'.1
        have hgood : R.IsRespected phi := by
          exact hgoodData.2
        have hadd : IsAdditiveTuple R.x := by
          have hIsIn : R.IsIn B := by
            simpa [restrictionArrangements] using hgoodData.1
          exact hIsIn.1
        rw [restriction_regular_good_average_base hN phi R hadd hR'.2 hgood]
      _ = (((2 : Real)⁻¹) ^ 32 *
            (1 + ((2 : Real)⁻¹) ^ 31)) ^ r *
          (restrictionGoodRegular B phi).card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hbadavg :
      (𝔼 C : Fin r → restrictionPhaseTriple N,
        ∑ R ∈ restrictionBadRegular B phi,
          ∏ j : restrictionIndex,
            multiStageRestrictionWeight C phi (restrictionVertex R j)) =
        (((2 : Real)⁻¹) ^ 32) ^ r *
          (restrictionBadRegular B phi).card := by
    rw [Finset.expect_sum_comm]
    calc
      (∑ R ∈ restrictionBadRegular B phi,
          𝔼 C : Fin r → restrictionPhaseTriple N,
            ∏ j : restrictionIndex,
              multiStageRestrictionWeight C phi (restrictionVertex R j)) =
          ∑ _R ∈ restrictionBadRegular B phi,
            (((2 : Real)⁻¹) ^ 32) ^ r := by
        apply Finset.sum_congr rfl
        intro R hR
        rw [restriction_multiStage_indexed_average]
        have hR' := Finset.mem_filter.mp hR
        have hbadMem := Finset.mem_sdiff.mp hR'.1
        have hadd : IsAdditiveTuple R.x := by
          have hIsIn : R.IsIn B := by
            simpa [restrictionArrangements] using hbadMem.1
          exact hIsIn.1
        have hbad : ¬R.IsRespected phi := by
          intro hrespected
          apply hbadMem.2
          have hIsIn : R.IsIn B := by
            simpa [restrictionArrangements] using hbadMem.1
          simp [respectedRestrictionArrangements, restrictionArrangements,
            hIsIn, hrespected]
        rw [restriction_regular_bad_average_base hN phi R hadd hR'.2 hbad]
      _ = (((2 : Real)⁻¹) ^ 32) ^ r *
          (restrictionBadRegular B phi).card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [Finset.expect_sub_distrib]
  rw [← Finset.mul_expect]
  rw [hgoodavg, hbadavg]
  ring

private noncomputable def restrictionIrregularFinset (N : Nat) [NeZero N] :
    Finset (DArrangement N 8) := by
  classical
  exact Finset.univ.filter fun R ↦
    IsAdditiveTuple R.x ∧ ¬IsRegularRestriction R

private lemma restrictionIrregularFinset_card (N : Nat) [NeZero N] :
    (restrictionIrregularFinset N).card =
      Fintype.card (restrictionIrregularArrangements N) := by
  classical
  unfold restrictionIrregularFinset
  rw [Finset.filter_congr_decidable]
  exact (Fintype.card_subtype (fun R : DArrangement N 8 ↦
    IsAdditiveTuple R.x ∧ ¬IsRegularRestriction R)).symm

private lemma restrictionGoodRegular_card_lower {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    (respectedRestrictionArrangements B phi).card ≤
      (restrictionGoodRegular B phi).card +
        Fintype.card (restrictionIrregularArrangements N) := by
  classical
  let badReg := (respectedRestrictionArrangements B phi).filter
    fun R ↦ ¬IsRegularRestriction R
  have hsplit :
      (restrictionGoodRegular B phi).card + badReg.card =
        (respectedRestrictionArrangements B phi).card := by
    exact Finset.filter_card_add_filter_neg_card_eq_card
      (s := respectedRestrictionArrangements B phi) IsRegularRestriction
  have hsub : badReg ⊆ restrictionIrregularFinset N := by
    intro R hR
    have hR' := Finset.mem_filter.mp hR
    have hgoodData :
        R ∈ restrictionArrangements B ∧ R.IsRespected phi := by
      simpa [respectedRestrictionArrangements] using hR'.1
    have hIsIn : R.IsIn B := by
      simpa [restrictionArrangements] using hgoodData.1
    simp [restrictionIrregularFinset, hIsIn.1, hR'.2]
  have hbadcard : badReg.card ≤
      Fintype.card (restrictionIrregularArrangements N) := by
    calc
      badReg.card ≤ (restrictionIrregularFinset N).card :=
        Finset.card_le_card hsub
      _ = Fintype.card (restrictionIrregularArrangements N) :=
        restrictionIrregularFinset_card N
  omega

private lemma restrictionBadRegular_card_upper {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    (restrictionBadRegular B phi).card ≤ (restrictionArrangements B).card := by
  classical
  apply Finset.card_le_card
  intro R hR
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hR).1).1

private lemma restriction_carrier_score_lower {N r : Nat} [NeZero N]
    (eta : Real) (heta : 0 ≤ eta) (B : Finset (Pair N))
    (phi : Pair N → ZMod N) (C : Fin r → restrictionPhaseTriple N) :
    eta * (∑ R ∈ restrictionGoodRegular B phi,
      ∏ j : restrictionIndex,
        multiStageRestrictionWeight C phi (restrictionVertex R j)) -
      (∑ R ∈ restrictionBadRegular B phi,
        ∏ j : restrictionIndex,
          multiStageRestrictionWeight C phi (restrictionVertex R j)) -
      Fintype.card (restrictionIrregularArrangements N) ≤
    eta * (∑ R ∈ respectedRestrictionArrangements B phi,
      ∏ z ∈ restrictionCarrier R, multiStageRestrictionWeight C phi z) -
      ∑ R ∈ restrictionBadArrangements B phi,
        ∏ z ∈ restrictionCarrier R, multiStageRestrictionWeight C phi z := by
  classical
  let badIrregular := (restrictionBadArrangements B phi).filter
    fun R ↦ ¬IsRegularRestriction R
  have hp0 (z : Pair N) :
      0 ≤ multiStageRestrictionWeight C phi z :=
    multiStageRestrictionWeight_nonneg C phi z
  have hp1 (z : Pair N) :
      multiStageRestrictionWeight C phi z ≤ 1 :=
    multiStageRestrictionWeight_le_one C phi z
  have hgoodSub : restrictionGoodRegular B phi ⊆
      respectedRestrictionArrangements B phi := fun R hR ↦
    (Finset.mem_filter.mp hR).1
  have hgoodSum :
      (∑ R ∈ restrictionGoodRegular B phi,
          ∏ j : restrictionIndex,
            multiStageRestrictionWeight C phi (restrictionVertex R j)) ≤
        ∑ R ∈ respectedRestrictionArrangements B phi,
          ∏ z ∈ restrictionCarrier R, multiStageRestrictionWeight C phi z := by
    calc
      (∑ R ∈ restrictionGoodRegular B phi,
          ∏ j : restrictionIndex,
            multiStageRestrictionWeight C phi (restrictionVertex R j)) =
          ∑ R ∈ restrictionGoodRegular B phi,
            ∏ z ∈ restrictionCarrier R,
              multiStageRestrictionWeight C phi z := by
        apply Finset.sum_congr rfl
        intro R hR
        symm
        exact restrictionCarrier_prod_of_regular R
          (Finset.mem_filter.mp hR).2 _
      _ ≤ ∑ R ∈ respectedRestrictionArrangements B phi,
          ∏ z ∈ restrictionCarrier R,
            multiStageRestrictionWeight C phi z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hgoodSub
        intro R hR hnot
        exact Finset.prod_nonneg fun z hz ↦ hp0 z
  have hbadSplit :
      (∑ R ∈ restrictionBadArrangements B phi,
          ∏ z ∈ restrictionCarrier R,
            multiStageRestrictionWeight C phi z) =
        (∑ R ∈ restrictionBadRegular B phi,
          ∏ z ∈ restrictionCarrier R,
            multiStageRestrictionWeight C phi z) +
        ∑ R ∈ badIrregular,
          ∏ z ∈ restrictionCarrier R,
            multiStageRestrictionWeight C phi z := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := restrictionBadArrangements B phi)
      (p := IsRegularRestriction)]
    rfl
  have hbadRegularEq :
      (∑ R ∈ restrictionBadRegular B phi,
          ∏ z ∈ restrictionCarrier R,
            multiStageRestrictionWeight C phi z) =
        ∑ R ∈ restrictionBadRegular B phi,
          ∏ j : restrictionIndex,
            multiStageRestrictionWeight C phi (restrictionVertex R j) := by
    apply Finset.sum_congr rfl
    intro R hR
    exact restrictionCarrier_prod_of_regular R
      (Finset.mem_filter.mp hR).2 _
  have hbadIrregularSum :
      (∑ R ∈ badIrregular,
          ∏ z ∈ restrictionCarrier R,
            multiStageRestrictionWeight C phi z) ≤
        Fintype.card (restrictionIrregularArrangements N) := by
    have hterm :
        (∑ R ∈ badIrregular,
            ∏ z ∈ restrictionCarrier R,
              multiStageRestrictionWeight C phi z) ≤
          ∑ _R ∈ badIrregular, (1 : Real) := by
      apply Finset.sum_le_sum
      intro R hR
      exact Finset.prod_le_one (fun z hz ↦ hp0 z) (fun z hz ↦ hp1 z)
    have hsub : badIrregular ⊆ restrictionIrregularFinset N := by
      intro R hR
      have hR' := Finset.mem_filter.mp hR
      have hbadMem := Finset.mem_sdiff.mp hR'.1
      have hIsIn : R.IsIn B := by
        simpa [restrictionArrangements] using hbadMem.1
      simp [restrictionIrregularFinset, hIsIn.1, hR'.2]
    calc
      (∑ R ∈ badIrregular,
          ∏ z ∈ restrictionCarrier R,
            multiStageRestrictionWeight C phi z) ≤
          ∑ _R ∈ badIrregular, (1 : Real) := hterm
      _ = (badIrregular.card : Real) := by simp
      _ ≤ (restrictionIrregularFinset N).card := by exact_mod_cast Finset.card_le_card hsub
      _ = Fintype.card (restrictionIrregularArrangements N) := by
        norm_cast
        exact restrictionIrregularFinset_card N
  rw [hbadSplit, hbadRegularEq]
  have hgoodScaled := mul_le_mul_of_nonneg_left hgoodSum heta
  nlinarith

private lemma restriction_arrangement_real_upper {N : Nat} [NeZero N]
    (beta : Real) (B : Finset (Pair N))
    (hBcard : (B.card : Real) = beta * (N : Real) ^ 2) :
    (arrangementCount 8 B : Real) ≤ beta ^ 15 * (N : Real) ^ 32 := by
  have hnat := arrangementCount_le_card_pow B
  have hreal : (arrangementCount 8 B : Real) ≤
      (B.card : Real) ^ 15 * (N : Real) ^ 2 := by
    exact_mod_cast hnat
  calc
    (arrangementCount 8 B : Real) ≤
        (B.card : Real) ^ 15 * (N : Real) ^ 2 := hreal
    _ = beta ^ 15 * (N : Real) ^ 32 := by rw [hBcard]; ring

set_option maxHeartbeats 2000000 in
private theorem restriction_scale_estimate
    (alpha scale eta : Real) (halpha : 0 < alpha) (hscale : 0 < scale)
    (heta : 0 < eta) (heta_one : eta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
      ∀ (B : Finset (Pair N)) (phi : Pair N → ZMod N),
        (arrangementCount 8 B : Real) ≤ scale * (N : Real) ^ 32 →
        alpha * scale * (N : Real) ^ 32 ≤
          respectedArrangementCount 8 B phi →
        ∃ B' : Finset (Pair N), B' ⊆ B ∧
          (alpha * eta / 4) ^ ((2 : Nat) ^ 36) * scale *
              (N : Real) ^ 32 ≤ arrangementCount 8 B' ∧
          (1 - eta) * arrangementCount 8 B' ≤
            respectedArrangementCount 8 B' phi := by
  by_cases halpha_one : alpha ≤ 1
  · obtain ⟨m : Nat, hmargin₀⟩ :=
      restriction_exists_stage_margin alpha eta halpha heta halpha_one heta_one
    let r : Nat := (2 : Nat) ^ 31 * m
    let qb : Real := ((2 : Real)⁻¹) ^ 32
    let amp : Real := 1 + ((2 : Real)⁻¹) ^ 31
    let qg : Real := qb * amp
    let target : Real := restrictionTarget alpha eta
    let margin : Real :=
      qb ^ r * (alpha * eta * amp ^ r - 1) - eta * target
    have hmargin : 0 < margin := by
      exact hmargin₀
    obtain ⟨Nsmall : Nat, hsmall⟩ :=
      restrictionIrregularArrangements_real_small scale (margin / 2)
        hscale (by positivity)
    refine ⟨max 3 Nsmall, ?_⟩
    intro N _ hN B phi harrangementUpper hrespected
    have hN3 : 3 ≤ N := (le_max_left 3 Nsmall).trans hN
    have hNsmall : Nsmall ≤ N := (le_max_right 3 Nsmall).trans hN
    let M : Real := scale * (N : Real) ^ 32
    let exceptional : Real :=
      Fintype.card (restrictionIrregularArrangements N)
    have hNpos : 0 < (N : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hMpos : 0 < M := by
      dsimp [M]
      positivity
    have hexceptional0 : 0 ≤ exceptional := by positivity
    have hexceptional : exceptional ≤ (margin / 2) * M := by
      simpa only [exceptional, M, mul_assoc] using hsmall N hNsmall
    have hgoodCardNat := restrictionGoodRegular_card_lower B phi
    have hgoodCard :
        (respectedArrangementCount 8 B phi : Real) ≤
          ((restrictionGoodRegular B phi).card : Real) + exceptional := by
      rw [← respectedRestrictionArrangements_card]
      dsimp [exceptional]
      exact_mod_cast hgoodCardNat
    have hgoodLower :
        alpha * M - exceptional ≤
          ((restrictionGoodRegular B phi).card : Real) := by
      linarith only [hrespected, hgoodCard]
    have hbadCardNat := restrictionBadRegular_card_upper B phi
    have hbadCard :
        ((restrictionBadRegular B phi).card : Real) ≤
          (restrictionArrangements B).card := by
      exact_mod_cast hbadCardNat
    have hbadUpper :
        ((restrictionBadRegular B phi).card : Real) ≤ M := by
      rw [restrictionArrangements_card] at hbadCard
      exact hbadCard.trans harrangementUpper
    have hqg0 : 0 ≤ qg := by
      dsimp [qg, qb, amp]
      positivity
    have hqg1 : qg ≤ 1 := by
      dsimp [qg, qb, amp]
      norm_num
    have hqgPow0 : 0 ≤ qg ^ r := pow_nonneg hqg0 r
    have hqgPow1 : qg ^ r ≤ 1 := pow_le_one₀ hqg0 hqg1
    have hqbPow0 : 0 ≤ qb ^ r := by
      dsimp [qb]
      positivity
    have hgoodScaled :
        eta * qg ^ r * (alpha * M - exceptional) ≤
          eta * qg ^ r * (restrictionGoodRegular B phi).card :=
      mul_le_mul_of_nonneg_left hgoodLower
        (mul_nonneg heta.le hqgPow0)
    have hbadScaled :
        qb ^ r * (restrictionBadRegular B phi).card ≤ qb ^ r * M :=
      mul_le_mul_of_nonneg_left hbadUpper hqbPow0
    have havgLower :
        qb ^ r * (alpha * eta * amp ^ r - 1) * M -
            eta * qg ^ r * exceptional ≤
          eta * qg ^ r * (restrictionGoodRegular B phi).card -
            qb ^ r * (restrictionBadRegular B phi).card := by
      calc
        qb ^ r * (alpha * eta * amp ^ r - 1) * M -
              eta * qg ^ r * exceptional =
            eta * qg ^ r * (alpha * M - exceptional) - qb ^ r * M := by
          dsimp [qg]
          rw [mul_pow]
          ring
        _ ≤ eta * qg ^ r * (restrictionGoodRegular B phi).card -
              qb ^ r * (restrictionBadRegular B phi).card :=
          sub_le_sub hgoodScaled hbadScaled
    have hetaQ : eta * qg ^ r ≤ 1 := by
      calc
        eta * qg ^ r ≤ 1 * qg ^ r :=
          mul_le_mul_of_nonneg_right heta_one hqgPow0
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hqgPow1 (by norm_num)
        _ = 1 := mul_one _
    have herror : (eta * qg ^ r + 1) * exceptional ≤ margin * M := by
      have hfactor : eta * qg ^ r + 1 ≤ 2 := by linarith only [hetaQ]
      have hfirst := mul_le_mul_of_nonneg_right hfactor hexceptional0
      have hsecond : 2 * exceptional ≤ margin * M := by
        calc
          2 * exceptional ≤ 2 * ((margin / 2) * M) :=
            mul_le_mul_of_nonneg_left hexceptional (by norm_num)
          _ = margin * M := by ring
      exact hfirst.trans hsecond
    have htargetToAverage :
        eta * target * M + exceptional ≤
          eta * qg ^ r * (restrictionGoodRegular B phi).card -
            qb ^ r * (restrictionBadRegular B phi).card := by
      calc
        eta * target * M + exceptional =
            qb ^ r * (alpha * eta * amp ^ r - 1) * M -
                eta * qg ^ r * exceptional -
              (margin * M - (eta * qg ^ r + 1) * exceptional) := by
          dsimp [margin]
          ring
        _ ≤ qb ^ r * (alpha * eta * amp ^ r - 1) * M -
              eta * qg ^ r * exceptional :=
          sub_le_self _ (sub_nonneg.mpr herror)
        _ ≤ eta * qg ^ r * (restrictionGoodRegular B phi).card -
              qb ^ r * (restrictionBadRegular B phi).card := havgLower
    have hphaseExpected :
        eta * target * M + exceptional ≤
          𝔼 C : Fin r → restrictionPhaseTriple N,
            (eta * (∑ R ∈ restrictionGoodRegular B phi,
              ∏ j : restrictionIndex,
                multiStageRestrictionWeight C phi (restrictionVertex R j)) -
              ∑ R ∈ restrictionBadRegular B phi,
                ∏ j : restrictionIndex,
                  multiStageRestrictionWeight C phi
                    (restrictionVertex R j)) := by
      rw [restriction_phase_score_average hN3]
      exact htargetToAverage
    obtain ⟨C, hCmem, hC⟩ := Finset.exists_le_of_le_expect
      (Finset.univ_nonempty : (Finset.univ :
        Finset (Fin r → restrictionPhaseTriple N)).Nonempty) hphaseExpected
    have hcarrierLower :=
      restriction_carrier_score_lower eta heta.le B phi C
    have hcarrierAverage :
        eta * target * M ≤
          eta * (∑ R ∈ respectedRestrictionArrangements B phi,
            ∏ z ∈ restrictionCarrier R,
              multiStageRestrictionWeight C phi z) -
            ∑ R ∈ restrictionBadArrangements B phi,
              ∏ z ∈ restrictionCarrier R,
                multiStageRestrictionWeight C phi z := by
      linarith only [hC, hcarrierLower]
    have hgoodCarrier : ∀ R ∈ respectedRestrictionArrangements B phi,
        restrictionCarrier R ⊆ B := by
      intro R hR
      have hdata : R.IsIn B ∧ R.IsRespected phi := by
        simpa [respectedRestrictionArrangements, restrictionArrangements] using hR
      exact restrictionCarrier_subset B R hdata.1
    have hbadCarrier : ∀ R ∈ restrictionBadArrangements B phi,
        restrictionCarrier R ⊆ B := by
      intro R hR
      have hmem := (Finset.mem_sdiff.mp hR).1
      have hIsIn : R.IsIn B := by simpa [restrictionArrangements] using hmem
      exact restrictionCarrier_subset B R hIsIn
    obtain ⟨B', hB'B, hscore⟩ := exists_subset_count_score
      B (multiStageRestrictionWeight C phi)
      (fun z hz ↦ multiStageRestrictionWeight_nonneg C phi z)
      (fun z hz ↦ multiStageRestrictionWeight_le_one C phi z)
      (respectedRestrictionArrangements B phi)
      (restrictionBadArrangements B phi) restrictionCarrier
      hgoodCarrier hbadCarrier eta (eta * target * M) hcarrierAverage
    let goodCount :=
      ((respectedRestrictionArrangements B phi).filter fun R ↦
        restrictionCarrier R ⊆ B').card
    let badCount :=
      ((restrictionBadArrangements B phi).filter fun R ↦
        restrictionCarrier R ⊆ B').card
    have hgoodCount : goodCount = respectedArrangementCount 8 B' phi := by
      exact restriction_good_restrict_card B B' phi hB'B
    have htotalCount : goodCount + badCount = arrangementCount 8 B' := by
      exact restriction_good_bad_restrict_card B B' phi hB'B
    have htotalCountReal :
        (goodCount : Real) + badCount = arrangementCount 8 B' := by
      exact_mod_cast htotalCount
    have htargetPos : 0 < target := by
      dsimp only [target]
      rw [restrictionTarget_eq]
      exact pow_pos (div_pos (mul_pos halpha heta) (by norm_num)) _
    have harrangementLower :
        target * M ≤ (arrangementCount 8 B' : Real) := by
      change eta * target * M ≤ eta * (goodCount : Real) - badCount at hscore
      have hbad0 : 0 ≤ (badCount : Real) := Nat.cast_nonneg _
      have hgoodLeTotal : (goodCount : Real) ≤ arrangementCount 8 B' := by
        calc
          (goodCount : Real) ≤ (goodCount : Real) + badCount :=
            le_add_of_nonneg_right hbad0
          _ = arrangementCount 8 B' := htotalCountReal
      have hscoreUpper :
          eta * (goodCount : Real) - badCount ≤
            eta * (arrangementCount 8 B' : Real) := by
        calc
          eta * (goodCount : Real) - badCount ≤ eta * goodCount :=
            sub_le_self _ hbad0
          _ ≤ eta * (arrangementCount 8 B' : Real) :=
            mul_le_mul_of_nonneg_left hgoodLeTotal heta.le
      have := hscore.trans hscoreUpper
      apply (mul_le_mul_iff_of_pos_left heta).mp
      calc
        eta * (target * M) = eta * target * M := by ring
        _ ≤ eta * (arrangementCount 8 B' : Real) := this
    have hdensity :
        (1 - eta) * (arrangementCount 8 B' : Real) ≤
          respectedArrangementCount 8 B' phi := by
      change eta * target * M ≤ eta * (goodCount : Real) - badCount at hscore
      have hpositive : 0 ≤ eta * target * M :=
        (mul_pos (mul_pos heta htargetPos) hMpos).le
      have hbad_le : (badCount : Real) ≤ eta * goodCount := by
        exact sub_nonneg.mp (hpositive.trans hscore)
      have hbad0 : 0 ≤ (badCount : Real) := Nat.cast_nonneg _
      have honeeta0 : 0 ≤ 1 - eta := sub_nonneg.mpr heta_one
      have honeeta1 : 1 - eta ≤ 1 := by linarith only [heta]
      have hbadScaled : (1 - eta) * (badCount : Real) ≤ badCount := by
        calc
          (1 - eta) * (badCount : Real) ≤ 1 * badCount :=
            mul_le_mul_of_nonneg_right honeeta1 hbad0
          _ = badCount := one_mul _
      rw [← hgoodCount]
      calc
        (1 - eta) * (arrangementCount 8 B' : Real) =
            (1 - eta) * (goodCount + badCount) := by rw [htotalCountReal]
        _ = (1 - eta) * goodCount + (1 - eta) * badCount := by ring
        _ ≤ (1 - eta) * goodCount + eta * goodCount :=
          by simpa only [add_comm] using
            add_le_add_left (hbadScaled.trans hbad_le)
              ((1 - eta) * (goodCount : Real))
        _ = goodCount := by ring
    refine ⟨B', hB'B, ?_, hdensity⟩
    rw [← restrictionTarget_eq]
    dsimp only [target, M] at harrangementLower
    simpa only [mul_assoc] using harrangementLower
  · refine ⟨1, ?_⟩
    intro N _ hN B phi harrangementUpper hrespected
    exfalso
    let M : Real := scale * (N : Real) ^ 32
    have hNpos : 0 < (N : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hMpos : 0 < M := by
      dsimp [M]
      positivity
    have hrespectedUpperNat := restriction_respected_le_arrangement B phi
    have hrespectedUpper :
        (respectedArrangementCount 8 B phi : Real) ≤
          arrangementCount 8 B := by
      exact_mod_cast hrespectedUpperNat
    have halpha_gt : 1 < alpha := lt_of_not_ge halpha_one
    nlinarith

private lemma restriction_arrangement_ambient_upper {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    (arrangementCount 8 B : Real) ≤ (N : Real) ^ 32 := by
  have hnat := arrangementCount_le_card_pow B
  have hreal : (arrangementCount 8 B : Real) ≤
      (B.card : Real) ^ 15 * (N : Real) ^ 2 := by
    exact_mod_cast hnat
  have hcardNat : B.card ≤ N ^ 2 := by
    calc
      B.card ≤ (Finset.univ : Finset (Pair N)).card :=
        Finset.card_le_card (Finset.subset_univ B)
      _ = Fintype.card (Pair N) := Finset.card_univ
      _ = N ^ 2 := by simp [Pair, pow_two]
  have hcardReal : (B.card : Real) ≤ (N : Real) ^ 2 := by
    exact_mod_cast hcardNat
  calc
    (arrangementCount 8 B : Real) ≤
        (B.card : Real) ^ 15 * (N : Real) ^ 2 := hreal
    _ ≤ ((N : Real) ^ 2) ^ 15 * (N : Real) ^ 2 := by gcongr
    _ = (N : Real) ^ 32 := by ring

/-- A density-uniform form of Lemma 12.5.  Its threshold depends only on the
lower bound for the proportion of respected arrangements, not on the exact
cardinality of the ambient set. -/
theorem lemma_12_5_uniform_holds :
    ∀ alpha eta : Real, 0 < alpha → 0 < eta → eta ≤ 1 →
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
        ∀ (B : Finset (Pair N)) (phi : Pair N → ZMod N),
          alpha * (N : Real) ^ 32 ≤ respectedArrangementCount 8 B phi →
          ∃ B' : Finset (Pair N), B' ⊆ B ∧
            (alpha * eta / 4) ^ ((2 : Nat) ^ 36) * (N : Real) ^ 32 ≤
              arrangementCount 8 B' ∧
            (1 - eta) * arrangementCount 8 B' ≤
              respectedArrangementCount 8 B' phi := by
  intro alpha eta halpha heta heta_one
  obtain ⟨N0, hN0⟩ := restriction_scale_estimate alpha 1 eta halpha
    (by norm_num) heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN B phi hrespected
  have h := hN0 N hN B phi (by
    simpa only [one_mul] using restriction_arrangement_ambient_upper B) (by
    simpa only [mul_one] using hrespected)
  simpa only [one_mul, mul_one] using h

/-- **Lemma 12.5.** The random restriction estimate at exact density. -/
theorem lemma_12_5_holds : lemma_12_5 := by
  intro alpha beta eta halpha hbeta heta heta_one
  obtain ⟨N0, hN0⟩ := restriction_scale_estimate alpha (beta ^ 15) eta
    halpha (pow_pos hbeta _) heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN B phi hBcard hrespected
  exact hN0 N hN B phi
    (restriction_arrangement_real_upper beta B hBcard) hrespected

end LeanProofs.GowersSzemeredi
