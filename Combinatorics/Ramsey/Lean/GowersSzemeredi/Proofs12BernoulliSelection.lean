import GowersSzemeredi.Proofs12Amplification

/-! Finite Bernoulli averaging and score selection for arbitrary hyperedges.
Repeated physical vertices occur once in each carrier. -/
set_option autoImplicit false
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

theorem exists_subset_count_score {X E : Type*} [DecidableEq X]
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

/-- Average over finite seeds before selecting one actual subset. -/
theorem exists_subset_seed_count_score {X E C : Type*} [DecidableEq X]
    [DecidableEq E] [Fintype C] [Nonempty C]
    (U : Finset X) (p : C → X → Real)
    (hp0 : ∀ c x, x ∈ U → 0 ≤ p c x) (hp1 : ∀ c x, x ∈ U → p c x ≤ 1)
    (good bad : Finset E) (carrier : E → Finset X)
    (hgood : ∀ e ∈ good, carrier e ⊆ U) (hbad : ∀ e ∈ bad, carrier e ⊆ U)
    (eta A : Real)
    (haverage : A ≤ 𝔼 c : C,
      (eta * (∑ e ∈ good, ∏ x ∈ carrier e, p c x) -
        ∑ e ∈ bad, ∏ x ∈ carrier e, p c x)) :
    ∃ S ⊆ U, A ≤ eta * ((good.filter fun e ↦ carrier e ⊆ S).card : Real) -
      ((bad.filter fun e ↦ carrier e ⊆ S).card : Real) := by
  obtain ⟨c, _, hc⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty haverage
  exact exists_subset_count_score U (p c) (hp0 c) (hp1 c) good bad carrier hgood hbad eta A hc

/-- A positive score simultaneously retains good mass and controls the bad
proportion. This is the finite selection step used by purification. -/
theorem exists_subset_seed_purification {X E C : Type*} [DecidableEq X]
    [DecidableEq E] [Fintype C] [Nonempty C]
    (U : Finset X) (p : C → X → Real)
    (hp0 : ∀ c x, x ∈ U → 0 ≤ p c x) (hp1 : ∀ c x, x ∈ U → p c x ≤ 1)
    (good bad : Finset E) (carrier : E → Finset X)
    (hgood : ∀ e ∈ good, carrier e ⊆ U) (hbad : ∀ e ∈ bad, carrier e ⊆ U)
    (eta mass : Real) (heta : 0 < eta) (hmass : 0 < mass)
    (haverage : eta * mass ≤ 𝔼 c : C,
      (eta * (∑ e ∈ good, ∏ x ∈ carrier e, p c x) -
        ∑ e ∈ bad, ∏ x ∈ carrier e, p c x)) :
    ∃ S ⊆ U, mass ≤ ((good.filter fun e ↦ carrier e ⊆ S).card : Real) ∧
      ((bad.filter fun e ↦ carrier e ⊆ S).card : Real) ≤
        eta * ((good.filter fun e ↦ carrier e ⊆ S).card : Real) := by
  obtain ⟨S, hS, hscore⟩ := exists_subset_seed_count_score U p hp0 hp1 good bad carrier
    hgood hbad eta (eta * mass) haverage
  have hbad0 : (0 : Real) ≤ (bad.filter fun e ↦ carrier e ⊆ S).card := Nat.cast_nonneg _
  refine ⟨S, hS, ?_, ?_⟩
  · nlinarith only [hscore, hbad0, heta]
  · nlinarith only [hscore, heta, hmass]

end LeanProofs.GowersSzemeredi
