import GowersSzemeredi.Definitions

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

private lemma restrictionWeight_sum {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) :
    ∑ S ∈ U.powerset, restrictionWeight U p S = 1 := by
  have h (x : X) : p x + (1 - p x) = 1 := by ring
  simpa only [restrictionWeight, h, Finset.prod_const_one] using
    (Finset.prod_add p (fun x => 1 - p x) U).symm

private lemma restrictionWeight_event {X : Type*} [DecidableEq X]
    (U C : Finset X) (p : X → Real) (hC : C ⊆ U) :
    ∑ S ∈ U.powerset, restrictionWeight U p S * (if C ⊆ S then 1 else 0) =
      ∏ x ∈ C, p x := by
  calc
    _ = ∑ S ∈ U.powerset, (∏ x ∈ S, p x) *
        ∏ x ∈ U \ S, (if x ∉ C then 1 - p x else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSC : (∀ x ∈ U \ S, x ∉ C) ↔ C ⊆ S := by
        constructor
        · intro h x hx
          by_contra hxs
          exact h x (Finset.mem_sdiff.mpr ⟨hC hx, hxs⟩) hx
        · intro h x hx hxc
          exact (Finset.mem_sdiff.mp hx).2 (h hxc)
      simp only [Finset.prod_ite_zero, hSC]
      by_cases h : C ⊆ S <;> simp [restrictionWeight, h]
    _ = ∏ x ∈ U, (p x + if x ∉ C then 1 - p x else 0) :=
      (Finset.prod_add p (fun x => if x ∉ C then 1 - p x else 0) U).symm
    _ = ∏ x ∈ C, p x := by
      calc
        _ = ∏ x ∈ U, (if x ∈ C then p x else 1) := by
          apply Finset.prod_congr rfl
          intro x hx
          by_cases hxC : x ∈ C <;> simp [hxC] <;> ring
        _ = _ := by rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hC]

private lemma exists_subset_of_weighted_average {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (hp0 : ∀ x ∈ U, 0 ≤ p x)
    (hp1 : ∀ x ∈ U, p x ≤ 1) (F : Finset X → Real) (A : Real)
    (haverage : A ≤ ∑ S ∈ U.powerset, restrictionWeight U p S * F S) :
    ∃ S ⊆ U, A ≤ F S := by
  obtain ⟨S, hS, hmax⟩ :=
    Finset.exists_max_image U.powerset F (Finset.powerset_nonempty U)
  refine ⟨S, Finset.mem_powerset.mp hS, haverage.trans ?_⟩
  calc
    (∑ T ∈ U.powerset, restrictionWeight U p T * F T) ≤
        ∑ T ∈ U.powerset, restrictionWeight U p T * F S := by
      exact Finset.sum_le_sum fun T hT =>
        mul_le_mul_of_nonneg_left (hmax T hT)
          (restrictionWeight_nonneg U p hp0 hp1 T (Finset.mem_powerset.mp hT))
    _ = F S := by rw [← Finset.sum_mul, restrictionWeight_sum, one_mul]

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
      intro S _
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
