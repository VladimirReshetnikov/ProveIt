import GowersSzemeredi.Proofs15DegenerateArrangements

/-!
# The random restriction for higher-dimensional arrangements

This file proves Lemma 15.5.  It uses the same finite Riesz-product and
Bernoulli averaging method as Lemma 12.5, with the monomials in all
`k + 1` coordinates as the phase features.  Degenerate arrangements are
the exceptional set controlled by Lemma 15.4.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Finite Bernoulli averaging -/

private def selectionWeight {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (S : Finset X) : Real :=
  (∏ x ∈ S, p x) * ∏ x ∈ U \ S, (1 - p x)

private lemma selectionWeight_nonneg {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (hp0 : ∀ x ∈ U, 0 ≤ p x)
    (hp1 : ∀ x ∈ U, p x ≤ 1) (S : Finset X) (hS : S ⊆ U) :
    0 ≤ selectionWeight U p S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun x hx ↦ hp0 x (hS hx)
  · exact Finset.prod_nonneg fun x hx ↦
      sub_nonneg.mpr (hp1 x (Finset.mem_sdiff.mp hx).1)

private lemma selectionWeight_insert {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (a : X) (ha : a ∉ U) (S : Finset X)
    (hS : S ⊆ U) :
    selectionWeight (insert a U) p (insert a S) =
      p a * selectionWeight U p S := by
  simp only [selectionWeight]
  rw [Finset.prod_insert (notMem_mono hS ha)]
  have hdiff : insert a U \ insert a S = U \ S := by
    ext x
    simp only [mem_sdiff, mem_insert]
    aesop
  rw [hdiff]
  ring

private lemma selectionWeight_not_insert {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) (a : X) (ha : a ∉ U) (S : Finset X)
    (hS : S ⊆ U) :
    selectionWeight (insert a U) p S =
      (1 - p a) * selectionWeight U p S := by
  simp only [selectionWeight]
  have haS : a ∉ S := fun h ↦ ha (hS h)
  have hdiff : insert a U \ S = insert a (U \ S) := by
    ext x
    simp only [mem_sdiff, mem_insert]
    aesop
  rw [hdiff, Finset.prod_insert]
  · ring
  · simp [ha]

private lemma selectionWeight_sum {X : Type*} [DecidableEq X]
    (U : Finset X) (p : X → Real) :
    ∑ S ∈ U.powerset, selectionWeight U p S = 1 := by
  induction U using Finset.induction_on with
  | empty => simp [selectionWeight]
  | @insert a U ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hleft :
          (∑ S ∈ U.powerset, selectionWeight (insert a U) p S) =
            (1 - p a) * ∑ S ∈ U.powerset, selectionWeight U p S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [selectionWeight_not_insert U p a ha S
          (Finset.mem_powerset.mp hS)]
      have hright :
          (∑ S ∈ U.powerset, selectionWeight (insert a U) p (insert a S)) =
            p a * ∑ S ∈ U.powerset, selectionWeight U p S := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro S hS
        rw [selectionWeight_insert U p a ha S
          (Finset.mem_powerset.mp hS)]
      rw [hleft, hright, ih]
      ring

private lemma selectionWeight_event {X : Type*} [DecidableEq X]
    (U C : Finset X) (p : X → Real) (hC : C ⊆ U) :
    ∑ S ∈ U.powerset, selectionWeight U p S * (if C ⊆ S then 1 else 0) =
      ∏ x ∈ C, p x := by
  induction U using Finset.induction_on generalizing C with
  | empty =>
      have hC0 : C = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun x hx ↦
        (Finset.notMem_empty x) (hC hx)
      subst C
      simp [selectionWeight]
  | @insert a U ha ih =>
      rw [Finset.sum_powerset_insert ha]
      by_cases haC : a ∈ C
      · let C₀ := C.erase a
        have hCeq : C = insert a C₀ := (Finset.insert_erase haC).symm
        have hC₀ : C₀ ⊆ U := by
          intro x hx
          have hxC : x ∈ C := Finset.mem_of_mem_erase hx
          rcases Finset.mem_insert.mp (hC hxC) with hxa | hxU
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
            rcases Finset.mem_insert.mp (hsub hx) with hxa | hxS
            · subst x
              exact (haC₀ hx).elim
            · exact hxS
          · intro hsub
            exact ⟨Finset.mem_insert_self _ _, fun x hx ↦
              Finset.mem_insert_of_mem (hsub hx)⟩
        have hleft :
            (∑ S ∈ U.powerset,
              selectionWeight (insert a U) p S *
                (if C ⊆ S then 1 else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro S hS
          rw [if_neg (hfalse S hS), mul_zero]
        have hright :
            (∑ S ∈ U.powerset,
              selectionWeight (insert a U) p (insert a S) *
                (if C ⊆ insert a S then 1 else 0)) =
              p a * ∑ S ∈ U.powerset,
                selectionWeight U p S * (if C₀ ⊆ S then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          rw [selectionWeight_insert U p a ha S
            (Finset.mem_powerset.mp hS)]
          simp only [hins S hS]
          ring
        rw [hleft, zero_add, hright, ih C₀ hC₀, hCeq,
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
              selectionWeight (insert a U) p S *
                (if C ⊆ S then 1 else 0)) =
              (1 - p a) * ∑ S ∈ U.powerset,
                selectionWeight U p S * (if C ⊆ S then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          rw [selectionWeight_not_insert U p a ha S
            (Finset.mem_powerset.mp hS)]
          ring
        have hright :
            (∑ S ∈ U.powerset,
              selectionWeight (insert a U) p (insert a S) *
                (if C ⊆ insert a S then 1 else 0)) =
              p a * ∑ S ∈ U.powerset,
                selectionWeight U p S * (if C ⊆ S then 1 else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          rw [selectionWeight_insert U p a ha S
            (Finset.mem_powerset.mp hS)]
          simp only [hevent S hS]
          ring
        rw [hleft, hright, ih C hCU]
        ring

private lemma selectionWeight_count {X E : Type*} [DecidableEq X]
    [DecidableEq E] (U : Finset X) (p : X → Real) (edges : Finset E)
    (carrier : E → Finset X) (hcarrier : ∀ e ∈ edges, carrier e ⊆ U) :
    (∑ S ∈ U.powerset, selectionWeight U p S *
        ((edges.filter fun e ↦ carrier e ⊆ S).card : Real)) =
      ∑ e ∈ edges, ∏ x ∈ carrier e, p x := by
  classical
  simp_rw [Finset.cast_card, Finset.sum_filter]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← selectionWeight_event U (carrier e) p (hcarrier e he)]

private lemma exists_subset_count_score {X E : Type*} [DecidableEq X]
    [DecidableEq E] (U : Finset X) (p : X → Real)
    (hp0 : ∀ x ∈ U, 0 ≤ p x) (hp1 : ∀ x ∈ U, p x ≤ 1)
    (good bad : Finset E) (carrier : E → Finset X)
    (hgood : ∀ e ∈ good, carrier e ⊆ U)
    (hbad : ∀ e ∈ bad, carrier e ⊆ U) (eta A : Real)
    (haverage : A ≤
      eta * (∑ e ∈ good, ∏ x ∈ carrier e, p x) -
        ∑ e ∈ bad, ∏ x ∈ carrier e, p x) :
    ∃ S ⊆ U, A ≤
      eta * ((good.filter fun e ↦ carrier e ⊆ S).card : Real) -
        ((bad.filter fun e ↦ carrier e ⊆ S).card : Real) := by
  let F : Finset X → Real := fun S ↦
    eta * ((good.filter fun e ↦ carrier e ⊆ S).card : Real) -
      ((bad.filter fun e ↦ carrier e ⊆ S).card : Real)
  have hmean : A ≤
      ∑ S ∈ U.powerset, selectionWeight U p S * F S := by
    have hgoodMean := selectionWeight_count U p good carrier hgood
    have hbadMean := selectionWeight_count U p bad carrier hbad
    dsimp only [F]
    calc
      A ≤ eta * (∑ e ∈ good, ∏ x ∈ carrier e, p x) -
          ∑ e ∈ bad, ∏ x ∈ carrier e, p x := haverage
      _ = eta *
            (∑ S ∈ U.powerset, selectionWeight U p S *
              ((good.filter fun e ↦ carrier e ⊆ S).card : Real)) -
          (∑ S ∈ U.powerset, selectionWeight U p S *
              ((bad.filter fun e ↦ carrier e ⊆ S).card : Real)) := by
        rw [hgoodMean, hbadMean]
      _ = ∑ S ∈ U.powerset, selectionWeight U p S *
          (eta * ((good.filter fun e ↦ carrier e ⊆ S).card : Real) -
            ((bad.filter fun e ↦ carrier e ⊆ S).card : Real)) := by
        rw [Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro S hS
        ring
  by_contra hno
  push Not at hno
  have hstrict :
      (∑ S ∈ U.powerset, selectionWeight U p S * F S) < A := by
    have hle : ∀ S ∈ U.powerset,
        selectionWeight U p S * F S ≤ selectionWeight U p S * A := by
      intro S hS
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (hno S (Finset.mem_powerset.mp hS)))
        (selectionWeight_nonneg U p hp0 hp1 S
          (Finset.mem_powerset.mp hS))
    have hex : ∃ T ∈ U.powerset, 0 < selectionWeight U p T := by
      by_contra hz
      push Not at hz
      have hall : ∀ T ∈ U.powerset, selectionWeight U p T = 0 := by
        intro T hT
        exact le_antisymm (hz T hT)
          (selectionWeight_nonneg U p hp0 hp1 T
            (Finset.mem_powerset.mp hT))
      have hsum := selectionWeight_sum U p
      have : (∑ T ∈ U.powerset, selectionWeight U p T) = 0 := by
        exact Finset.sum_eq_zero fun T hT ↦ hall T hT
      rw [this] at hsum
      norm_num at hsum
    have hsumlt :
        (∑ S ∈ U.powerset, selectionWeight U p S * F S) <
          ∑ S ∈ U.powerset, selectionWeight U p S * A := by
      apply Finset.sum_lt_sum hle
      obtain ⟨T, hT, hTpos⟩ := hex
      exact ⟨T, hT, mul_lt_mul_of_pos_left
        (hno T (Finset.mem_powerset.mp hT)) hTpos⟩
    have hright :
        (∑ S ∈ U.powerset, selectionWeight U p S * A) = A := by
      rw [← Finset.sum_mul, selectionWeight_sum]
      simp
    simpa only [hright] using hsumlt
  exact (hmean.trans_lt hstrict).false

/-! ## Arrangements as finite hyperedges -/

private abbrev selectionIndex (k : Nat) :=
  (Fin k → Bool) × Fin 16

private def selectionVertex {N k : Nat} (R : GeneralArrangement N k 8)
    (z : selectionIndex k) : Point N (k + 1) :=
  R.vertex z.1 z.2

private noncomputable def selectionCarrier {N k : Nat}
    (R : GeneralArrangement N k 8) : Finset (Point N (k + 1)) := by
  classical
  exact Finset.univ.image (selectionVertex R)

private lemma selectionCarrier_subset {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (R : GeneralArrangement N k 8)
    (hR : R.IsIn B) : selectionCarrier R ⊆ B := by
  classical
  intro z hz
  rw [selectionCarrier, Finset.mem_image] at hz
  obtain ⟨i, -, rfl⟩ := hz
  exact hR.2 i.1 i.2

private lemma selection_isIn_iff {N k : Nat} [NeZero N]
    (B B' : Finset (Point N (k + 1)))
    (R : GeneralArrangement N k 8) (hR : R.IsIn B) :
    R.IsIn B' ↔ selectionCarrier R ⊆ B' := by
  constructor
  · intro h z hz
    rw [selectionCarrier, Finset.mem_image] at hz
    obtain ⟨i, -, rfl⟩ := hz
    exact h.2 i.1 i.2
  · intro h
    refine ⟨hR.1, ?_⟩
    intro e j
    apply h
    rw [selectionCarrier, Finset.mem_image]
    exact ⟨(e, j), Finset.mem_univ _, rfl⟩

private noncomputable def selectionArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) : Finset (GeneralArrangement N k 8) := by
  classical
  exact Finset.univ.filter fun R ↦ R.IsIn B

private noncomputable def selectionGoodArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (selectionArrangements B).filter fun R ↦ R.IsRespected phi

private noncomputable def selectionBadArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact selectionArrangements B \ selectionGoodArrangements B phi

private lemma selectionArrangements_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :
    (selectionArrangements B).card = generalArrangementCount 8 B := by
  classical
  unfold selectionArrangements generalArrangementCount countWhere
  rw [Finset.filter_congr_decidable]

private lemma selectionGoodArrangements_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    (selectionGoodArrangements B phi).card =
      respectedGeneralArrangementCount 8 B phi := by
  classical
  unfold selectionGoodArrangements selectionArrangements
    respectedGeneralArrangementCount countWhere
  simp only [Finset.filter_filter]
  rw [Finset.filter_congr_decidable]
  apply congrArg Finset.card
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private lemma selection_respected_le_arrangement {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    respectedGeneralArrangementCount 8 B phi ≤ generalArrangementCount 8 B := by
  classical
  rw [← selectionGoodArrangements_card, ← selectionArrangements_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

private lemma selection_good_restrict_card {N k : Nat} [NeZero N]
    (B B' : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (hB'B : B' ⊆ B) :
    ((selectionGoodArrangements B phi).filter fun R ↦
      selectionCarrier R ⊆ B').card =
        respectedGeneralArrangementCount 8 B' phi := by
  classical
  unfold selectionGoodArrangements selectionArrangements
    respectedGeneralArrangementCount countWhere
  simp only [Finset.filter_filter]
  rw [Finset.filter_congr_decidable]
  apply congrArg Finset.card
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hRB, hrespect⟩, hcarrier⟩
    exact ⟨(selection_isIn_iff B B' R hRB).mpr hcarrier, hrespect⟩
  · rintro ⟨hRB', hrespect⟩
    have hRB : R.IsIn B := ⟨hRB'.1, fun e j ↦ hB'B (hRB'.2 e j)⟩
    exact ⟨⟨hRB, hrespect⟩,
      (selection_isIn_iff B B' R hRB).mp hRB'⟩

private lemma selection_good_bad_restrict_card {N k : Nat} [NeZero N]
    (B B' : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (hB'B : B' ⊆ B) :
    ((selectionGoodArrangements B phi).filter fun R ↦
        selectionCarrier R ⊆ B').card +
      ((selectionBadArrangements B phi).filter fun R ↦
        selectionCarrier R ⊆ B').card =
      generalArrangementCount 8 B' := by
  classical
  let all' := (selectionArrangements B).filter fun R ↦
    selectionCarrier R ⊆ B'
  let good' := (selectionGoodArrangements B phi).filter fun R ↦
    selectionCarrier R ⊆ B'
  let bad' := (selectionBadArrangements B phi).filter fun R ↦
    selectionCarrier R ⊆ B'
  have hdisj : Disjoint good' bad' := by
    apply Finset.disjoint_left.mpr
    intro R hgood hbad
    have hg : R ∈ selectionGoodArrangements B phi :=
      (Finset.mem_filter.mp hgood).1
    have hb : R ∈ selectionBadArrangements B phi :=
      (Finset.mem_filter.mp hbad).1
    exact (Finset.mem_sdiff.mp hb).2 hg
  have hunion : good' ∪ bad' = all' := by
    ext R
    simp only [good', bad', all', selectionBadArrangements,
      selectionGoodArrangements,
      Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hallcard : all'.card = generalArrangementCount 8 B' := by
    unfold all' selectionArrangements generalArrangementCount countWhere
    simp only [Finset.filter_filter]
    rw [Finset.filter_congr_decidable]
    apply congrArg Finset.card
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hRB, hcarrier⟩
      exact (selection_isIn_iff B B' R hRB).mpr hcarrier
    · intro hRB'
      have hRB : R.IsIn B := ⟨hRB'.1, fun e j ↦ hB'B (hRB'.2 e j)⟩
      exact ⟨hRB, (selection_isIn_iff B B' R hRB).mp hRB'⟩
  rw [← hallcard, ← hunion, Finset.card_union_of_disjoint hdisj]

private def selectionIndexSign {N : Nat} (j : Fin 16) : ZMod N :=
  if (j : Nat) < 8 then 1 else -1

private lemma selection_additive_iff {N : Nat} (x : Fin 16 → ZMod N) :
    IsAdditiveTuple (k := 8) x ↔
      ∑ j, selectionIndexSign (N := N) j * x j = 0 := by
  classical
  let L := Finset.univ.filter fun j : Fin 16 ↦ (j : Nat) < 8
  let U := Finset.univ.filter fun j : Fin 16 ↦ 8 ≤ (j : Nat)
  have hcomp :
      (Finset.univ.filter fun j : Fin 16 ↦ ¬ (j : Nat) < 8) = U := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, U]
    omega
  have hsum :
      (∑ j, selectionIndexSign (N := N) j * x j) =
        (∑ j ∈ L, x j) - ∑ j ∈ U, x j := by
    dsimp only [L, U]
    simp_rw [selectionIndexSign, ite_mul, one_mul, neg_one_mul]
    rw [Finset.sum_ite, hcomp, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hsum, sub_eq_zero]
  rfl

private lemma selection_sum_mul_sub_eq_one {N : Nat} {I : Type*}
    [Fintype I] [DecidableEq I] (a x y : I → ZMod N) (i : I)
    (hoff : ∀ t, t ≠ i → x t = y t) :
    (∑ t, a t * x t) - (∑ t, a t * y t) = a i * (x i - y i) := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ t, (a t * x t - a t * y t)) = ∑ t, a t * (x t - y t) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ t ∈ ({i} : Finset I), a t * (x t - y t) := by
      symm
      apply Finset.sum_subset (by simp)
      intro t _ ht
      have hti : t ≠ i := by simpa using ht
      rw [hoff t hti, sub_self, mul_zero]
    _ = a i * (x i - y i) := by simp

private abbrev SelectionArrangementCode {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :=
  (Fin 15 → {z : Point N (k + 1) // z ∈ B}) × Point N k × Point N k

private lemma selection_arrangement_count_le_card_pow {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :
    generalArrangementCount 8 B ≤ B.card ^ 15 * N ^ (2 * k) := by
  classical
  let source := {R : GeneralArrangement N k 8 // R.IsIn B}
  let efalse : Fin k → Bool := fun _ ↦ false
  let enc : source → SelectionArrangementCode B := fun R ↦
    ⟨fun j ↦ ⟨R.1.vertex efalse j.castSucc, R.2.2 efalse j.castSucc⟩,
      R.1.side, R.1.base (Fin.last 15)⟩
  have hinj : Function.Injective enc := by
    intro R S hRS
    apply Subtype.ext
    have hverts := congrArg (fun z ↦ z.1) hRS
    have hside := congrArg (fun z ↦ z.2.1) hRS
    have hlast := congrArg (fun z ↦ z.2.2) hRS
    dsimp only [enc] at hverts hside hlast
    change R.1.side = S.1.side at hside
    change R.1.base (Fin.last 15) = S.1.base (Fin.last 15) at hlast
    have hbase : R.1.base = S.1.base := by
      funext j
      refine Fin.lastCases hlast (fun t ↦ ?_) j
      have hv := congrArg Subtype.val (congrFun hverts t)
      funext i
      have hii := congrFun hv i.castSucc
      simpa [efalse, GeneralArrangement.vertex, GeneralArrangement.cube,
        AxisCube.vertex, AxisCube.base, AxisCube.side, appendCoordinate] using hii
    have hcrossTail : ∀ j, j ≠ Fin.last 15 →
        R.1.crossSection j = S.1.crossSection j := by
      intro j hj
      obtain ⟨t, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      have hv := congrArg Subtype.val (congrFun hverts t)
      have hc := congrFun hv (Fin.last k)
      simpa [efalse, GeneralArrangement.vertex, appendCoordinate] using hc
    have hcrossLast : R.1.crossSection (Fin.last 15) =
        S.1.crossSection (Fin.last 15) := by
      let a : Fin 16 → ZMod N := selectionIndexSign
      have hdiff := selection_sum_mul_sub_eq_one a R.1.crossSection
        S.1.crossSection (Fin.last 15) hcrossTail
      have hRadd := (selection_additive_iff R.1.crossSection).mp R.2.1
      have hSadd := (selection_additive_iff S.1.crossSection).mp S.2.1
      change (∑ j, a j * R.1.crossSection j) = 0 at hRadd
      change (∑ j, a j * S.1.crossSection j) = 0 at hSadd
      rw [hRadd, hSadd, sub_self] at hdiff
      have ha : a (Fin.last 15) = -1 := by
        simp [a, selectionIndexSign]
      rw [ha, neg_one_mul] at hdiff
      exact sub_eq_zero.mp (neg_eq_zero.mp hdiff.symm)
    have hcross : R.1.crossSection = S.1.crossSection := by
      funext j
      by_cases hj : j = Fin.last 15
      · subst j
        exact hcrossLast
      · exact hcrossTail j hj
    exact Prod.ext hside (Prod.ext hbase hcross)
  have hsourceCard : Fintype.card source = generalArrangementCount 8 B := by
    unfold source generalArrangementCount countWhere
    rw [Finset.filter_congr_decidable]
    exact Fintype.card_subtype _
  rw [← hsourceCard]
  calc
    Fintype.card source ≤ Fintype.card (SelectionArrangementCode B) :=
      Fintype.card_le_of_injective enc hinj
    _ = B.card ^ 15 * N ^ (2 * k) := by
      simp only [SelectionArrangementCode, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_coe, Point, ZMod.card]
      rw [← pow_add]
      ring_nf

private lemma selection_arrangement_real_upper {N k : Nat} [NeZero N]
    (beta : Real) (B : Finset (Point N (k + 1)))
    (hBcard : (B.card : Real) = beta * (N : Real) ^ (k + 1)) :
    (generalArrangementCount 8 B : Real) ≤
      beta ^ 15 * (N : Real) ^ (17 * k + 15) := by
  have hnat := selection_arrangement_count_le_card_pow B
  have hreal : (generalArrangementCount 8 B : Real) ≤
      (B.card : Real) ^ 15 * (N : Real) ^ (2 * k) := by
    exact_mod_cast hnat
  calc
    (generalArrangementCount 8 B : Real) ≤
        (B.card : Real) ^ 15 * (N : Real) ^ (2 * k) := hreal
    _ = beta ^ 15 * (N : Real) ^ (17 * k + 15) := by
      rw [hBcard]
      ring

/-! ## One-stage Riesz weights -/

private abbrev SelectionFeature (k : Nat) :=
  Option (Finset (Fin (k + 1)))

private abbrev SelectionPhase (N k : Nat) :=
  SelectionFeature k → ZMod N

private def selectionDigitInt (j : Fin 4) : Int :=
  ![0, 0, 1, -1] j

private def selectionDigit {N : Nat} (j : Fin 4) : ZMod N :=
  (selectionDigitInt j : ZMod N)

private lemma selectionDigitInt_ternary (j : Fin 4) :
    selectionDigitInt j = -1 ∨ selectionDigitInt j = 0 ∨
      selectionDigitInt j = 1 := by
  fin_cases j <;> simp [selectionDigitInt]

private lemma selection_index_card (k : Nat) :
    Fintype.card (selectionIndex k) = 2 ^ (k + 4) := by
  simp only [selectionIndex, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  rw [show 16 = 2 ^ 4 by norm_num, ← pow_add]

private def selectionFeatureValue {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (F : SelectionFeature k)
    (z : Point N (k + 1)) : ZMod N :=
  match F with
  | none => phi z
  | some A => ∏ i ∈ A, z i

private def selectionPhaseValue {N k : Nat} [NeZero N]
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : ZMod N :=
  ∑ F, C F * selectionFeatureValue phi F z

private def selectionRelation {N k : Nat} [NeZero N]
    (eps : selectionIndex k → Fin 4) (F : SelectionFeature k)
    (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) : ZMod N :=
  ∑ z, selectionDigit (N := N) (eps z) *
    selectionFeatureValue phi F (selectionVertex R z)

private def oneStageSelectionWeight {N k : Nat} [NeZero N]
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : Real :=
  Complex.normSq (1 + exponential (selectionPhaseValue C phi z)) / 4

private lemma oneStageSelectionWeight_nonneg {N k : Nat} [NeZero N]
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : 0 ≤ oneStageSelectionWeight C phi z := by
  unfold oneStageSelectionWeight
  exact div_nonneg (Complex.normSq_nonneg _) (by norm_num)

private lemma oneStageSelectionWeight_le_one {N k : Nat} [NeZero N]
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : oneStageSelectionWeight C phi z ≤ 1 := by
  have hexp : ‖exponential (selectionPhaseValue C phi z)‖ = 1 :=
    (ZMod.stdAddChar (N := N)).norm_apply _
  have hn : ‖1 + exponential (selectionPhaseValue C phi z)‖ ≤ 2 := by
    calc
      ‖1 + exponential (selectionPhaseValue C phi z)‖ ≤
          ‖(1 : Complex)‖ + ‖exponential (selectionPhaseValue C phi z)‖ :=
        norm_add_le _ _
      _ = 2 := by rw [norm_one, hexp]; norm_num
  have hn0 : 0 ≤ ‖1 + exponential (selectionPhaseValue C phi z)‖ :=
    norm_nonneg _
  have hsq : Complex.normSq
      (1 + exponential (selectionPhaseValue C phi z)) ≤ 4 := by
    rw [← Complex.sq_norm]
    nlinarith
  unfold oneStageSelectionWeight
  linarith

@[simp] private lemma selection_exponential_add {N : Nat} [NeZero N]
    (x y : ZMod N) : exponential (x + y) = exponential x * exponential y := by
  exact AddChar.map_add_eq_mul (ZMod.stdAddChar (N := N)) x y

@[simp] private lemma selection_star_exponential {N : Nat} [NeZero N]
    (x : ZMod N) : star (exponential x) = exponential (-x) := by
  simpa only [exponential, starRingEnd_apply] using
    (AddChar.map_neg_eq_conj (ZMod.stdAddChar (N := N)) x).symm

@[simp] private lemma selection_exponential_zero {N : Nat} [NeZero N] :
    exponential (0 : ZMod N) = 1 := by
  exact AddChar.map_zero_eq_one (ZMod.stdAddChar (N := N))

private lemma oneStageSelectionWeight_complex {N k : Nat} [NeZero N]
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) :
    ((oneStageSelectionWeight C phi z : Real) : Complex) =
      (4 : Complex)⁻¹ * ∑ j : Fin 4,
        exponential (selectionDigit (N := N) j *
          selectionPhaseValue C phi z) := by
  let u := exponential (selectionPhaseValue C phi z)
  have hsum :
      (∑ j : Fin 4, exponential (selectionDigit (N := N) j *
        selectionPhaseValue C phi z)) = 2 + u + star u := by
    rw [Fin.sum_univ_four]
    simp [selectionDigit, selectionDigitInt, u]
    ring
  unfold oneStageSelectionWeight
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, hsum]
  rw [div_eq_mul_inv, mul_comm _ (4 : Complex)⁻¹]
  change ((4 : Complex)⁻¹ * ((star (1 + u)) * (1 + u))) =
    (4 : Complex)⁻¹ * (2 + u + star u)
  congr 1
  simp only [star_add, star_one]
  have hu : star u * u = 1 := by
    change star (exponential (selectionPhaseValue C phi z)) *
      exponential (selectionPhaseValue C phi z) = 1
    rw [selection_star_exponential, ← selection_exponential_add]
    simp
  calc
    (1 + star u) * (1 + u) = 1 + u + star u + star u * u := by ring
    _ = 2 + u + star u := by rw [hu]; ring

private lemma selection_prod_exponential {N : Nat} [NeZero N]
    {I : Type*} [Fintype I] (f : I → ZMod N) :
    ∏ i, exponential (f i) = exponential (∑ i, f i) := by
  classical
  symm
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, selection_exponential_add,
        Finset.prod_insert hi, ih]

private lemma selection_phase_relation {N k : Nat} [NeZero N]
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) (eps : selectionIndex k → Fin 4) :
    (∑ z, selectionDigit (N := N) (eps z) *
      selectionPhaseValue C phi (selectionVertex R z)) =
      ∑ F, C F * selectionRelation eps F phi R := by
  unfold selectionPhaseValue selectionRelation
  calc
    (∑ z, selectionDigit (N := N) (eps z) *
        ∑ F, C F * selectionFeatureValue phi F (selectionVertex R z)) =
        ∑ z, ∑ F, selectionDigit (N := N) (eps z) *
          (C F * selectionFeatureValue phi F (selectionVertex R z)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
    _ = ∑ F, ∑ z, selectionDigit (N := N) (eps z) *
          (C F * selectionFeatureValue phi F (selectionVertex R z)) :=
      Finset.sum_comm
    _ = ∑ F, C F * ∑ z, selectionDigit (N := N) (eps z) *
          selectionFeatureValue phi F (selectionVertex R z) := by
      apply Finset.sum_congr rfl
      intro F _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

private lemma selection_product_complex {N k : Nat} [NeZero N]
    (C : SelectionPhase N k) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) :
    ((∏ z : selectionIndex k,
        oneStageSelectionWeight C phi (selectionVertex R z) : Real) : Complex) =
      ((4 : Complex)⁻¹) ^ (2 ^ (k + 4)) *
        ∑ eps : selectionIndex k → Fin 4,
          exponential (∑ F, C F * selectionRelation eps F phi R) := by
  rw [Complex.ofReal_prod]
  simp_rw [oneStageSelectionWeight_complex]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, selection_index_card]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro eps _
  rw [selection_prod_exponential]
  congr 1
  exact selection_phase_relation C phi R eps

private lemma selection_sum_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    ∑ u : ZMod N, exponential (x * u) =
      if x = 0 then (N : Complex) else 0 := by
  simpa [exponential, mul_comm] using
    AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar N)

private lemma selection_expect_exponential_mul {N : Nat} [NeZero N]
    (x : ZMod N) :
    (𝔼 u : ZMod N, exponential (x * u)) = if x = 0 then 1 else 0 := by
  have hN : N ≠ 0 := NeZero.ne N
  by_cases hx : x = 0
  · rw [if_pos hx]
    have h := Fintype.card_mul_expect
      (fun u : ZMod N ↦ exponential (x * u))
    rw [ZMod.card, selection_sum_exponential_mul, if_pos hx] at h
    exact (mul_left_cancel₀ (Nat.cast_ne_zero.mpr hN) (by simpa using h))
  · rw [if_neg hx]
    have h := Fintype.card_mul_expect
      (fun u : ZMod N ↦ exponential (x * u))
    rw [ZMod.card, selection_sum_exponential_mul, if_neg hx] at h
    exact (mul_eq_zero.mp (by simpa using h)).resolve_left
      (Nat.cast_ne_zero.mpr hN)

private lemma selection_expect_pi_prod {I C : Type*} [Fintype I]
    [DecidableEq I]
    [Fintype C] [Nonempty C] (f : I → C → Complex) :
    (𝔼 g : I → C, ∏ i : I, f i (g i)) =
      ∏ i : I, 𝔼 c : C, f i c := by
  classical
  simp only [Finset.expect_univ, Fintype.card_fun]
  rw [← Fintype.prod_sum]
  simp only [NNRat.smul_def, NNRat.cast_inv, NNRat.cast_natCast,
    Nat.cast_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp [inv_pow]

private lemma selection_expect_phase {N k : Nat} [NeZero N]
    (rel : SelectionFeature k → ZMod N) :
    (𝔼 C : SelectionPhase N k,
      exponential (∑ F, C F * rel F)) =
      if ∀ F, rel F = 0 then 1 else 0 := by
  classical
  have hexp (C : SelectionPhase N k) :
      exponential (∑ F, C F * rel F) =
        ∏ F, exponential (C F * rel F) := by
    exact (selection_prod_exponential (fun F ↦ C F * rel F)).symm
  simp_rw [hexp]
  rw [selection_expect_pi_prod
    (I := SelectionFeature k) (C := ZMod N)
    (f := fun F c ↦ exponential (c * rel F))]
  have hfactor (F : SelectionFeature k) :
      (𝔼 c : ZMod N, exponential (c * rel F)) =
        if rel F = 0 then 1 else 0 := by
    simpa only [mul_comm] using selection_expect_exponential_mul (rel F)
  simp_rw [hfactor]
  by_cases hrel : ∀ F, rel F = 0
  · simp [hrel]
  · rw [if_neg hrel]
    push Not at hrel
    obtain ⟨F, hF⟩ := hrel
    apply Finset.prod_eq_zero (Finset.mem_univ F)
    rw [if_neg hF]

private noncomputable def selectionValidRelations {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    Finset (selectionIndex k → Fin 4) := by
  classical
  exact Finset.univ.filter fun eps ↦
    ∀ F, selectionRelation eps F phi R = 0

private lemma selection_oneStage_average {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    (𝔼 C : SelectionPhase N k,
      ∏ z : selectionIndex k,
        oneStageSelectionWeight C phi (selectionVertex R z)) =
      ((4 : Real)⁻¹) ^ (2 ^ (k + 4)) *
        (selectionValidRelations phi R).card := by
  apply Complex.ofReal_injective
  change Complex.ofRealHom
      (𝔼 C : SelectionPhase N k,
        ∏ z : selectionIndex k,
          oneStageSelectionWeight C phi (selectionVertex R z)) =
    Complex.ofRealHom
      (((4 : Real)⁻¹) ^ (2 ^ (k + 4)) *
        (selectionValidRelations phi R).card)
  rw [map_expect Complex.ofRealHom]
  have hrewrite (C : SelectionPhase N k) :
      Complex.ofRealHom
          (∏ z : selectionIndex k,
            oneStageSelectionWeight C phi (selectionVertex R z)) =
        ((4 : Complex)⁻¹) ^ (2 ^ (k + 4)) *
          ∑ eps : selectionIndex k → Fin 4,
            exponential (∑ F, C F * selectionRelation eps F phi R) := by
    change ((∏ z : selectionIndex k,
      oneStageSelectionWeight C phi (selectionVertex R z) : Real) : Complex) = _
    exact selection_product_complex C phi R
  simp_rw [hrewrite]
  rw [← Finset.mul_expect, Finset.expect_sum_comm]
  simp_rw [selection_expect_phase]
  unfold selectionValidRelations
  simp_rw [Finset.cast_card, Finset.sum_filter]
  rw [map_mul, map_pow, map_inv₀, map_ofNat, map_sum]
  apply congrArg (((4 : Complex)⁻¹) ^ (2 ^ (k + 4)) * ·)
  apply Finset.sum_congr rfl
  intro eps _
  by_cases hvalid : ∀ F, selectionRelation eps F phi R = 0 <;>
    simp [hvalid]

/-! ## The distinguished relation and nondegeneracy -/

private abbrev selectionEta {k : Nat}
    (eps : selectionIndex k → Fin 4) :=
  fun e j ↦ selectionDigitInt (eps (e, j))

private lemma selectionEta_ternary {k : Nat}
    (eps : selectionIndex k → Fin 4) :
    IsTernaryCoefficient
      (fun z : (Fin k → Bool) × Fin 16 ↦ selectionEta eps z.1 z.2) := by
  intro z
  exact selectionDigitInt_ternary (eps z)

private lemma selectionRelation_some {N k : Nat} [NeZero N]
    (eps : selectionIndex k → Fin 4) (A : Finset (Fin (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    selectionRelation eps (some A) phi R =
      arrangementMoment R (selectionEta eps) A := by
  classical
  unfold selectionRelation arrangementMoment selectionFeatureValue selectionEta
  rw [Fintype.sum_prod_type]
  rfl

private def selectionEtaZero {k : Nat} (e : Fin k → Bool) (j : Fin 16) : Int :=
  (if (j : Nat) < 8 then 1 else -1) * (-1 : Int) ^ boolWeight e

private lemma selectionEtaZero_cast {N k : Nat} (e : Fin k → Bool)
    (j : Fin 16) :
    (selectionEtaZero e j : ZMod N) =
      arrangementParityCoefficient (N := N) (d := 8) e j := by
  by_cases hj : (j : Nat) < 8 <;>
    simp [selectionEtaZero, arrangementParityCoefficient, parityCharacter, hj]

private lemma selectionEtaZero_cases {k : Nat} (e : Fin k → Bool)
    (j : Fin 16) : selectionEtaZero e j = 1 ∨ selectionEtaZero e j = -1 := by
  by_cases he : Even (boolWeight e)
  · have hp : (-1 : Int) ^ boolWeight e = 1 := he.neg_one_pow
    by_cases hj : (j : Nat) < 8 <;> simp [selectionEtaZero, hp, hj]
  · have hp : (-1 : Int) ^ boolWeight e = -1 :=
      (Nat.not_even_iff_odd.mp he).neg_one_pow
    by_cases hj : (j : Nat) < 8 <;> simp [selectionEtaZero, hp, hj]

private def selectionCanonicalDigit {k : Nat} (z : selectionIndex k) : Fin 4 :=
  if selectionEtaZero z.1 z.2 = 1 then 2 else 3

private def selectionNegativeCanonicalDigit {k : Nat}
    (z : selectionIndex k) : Fin 4 :=
  if selectionEtaZero z.1 z.2 = 1 then 3 else 2

private lemma selectionDigit_eq_zero_iff (N : Nat) [Fact (1 < N)]
    (d : Fin 4) : selectionDigit (N := N) d = 0 ↔ (d : Nat) < 2 := by
  fin_cases d <;> norm_num [selectionDigit, selectionDigitInt]

private lemma selectionDigit_eq_one_iff (N : Nat) (hN : 3 ≤ N)
    (d : Fin 4) : selectionDigit (N := N) d = 1 ↔ d = 2 := by
  letI : Fact (1 < N) := ⟨by omega⟩
  letI : Fact (2 < N) := ⟨by omega⟩
  fin_cases d <;>
    simp [selectionDigit, selectionDigitInt, Fin.ext_iff,
      ZMod.neg_one_ne_one (n := N)]

private lemma selectionDigit_eq_neg_one_iff (N : Nat) (hN : 3 ≤ N)
    (d : Fin 4) : selectionDigit (N := N) d = -1 ↔ d = 3 := by
  letI : Fact (1 < N) := ⟨by omega⟩
  letI : Fact (2 < N) := ⟨by omega⟩
  have hone : (1 : ZMod N) ≠ -1 := (ZMod.neg_one_ne_one (n := N)).symm
  fin_cases d <;>
    simp [selectionDigit, selectionDigitInt, Fin.ext_iff, hone]

private lemma selectionDigit_canonical {N k : Nat}
    (z : selectionIndex k) :
    selectionDigit (N := N) (selectionCanonicalDigit z) =
      arrangementParityCoefficient (N := N) (d := 8) z.1 z.2 := by
  rcases selectionEtaZero_cases z.1 z.2 with h | h
  · simp [selectionCanonicalDigit, h, selectionDigit, selectionDigitInt,
      ← selectionEtaZero_cast]
  · simp [selectionCanonicalDigit, h, selectionDigit, selectionDigitInt,
      ← selectionEtaZero_cast]

private lemma selectionDigit_negativeCanonical {N k : Nat}
    (z : selectionIndex k) :
    selectionDigit (N := N) (selectionNegativeCanonicalDigit z) =
      -arrangementParityCoefficient (N := N) (d := 8) z.1 z.2 := by
  rcases selectionEtaZero_cases z.1 z.2 with h | h
  · simp [selectionNegativeCanonicalDigit, h, selectionDigit, selectionDigitInt,
      ← selectionEtaZero_cast]
  · simp [selectionNegativeCanonicalDigit, h, selectionDigit, selectionDigitInt,
      ← selectionEtaZero_cast]

private lemma selectionDigit_eq_canonical_iff {N k : Nat}
    (hN : 3 ≤ N) (d : Fin 4) (z : selectionIndex k) :
    selectionDigit (N := N) d =
        arrangementParityCoefficient (N := N) (d := 8) z.1 z.2 ↔
      d = selectionCanonicalDigit z := by
  rcases selectionEtaZero_cases z.1 z.2 with h | h
  · rw [← selectionEtaZero_cast, h, Int.cast_one,
      selectionDigit_eq_one_iff N hN]
    simp [selectionCanonicalDigit, h]
  · rw [← selectionEtaZero_cast, h, Int.cast_neg, Int.cast_one,
      selectionDigit_eq_neg_one_iff N hN]
    simp [selectionCanonicalDigit, h]

private lemma selectionDigit_eq_negativeCanonical_iff {N k : Nat}
    (hN : 3 ≤ N) (d : Fin 4) (z : selectionIndex k) :
    selectionDigit (N := N) d =
        -arrangementParityCoefficient (N := N) (d := 8) z.1 z.2 ↔
      d = selectionNegativeCanonicalDigit z := by
  rcases selectionEtaZero_cases z.1 z.2 with h | h
  · rw [← selectionEtaZero_cast, h, Int.cast_one,
      selectionDigit_eq_neg_one_iff N hN]
    simp [selectionNegativeCanonicalDigit, h]
  · rw [← selectionEtaZero_cast, h, Int.cast_neg, Int.cast_one,
      neg_neg, selectionDigit_eq_one_iff N hN]
    simp [selectionNegativeCanonicalDigit, h]

private lemma selection_multiple_classification {N k : Nat} [NeZero N]
    (hN : 3 ≤ N) (eps : selectionIndex k → Fin 4)
    (hmultiple : IsModularMultiple
      (fun z : (Fin k → Bool) × Fin 16 ↦ selectionEta eps z.1 z.2)
      (fun z ↦ arrangementParityCoefficient (N := N) (d := 8) z.1 z.2)) :
    (∀ z, selectionDigit (N := N) (eps z) = 0) ∨
      eps = selectionCanonicalDigit ∨ eps = selectionNegativeCanonicalDigit := by
  classical
  rcases hmultiple with ⟨q, hq⟩
  let z₀ : selectionIndex k := (fun _ ↦ false, (0 : Fin 16))
  have heta₀ : arrangementParityCoefficient (N := N) (d := 8)
      z₀.1 z₀.2 = 1 := by
    simp [z₀, arrangementParityCoefficient, parityCharacter, boolWeight,
      countWhere]
  have hq₀ := hq z₀
  change selectionDigit (N := N) (eps z₀) =
    q * arrangementParityCoefficient (N := N) (d := 8) z₀.1 z₀.2 at hq₀
  rw [heta₀, mul_one] at hq₀
  let d₀ := eps z₀
  have hqd₀ : selectionDigit (N := N) d₀ = q := by
    simpa only [d₀] using hq₀
  rcases selectionDigitInt_ternary d₀ with hdneg | hdzero | hdone
  · have hqneg : q = -1 := by
      calc
        q = selectionDigit (N := N) d₀ := hqd₀.symm
        _ = -1 := by simp [selectionDigit, hdneg]
    right
    right
    funext z
    apply (selectionDigit_eq_negativeCanonical_iff hN (eps z) z).mp
    have hz := hq z
    change selectionDigit (N := N) (eps z) =
      q * arrangementParityCoefficient (N := N) (d := 8) z.1 z.2 at hz
    simpa [hqneg] using hz
  · have hqzero : q = 0 := by
      calc
        q = selectionDigit (N := N) d₀ := hqd₀.symm
        _ = 0 := by simp [selectionDigit, hdzero]
    left
    intro z
    have hz := hq z
    change selectionDigit (N := N) (eps z) =
      q * arrangementParityCoefficient (N := N) (d := 8) z.1 z.2 at hz
    simpa [hqzero] using hz
  · have hqone : q = 1 := by
      calc
        q = selectionDigit (N := N) d₀ := hqd₀.symm
        _ = 1 := by simp [selectionDigit, hdone]
    right
    left
    funext z
    apply (selectionDigit_eq_canonical_iff hN (eps z) z).mp
    have hz := hq z
    change selectionDigit (N := N) (eps z) =
      q * arrangementParityCoefficient (N := N) (d := 8) z.1 z.2 at hz
    simpa [hqone] using hz

private lemma selection_valid_classification_of_nondegenerate
    {N k : Nat} [NeZero N] (hN : 3 ≤ N)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hnondegenerate : ¬ R.IsDegenerate) (eps : selectionIndex k → Fin 4)
    (hvalid : ∀ F, selectionRelation eps F phi R = 0) :
    (∀ z, selectionDigit (N := N) (eps z) = 0) ∨
      eps = selectionCanonicalDigit ∨ eps = selectionNegativeCanonicalDigit := by
  apply selection_multiple_classification hN eps
  by_contra hnot
  apply hnondegenerate
  refine ⟨selectionEta eps, selectionEta_ternary eps, hnot, ?_⟩
  intro A
  rw [← selectionRelation_some]
  exact hvalid (some A)

private lemma selection_parity_eq_prod {N k : Nat} (e : Fin k → Bool) :
    parityCharacter (N := N) e =
      ∏ i : Fin k, if e i then (-1 : ZMod N) else 1 := by
  classical
  simp only [parityCharacter, boolWeight, countWhere]
  rw [← Finset.prod_const, Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : e i = true <;> simp [h]

private lemma selection_parity_cube_sum_subset {N k : Nat} [NeZero N]
    (h y : Point N k) (A : Finset (Fin k)) :
    (∑ e : Fin k → Bool, parityCharacter (N := N) e *
      ∏ i ∈ A, (y i + if e i then h i else 0)) =
      ∏ i : Fin k, if i ∈ A then -h i else 0 := by
  classical
  have hprod (e : Fin k → Bool) :
      (∏ i ∈ A, (y i + if e i then h i else 0)) =
        ∏ i : Fin k,
          if i ∈ A then (y i + if e i then h i else 0) else 1 := by
    rw [← Finset.prod_filter]
    simp
  simp_rw [selection_parity_eq_prod, hprod, ← Finset.prod_mul_distrib]
  calc
    (∑ e : Fin k → Bool,
        ∏ i : Fin k, (if e i then (-1 : ZMod N) else 1) *
          (if i ∈ A then (y i + if e i then h i else 0) else 1)) =
        ∏ i : Fin k, ∑ b : Bool,
          (if b then (-1 : ZMod N) else 1) *
            (if i ∈ A then (y i + if b then h i else 0) else 1) := by
      exact (Fintype.prod_sum (fun i (b : Bool) ↦
        (if b then (-1 : ZMod N) else 1) *
          (if i ∈ A then (y i + if b then h i else 0) else 1))).symm
    _ = ∏ i : Fin k, if i ∈ A then -h i else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.sum_bool]
      by_cases hi : i ∈ A <;> simp [hi]

private lemma selection_vertex_product_split {N k : Nat}
    (R : GeneralArrangement N k 8) (e : Fin k → Bool) (j : Fin 16)
    (A : Finset (Fin (k + 1))) :
    (∏ i ∈ A, R.vertex e j i) =
      (∏ i : Fin k, if i.castSucc ∈ A then
        (R.base j i + if e i then R.side i else 0) else 1) *
      (if Fin.last k ∈ A then R.crossSection j else 1) := by
  classical
  calc
    (∏ i ∈ A, R.vertex e j i) =
        ∏ i : Fin (k + 1), if i ∈ A then R.vertex e j i else 1 := by
      rw [← Finset.prod_filter]
      simp
    _ = (∏ i : Fin k, if i.castSucc ∈ A then
          (R.base j i + if e i then R.side i else 0) else 1) *
        (if Fin.last k ∈ A then R.crossSection j else 1) := by
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        simp [GeneralArrangement.vertex, GeneralArrangement.cube,
          AxisCube.vertex, AxisCube.base, AxisCube.side, appendCoordinate]
      · simp [GeneralArrangement.vertex, appendCoordinate]

private lemma selectionEtaZero_moment {N k : Nat} [NeZero N]
    (R : GeneralArrangement N k 8) (hadd : IsAdditiveTuple R.crossSection)
    (A : Finset (Fin (k + 1))) :
    arrangementMoment R selectionEtaZero A = 0 := by
  classical
  let A₀ : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ i.castSucc ∈ A
  let P : ZMod N := ∏ i : Fin k, if i ∈ A₀ then -R.side i else 0
  have heta (e : Fin k → Bool) (j : Fin 16) :
      (selectionEtaZero e j : ZMod N) =
        selectionIndexSign (N := N) j * parityCharacter (N := N) e := by
    rw [selectionEtaZero_cast]
    by_cases hj : (j : Nat) < 8 <;>
      simp [arrangementParityCoefficient, selectionIndexSign, hj]
  have hinner (j : Fin 16) :
      (∑ e : Fin k → Bool, parityCharacter (N := N) e *
        ∏ i : Fin k, if i.castSucc ∈ A then
          (R.base j i + if e i then R.side i else 0) else 1) = P := by
    calc
      (∑ e : Fin k → Bool, parityCharacter (N := N) e *
          ∏ i : Fin k, if i.castSucc ∈ A then
            (R.base j i + if e i then R.side i else 0) else 1) =
          ∑ e : Fin k → Bool, parityCharacter (N := N) e *
            ∏ i ∈ A₀, (R.base j i + if e i then R.side i else 0) := by
        apply Finset.sum_congr rfl
        intro e _
        congr 1
        rw [← Finset.prod_filter]
      _ = P := selection_parity_cube_sum_subset R.side (R.base j) A₀
  unfold arrangementMoment
  rw [Finset.sum_comm]
  calc
    (∑ j : Fin 16, ∑ e : Fin k → Bool,
        (selectionEtaZero e j : ZMod N) * ∏ i ∈ A, R.vertex e j i) =
        ∑ j : Fin 16, selectionIndexSign (N := N) j *
          (P * (if Fin.last k ∈ A then R.crossSection j else 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [heta, selection_vertex_product_split]
      calc
        (∑ e : Fin k → Bool,
            (selectionIndexSign (N := N) j * parityCharacter (N := N) e) *
              ((∏ i : Fin k, if i.castSucc ∈ A then
                (R.base j i + if e i then R.side i else 0) else 1) *
                (if Fin.last k ∈ A then R.crossSection j else 1))) =
            selectionIndexSign (N := N) j *
              ((∑ e : Fin k → Bool, parityCharacter (N := N) e *
                ∏ i : Fin k, if i.castSucc ∈ A then
                  (R.base j i + if e i then R.side i else 0) else 1) *
                (if Fin.last k ∈ A then R.crossSection j else 1)) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = selectionIndexSign (N := N) j *
            (P * (if Fin.last k ∈ A then R.crossSection j else 1)) := by
          rw [hinner]
    _ = 0 := by
      by_cases hfull : A₀ = Finset.univ
      · by_cases hlast : Fin.last k ∈ A
        · simp only [if_pos hlast]
          have hadd' := (selection_additive_iff R.crossSection).mp hadd
          calc
            (∑ j : Fin 16, selectionIndexSign (N := N) j *
                (P * R.crossSection j)) =
                P * ∑ j : Fin 16,
                  selectionIndexSign (N := N) j * R.crossSection j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = 0 := by rw [hadd', mul_zero]
        · simp only [if_neg hlast, mul_one]
          have hsign : (∑ j : Fin 16, selectionIndexSign (N := N) j) = 0 := by
            have hconst : IsAdditiveTuple (k := 8)
                (fun _ : Fin 16 ↦ (1 : ZMod N)) := by
              have hleft :
                  (Finset.univ.filter fun i : Fin 16 ↦ (i : Nat) < 8).card = 8 := by
                decide
              have hright :
                  (Finset.univ.filter fun i : Fin 16 ↦ 8 ≤ (i : Nat)).card = 8 := by
                decide
              unfold IsAdditiveTuple
              simp [hleft, hright]
            simpa only [mul_one] using
              (selection_additive_iff (N := N) (fun _ : Fin 16 ↦ 1)).mp hconst
          rw [← Finset.sum_mul, hsign, zero_mul]
      · have hex : ∃ i : Fin k, i ∉ A₀ := by
          by_contra hno
          push Not at hno
          apply hfull
          exact Finset.eq_univ_of_forall hno
        obtain ⟨i, hi⟩ := hex
        have hP : P = 0 := by
          unfold P
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [hi]
        simp [hP]

private lemma selectionEta_canonical {k : Nat} :
    selectionEta (selectionCanonicalDigit (k := k)) = selectionEtaZero := by
  funext e j
  rcases selectionEtaZero_cases e j with h | h <;>
    simp [selectionEta, selectionCanonicalDigit, selectionDigitInt, h]

private lemma selectionEta_negativeCanonical {k : Nat} :
    selectionEta (selectionNegativeCanonicalDigit (k := k)) =
      fun e j ↦ -selectionEtaZero e j := by
  funext e j
  rcases selectionEtaZero_cases e j with h | h <;>
    simp [selectionEta, selectionNegativeCanonicalDigit, selectionDigitInt, h]

private lemma selectionRelation_canonical_some {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hadd : IsAdditiveTuple R.crossSection) (A : Finset (Fin (k + 1))) :
    selectionRelation selectionCanonicalDigit (some A) phi R = 0 := by
  rw [selectionRelation_some, selectionEta_canonical]
  exact selectionEtaZero_moment R hadd A

private lemma selectionRelation_negative {N k : Nat} [NeZero N]
    (F : SelectionFeature k) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) :
    selectionRelation selectionNegativeCanonicalDigit F phi R =
      -selectionRelation selectionCanonicalDigit F phi R := by
  classical
  unfold selectionRelation
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [selectionDigit_negativeCanonical, selectionDigit_canonical]
  ring

private lemma selectionRelation_canonical_none_iff {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    selectionRelation selectionCanonicalDigit none phi R = 0 ↔
      R.IsRespected phi := by
  have heq : selectionRelation selectionCanonicalDigit none phi R =
      ∑ j : Fin 16, selectionIndexSign (N := N) j * R.cubeValue phi j := by
    classical
    unfold selectionRelation selectionFeatureValue GeneralArrangement.cubeValue
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [selectionDigit_canonical]
    by_cases hj : (j : Nat) < 8 <;>
      simp [arrangementParityCoefficient, parityCharacter, selectionIndexSign, hj,
        selectionVertex]
  rw [heq]
  unfold GeneralArrangement.IsRespected
  exact (selection_additive_iff (R.cubeValue phi)).symm

private noncomputable def selectionZeroRelations (N k : Nat) :
    Finset (selectionIndex k → Fin 4) := by
  classical
  exact Finset.univ.filter fun eps ↦
    ∀ z, selectionDigit (N := N) (eps z) = 0

private def selectionZeroDigitEquiv (N : Nat) [Fact (1 < N)] :
    {d : Fin 4 // selectionDigit (N := N) d = 0} ≃ Bool where
  toFun d := d.1 = 1
  invFun b := if b then ⟨1, by simp [selectionDigit, selectionDigitInt]⟩
    else ⟨0, by simp [selectionDigit, selectionDigitInt]⟩
  left_inv d := by
    have hdlt : (d.1 : Nat) < 2 := by
      exact (selectionDigit_eq_zero_iff N d.1).mp d.2
    apply Subtype.ext
    by_cases hd : (d.1 : Nat) = 1
    · have hdfin : d.1 = (1 : Fin 4) := Fin.ext hd
      simp [hdfin]
    · have hdval : (d.1 : Nat) = 0 := by omega
      have hdfin : d.1 = (0 : Fin 4) := Fin.ext hdval
      simp [hdfin]
  right_inv b := by cases b <;> simp

private lemma selection_zeroDigit_card (N : Nat) (hN : 3 ≤ N) :
    Fintype.card {d : Fin 4 // selectionDigit (N := N) d = 0} = 2 := by
  letI : Fact (1 < N) := ⟨by omega⟩
  rw [Fintype.card_congr (selectionZeroDigitEquiv N)]
  decide

private lemma selectionZeroRelations_card (N k : Nat) (hN : 3 ≤ N) :
    (selectionZeroRelations N k).card = 2 ^ (2 ^ (k + 4)) := by
  classical
  letI : Fact (1 < N) := ⟨by omega⟩
  have hdigit := selection_zeroDigit_card N hN
  unfold selectionZeroRelations
  calc
    (Finset.univ.filter fun eps : selectionIndex k → Fin 4 ↦
        ∀ z, selectionDigit (N := N) (eps z) = 0).card =
        Fintype.card {eps : selectionIndex k → Fin 4 //
          ∀ z, selectionDigit (N := N) (eps z) = 0} := by
      rw [Finset.filter_congr_decidable]
      exact (Fintype.card_subtype _).symm
    _ = Fintype.card
        ((z : selectionIndex k) →
          {d : Fin 4 // selectionDigit (N := N) d = 0}) :=
      Fintype.card_congr
        (Equiv.subtypePiEquivPi
          (p := fun (_ : selectionIndex k) d ↦
            selectionDigit (N := N) d = 0))
    _ = 2 ^ (2 ^ (k + 4)) := by
      rw [Fintype.card_fun, hdigit, selection_index_card]

private lemma selectionCanonical_not_zeroRelation (N k : Nat) (hN : 3 ≤ N) :
    selectionCanonicalDigit (k := k) ∉ selectionZeroRelations N k := by
  classical
  letI : NeZero N := ⟨by omega⟩
  letI : Fact (1 < N) := ⟨by omega⟩
  simp only [selectionZeroRelations, Finset.mem_filter, Finset.mem_univ, true_and]
  push Not
  let z₀ : selectionIndex k := (fun _ ↦ false, (0 : Fin 16))
  refine ⟨z₀, ?_⟩
  have hval : arrangementParityCoefficient (N := N) (d := 8) z₀.1 z₀.2 = 1 := by
    simp [z₀, arrangementParityCoefficient, parityCharacter, boolWeight,
      countWhere]
  rw [selectionDigit_canonical, hval]
  exact (one_ne_zero : (1 : ZMod N) ≠ 0)

private lemma selectionNegativeCanonical_not_zeroRelation
    (N k : Nat) (hN : 3 ≤ N) :
    selectionNegativeCanonicalDigit (k := k) ∉ selectionZeroRelations N k := by
  classical
  letI : NeZero N := ⟨by omega⟩
  letI : Fact (1 < N) := ⟨by omega⟩
  simp only [selectionZeroRelations, Finset.mem_filter, Finset.mem_univ, true_and]
  push Not
  let z₀ : selectionIndex k := (fun _ ↦ false, (0 : Fin 16))
  refine ⟨z₀, ?_⟩
  have hval : arrangementParityCoefficient (N := N) (d := 8) z₀.1 z₀.2 = 1 := by
    simp [z₀, arrangementParityCoefficient, parityCharacter, boolWeight,
      countWhere]
  rw [selectionDigit_negativeCanonical, hval]
  exact neg_ne_zero.mpr (one_ne_zero : (1 : ZMod N) ≠ 0)

private lemma selectionCanonical_ne_negative {k : Nat} :
    selectionCanonicalDigit (k := k) ≠ selectionNegativeCanonicalDigit := by
  intro h
  let z₀ : selectionIndex k := (fun _ ↦ false, (0 : Fin 16))
  have hz := congrFun h z₀
  norm_num [selectionCanonicalDigit, selectionNegativeCanonicalDigit,
    selectionEtaZero, z₀, boolWeight, countWhere] at hz
  omega

private lemma selectionRelation_zero_of_zeroDigits {N k : Nat} [NeZero N]
    (eps : selectionIndex k → Fin 4)
    (heps : ∀ z, selectionDigit (N := N) (eps z) = 0)
    (F : SelectionFeature k) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) :
    selectionRelation eps F phi R = 0 := by
  unfold selectionRelation
  apply Finset.sum_eq_zero
  intro z _
  rw [heps z, zero_mul]

private lemma selectionValidRelations_eq_zero_of_nondegenerate
    {N k : Nat} [NeZero N] (hN : 3 ≤ N)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hnondegenerate : ¬ R.IsDegenerate) (hbad : ¬ R.IsRespected phi) :
    selectionValidRelations phi R = selectionZeroRelations N k := by
  classical
  ext eps
  simp only [selectionValidRelations, selectionZeroRelations,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hvalid
    rcases selection_valid_classification_of_nondegenerate hN phi R
        hnondegenerate eps hvalid with hzero | hcanon | hneg
    · exact hzero
    · subst eps
      exact (hbad ((selectionRelation_canonical_none_iff phi R).mp
        (hvalid none))).elim
    · subst eps
      have hc : selectionRelation selectionCanonicalDigit none phi R = 0 := by
        have hn := hvalid none
        rw [selectionRelation_negative] at hn
        exact neg_eq_zero.mp hn
      exact (hbad ((selectionRelation_canonical_none_iff phi R).mp hc)).elim
  · intro hzero F
    exact selectionRelation_zero_of_zeroDigits eps hzero F phi R

private lemma selectionValidRelations_eq_insert_of_nondegenerate
    {N k : Nat} [NeZero N] (hN : 3 ≤ N)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hadd : IsAdditiveTuple R.crossSection) (hnondegenerate : ¬ R.IsDegenerate)
    (hgood : R.IsRespected phi) :
    selectionValidRelations phi R =
      insert selectionCanonicalDigit
        (insert selectionNegativeCanonicalDigit (selectionZeroRelations N k)) := by
  classical
  ext eps
  simp only [selectionValidRelations, selectionZeroRelations,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hvalid
    rcases selection_valid_classification_of_nondegenerate hN phi R
        hnondegenerate eps hvalid with hzero | hcanon | hneg
    · exact Or.inr (Or.inr hzero)
    · exact Or.inl hcanon
    · exact Or.inr (Or.inl hneg)
  · rintro (hcanon | hneg | hzero)
    · subst eps
      intro F
      rcases F with _ | A
      · exact (selectionRelation_canonical_none_iff phi R).mpr hgood
      · exact selectionRelation_canonical_some phi R hadd A
    · subst eps
      intro F
      rw [selectionRelation_negative]
      rcases F with _ | A
      · rw [(selectionRelation_canonical_none_iff phi R).mpr hgood, neg_zero]
      · rw [selectionRelation_canonical_some phi R hadd A, neg_zero]
    · intro F
      exact selectionRelation_zero_of_zeroDigits eps hzero F phi R

private lemma selectionValidRelations_card_good {N k : Nat} [NeZero N]
    (hN : 3 ≤ N) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) (hadd : IsAdditiveTuple R.crossSection)
    (hnondegenerate : ¬ R.IsDegenerate) (hgood : R.IsRespected phi) :
    (selectionValidRelations phi R).card = 2 ^ (2 ^ (k + 4)) + 2 := by
  classical
  rw [selectionValidRelations_eq_insert_of_nondegenerate hN phi R hadd
    hnondegenerate hgood]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_insert_of_notMem
      (selectionNegativeCanonical_not_zeroRelation N k hN),
      selectionZeroRelations_card N k hN]
  · simp only [Finset.mem_insert, not_or]
    exact ⟨selectionCanonical_ne_negative,
      selectionCanonical_not_zeroRelation N k hN⟩

private lemma selectionValidRelations_card_bad {N k : Nat} [NeZero N]
    (hN : 3 ≤ N) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) (hnondegenerate : ¬ R.IsDegenerate)
    (hbad : ¬ R.IsRespected phi) :
    (selectionValidRelations phi R).card = 2 ^ (2 ^ (k + 4)) := by
  rw [selectionValidRelations_eq_zero_of_nondegenerate hN phi R
    hnondegenerate hbad, selectionZeroRelations_card N k hN]

private lemma selection_good_average_base {N k : Nat} [NeZero N]
    (hN : 3 ≤ N) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) (hadd : IsAdditiveTuple R.crossSection)
    (hnondegenerate : ¬ R.IsDegenerate) (hgood : R.IsRespected phi) :
    ((4 : Real)⁻¹) ^ (2 ^ (k + 4)) * (selectionValidRelations phi R).card =
      ((2 : Real)⁻¹) ^ (2 ^ (k + 4)) *
        (1 + 2 * ((2 : Real)⁻¹) ^ (2 ^ (k + 4))) := by
  rw [selectionValidRelations_card_good hN phi R hadd hnondegenerate hgood]
  push_cast
  let M := 2 ^ (k + 4)
  change ((4 : Real)⁻¹) ^ M * ((2 : Real) ^ M + 2) =
    ((2 : Real)⁻¹) ^ M * (1 + 2 * ((2 : Real)⁻¹) ^ M)
  rw [mul_add]
  rw [show ((4 : Real)⁻¹) ^ M * (2 : Real) ^ M =
      ((2 : Real)⁻¹) ^ M by
    rw [← mul_pow]
    norm_num]
  have hfour : ((4 : Real)⁻¹) ^ M =
      ((2 : Real)⁻¹) ^ (2 * M) := by
    rw [show (4 : Real)⁻¹ = ((2 : Real)⁻¹) ^ 2 by norm_num,
      ← pow_mul]
  rw [hfour]
  rw [show 2 * M = M + M by omega, pow_add]
  ring

private lemma selection_bad_average_base {N k : Nat} [NeZero N]
    (hN : 3 ≤ N) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) (hnondegenerate : ¬ R.IsDegenerate)
    (hbad : ¬ R.IsRespected phi) :
    ((4 : Real)⁻¹) ^ (2 ^ (k + 4)) * (selectionValidRelations phi R).card =
      ((2 : Real)⁻¹) ^ (2 ^ (k + 4)) := by
  rw [selectionValidRelations_card_bad hN phi R hnondegenerate hbad]
  push_cast
  rw [← mul_pow]
  norm_num

private lemma selection_third_index {k : Nat}
    (u v : selectionIndex k) :
    ∃ w : selectionIndex k, w ≠ u ∧ w ≠ v := by
  classical
  let e₀ : Fin k → Bool := fun _ ↦ false
  let z₀ : selectionIndex k := (e₀, (0 : Fin 16))
  let z₁ : selectionIndex k := (e₀, (1 : Fin 16))
  let z₂ : selectionIndex k := (e₀, (2 : Fin 16))
  have h₀₁ : z₀ ≠ z₁ := by
    intro h
    have := congrArg (fun z : selectionIndex k ↦ (z.2 : Nat)) h
    norm_num [z₀, z₁] at this
  have h₀₂ : z₀ ≠ z₂ := by
    intro h
    have := congrArg (fun z : selectionIndex k ↦ (z.2 : Nat)) h
    norm_num [z₀, z₂] at this
  have h₁₂ : z₁ ≠ z₂ := by
    intro h
    have := congrArg (fun z : selectionIndex k ↦ (z.2 : Nat)) h
    norm_num [z₁, z₂] at this
  by_cases h₀ : z₀ ≠ u ∧ z₀ ≠ v
  · exact ⟨z₀, h₀⟩
  by_cases h₁ : z₁ ≠ u ∧ z₁ ≠ v
  · exact ⟨z₁, h₁⟩
  refine ⟨z₂, ?_, ?_⟩ <;>
    push Not at h₀ h₁ <;> aesop

private lemma selection_injective_of_nondegenerate {N k : Nat} [NeZero N]
    (hN : 2 ≤ N) (R : GeneralArrangement N k 8)
    (hnondegenerate : ¬ R.IsDegenerate) :
    Function.Injective (selectionVertex R) := by
  classical
  letI : Fact (1 < N) := ⟨by omega⟩
  intro u v huvVertex
  by_contra huv
  apply hnondegenerate
  have hvu : v ≠ u := by
    intro h
    exact huv h.symm
  obtain ⟨w, hwu, hwv⟩ := selection_third_index u v
  let eta : (Fin k → Bool) → Fin 16 → Int := fun e j ↦
    if (e, j) = u then 1 else if (e, j) = v then -1 else 0
  have hetaTernary : IsTernaryCoefficient
      (fun z : (Fin k → Bool) × Fin 16 ↦ eta z.1 z.2) := by
    intro z
    by_cases hzu : z = u <;> by_cases hzv : z = v <;>
      simp [eta, hzu, hzv, hvu]
  have hmoment : ∀ A : Finset (Fin (k + 1)),
      arrangementMoment R eta A = 0 := by
    intro A
    unfold arrangementMoment
    rw [← Fintype.sum_prod_type (fun z : selectionIndex k ↦
      ((eta z.1 z.2 : Int) : ZMod N) *
        ∏ i ∈ A, R.vertex z.1 z.2 i)]
    let f : selectionIndex k → ZMod N := fun z ↦
      ∏ i ∈ A, R.vertex z.1 z.2 i
    have hf : f u = f v := by
      change R.vertex u.1 u.2 = R.vertex v.1 v.2 at huvVertex
      unfold f
      apply Finset.prod_congr rfl
      intro i _
      exact congrFun huvVertex i
    simp only [eta, Int.cast_ite, Int.cast_one, Int.cast_neg, Int.cast_zero]
    simp_rw [ite_mul, one_mul, neg_one_mul, zero_mul]
    change (∑ z, if z = u then f z else if z = v then -f z else 0) = 0
    calc
      (∑ z, if z = u then f z else if z = v then -f z else 0) =
          (∑ z, if z = u then f z else 0) +
            ∑ z, if z = v then -f z else 0 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro z _
        by_cases hzu : z = u <;> by_cases hzv : z = v <;>
          simp [hzu, hzv, huv, hvu]
      _ = f u + -f v := by
        rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
        simp
      _ = 0 := by rw [hf]; ring
  have hnotmultiple : ¬ IsModularMultiple
      (fun z : (Fin k → Bool) × Fin 16 ↦ eta z.1 z.2)
      (fun z ↦ arrangementParityCoefficient (N := N) (d := 8) z.1 z.2) := by
    rintro ⟨q, hq⟩
    have hqu := hq u
    have hqw := hq w
    have hparityUnit (z : selectionIndex k) :
        IsUnit (arrangementParityCoefficient (N := N) (d := 8) z.1 z.2) := by
      unfold arrangementParityCoefficient parityCharacter
      split
      · exact (isUnit_one.neg.pow _)
      · exact (isUnit_one.neg.pow _).neg
    have hqne : q ≠ 0 := by
      intro hqzero
      rw [hqzero, zero_mul] at hqu
      simp [eta] at hqu
    have hqwzero : q *
        arrangementParityCoefficient (N := N) (d := 8) w.1 w.2 = 0 := by
      simpa [eta, hwu, hwv] using hqw.symm
    apply hqne
    apply (hparityUnit w).mul_right_cancel
    simpa using hqwzero
  exact ⟨eta, hetaTernary, hnotmultiple, hmoment⟩

private lemma selectionCarrier_prod_of_nondegenerate {N k : Nat} [NeZero N]
    (hN : 2 ≤ N) (R : GeneralArrangement N k 8)
    (hnondegenerate : ¬ R.IsDegenerate)
    (p : Point N (k + 1) → Real) :
    (∏ z ∈ selectionCarrier R, p z) =
      ∏ i : selectionIndex k, p (selectionVertex R i) := by
  classical
  unfold selectionCarrier
  rw [Finset.prod_image
    (selection_injective_of_nondegenerate hN R hnondegenerate).injOn]

/-! ## Iterating the one-stage selection -/

private lemma selection_expect_pi_prod_real {I C : Type*} [Fintype I]
    [DecidableEq I] [Fintype C] [Nonempty C] (f : I → C → Real) :
    (𝔼 g : I → C, ∏ i : I, f i (g i)) =
      ∏ i : I, 𝔼 c : C, f i c := by
  classical
  simp only [Finset.expect_univ, Fintype.card_fun]
  rw [← Fintype.prod_sum]
  simp only [NNRat.smul_def, NNRat.cast_inv, NNRat.cast_natCast,
    Nat.cast_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simp [inv_pow]

private def multiStageSelectionWeight {N k r : Nat} [NeZero N]
    (C : Fin r → SelectionPhase N k)
    (phi : Point N (k + 1) → ZMod N) (z : Point N (k + 1)) : Real :=
  ∏ i : Fin r, oneStageSelectionWeight (C i) phi z

private lemma multiStageSelectionWeight_nonneg {N k r : Nat} [NeZero N]
    (C : Fin r → SelectionPhase N k)
    (phi : Point N (k + 1) → ZMod N) (z : Point N (k + 1)) :
    0 ≤ multiStageSelectionWeight C phi z := by
  exact Finset.prod_nonneg fun i hi ↦
    oneStageSelectionWeight_nonneg (C i) phi z

private lemma multiStageSelectionWeight_le_one {N k r : Nat} [NeZero N]
    (C : Fin r → SelectionPhase N k)
    (phi : Point N (k + 1) → ZMod N) (z : Point N (k + 1)) :
    multiStageSelectionWeight C phi z ≤ 1 := by
  unfold multiStageSelectionWeight
  exact Finset.prod_le_one
    (fun _ _ ↦ oneStageSelectionWeight_nonneg _ _ _)
    (fun _ _ ↦ oneStageSelectionWeight_le_one _ _ _)

private lemma selection_multiStage_indexed_average {N k r : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    (𝔼 C : Fin r → SelectionPhase N k,
      ∏ z : selectionIndex k,
        multiStageSelectionWeight C phi (selectionVertex R z)) =
      (((4 : Real)⁻¹) ^ (2 ^ (k + 4)) *
        (selectionValidRelations phi R).card) ^ r := by
  classical
  calc
    (𝔼 C : Fin r → SelectionPhase N k,
        ∏ z : selectionIndex k,
          multiStageSelectionWeight C phi (selectionVertex R z)) =
        𝔼 C : Fin r → SelectionPhase N k,
          ∏ i : Fin r, ∏ z : selectionIndex k,
            oneStageSelectionWeight (C i) phi (selectionVertex R z) := by
      apply Finset.expect_congr rfl
      intro C hC
      simp only [multiStageSelectionWeight]
      rw [Finset.prod_comm]
    _ = ∏ _i : Fin r,
          𝔼 c : SelectionPhase N k,
            ∏ z : selectionIndex k,
              oneStageSelectionWeight c phi (selectionVertex R z) := by
      exact selection_expect_pi_prod_real
        (fun _i c ↦ ∏ z : selectionIndex k,
          oneStageSelectionWeight c phi (selectionVertex R z))
    _ = ∏ _i : Fin r,
          (((4 : Real)⁻¹) ^ (2 ^ (k + 4)) *
            (selectionValidRelations phi R).card) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact selection_oneStage_average phi R
    _ = (((4 : Real)⁻¹) ^ (2 ^ (k + 4)) *
          (selectionValidRelations phi R).card) ^ r := by simp

private noncomputable def selectionGoodNondegenerate {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (selectionGoodArrangements B phi).filter fun R ↦ ¬ R.IsDegenerate

private noncomputable def selectionBadNondegenerate {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (selectionBadArrangements B phi).filter fun R ↦ ¬ R.IsDegenerate

private lemma selection_phase_score_average {N k r : Nat} [NeZero N]
    (hN : 3 ≤ N) (eta : Real) (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    (𝔼 C : Fin r → SelectionPhase N k, (
      eta * (∑ R ∈ selectionGoodNondegenerate B phi,
        ∏ z : selectionIndex k,
          multiStageSelectionWeight C phi (selectionVertex R z)) -
      ∑ R ∈ selectionBadNondegenerate B phi,
        ∏ z : selectionIndex k,
          multiStageSelectionWeight C phi (selectionVertex R z))) =
      eta *
          (((2 : Real)⁻¹) ^ (2 ^ (k + 4)) *
            (1 + 2 * ((2 : Real)⁻¹) ^ (2 ^ (k + 4)))) ^ r *
          (selectionGoodNondegenerate B phi).card -
        (((2 : Real)⁻¹) ^ (2 ^ (k + 4))) ^ r *
          (selectionBadNondegenerate B phi).card := by
  classical
  have hgoodavg :
      (𝔼 C : Fin r → SelectionPhase N k,
        ∑ R ∈ selectionGoodNondegenerate B phi,
          ∏ z : selectionIndex k,
            multiStageSelectionWeight C phi (selectionVertex R z)) =
        (((2 : Real)⁻¹) ^ (2 ^ (k + 4)) *
          (1 + 2 * ((2 : Real)⁻¹) ^ (2 ^ (k + 4)))) ^ r *
            (selectionGoodNondegenerate B phi).card := by
    rw [Finset.expect_sum_comm]
    calc
      (∑ R ∈ selectionGoodNondegenerate B phi,
          𝔼 C : Fin r → SelectionPhase N k,
            ∏ z : selectionIndex k,
              multiStageSelectionWeight C phi (selectionVertex R z)) =
          ∑ _R ∈ selectionGoodNondegenerate B phi,
            (((2 : Real)⁻¹) ^ (2 ^ (k + 4)) *
              (1 + 2 * ((2 : Real)⁻¹) ^ (2 ^ (k + 4)))) ^ r := by
        apply Finset.sum_congr rfl
        intro R hR
        rw [selection_multiStage_indexed_average]
        have hR' := Finset.mem_filter.mp hR
        have hgoodData :
            R ∈ selectionArrangements B ∧ R.IsRespected phi := by
          simpa [selectionGoodArrangements] using hR'.1
        have hadd : IsAdditiveTuple R.crossSection := by
          have hIsIn : R.IsIn B := by
            simpa [selectionArrangements] using hgoodData.1
          exact hIsIn.1
        rw [selection_good_average_base hN phi R hadd hR'.2 hgoodData.2]
      _ = (((2 : Real)⁻¹) ^ (2 ^ (k + 4)) *
            (1 + 2 * ((2 : Real)⁻¹) ^ (2 ^ (k + 4)))) ^ r *
          (selectionGoodNondegenerate B phi).card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  have hbadavg :
      (𝔼 C : Fin r → SelectionPhase N k,
        ∑ R ∈ selectionBadNondegenerate B phi,
          ∏ z : selectionIndex k,
            multiStageSelectionWeight C phi (selectionVertex R z)) =
        (((2 : Real)⁻¹) ^ (2 ^ (k + 4))) ^ r *
          (selectionBadNondegenerate B phi).card := by
    rw [Finset.expect_sum_comm]
    calc
      (∑ R ∈ selectionBadNondegenerate B phi,
          𝔼 C : Fin r → SelectionPhase N k,
            ∏ z : selectionIndex k,
              multiStageSelectionWeight C phi (selectionVertex R z)) =
          ∑ _R ∈ selectionBadNondegenerate B phi,
            (((2 : Real)⁻¹) ^ (2 ^ (k + 4))) ^ r := by
        apply Finset.sum_congr rfl
        intro R hR
        rw [selection_multiStage_indexed_average]
        have hR' := Finset.mem_filter.mp hR
        have hbadMem := Finset.mem_sdiff.mp hR'.1
        have hIsIn : R.IsIn B := by
          simpa [selectionArrangements] using hbadMem.1
        have hbad : ¬ R.IsRespected phi := by
          intro hrespect
          apply hbadMem.2
          simp [selectionGoodArrangements, hbadMem.1, hrespect]
        rw [selection_bad_average_base hN phi R hR'.2 hbad]
      _ = (((2 : Real)⁻¹) ^ (2 ^ (k + 4))) ^ r *
          (selectionBadNondegenerate B phi).card := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
  rw [Finset.expect_sub_distrib, ← Finset.mul_expect, hgoodavg, hbadavg]
  ring

private noncomputable def selectionDegenerateFinset (N k : Nat) [NeZero N] :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact Finset.univ.filter fun R ↦
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerate

@[simp] private lemma mem_selectionDegenerateFinset {N k : Nat} [NeZero N]
    (R : GeneralArrangement N k 8) :
    R ∈ selectionDegenerateFinset N k ↔
      IsAdditiveTuple R.crossSection ∧ R.IsDegenerate := by
  simp [selectionDegenerateFinset]

private lemma selectionDegenerateFinset_card (N k : Nat) [NeZero N] :
    (selectionDegenerateFinset N k).card =
      degenerateGeneralArrangementCount (N := N) (k := k) 8 := by
  classical
  unfold selectionDegenerateFinset degenerateGeneralArrangementCount countWhere
  apply congrArg Finset.card
  ext R
  simp

private lemma selectionGoodNondegenerate_card_lower {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    (selectionGoodArrangements B phi).card ≤
      (selectionGoodNondegenerate B phi).card +
        degenerateGeneralArrangementCount (N := N) (k := k) 8 := by
  classical
  let badDeg := (selectionGoodArrangements B phi).filter
    fun R ↦ R.IsDegenerate
  have hsplit :
      (selectionGoodNondegenerate B phi).card + badDeg.card =
        (selectionGoodArrangements B phi).card := by
    simpa [selectionGoodNondegenerate, badDeg] using
      (Finset.card_filter_add_card_filter_not
        (s := selectionGoodArrangements B phi) (fun R ↦ ¬ R.IsDegenerate))
  have hsub : badDeg ⊆ selectionDegenerateFinset N k := by
    intro R hR
    have hR' := Finset.mem_filter.mp hR
    have hgoodData : R ∈ selectionArrangements B ∧ R.IsRespected phi := by
      simpa [selectionGoodArrangements] using hR'.1
    have hIsIn : R.IsIn B := by
      simpa [selectionArrangements] using hgoodData.1
    simp [selectionDegenerateFinset, hIsIn.1, hR'.2]
  have hbadcard : badDeg.card ≤
      degenerateGeneralArrangementCount (N := N) (k := k) 8 := by
    calc
      badDeg.card ≤ (selectionDegenerateFinset N k).card :=
        Finset.card_le_card hsub
      _ = degenerateGeneralArrangementCount (N := N) (k := k) 8 :=
        selectionDegenerateFinset_card N k
  omega

private lemma selectionBadNondegenerate_card_upper {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    (selectionBadNondegenerate B phi).card ≤
      (selectionArrangements B).card := by
  classical
  apply Finset.card_le_card
  intro R hR
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hR).1).1

private lemma selection_carrier_score_lower {N k r : Nat} [NeZero N]
    (hN : 2 ≤ N) (eta : Real) (heta : 0 ≤ eta)
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N)
    (C : Fin r → SelectionPhase N k) :
    eta * (∑ R ∈ selectionGoodNondegenerate B phi,
      ∏ z : selectionIndex k,
        multiStageSelectionWeight C phi (selectionVertex R z)) -
      (∑ R ∈ selectionBadNondegenerate B phi,
        ∏ z : selectionIndex k,
          multiStageSelectionWeight C phi (selectionVertex R z)) -
      degenerateGeneralArrangementCount (N := N) (k := k) 8 ≤
    eta * (∑ R ∈ selectionGoodArrangements B phi,
      ∏ z ∈ selectionCarrier R, multiStageSelectionWeight C phi z) -
      ∑ R ∈ selectionBadArrangements B phi,
        ∏ z ∈ selectionCarrier R,
          multiStageSelectionWeight C phi z := by
  classical
  let badDeg := (selectionBadArrangements B phi).filter
    fun R ↦ R.IsDegenerate
  have hp0 (z : Point N (k + 1)) :
      0 ≤ multiStageSelectionWeight C phi z :=
    multiStageSelectionWeight_nonneg C phi z
  have hp1 (z : Point N (k + 1)) :
      multiStageSelectionWeight C phi z ≤ 1 :=
    multiStageSelectionWeight_le_one C phi z
  have hgoodSub : selectionGoodNondegenerate B phi ⊆
      selectionGoodArrangements B phi := fun R hR ↦
    (Finset.mem_filter.mp hR).1
  have hgoodSum :
      (∑ R ∈ selectionGoodNondegenerate B phi,
          ∏ z : selectionIndex k,
            multiStageSelectionWeight C phi (selectionVertex R z)) ≤
        ∑ R ∈ selectionGoodArrangements B phi,
          ∏ z ∈ selectionCarrier R,
            multiStageSelectionWeight C phi z := by
    calc
      (∑ R ∈ selectionGoodNondegenerate B phi,
          ∏ z : selectionIndex k,
            multiStageSelectionWeight C phi (selectionVertex R z)) =
          ∑ R ∈ selectionGoodNondegenerate B phi,
            ∏ z ∈ selectionCarrier R,
              multiStageSelectionWeight C phi z := by
        apply Finset.sum_congr rfl
        intro R hR
        symm
        exact selectionCarrier_prod_of_nondegenerate hN R
          (Finset.mem_filter.mp hR).2 _
      _ ≤ ∑ R ∈ selectionGoodArrangements B phi,
          ∏ z ∈ selectionCarrier R,
            multiStageSelectionWeight C phi z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hgoodSub
        intro R hR hnot
        exact Finset.prod_nonneg fun z hz ↦ hp0 z
  have hbadSplit :
      (∑ R ∈ selectionBadArrangements B phi,
          ∏ z ∈ selectionCarrier R,
            multiStageSelectionWeight C phi z) =
        (∑ R ∈ selectionBadNondegenerate B phi,
          ∏ z ∈ selectionCarrier R,
            multiStageSelectionWeight C phi z) +
        ∑ R ∈ badDeg,
          ∏ z ∈ selectionCarrier R,
            multiStageSelectionWeight C phi z := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := selectionBadArrangements B phi)
      (p := fun R ↦ ¬ R.IsDegenerate)]
    simp [selectionBadNondegenerate, badDeg]
  have hbadNondegenerateEq :
      (∑ R ∈ selectionBadNondegenerate B phi,
          ∏ z ∈ selectionCarrier R,
            multiStageSelectionWeight C phi z) =
        ∑ R ∈ selectionBadNondegenerate B phi,
          ∏ z : selectionIndex k,
            multiStageSelectionWeight C phi (selectionVertex R z) := by
    apply Finset.sum_congr rfl
    intro R hR
    exact selectionCarrier_prod_of_nondegenerate hN R
      (Finset.mem_filter.mp hR).2 _
  have hbadDegenerateSum :
      (∑ R ∈ badDeg,
          ∏ z ∈ selectionCarrier R,
            multiStageSelectionWeight C phi z) ≤
        degenerateGeneralArrangementCount (N := N) (k := k) 8 := by
    have hterm :
        (∑ R ∈ badDeg,
            ∏ z ∈ selectionCarrier R,
              multiStageSelectionWeight C phi z) ≤
          ∑ _R ∈ badDeg, (1 : Real) := by
      apply Finset.sum_le_sum
      intro R hR
      exact Finset.prod_le_one (fun z hz ↦ hp0 z) (fun z hz ↦ hp1 z)
    have hsub : badDeg ⊆ selectionDegenerateFinset N k := by
      intro R hR
      have hR' := Finset.mem_filter.mp hR
      have hbadMem := Finset.mem_sdiff.mp hR'.1
      have hIsIn : R.IsIn B := by
        simpa [selectionArrangements] using hbadMem.1
      simp [selectionDegenerateFinset, hIsIn.1, hR'.2]
    calc
      (∑ R ∈ badDeg,
          ∏ z ∈ selectionCarrier R,
            multiStageSelectionWeight C phi z) ≤
          ∑ _R ∈ badDeg, (1 : Real) := hterm
      _ = (badDeg.card : Real) := by simp
      _ ≤ (selectionDegenerateFinset N k).card := by
        exact_mod_cast Finset.card_le_card hsub
      _ = degenerateGeneralArrangementCount (N := N) (k := k) 8 := by
        norm_cast
        exact selectionDegenerateFinset_card N k
  rw [hbadSplit, hbadNondegenerateEq]
  have hgoodScaled := mul_le_mul_of_nonneg_left hgoodSum heta
  nlinarith

/-! ## Amplification and the choice of the number of stages -/

private lemma selection_vertex_times_amplification (k : Nat) :
    2 ^ (k + 4) * 2 ^ (2 ^ (k + 4) - 1) =
      arrangementSelectionExponent k := by
  unfold arrangementSelectionExponent
  rw [← pow_add]
  congr 1
  have hpos : 1 ≤ 2 ^ (k + 4) :=
    Nat.one_le_pow _ 2 (by norm_num)
  omega

private lemma selection_amplification_step (k : Nat) :
    (2 : Real) ≤
      (1 + 2 * ((2 : Real)⁻¹) ^ (2 ^ (k + 4))) ^
        (2 ^ (2 ^ (k + 4) - 1)) := by
  let M : Nat := 2 ^ (k + 4)
  let K : Nat := 2 ^ (M - 1)
  let a : Real := 2 * ((2 : Real)⁻¹) ^ M
  have hM : 1 ≤ M := by
    dsimp only [M]
    exact Nat.one_le_pow _ 2 (by norm_num)
  have hKa : (K : Real) * a = 1 := by
    dsimp only [K, a]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    calc
      (2 : Real) ^ (M - 1) *
          (2 * ((2 : Real)⁻¹) ^ M) =
          ((2 : Real) ^ (M - 1) * 2) * ((2 : Real)⁻¹) ^ M := by ring
      _ = (2 : Real) ^ M * ((2 : Real)⁻¹) ^ M := by
        rw [← pow_succ]
        congr 2
        omega
      _ = 1 := by
        rw [← mul_pow]
        norm_num
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    positivity
  have hbern := one_add_mul_le_pow (a := a) (by linarith) K
  change (2 : Real) ≤ (1 + a) ^ K
  calc
    (2 : Real) = 1 + (K : Real) * a := by rw [hKa]; norm_num
    _ ≤ (1 + a) ^ K := hbern

private noncomputable def selectionTarget (k : Nat) (alpha eta : Real) : Real :=
  (alpha * eta / 4) ^ arrangementSelectionExponent k

private lemma selectionTarget_eq (k : Nat) (alpha eta : Real) :
    selectionTarget k alpha eta =
      (alpha * eta / 4) ^ arrangementSelectionExponent k := by rfl

attribute [irreducible] selectionTarget

private lemma selection_exists_stage_margin (k : Nat) (alpha eta : Real)
    (halpha : 0 < alpha) (heta : 0 < eta)
    (halpha_one : alpha ≤ 1) (heta_one : eta ≤ 1) :
    ∃ m : Nat, 0 <
      (((2 : Real)⁻¹) ^ (2 ^ (k + 4))) ^
          (2 ^ (2 ^ (k + 4) - 1) * m) *
        (alpha * eta *
            (1 + 2 * ((2 : Real)⁻¹) ^ (2 ^ (k + 4))) ^
              (2 ^ (2 ^ (k + 4) - 1) * m) - 1) -
        eta * selectionTarget k alpha eta := by
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
  have hqupper : q < a / 2 := hnupper
  have hqlower : a / 4 ≤ q := by
    dsimp [q, m]
    rw [pow_succ]
    norm_num
    nlinarith
  let M : Nat := 2 ^ (k + 4)
  let K : Nat := 2 ^ (M - 1)
  let E : Nat := arrangementSelectionExponent k
  let amp : Real := 1 + 2 * ((2 : Real)⁻¹) ^ M
  have hamp : (2 : Real) ≤ amp ^ K := by
    exact selection_amplification_step k
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
  have hME : M * K = E := by
    exact selection_vertex_times_amplification k
  have hpower :
      (((2 : Real)⁻¹) ^ M) ^ (K * m) = q ^ E := by
    calc
      (((2 : Real)⁻¹) ^ M) ^ (K * m) =
          ((2 : Real)⁻¹) ^ (M * (K * m)) :=
        (pow_mul ((2 : Real)⁻¹) M (K * m)).symm
      _ = ((2 : Real)⁻¹) ^ (E * m) := by
        rw [← Nat.mul_assoc, hME]
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
  unfold selectionTarget
  change 0 <
    (((2 : Real)⁻¹) ^ M) ^ (K * m) *
        (a * amp ^ (K * m) - 1) - eta * (a / 4) ^ E
  rw [hpower]
  exact sub_pos.mpr (htarget.trans_lt hstrict)

/-! ## Absorbing the degenerate arrangements -/

/-! The height-zero case used by Lemma 9.3 does not need a field.  After the
defining additive relation eliminates one coordinate, every genuinely new
ternary relation has a nonzero coefficient in `{±1, ±2}`.  Such a coefficient
has fibres of size at most two in every cyclic group. -/

private def selectionZeroBool : Fin 0 → Bool := default

private def selectionZeroCoefficient {N : Nat}
    (eps : selectionIndex 0 → Fin 4) (j : Fin 16) : ZMod N :=
  selectionDigit (eps (selectionZeroBool, j))

private def selectionZeroReducedCoefficient {N : Nat}
    (eps : selectionIndex 0 → Fin 4) (j : Fin 16) : ZMod N :=
  selectionZeroCoefficient eps j -
    selectionZeroCoefficient eps 0 * selectionIndexSign j

private def selectionZeroNoncanonical {N : Nat}
    (eps : selectionIndex 0 → Fin 4) : Prop :=
  ¬ ∃ q : ZMod N, ∀ j,
    selectionZeroCoefficient eps j = q * selectionIndexSign j

private lemma selectionZero_parityCoefficient {N : Nat}
    (e : Fin 0 → Bool) (j : Fin 16) :
    arrangementParityCoefficient (N := N) (d := 8) e j =
      selectionIndexSign j := by
  have he : e = selectionZeroBool := Subsingleton.elim _ _
  subst e
  simp [selectionZeroBool, arrangementParityCoefficient, parityCharacter,
    boolWeight, countWhere, selectionIndexSign]

private lemma selectionZero_exists_reducedCoefficient {N : Nat}
    (eps : selectionIndex 0 → Fin 4) (hnoncanonical :
      selectionZeroNoncanonical (N := N) eps) :
    ∃ j : Fin 16, j ≠ 0 ∧
      selectionZeroReducedCoefficient (N := N) eps j ≠ 0 := by
  unfold selectionZeroNoncanonical at hnoncanonical
  push Not at hnoncanonical
  obtain ⟨j, hj⟩ :=
    hnoncanonical (selectionZeroCoefficient (N := N) eps 0)
  refine ⟨j, ?_, ?_⟩
  · intro hj0
    subst j
    apply hj
    simp [selectionIndexSign]
  · simpa [selectionZeroReducedCoefficient, sub_ne_zero] using hj

private lemma selectionZero_reducedCoefficient_small {N : Nat}
    (eps : selectionIndex 0 → Fin 4) (j : Fin 16)
    (hne : selectionZeroReducedCoefficient (N := N) eps j ≠ 0) :
    selectionZeroReducedCoefficient (N := N) eps j = 1 ∨
      selectionZeroReducedCoefficient (N := N) eps j = -1 ∨
      selectionZeroReducedCoefficient (N := N) eps j = 2 ∨
      selectionZeroReducedCoefficient (N := N) eps j = -2 := by
  generalize ha : eps (selectionZeroBool, (0 : Fin 16)) = a
  generalize hb : eps (selectionZeroBool, j) = b
  fin_cases a <;> fin_cases b <;>
    by_cases hj : (j : Nat) < 8 <;>
    simp [selectionZeroReducedCoefficient, selectionZeroCoefficient,
      selectionDigit, selectionDigitInt, selectionIndexSign, ha, hb, hj]
      at hne ⊢
  all_goals (ring_nf at hne ⊢; simp_all)

private lemma selectionZero_mulLeft_range {N : Nat} [NeZero N]
    (h : ZMod N) :
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

private lemma selectionZero_mul_kernel_card {N : Nat} [NeZero N]
    (h : ZMod N) :
    Fintype.card {x : ZMod N // h * x = 0} = N.gcd h.val := by
  let f : ZMod N →+ ZMod N := AddMonoidHom.mulLeft h
  have hrange : Nat.card f.range = addOrderOf h := by
    rw [selectionZero_mulLeft_range h, Nat.card_zmultiples]
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
  have hker : Nat.card f.ker = N.gcd h.val :=
    Nat.eq_of_mul_eq_mul_right hquotpos (hprod.trans heq.symm)
  let e : {x : ZMod N // h * x = 0} ≃ f.ker :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun _ ↦ by rfl)
  calc
    Fintype.card {x : ZMod N // h * x = 0} = Fintype.card f.ker :=
      Fintype.card_congr e
    _ = N.gcd h.val := by
      simpa [Nat.card_eq_fintype_card] using hker

private lemma selectionZero_smallCoefficient_kernel_card_le_two {N : Nat}
    [NeZero N] (hN : 3 ≤ N) (c : ZMod N)
    (hc : c = 1 ∨ c = -1 ∨ c = 2 ∨ c = -2) :
    Fintype.card {x : ZMod N // c * x = 0} ≤ 2 := by
  rcases hc with rfl | rfl | rfl | rfl
  · have hcard : Fintype.card {x : ZMod N // (1 : ZMod N) * x = 0} ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      intro x y
      apply Subtype.ext
      simpa using x.2.trans y.2.symm
    omega
  · have hcard : Fintype.card {x : ZMod N // (-1 : ZMod N) * x = 0} ≤ 1 := by
      apply Fintype.card_le_one_iff.mpr
      intro x y
      apply Subtype.ext
      have hx : -x.1 = 0 := by simpa using x.2
      have hy : -y.1 = 0 := by simpa using y.2
      exact neg_injective (hx.trans hy.symm)
    omega
  · have hval : (2 : ZMod N).val = 2 := ZMod.val_natCast_of_lt
      (lt_of_lt_of_le (by norm_num : 2 < 3) hN)
    rw [selectionZero_mul_kernel_card, hval]
    exact Nat.gcd_le_right N (by norm_num)
  · let e : {x : ZMod N // (-2 : ZMod N) * x = 0} ≃
        {x : ZMod N // (2 : ZMod N) * x = 0} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦ by simp [neg_mul])
    rw [Fintype.card_congr e]
    have hval : (2 : ZMod N).val = 2 := ZMod.val_natCast_of_lt
      (lt_of_lt_of_le (by norm_num : 2 < 3) hN)
    rw [selectionZero_mul_kernel_card, hval]
    exact Nat.gcd_le_right N (by norm_num)

private def selectionZeroDoubleExceptEquiv (i j : Fin 16) (hij : i ≠ j) :
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
  left_inv _ := rfl
  right_inv _ := rfl

private lemma selectionZero_doubleExcept_card (i j : Fin 16) (hij : i ≠ j) :
    Fintype.card {q : Fin 16 // q ≠ i ∧ q ≠ j} = 14 := by
  rw [Fintype.card_congr (selectionZeroDoubleExceptEquiv i j hij)]
  rw [Fintype.card_subtype_compl]
  simp

private lemma selectionZero_sum_mul_sub_eq_two {N : Nat}
    (f x y : Fin 16 → ZMod N) (i j : Fin 16) (hij : i ≠ j)
    (hoff : ∀ q, q ≠ i → q ≠ j → x q = y q) :
    (∑ q, f q * x q) - (∑ q, f q * y q) =
      f i * (x i - y i) + f j * (x j - y j) := by
  classical
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ q, (f q * x q - f q * y q)) =
        ∑ q, f q * (x q - y q) := by
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = ∑ q ∈ ({i, j} : Finset (Fin 16)), f q * (x q - y q) := by
      symm
      apply Finset.sum_subset (by simp)
      intro q _ hqpair
      have hqi : q ≠ i := by
        intro h
        subst q
        exact hqpair (by simp)
      have hqj : q ≠ j := by
        intro h
        subst q
        exact hqpair (by simp)
      rw [hoff q hqi hqj, sub_self, mul_zero]
    _ = f i * (x i - y i) + f j * (x j - y j) := by simp [hij]

private abbrev SelectionZeroRelationSolutions {N : Nat} [NeZero N]
    (eps : selectionIndex 0 → Fin 4) :=
  {R : GeneralArrangement N 0 8 //
    IsAdditiveTuple R.crossSection ∧
      ∑ j, selectionZeroCoefficient eps j * R.crossSection j = 0}

private noncomputable instance selectionZeroRelationSolutionsFintype
    {N : Nat} [NeZero N] (eps : selectionIndex 0 → Fin 4) :
    Fintype (SelectionZeroRelationSolutions (N := N) eps) := by
  letI : Finite (SelectionZeroRelationSolutions (N := N) eps) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

private abbrev SelectionZeroRelationBase (N : Nat) (j : Fin 16) :=
  {q : Fin 16 // q ≠ 0 ∧ q ≠ j} → ZMod N

private def selectionZeroRelationProjection {N : Nat} [NeZero N]
    (eps : selectionIndex 0 → Fin 4) (j : Fin 16) :
    SelectionZeroRelationSolutions (N := N) eps →
      SelectionZeroRelationBase N j :=
  fun R q ↦ R.1.crossSection q

private lemma selectionZero_card_le_of_fiber_le {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] (f : A → B) (m : Nat)
    (h : ∀ b, Fintype.card {a : A // f a = b} ≤ m) :
    Fintype.card A ≤ Fintype.card B * m := by
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv f), Fintype.card_sigma]
  calc
    (∑ b : B, Fintype.card {a : A // f a = b}) ≤ ∑ _ : B, m :=
      Finset.sum_le_sum fun b _ ↦ h b
    _ = Fintype.card B * m := by simp

private lemma selectionZeroRelationSolutions_card_le {N : Nat} [NeZero N]
    (hN : 3 ≤ N) (eps : selectionIndex 0 → Fin 4)
    (hnoncanonical : selectionZeroNoncanonical (N := N) eps) :
    Fintype.card (SelectionZeroRelationSolutions (N := N) eps) ≤
      2 * N ^ 14 := by
  classical
  obtain ⟨j, hj0, hcne⟩ :=
    selectionZero_exists_reducedCoefficient eps hnoncanonical
  let c := selectionZeroReducedCoefficient (N := N) eps j
  have hcsmall := selectionZero_reducedCoefficient_small eps j hcne
  let proj := selectionZeroRelationProjection (N := N) eps j
  have hfiber : ∀ b : SelectionZeroRelationBase N j,
      Fintype.card
        {R : SelectionZeroRelationSolutions (N := N) eps // proj R = b} ≤ 2 := by
    intro b
    by_cases hex : Nonempty
        {R : SelectionZeroRelationSolutions (N := N) eps // proj R = b}
    · let R₀ := Classical.choice hex
      let enc :
          {R : SelectionZeroRelationSolutions (N := N) eps // proj R = b} →
            {v : ZMod N // c * v = 0} := fun R ↦ by
        let A := R.1.1
        let A₀ := R₀.1.1
        have hproj : proj R.1 = proj R₀.1 := R.2.trans R₀.2.symm
        have hoff : ∀ q : Fin 16, q ≠ 0 → q ≠ j →
            A.crossSection q = A₀.crossSection q := by
          intro q hq0 hqj
          exact congrFun hproj ⟨q, hq0, hqj⟩
        have haddDiff :
            selectionIndexSign (N := N) 0 *
                (A.crossSection 0 - A₀.crossSection 0) +
              selectionIndexSign (N := N) j *
                (A.crossSection j - A₀.crossSection j) = 0 := by
          rw [← selectionZero_sum_mul_sub_eq_two selectionIndexSign
            A.crossSection A₀.crossSection 0 j hj0.symm hoff]
          have hA := (selection_additive_iff A.crossSection).mp R.1.2.1
          have hA₀ := (selection_additive_iff A₀.crossSection).mp R₀.1.2.1
          rw [hA, hA₀, sub_self]
        have hrelDiff :
            selectionZeroCoefficient eps 0 *
                (A.crossSection 0 - A₀.crossSection 0) +
              selectionZeroCoefficient eps j *
                (A.crossSection j - A₀.crossSection j) = 0 := by
          rw [← selectionZero_sum_mul_sub_eq_two
            (selectionZeroCoefficient eps) A.crossSection A₀.crossSection
              0 j hj0.symm hoff]
          rw [R.1.2.2, R₀.1.2.2, sub_self]
        refine ⟨A.crossSection j - A₀.crossSection j, ?_⟩
        dsimp only [c]
        unfold selectionZeroReducedCoefficient
        have h0lt : ((0 : Fin 16) : Nat) < 8 := by norm_num
        by_cases hjlt : (j : Nat) < 8
        · simp only [selectionIndexSign, if_pos h0lt, if_pos hjlt, one_mul]
            at haddDiff ⊢
          linear_combination hrelDiff -
            selectionZeroCoefficient eps 0 * haddDiff
        · simp only [selectionIndexSign, if_pos h0lt, if_neg hjlt, one_mul,
            mul_neg, mul_one, neg_mul] at haddDiff ⊢
          linear_combination hrelDiff -
            selectionZeroCoefficient eps 0 * haddDiff
      have henc : Function.Injective enc := by
        intro R S hRS
        have hproj : proj R.1 = proj S.1 := R.2.trans S.2.symm
        have hoff : ∀ q : Fin 16, q ≠ 0 → q ≠ j →
            R.1.1.crossSection q = S.1.1.crossSection q := by
          intro q hq0 hqj
          exact congrFun hproj ⟨q, hq0, hqj⟩
        have hj : R.1.1.crossSection j = S.1.1.crossSection j := by
          have hval := congrArg Subtype.val hRS
          dsimp only [enc] at hval
          exact sub_left_injective hval
        have haddDiff :
            selectionIndexSign (N := N) 0 *
                (R.1.1.crossSection 0 - S.1.1.crossSection 0) +
              selectionIndexSign (N := N) j *
                (R.1.1.crossSection j - S.1.1.crossSection j) = 0 := by
          rw [← selectionZero_sum_mul_sub_eq_two selectionIndexSign
            R.1.1.crossSection S.1.1.crossSection 0 j hj0.symm hoff]
          have hR := (selection_additive_iff R.1.1.crossSection).mp R.1.2.1
          have hS := (selection_additive_iff S.1.1.crossSection).mp S.1.2.1
          rw [hR, hS, sub_self]
        have hzero : R.1.1.crossSection 0 = S.1.1.crossSection 0 := by
          rw [hj, sub_self, mul_zero, add_zero] at haddDiff
          simpa [selectionIndexSign, sub_eq_zero] using haddDiff
        have hcross : R.1.1.crossSection = S.1.1.crossSection := by
          funext q
          by_cases hq0 : q = 0
          · subst q
            exact hzero
          by_cases hqj : q = j
          · subst q
            exact hj
          exact hoff q hq0 hqj
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (Subsingleton.elim _ _)
          (Prod.ext (Subsingleton.elim _ _) hcross)
      calc
        Fintype.card
            {R : SelectionZeroRelationSolutions (N := N) eps // proj R = b} ≤
            Fintype.card {v : ZMod N // c * v = 0} :=
          Fintype.card_le_of_injective enc henc
        _ ≤ 2 := selectionZero_smallCoefficient_kernel_card_le_two hN c hcsmall
    · haveI : IsEmpty
          {R : SelectionZeroRelationSolutions (N := N) eps // proj R = b} :=
        ⟨fun R ↦ hex ⟨R⟩⟩
      simp
  have htotal := selectionZero_card_le_of_fiber_le proj 2 hfiber
  have hbase : Fintype.card (SelectionZeroRelationBase N j) = N ^ 14 := by
    simp only [SelectionZeroRelationBase, Fintype.card_fun, ZMod.card]
    rw [selectionZero_doubleExcept_card 0 j hj0.symm]
  calc
    Fintype.card (SelectionZeroRelationSolutions (N := N) eps) ≤
        Fintype.card (SelectionZeroRelationBase N j) * 2 := htotal
    _ = 2 * N ^ 14 := by rw [hbase]; ring

private noncomputable def selectionZeroPatternFinset (N : Nat) :
    Finset (selectionIndex 0 → Fin 4) := by
  classical
  exact Finset.univ.filter (selectionZeroNoncanonical (N := N))

private noncomputable def selectionZeroRelationFinset (N : Nat) [NeZero N]
    (eps : selectionIndex 0 → Fin 4) : Finset (GeneralArrangement N 0 8) := by
  classical
  exact Finset.univ.filter fun R ↦
    IsAdditiveTuple R.crossSection ∧
      ∑ j, selectionZeroCoefficient eps j * R.crossSection j = 0

@[simp] private lemma mem_selectionZeroRelationFinset
    {N : Nat} [NeZero N] (eps : selectionIndex 0 → Fin 4)
    (R : GeneralArrangement N 0 8) :
    R ∈ selectionZeroRelationFinset N eps ↔
      IsAdditiveTuple R.crossSection ∧
        ∑ j, selectionZeroCoefficient eps j * R.crossSection j = 0 := by
  simp [selectionZeroRelationFinset]

private noncomputable def selectionZeroExceptionalFinset (N : Nat) [NeZero N] :
    Finset (GeneralArrangement N 0 8) := by
  classical
  exact (selectionZeroPatternFinset N).biUnion
    (selectionZeroRelationFinset N)

private lemma selectionZeroPatternFinset_card_le (N : Nat) :
    (selectionZeroPatternFinset N).card ≤ 4 ^ 16 := by
  classical
  calc
    (selectionZeroPatternFinset N).card ≤
        (Finset.univ : Finset (selectionIndex 0 → Fin 4)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 4 ^ 16 := by
      simp [selectionIndex]

private lemma selectionZeroRelationFinset_card_le {N : Nat} [NeZero N]
    (hN : 3 ≤ N) (eps : selectionIndex 0 → Fin 4)
    (heps : eps ∈ selectionZeroPatternFinset N) :
    (selectionZeroRelationFinset N eps).card ≤ 2 * N ^ 14 := by
  classical
  have hnoncanonical : selectionZeroNoncanonical (N := N) eps := by
    simpa [selectionZeroPatternFinset] using heps
  calc
    (selectionZeroRelationFinset N eps).card =
        Fintype.card (SelectionZeroRelationSolutions (N := N) eps) := by
      unfold selectionZeroRelationFinset
      rw [Finset.filter_congr_decidable]
      exact (Fintype.card_subtype _).symm
    _ ≤ 2 * N ^ 14 :=
      selectionZeroRelationSolutions_card_le hN eps hnoncanonical

private lemma selectionZeroExceptionalFinset_card_le {N : Nat} [NeZero N]
    (hN : 3 ≤ N) :
    (selectionZeroExceptionalFinset N).card ≤ (2 * 4 ^ 16) * N ^ 14 := by
  classical
  calc
    (selectionZeroExceptionalFinset N).card ≤
        ∑ eps ∈ selectionZeroPatternFinset N,
          (selectionZeroRelationFinset N eps).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _eps ∈ selectionZeroPatternFinset N, 2 * N ^ 14 := by
      apply Finset.sum_le_sum
      intro eps heps
      exact selectionZeroRelationFinset_card_le hN eps heps
    _ = (selectionZeroPatternFinset N).card * (2 * N ^ 14) := by simp
    _ ≤ (4 ^ 16) * (2 * N ^ 14) := by
      exact Nat.mul_le_mul_right _ (selectionZeroPatternFinset_card_le N)
    _ = (2 * 4 ^ 16) * N ^ 14 := by ring

private def selectionZeroTernaryDigit (a : Int) : Fin 4 :=
  if a = -1 then 3 else if a = 0 then 0 else 2

private lemma selectionZeroTernaryDigit_spec (a : Int)
    (ha : a = -1 ∨ a = 0 ∨ a = 1) :
    selectionDigitInt (selectionZeroTernaryDigit a) = a := by
  rcases ha with rfl | rfl | rfl <;>
    simp [selectionZeroTernaryDigit, selectionDigitInt]

private def selectionZeroEncodeEta
    (eta : (Fin 0 → Bool) → Fin 16 → Int) : selectionIndex 0 → Fin 4 :=
  fun z ↦ selectionZeroTernaryDigit (eta z.1 z.2)

private lemma selectionZeroEncodeEta_spec
    (eta : (Fin 0 → Bool) → Fin 16 → Int)
    (heta : IsTernaryCoefficient
      (fun z : (Fin 0 → Bool) × Fin 16 ↦ eta z.1 z.2)) :
    selectionEta (selectionZeroEncodeEta eta) = eta := by
  funext e j
  exact selectionZeroTernaryDigit_spec (eta e j) (heta (e, j))

private lemma selectionZero_moment_univ {N : Nat} [NeZero N]
    (R : GeneralArrangement N 0 8)
    (eta : (Fin 0 → Bool) → Fin 16 → Int) :
    arrangementMoment R eta Finset.univ =
      ∑ j, (eta selectionZeroBool j : ZMod N) * R.crossSection j := by
  classical
  unfold arrangementMoment
  rw [Finset.sum_eq_single selectionZeroBool]
  · apply Finset.sum_congr rfl
    intro j _
    rw [selection_vertex_product_split]
    simp
  · intro e _ he
    exact (he (Subsingleton.elim _ _)).elim
  · intro he
    exact (he (Finset.mem_univ selectionZeroBool)).elim

private structure SelectionZeroDegenerateData {N : Nat} [NeZero N]
    (R : GeneralArrangement N 0 8) where
  additive : IsAdditiveTuple R.crossSection
  coefficient : (Fin 0 → Bool) → Fin 16 → Int
  ternary : IsTernaryCoefficient
    (fun z : (Fin 0 → Bool) × Fin 16 ↦ coefficient z.1 z.2)
  notMultiple : ¬ IsModularMultiple
    (fun z : (Fin 0 → Bool) × Fin 16 ↦ coefficient z.1 z.2)
    (fun z ↦ arrangementParityCoefficient (N := N) (d := 8) z.1 z.2)
  moment : ∀ A : Finset (Fin 1), arrangementMoment R coefficient A = 0

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
@[simp] private lemma mem_selectionZeroDegenerateFinset_iff_data
    {N : Nat} [NeZero N] (R : GeneralArrangement N 0 8) :
    R ∈ selectionDegenerateFinset N 0 ↔
      Nonempty (SelectionZeroDegenerateData R) := by
  rw [mem_selectionDegenerateFinset]
  constructor
  · rintro ⟨hadditive, eta, heta, hnotmultiple, hmoment⟩
    exact ⟨{
      additive := hadditive
      coefficient := eta
      ternary := heta
      notMultiple := hnotmultiple
      moment := hmoment
    }⟩
  · rintro ⟨hRdata⟩
    exact ⟨hRdata.additive, hRdata.coefficient, hRdata.ternary,
      hRdata.notMultiple, hRdata.moment⟩

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
private lemma selectionZeroDegenerateData_noncanonical
    {N : Nat} [NeZero N] {R : GeneralArrangement N 0 8}
    (hRdata : SelectionZeroDegenerateData R) :
    selectionZeroNoncanonical (N := N)
      (selectionZeroEncodeEta hRdata.coefficient) := by
  let eta := hRdata.coefficient
  let eps := selectionZeroEncodeEta eta
  change selectionZeroNoncanonical (N := N) eps
  have hetaEq : selectionEta eps = eta :=
    selectionZeroEncodeEta_spec eta hRdata.ternary
  rintro ⟨q, hq⟩
  apply hRdata.notMultiple
  refine ⟨q, ?_⟩
  rintro ⟨e, j⟩
  have he : e = selectionZeroBool := Subsingleton.elim _ _
  rw [he]
  change (eta selectionZeroBool j : ZMod N) =
    q * arrangementParityCoefficient (N := N) (d := 8)
      selectionZeroBool j
  rw [← hetaEq]
  change selectionZeroCoefficient (N := N) eps j =
    q * arrangementParityCoefficient (N := N) (d := 8)
      selectionZeroBool j
  rw [selectionZero_parityCoefficient]
  exact hq j

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
private lemma selectionZeroDegenerateData_relation
    {N : Nat} [NeZero N] {R : GeneralArrangement N 0 8}
    (hRdata : SelectionZeroDegenerateData R) :
    (∑ j, selectionZeroCoefficient (N := N)
      (selectionZeroEncodeEta hRdata.coefficient) j *
        R.crossSection j) = 0 := by
  let eta := hRdata.coefficient
  let eps := selectionZeroEncodeEta eta
  change (∑ j, selectionZeroCoefficient (N := N) eps j *
    R.crossSection j) = 0
  have hetaEq : selectionEta eps = eta :=
    selectionZeroEncodeEta_spec eta hRdata.ternary
  have h := hRdata.moment Finset.univ
  rw [selectionZero_moment_univ] at h
  change (∑ j, ((selectionEta eps selectionZeroBool j : Int) : ZMod N) *
    R.crossSection j) = 0
  rw [hetaEq]
  exact h

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
private lemma selectionZeroDegenerateData_mem_exceptional
    {N : Nat} [NeZero N] {R : GeneralArrangement N 0 8}
    (hRdata : SelectionZeroDegenerateData R) :
    R ∈ selectionZeroExceptionalFinset N := by
  classical
  let eps := selectionZeroEncodeEta hRdata.coefficient
  have hnoncanonical : selectionZeroNoncanonical (N := N) eps := by
    simpa only [eps] using
      selectionZeroDegenerateData_noncanonical (N := N) (R := R) hRdata
  have hrelation :
      (∑ j, selectionZeroCoefficient (N := N) eps j *
        R.crossSection j) = 0 := by
    simpa only [eps] using
      selectionZeroDegenerateData_relation (N := N) (R := R) hRdata
  unfold selectionZeroExceptionalFinset
  rw [Finset.mem_biUnion]
  refine ⟨eps, ?_, ?_⟩
  · unfold selectionZeroPatternFinset
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnoncanonical⟩
  · rw [mem_selectionZeroRelationFinset]
    exact ⟨hRdata.additive, hrelation⟩

set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 1000000 in
private lemma selectionZeroDegenerate_subset_exceptional {N : Nat} [NeZero N] :
    selectionDegenerateFinset N 0 ⊆ selectionZeroExceptionalFinset N := by
  intro (R : GeneralArrangement N 0 8) hR
  rw [mem_selectionZeroDegenerateFinset_iff_data] at hR
  obtain ⟨hRdata⟩ := hR
  exact selectionZeroDegenerateData_mem_exceptional
    (N := N) (R := R) hRdata

private lemma selectionZeroDegenerateCount_le {N : Nat} [NeZero N]
    (hN : 3 ≤ N) :
    degenerateGeneralArrangementCount (N := N) (k := 0) 8 ≤
      (2 * 4 ^ 16) * N ^ 14 := by
  rw [← selectionDegenerateFinset_card N 0]
  exact (Finset.card_le_card selectionZeroDegenerate_subset_exceptional).trans
    (selectionZeroExceptionalFinset_card_le hN)

private lemma selectionDegenerate_real_small_zero (scale delta : Real)
    (hscale : 0 < scale) (hdelta : 0 < delta) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
      (degenerateGeneralArrangementCount (N := N) (k := 0) 8 : Real) ≤
        delta * scale * (N : Real) ^ 15 := by
  let C : Real := 2 * 4 ^ 16
  let D : Real := delta * scale
  have hD : 0 < D := mul_pos hdelta hscale
  obtain ⟨Nbase : Nat, hNbase⟩ := exists_nat_ge (C / D)
  refine ⟨max 3 Nbase, ?_⟩
  intro N _ hN
  have hN3 : 3 ≤ N := (le_max_left 3 Nbase).trans hN
  have hNbase' : Nbase ≤ N := (le_max_right 3 Nbase).trans hN
  have hNbaseReal : (Nbase : Real) ≤ N := by exact_mod_cast hNbase'
  have hratio : C / D ≤ (N : Real) := hNbase.trans hNbaseReal
  have hC : C ≤ D * (N : Real) := by
    simpa [mul_comm] using (div_le_iff₀ hD).mp hratio
  have hdegNat := selectionZeroDegenerateCount_le hN3
  have hdeg :
      (degenerateGeneralArrangementCount (N := N) (k := 0) 8 : Real) ≤
        C * (N : Real) ^ 14 := by
    simpa only [C, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using
      (show (degenerateGeneralArrangementCount (N := N) (k := 0) 8 : Real) ≤
          (((2 * 4 ^ 16) * N ^ 14 : Nat) : Real) by exact_mod_cast hdegNat)
  calc
    (degenerateGeneralArrangementCount (N := N) (k := 0) 8 : Real) ≤
        C * (N : Real) ^ 14 := hdeg
    _ ≤ (D * (N : Real)) * (N : Real) ^ 14 := by
      exact mul_le_mul_of_nonneg_right hC (pow_nonneg (Nat.cast_nonneg N) _)
    _ = delta * scale * (N : Real) ^ 15 := by
      dsimp only [D]
      rw [show 15 = 14 + 1 by omega, pow_succ]
      ring

private lemma selectionDegenerate_real_small (k : Nat) (scale delta : Real)
    (hk : 1 ≤ k) (hscale : 0 < scale) (hdelta : 0 < delta) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → N.Prime → Odd N →
      (degenerateGeneralArrangementCount (N := N) (k := k) 8 : Real) ≤
        delta * scale * (N : Real) ^ (17 * k + 15) := by
  let C : Real := (3 : Real) ^ (16 * 2 ^ k) * k
  let D : Real := delta * scale
  have hD : 0 < D := mul_pos hdelta hscale
  obtain ⟨N0 : Nat, hN0⟩ := exists_nat_ge (C / D)
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd
  have hN0Real : (N0 : Real) ≤ N := by exact_mod_cast hN
  have hratio : C / D ≤ (N : Real) := hN0.trans hN0Real
  have hC : C ≤ D * (N : Real) := by
    simpa [mul_comm] using (div_le_iff₀ hD).mp hratio
  have hdeg := lemma_15_4_holds N k 8 hprime hodd hk (by norm_num)
  have hdeg' :
      (degenerateGeneralArrangementCount (N := N) (k := k) 8 : Real) ≤
        C * (N : Real) ^ (17 * k + 14) := by
    simpa only [C, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_pow,
      show 2 * 8 = 16 by norm_num,
      show (2 * 8 + 1) * k + 2 * 8 - 2 = 17 * k + 14 by omega]
      using hdeg
  calc
    (degenerateGeneralArrangementCount (N := N) (k := k) 8 : Real) ≤
        C * (N : Real) ^ (17 * k + 14) := hdeg'
    _ ≤ (D * (N : Real)) * (N : Real) ^ (17 * k + 14) := by
      exact mul_le_mul_of_nonneg_right hC (pow_nonneg (Nat.cast_nonneg N) _)
    _ = delta * scale * (N : Real) ^ (17 * k + 15) := by
      dsimp only [D]
      rw [show 17 * k + 15 = (17 * k + 14) + 1 by omega, pow_succ]
      ring

/-! ## The scale-invariant selection estimate -/

set_option maxHeartbeats 3000000 in
private theorem selection_scale_estimate_of_exceptional_bound
    (valid : Nat → Prop) (k : Nat) (alpha scale eta : Real)
    (halpha : 0 < alpha) (hscale : 0 < scale)
    (heta : 0 < eta) (heta_one : eta ≤ 1)
    (hdegenerateSmall : ∀ delta : Real, 0 < delta →
      ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → valid N →
        (degenerateGeneralArrangementCount (N := N) (k := k) 8 : Real) ≤
          delta * scale * (N : Real) ^ (17 * k + 15)) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → valid N →
      ∀ (B : Finset (Point N (k + 1)))
          (phi : Point N (k + 1) → ZMod N),
        (generalArrangementCount 8 B : Real) ≤
            scale * (N : Real) ^ (17 * k + 15) →
        alpha * scale * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ arrangementSelectionExponent k * scale *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  by_cases halpha_one : alpha ≤ 1
  · obtain ⟨m : Nat, hmargin₀⟩ :=
      selection_exists_stage_margin k alpha eta halpha heta halpha_one heta_one
    let V : Nat := 2 ^ (k + 4)
    let K : Nat := 2 ^ (V - 1)
    let r : Nat := K * m
    let qb : Real := ((2 : Real)⁻¹) ^ V
    let amp : Real := 1 + 2 * ((2 : Real)⁻¹) ^ V
    let qg : Real := qb * amp
    let target : Real := selectionTarget k alpha eta
    let margin : Real :=
      qb ^ r * (alpha * eta * amp ^ r - 1) - eta * target
    have hmargin : 0 < margin := hmargin₀
    obtain ⟨Nsmall : Nat, hsmall⟩ :=
      hdegenerateSmall (margin / 2) (by positivity)
    refine ⟨max 3 Nsmall, ?_⟩
    intro N _ hN hvalid B phi harrangementUpper hrespected
    have hN3 : 3 ≤ N := (le_max_left 3 Nsmall).trans hN
    have hNsmall : Nsmall ≤ N := (le_max_right 3 Nsmall).trans hN
    let M : Real := scale * (N : Real) ^ (17 * k + 15)
    let exceptional : Real :=
      degenerateGeneralArrangementCount (N := N) (k := k) 8
    have hNpos : 0 < (N : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hMpos : 0 < M := by
      dsimp [M]
      positivity
    have hexceptional0 : 0 ≤ exceptional := by positivity
    have hexceptional : exceptional ≤ (margin / 2) * M := by
      simpa only [exceptional, M, mul_assoc] using
        hsmall N hNsmall hvalid
    have hgoodCardNat := selectionGoodNondegenerate_card_lower B phi
    have hgoodCard :
        (respectedGeneralArrangementCount 8 B phi : Real) ≤
          ((selectionGoodNondegenerate B phi).card : Real) + exceptional := by
      rw [← selectionGoodArrangements_card]
      dsimp [exceptional]
      exact_mod_cast hgoodCardNat
    have hgoodLower :
        alpha * M - exceptional ≤
          ((selectionGoodNondegenerate B phi).card : Real) := by
      linarith only [hrespected, hgoodCard]
    have hbadCardNat := selectionBadNondegenerate_card_upper B phi
    have hbadCard :
        ((selectionBadNondegenerate B phi).card : Real) ≤
          (selectionArrangements B).card := by
      exact_mod_cast hbadCardNat
    have hbadUpper :
        ((selectionBadNondegenerate B phi).card : Real) ≤ M := by
      rw [selectionArrangements_card] at hbadCard
      exact hbadCard.trans harrangementUpper
    have hV : 1 ≤ V := by
      dsimp only [V]
      exact Nat.one_le_pow _ 2 (by norm_num)
    have hqb0 : 0 ≤ qb := by
      dsimp [qb]
      positivity
    have hqbHalf : qb ≤ (2 : Real)⁻¹ := by
      dsimp only [qb]
      calc
        ((2 : Real)⁻¹) ^ V ≤ ((2 : Real)⁻¹) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hV
        _ = (2 : Real)⁻¹ := pow_one _
    have hamp0 : 0 ≤ amp := by
      dsimp [amp]
      positivity
    have hamp2 : amp ≤ 2 := by
      dsimp only [amp, qb] at hqbHalf ⊢
      linarith
    have hqg0 : 0 ≤ qg := by
      exact mul_nonneg hqb0 hamp0
    have hqg1 : qg ≤ 1 := by
      dsimp only [qg]
      calc
        qb * amp ≤ (2 : Real)⁻¹ * 2 :=
          mul_le_mul hqbHalf hamp2 hamp0 (by norm_num)
        _ = 1 := by norm_num
    have hqgPow0 : 0 ≤ qg ^ r := pow_nonneg hqg0 r
    have hqgPow1 : qg ^ r ≤ 1 := pow_le_one₀ hqg0 hqg1
    have hqbPow0 : 0 ≤ qb ^ r := pow_nonneg hqb0 r
    have hgoodScaled :
        eta * qg ^ r * (alpha * M - exceptional) ≤
          eta * qg ^ r * (selectionGoodNondegenerate B phi).card :=
      mul_le_mul_of_nonneg_left hgoodLower
        (mul_nonneg heta.le hqgPow0)
    have hbadScaled :
        qb ^ r * (selectionBadNondegenerate B phi).card ≤ qb ^ r * M :=
      mul_le_mul_of_nonneg_left hbadUpper hqbPow0
    have havgLower :
        qb ^ r * (alpha * eta * amp ^ r - 1) * M -
            eta * qg ^ r * exceptional ≤
          eta * qg ^ r * (selectionGoodNondegenerate B phi).card -
            qb ^ r * (selectionBadNondegenerate B phi).card := by
      calc
        qb ^ r * (alpha * eta * amp ^ r - 1) * M -
              eta * qg ^ r * exceptional =
            eta * qg ^ r * (alpha * M - exceptional) - qb ^ r * M := by
          dsimp [qg]
          rw [mul_pow]
          ring
        _ ≤ eta * qg ^ r * (selectionGoodNondegenerate B phi).card -
              qb ^ r * (selectionBadNondegenerate B phi).card :=
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
          eta * qg ^ r * (selectionGoodNondegenerate B phi).card -
            qb ^ r * (selectionBadNondegenerate B phi).card := by
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
        _ ≤ eta * qg ^ r * (selectionGoodNondegenerate B phi).card -
              qb ^ r * (selectionBadNondegenerate B phi).card := havgLower
    have hphaseExpected :
        eta * target * M + exceptional ≤
          𝔼 C : Fin r → SelectionPhase N k, (
            eta * (∑ R ∈ selectionGoodNondegenerate B phi,
              ∏ z : selectionIndex k,
                multiStageSelectionWeight C phi (selectionVertex R z)) -
            ∑ R ∈ selectionBadNondegenerate B phi,
              ∏ z : selectionIndex k,
                multiStageSelectionWeight C phi
                  (selectionVertex R z)) := by
      rw [selection_phase_score_average hN3]
      exact htargetToAverage
    obtain ⟨C, hCmem, hC⟩ := Finset.exists_le_of_le_expect
      (Finset.univ_nonempty : (Finset.univ :
        Finset (Fin r → SelectionPhase N k)).Nonempty) hphaseExpected
    have hcarrierLower :=
      selection_carrier_score_lower (by omega) eta heta.le B phi C
    have hcarrierAverage :
        eta * target * M ≤
          eta * (∑ R ∈ selectionGoodArrangements B phi,
            ∏ z ∈ selectionCarrier R,
              multiStageSelectionWeight C phi z) -
            ∑ R ∈ selectionBadArrangements B phi,
              ∏ z ∈ selectionCarrier R,
                multiStageSelectionWeight C phi z := by
      linarith only [hC, hcarrierLower]
    have hgoodCarrier : ∀ R ∈ selectionGoodArrangements B phi,
        selectionCarrier R ⊆ B := by
      intro R hR
      have hdata : R ∈ selectionArrangements B ∧ R.IsRespected phi := by
        simpa [selectionGoodArrangements] using hR
      have hIsIn : R.IsIn B := by
        simpa [selectionArrangements] using hdata.1
      exact selectionCarrier_subset B R hIsIn
    have hbadCarrier : ∀ R ∈ selectionBadArrangements B phi,
        selectionCarrier R ⊆ B := by
      intro R hR
      have hmem := (Finset.mem_sdiff.mp hR).1
      have hIsIn : R.IsIn B := by simpa [selectionArrangements] using hmem
      exact selectionCarrier_subset B R hIsIn
    obtain ⟨B', hB'B, hscore⟩ := exists_subset_count_score
      B (multiStageSelectionWeight C phi)
      (fun z hz ↦ multiStageSelectionWeight_nonneg C phi z)
      (fun z hz ↦ multiStageSelectionWeight_le_one C phi z)
      (selectionGoodArrangements B phi)
      (selectionBadArrangements B phi) selectionCarrier
      hgoodCarrier hbadCarrier eta (eta * target * M) hcarrierAverage
    let goodCount :=
      ((selectionGoodArrangements B phi).filter fun R ↦
        selectionCarrier R ⊆ B').card
    let badCount :=
      ((selectionBadArrangements B phi).filter fun R ↦
        selectionCarrier R ⊆ B').card
    have hgoodCount :
        goodCount = respectedGeneralArrangementCount 8 B' phi := by
      exact selection_good_restrict_card B B' phi hB'B
    have htotalCount :
        goodCount + badCount = generalArrangementCount 8 B' := by
      exact selection_good_bad_restrict_card B B' phi hB'B
    have htotalCountReal :
        (goodCount : Real) + badCount = generalArrangementCount 8 B' := by
      exact_mod_cast htotalCount
    have htargetPos : 0 < target := by
      dsimp only [target]
      rw [selectionTarget_eq]
      exact pow_pos (div_pos (mul_pos halpha heta) (by norm_num)) _
    have harrangementLower :
        target * M ≤ (generalArrangementCount 8 B' : Real) := by
      change eta * target * M ≤ eta * (goodCount : Real) - badCount at hscore
      have hbad0 : 0 ≤ (badCount : Real) := Nat.cast_nonneg _
      have hgoodLeTotal :
          (goodCount : Real) ≤ generalArrangementCount 8 B' := by
        calc
          (goodCount : Real) ≤ (goodCount : Real) + badCount :=
            le_add_of_nonneg_right hbad0
          _ = generalArrangementCount 8 B' := htotalCountReal
      have hscoreUpper :
          eta * (goodCount : Real) - badCount ≤
            eta * (generalArrangementCount 8 B' : Real) := by
        calc
          eta * (goodCount : Real) - badCount ≤ eta * goodCount :=
            sub_le_self _ hbad0
          _ ≤ eta * (generalArrangementCount 8 B' : Real) :=
            mul_le_mul_of_nonneg_left hgoodLeTotal heta.le
      have h := hscore.trans hscoreUpper
      apply (mul_le_mul_iff_of_pos_left heta).mp
      calc
        eta * (target * M) = eta * target * M := by ring
        _ ≤ eta * (generalArrangementCount 8 B' : Real) := h
    have hdensity :
        (1 - eta) * (generalArrangementCount 8 B' : Real) ≤
          respectedGeneralArrangementCount 8 B' phi := by
      change eta * target * M ≤ eta * (goodCount : Real) - badCount at hscore
      have hpositive : 0 ≤ eta * target * M :=
        (mul_pos (mul_pos heta htargetPos) hMpos).le
      have hbad_le : (badCount : Real) ≤ eta * goodCount :=
        sub_nonneg.mp (hpositive.trans hscore)
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
        (1 - eta) * (generalArrangementCount 8 B' : Real) =
            (1 - eta) * (goodCount + badCount) := by rw [htotalCountReal]
        _ = (1 - eta) * goodCount + (1 - eta) * badCount := by ring
        _ ≤ (1 - eta) * goodCount + eta * goodCount := by
          simpa only [add_comm] using
            add_le_add_left (hbadScaled.trans hbad_le)
              ((1 - eta) * (goodCount : Real))
        _ = goodCount := by ring
    refine ⟨B', hB'B, ?_, hdensity⟩
    rw [← selectionTarget_eq]
    dsimp only [target, M] at harrangementLower
    simpa only [mul_assoc] using harrangementLower
  · refine ⟨1, ?_⟩
    intro N _ hN hvalid B phi harrangementUpper hrespected
    exfalso
    let M : Real := scale * (N : Real) ^ (17 * k + 15)
    have hNpos : 0 < (N : Real) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hMpos : 0 < M := by
      dsimp [M]
      positivity
    have hrespectedUpperNat := selection_respected_le_arrangement B phi
    have hrespectedUpper :
        (respectedGeneralArrangementCount 8 B phi : Real) ≤
          generalArrangementCount 8 B := by
      exact_mod_cast hrespectedUpperNat
    have halpha_gt : 1 < alpha := lt_of_not_ge halpha_one
    nlinarith

private theorem selection_scale_estimate
    (k : Nat) (alpha scale eta : Real) (hk : 1 ≤ k)
    (halpha : 0 < alpha) (hscale : 0 < scale)
    (heta : 0 < eta) (heta_one : eta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → N.Prime → Odd N →
      ∀ (B : Finset (Point N (k + 1)))
          (phi : Point N (k + 1) → ZMod N),
        (generalArrangementCount 8 B : Real) ≤
            scale * (N : Real) ^ (17 * k + 15) →
        alpha * scale * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ arrangementSelectionExponent k * scale *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  obtain ⟨N0, hN0⟩ := selection_scale_estimate_of_exceptional_bound
    (fun N ↦ N.Prime ∧ Odd N) k alpha scale eta halpha hscale heta heta_one
    (fun delta hdelta ↦ by
      obtain ⟨Nsmall, hsmall⟩ :=
        selectionDegenerate_real_small k scale delta hk hscale hdelta
      exact ⟨Nsmall, fun N _ hN hvalid ↦
        hsmall N hN hvalid.1 hvalid.2⟩)
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd
  exact hN0 N hN ⟨hprime, hodd⟩

set_option maxHeartbeats 1000000 in
/-- The height-zero specialization of the random restriction.  Unlike the
higher-dimensional form, it is valid over every sufficiently large cyclic
group: a second ternary relation has a coefficient in `{±1, ±2}`, whose
fibres have uniformly bounded size even when the modulus is composite. -/
theorem lemma_15_5_zero_dimensional_holds
    (alpha beta eta : Real) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (heta : 0 < eta) (heta_one : eta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
      ∀ (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N),
        (B.card : Real) = beta * N →
        alpha * beta ^ 15 * (N : Real) ^ 15 ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N 1), B' ⊆ B ∧
          (alpha * eta / 4) ^ ((2 : Nat) ^ 19) * beta ^ 15 *
              (N : Real) ^ 15 ≤ generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  obtain ⟨N0, hN0⟩ := selection_scale_estimate_of_exceptional_bound
    (fun _ ↦ True) 0 alpha (beta ^ 15) eta halpha (pow_pos hbeta _)
      heta heta_one
      (fun delta hdelta ↦ by
        obtain ⟨Nsmall, hsmall⟩ := selectionDegenerate_real_small_zero
          (beta ^ 15) delta (pow_pos hbeta _) hdelta
        refine ⟨Nsmall, ?_⟩
        intro N _ hN _
        simpa only [Nat.mul_zero, zero_add] using hsmall N hN)
  refine ⟨N0, ?_⟩
  intro N _ hN B phi hBcard hrespected
  have hBcard' : (B.card : Real) = beta * (N : Real) ^ (0 + 1) := by
    simpa using hBcard
  obtain ⟨B', hB'B, hlower, hdensity⟩ := hN0 N hN trivial B phi
    (selection_arrangement_real_upper beta B hBcard') hrespected
  refine ⟨B', hB'B, ?_, ?_⟩
  · have hE : arrangementSelectionExponent 0 = 2 ^ 19 := by
      norm_num [arrangementSelectionExponent]
    rw [hE] at hlower
    exact hlower
  · exact hdensity

/-- **Lemma 15.5.** Random restriction for higher-dimensional arrangements. -/
theorem lemma_15_5_holds : lemma_15_5 := by
  unfold lemma_15_5
  intro k alpha beta eta hk halpha hbeta heta heta_one
  obtain ⟨N0, hN0⟩ := selection_scale_estimate k alpha (beta ^ 15) eta hk
    halpha (pow_pos hbeta _) heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd B phi hBcard hrespected
  exact hN0 N hN hprime hodd B phi
    (selection_arrangement_real_upper beta B hBcard) hrespected

end LeanProofs.GowersSzemeredi
