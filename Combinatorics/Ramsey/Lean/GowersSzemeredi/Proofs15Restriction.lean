import GowersSzemeredi.Proofs12BernoulliSelection
import GowersSzemeredi.Proofs15DegenerateArrangements
import GowersSzemeredi.Proofs15SelectionMargin

/-!
# The random restriction for higher-dimensional arrangements

This file develops the proof of Lemma 15.5, whose assembled form
`lemma_15_5_holds` is in `Proofs15RestrictionSide`.  The proof uses the same
finite Riesz-product and Bernoulli averaging method as Lemma 12.5, with the
monomials in all `k + 1` coordinates as the phase features.  Degenerate
arrangements are the exceptional set controlled by Lemma 15.4.

The 76 declarations of this module that the final route does not use are in
`Proofs15RestrictionSide`. -/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Arrangements as finite hyperedges -/

abbrev selectionIndex (k : Nat) :=
  (Fin k → Bool) × Fin 16

def selectionVertex {N k : Nat} (R : GeneralArrangement N k 8)
    (z : selectionIndex k) : Point N (k + 1) :=
  R.vertex z.1 z.2

noncomputable def selectionCarrier {N k : Nat}
    (R : GeneralArrangement N k 8) : Finset (Point N (k + 1)) := by
  classical
  exact Finset.univ.image (selectionVertex R)

lemma selectionCarrier_subset {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (R : GeneralArrangement N k 8)
    (hR : R.IsIn B) : selectionCarrier R ⊆ B := by
  classical
  intro z hz
  rw [selectionCarrier, Finset.mem_image] at hz
  obtain ⟨i, -, rfl⟩ := hz
  exact hR.2 i.1 i.2

lemma selection_isIn_iff {N k : Nat} [NeZero N]
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

noncomputable def selectionArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) : Finset (GeneralArrangement N k 8) := by
  classical
  exact Finset.univ.filter fun R ↦ R.IsIn B

noncomputable def selectionGoodArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (selectionArrangements B).filter fun R ↦ R.IsRespected phi

noncomputable def selectionBadArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact selectionArrangements B \ selectionGoodArrangements B phi

lemma selectionArrangements_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :
    (selectionArrangements B).card = generalArrangementCount 8 B := by
  classical
  unfold selectionArrangements generalArrangementCount countWhere
  rw [Finset.filter_congr_decidable]

lemma selectionGoodArrangements_card {N k : Nat} [NeZero N]
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

lemma selection_respected_le_arrangement {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    respectedGeneralArrangementCount 8 B phi ≤ generalArrangementCount 8 B := by
  classical
  rw [← selectionGoodArrangements_card, ← selectionArrangements_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma selection_good_restrict_card {N k : Nat} [NeZero N]
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

lemma selection_good_bad_restrict_card {N k : Nat} [NeZero N]
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

def selectionIndexSign {N : Nat} (j : Fin 16) : ZMod N :=
  if (j : Nat) < 8 then 1 else -1

lemma selection_additive_iff {N : Nat} (x : Fin 16 → ZMod N) :
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

private abbrev SelectionArrangementCode {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :=
  (Fin 15 → {z : Point N (k + 1) // z ∈ B}) × Point N k × Point N k

lemma selection_arrangement_count_le_card_pow {N k : Nat} [NeZero N]
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
      have hdiff := rangeDeg_sum_mul_sub_eq_one a R.1.crossSection
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

/-- The arrangement upper bound in terms of the actual density, also used
for thresholds uniform over sets with a prescribed density lower bound. -/
lemma selection_arrangement_real_upper {N k : Nat} [NeZero N]
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

abbrev SelectionFeature (k : Nat) :=
  Option (Finset (Fin (k + 1)))

abbrev SelectionPhase (N k : Nat) :=
  SelectionFeature k → ZMod N

def selectionDigitInt (j : Fin 4) : Int :=
  ![0, 0, 1, -1] j

def selectionDigit {N : Nat} (j : Fin 4) : ZMod N :=
  (selectionDigitInt j : ZMod N)

lemma selection_index_card (k : Nat) :
    Fintype.card (selectionIndex k) = 2 ^ (k + 4) := by
  simp only [selectionIndex, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  rw [show 16 = 2 ^ 4 by norm_num, ← pow_add]

def selectionFeatureValue {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (F : SelectionFeature k)
    (z : Point N (k + 1)) : ZMod N :=
  match F with
  | none => phi z
  | some A => ∏ i ∈ A, z i

attribute [simp] exponential_add

attribute [simp] star_exponential

attribute [simp] exponential_zero

lemma selection_expect_pi_prod {I C : Type*} [Fintype I]
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

lemma selection_expect_phase {N k : Nat} [NeZero N]
    (rel : SelectionFeature k → ZMod N) :
    (𝔼 C : SelectionPhase N k,
      exponential (∑ F, C F * rel F)) =
      if ∀ F, rel F = 0 then 1 else 0 := by
  classical
  have hexp (C : SelectionPhase N k) :
      exponential (∑ F, C F * rel F) =
        ∏ F, exponential (C F * rel F) := by
    exact (fejer_prod_exponential (fun F ↦ C F * rel F)).symm
  simp_rw [hexp]
  rw [selection_expect_pi_prod
    (I := SelectionFeature k) (C := ZMod N)
    (f := fun F c ↦ exponential (c * rel F))]
  have hfactor (F : SelectionFeature k) :
      (𝔼 c : ZMod N, exponential (c * rel F)) =
        if rel F = 0 then 1 else 0 := by
    simpa only [mul_comm] using fejer_expect_exponential_mul (rel F)
  simp_rw [hfactor]
  by_cases hrel : ∀ F, rel F = 0
  · simp [hrel]
  · rw [if_neg hrel]
    push Not at hrel
    obtain ⟨F, hF⟩ := hrel
    apply Finset.prod_eq_zero (Finset.mem_univ F)
    rw [if_neg hF]

/-! ## The distinguished relation and nondegeneracy -/

abbrev selectionEta {k : Nat}
    (eps : selectionIndex k → Fin 4) :=
  fun e j ↦ selectionDigitInt (eps (e, j))

def selectionEtaZero {k : Nat} (e : Fin k → Bool) (j : Fin 16) : Int :=
  (if (j : Nat) < 8 then 1 else -1) * (-1 : Int) ^ boolWeight e

lemma selectionEtaZero_cast {N k : Nat} (e : Fin k → Bool)
    (j : Fin 16) :
    (selectionEtaZero e j : ZMod N) =
      arrangementParityCoefficient (N := N) (d := 8) e j := by
  by_cases hj : (j : Nat) < 8 <;>
    simp [selectionEtaZero, arrangementParityCoefficient, parityCharacter, hj]

lemma selectionEtaZero_cases {k : Nat} (e : Fin k → Bool)
    (j : Fin 16) : selectionEtaZero e j = 1 ∨ selectionEtaZero e j = -1 := by
  by_cases he : Even (boolWeight e)
  · have hp : (-1 : Int) ^ boolWeight e = 1 := he.neg_one_pow
    by_cases hj : (j : Nat) < 8 <;> simp [selectionEtaZero, hp, hj]
  · have hp : (-1 : Int) ^ boolWeight e = -1 :=
      (Nat.not_even_iff_odd.mp he).neg_one_pow
    by_cases hj : (j : Nat) < 8 <;> simp [selectionEtaZero, hp, hj]

lemma selection_parity_cube_sum_subset {N k : Nat} [NeZero N]
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
  simp_rw [parityCharacter_eq_prod, hprod, ← Finset.prod_mul_distrib]
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

lemma selection_vertex_product_split {N k : Nat}
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

lemma selectionEtaZero_moment {N k : Nat} [NeZero N]
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
          exact hfull (Finset.eq_univ_of_forall hno)
        obtain ⟨i, hi⟩ := hex
        have hP : P = 0 := by
          unfold P
          apply Finset.prod_eq_zero (Finset.mem_univ i)
          simp [hi]
        simp [hP]

lemma selection_third_index {k : Nat}
    (u v : selectionIndex k) :
    ∃ w : selectionIndex k, w ≠ u ∧ w ≠ v := by
  classical
  let e₀ : Fin k → Bool := fun _ ↦ false
  let z₀ : selectionIndex k := (e₀, (0 : Fin 16))
  let z₁ : selectionIndex k := (e₀, (1 : Fin 16))
  let z₂ : selectionIndex k := (e₀, (2 : Fin 16))
  by_cases h₀ : z₀ ≠ u ∧ z₀ ≠ v
  · exact ⟨z₀, h₀⟩
  by_cases h₁ : z₁ ≠ u ∧ z₁ ≠ v
  · exact ⟨z₁, h₁⟩
  refine ⟨z₂, ?_, ?_⟩ <;>
    push Not at h₀ h₁ <;> aesop

lemma selection_injective_of_nondegenerate {N k : Nat} [NeZero N]
    (hN : 2 ≤ N) (R : GeneralArrangement N k 8)
    (hnondegenerate : ¬ R.IsDegenerate) :
    Function.Injective (selectionVertex R) := by
  classical
  letI : Fact (1 < N) := ⟨by omega⟩
  intro u v huvVertex
  by_contra huv
  apply hnondegenerate
  have hvu : v ≠ u := by
    exact fun h => huv h.symm
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

lemma selectionCarrier_prod_of_nondegenerate {N k : Nat} [NeZero N]
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

noncomputable def selectionDegenerateFinset (N k : Nat) [NeZero N] :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact Finset.univ.filter fun R ↦
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerate

@[simp] private lemma mem_selectionDegenerateFinset {N k : Nat} [NeZero N]
    (R : GeneralArrangement N k 8) :
    R ∈ selectionDegenerateFinset N k ↔
      IsAdditiveTuple R.crossSection ∧ R.IsDegenerate := by
  simp [selectionDegenerateFinset]

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

def selectionZeroNoncanonical {N : Nat}
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
    rw [restriction_mul_kernel_card, hval]
    exact Nat.gcd_le_right N (by norm_num)
  · let e : {x : ZMod N // (-2 : ZMod N) * x = 0} ≃
        {x : ZMod N // (2 : ZMod N) * x = 0} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun x ↦ by simp [neg_mul])
    rw [Fintype.card_congr e]
    have hval : (2 : ZMod N).val = 2 := ZMod.val_natCast_of_lt
      (lt_of_lt_of_le (by norm_num : 2 < 3) hN)
    rw [restriction_mul_kernel_card, hval]
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
  have htotal := lemma154_card_le_of_fiber_le proj 2 hfiber
  have hbase : Fintype.card (SelectionZeroRelationBase N j) = N ^ 14 := by
    simp only [SelectionZeroRelationBase, Fintype.card_fun, ZMod.card]
    rw [selectionZero_doubleExcept_card 0 j hj0.symm]
  calc
    Fintype.card (SelectionZeroRelationSolutions (N := N) eps) ≤
        Fintype.card (SelectionZeroRelationBase N j) * 2 := htotal
    _ = 2 * N ^ 14 := by rw [hbase]; ring

noncomputable def selectionZeroPatternFinset (N : Nat) :
    Finset (selectionIndex 0 → Fin 4) := by
  classical
  exact Finset.univ.filter (selectionZeroNoncanonical (N := N))

noncomputable def selectionZeroRelationFinset (N : Nat) [NeZero N]
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

noncomputable def selectionZeroExceptionalFinset (N : Nat) [NeZero N] :
    Finset (GeneralArrangement N 0 8) := by
  classical
  exact (selectionZeroPatternFinset N).biUnion
    (selectionZeroRelationFinset N)

lemma selectionZeroRelationFinset_card_le {N : Nat} [NeZero N]
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
lemma selectionZeroDegenerate_subset_exceptional {N : Nat} [NeZero N] :
    selectionDegenerateFinset N 0 ⊆ selectionZeroExceptionalFinset N := by
  intro (R : GeneralArrangement N 0 8) hR
  rw [mem_selectionZeroDegenerateFinset_iff_data] at hR
  obtain ⟨hRdata⟩ := hR
  exact selectionZeroDegenerateData_mem_exceptional
    (N := N) (R := R) hRdata

end LeanProofs.GowersSzemeredi
