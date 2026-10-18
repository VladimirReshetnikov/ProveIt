import GowersSzemeredi.Proofs12BernoulliSelection
import GowersSzemeredi.Proofs00Basics
import GowersSzemeredi.Proofs15Walsh2
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Fin.Tuple.Finset

/-!
# The random restriction for higher-dimensional arrangements

This file develops the proof of Lemma 15.5, whose assembled form
`lemma_15_5_holds` is in `Proofs15RestrictionSide`.  The proof uses the same
finite Riesz-product and Bernoulli averaging method as Lemma 12.5, with the
monomials in all `k + 1` coordinates as the phase features.  Degenerate
arrangements are the exceptional set controlled by Lemma 15.4.

The 112 declarations of this module that the final route does not use are in
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
    (selectionArrangements B).card = generalArrangementCount 8 B := rfl

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
  have hsub : selectionGoodArrangements B phi ⊆ selectionArrangements B :=
    Finset.filter_subset _ _
  have hall : (selectionArrangements B).filter (fun R ↦ selectionCarrier R ⊆ B') =
      selectionArrangements B' := by
    ext R
    simp only [selectionArrangements, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun h ↦ (selection_isIn_iff B B' R h.1).mpr h.2, fun h ↦ ?_⟩
    have hRB : R.IsIn B := ⟨h.1, fun e j ↦ hB'B (h.2 e j)⟩
    exact ⟨hRB, (selection_isIn_iff B B' R hRB).mp h⟩
  unfold selectionBadArrangements
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.disjoint_sdiff),
    ← Finset.filter_union, Finset.union_sdiff_of_subset hsub, hall, selectionArrangements_card]

def selectionIndexSign {N : Nat} (j : Fin 16) : ZMod N :=
  if (j : Nat) < 8 then 1 else -1

lemma selection_additive_iff {N : Nat} (x : Fin 16 → ZMod N) :
    IsAdditiveTuple (k := 8) x ↔
      ∑ j, selectionIndexSign (N := N) j * x j = 0 := by
  classical
  let L := Finset.univ.filter fun j : Fin 16 ↦ (j : Nat) < 8
  let U := Finset.univ.filter fun j : Fin 16 ↦ 8 ≤ (j : Nat)
  have hcomp :
      (Finset.univ.filter fun j : Fin 16 ↦ ¬ (j : Nat) < 8) = U := rfl
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
  -- the vertices at `e = 0` of the first 15 blocks give their bases and cross-sections; the
  -- last cross-section follows from additivity
  let enc : source → SelectionArrangementCode B := fun R ↦
    ⟨fun j ↦ ⟨R.1.vertex efalse j.castSucc, R.2.2 efalse j.castSucc⟩,
      R.1.side, R.1.base (Fin.last 15)⟩
  have hinj : Function.Injective enc := by
    intro R S hRS
    simp only [enc, Prod.mk.injEq] at hRS
    obtain ⟨hverts, hside, hlast⟩ := hRS
    have hv (t : Fin 15) (i : Fin (k + 1)) :
        R.1.vertex efalse t.castSucc i = S.1.vertex efalse t.castSucc i :=
      congrFun (congrArg Subtype.val (congrFun hverts t)) i
    have hbase : R.1.base = S.1.base := funext fun j => Fin.lastCases hlast
      (fun t => funext fun i => by
        simpa [efalse, GeneralArrangement.vertex, GeneralArrangement.cube, AxisCube.vertex,
          AxisCube.base, AxisCube.side, appendCoordinate] using hv t i.castSucc) j
    have hcrossTail (j : Fin 16) (hj : j ≠ Fin.last 15) :
        R.1.crossSection j = S.1.crossSection j := by
      obtain ⟨t, rfl⟩ := Fin.exists_castSucc_eq.mpr hj
      simpa [efalse, GeneralArrangement.vertex, appendCoordinate] using hv t (Fin.last k)
    have hcross : R.1.crossSection = S.1.crossSection := by
      funext j
      rcases eq_or_ne j (Fin.last 15) with rfl | hj
      · have h := rangeDeg_sum_mul_sub_eq_one selectionIndexSign _ _ _ hcrossTail
        rw [(selection_additive_iff _).mp R.2.1, (selection_additive_iff _).mp S.2.1, sub_self,
          show selectionIndexSign (N := N) (Fin.last 15) = -1 by simp [selectionIndexSign]] at h
        linear_combination h
      · exact hcrossTail j hj
    exact Subtype.ext (Prod.ext hside (Prod.ext hbase hcross))
  have hsourceCard : Fintype.card source = generalArrangementCount 8 B := by
    unfold source generalArrangementCount countWhere
    rw [Finset.filter_congr_decidable]
    exact Fintype.card_subtype _
  rw [← hsourceCard]
  refine (Fintype.card_le_of_injective enc hinj).trans_eq ?_
  simp only [SelectionArrangementCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_coe, Point, ZMod.card]
  ring

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
  simp_rw [← fejer_prod_exponential]
  rw [selection_expect_pi_prod (I := SelectionFeature k) (C := ZMod N)
    (f := fun F c ↦ exponential (c * rel F))]
  simp_rw [mul_comm _ (rel _), fejer_expect_exponential_mul]
  by_cases hrel : ∀ F, rel F = 0
  · simp [hrel]
  · obtain ⟨F, hF⟩ := not_forall.mp hrel
    rw [if_neg hrel]
    exact Finset.prod_eq_zero (Finset.mem_univ F) (if_neg hF)

/-! ## The distinguished relation and nondegeneracy -/

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
          if i ∈ A then (y i + if e i then h i else 0) else 1 := by norm_num
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
    _ = ∏ i : Fin k, if i ∈ A then -h i else 0 := by norm_num

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
        ∏ i : Fin (k + 1), if i ∈ A then R.vertex e j i else 1 := by norm_num
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
  have heta (e : Fin k → Bool) (j : Fin 16) :
      (selectionEtaZero e j : ZMod N) =
        selectionIndexSign (N := N) j * parityCharacter (N := N) e := by
    rw [selectionEtaZero_cast]
    by_cases hj : (j : Nat) < 8 <;>
      simp [arrangementParityCoefficient, selectionIndexSign, hj]
  -- block `j` contributes `sign j * (cross-section factor) * P`, where the parity sum `P` does
  -- not depend on `j` (`selection_parity_cube_sum_subset`); the signs then sum to zero against
  -- the additive cross-section, or against `1` when the last coordinate is not in `A`
  have hterm (j : Fin 16) (e : Fin k → Bool) :
      (selectionEtaZero e j : ZMod N) * ∏ i ∈ A, R.vertex e j i =
        selectionIndexSign (N := N) j * (if Fin.last k ∈ A then R.crossSection j else 1) *
          (parityCharacter (N := N) e * ∏ i ∈ univ.filter fun i : Fin k => i.castSucc ∈ A,
            (R.base j i + if e i then R.side i else 0)) := by
    rw [heta, selection_vertex_product_split, prod_filter]
    ring
  unfold arrangementMoment
  rw [sum_comm]
  simp only [hterm, ← mul_sum, selection_parity_cube_sum_subset, ← sum_mul]
  refine mul_eq_zero_of_left ?_ _
  by_cases hlast : Fin.last k ∈ A
  · simpa [hlast] using (selection_additive_iff R.crossSection).mp hadd
  · have hsign := (selection_additive_iff (N := N) fun _ ↦ 1).mp <| by
      simp only [IsAdditiveTuple, sum_const]
      congr 1 -- both halves of `Fin 16` have 8 elements
    simpa [hlast] using hsign

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
  -- two equal vertices `u ≠ v` give the ternary dependence `δ_u - δ_v`, which vanishes at a
  -- third index `w` and so is no multiple of the unit-valued parity coefficient
  intro u v huvVertex
  by_contra huv
  have hvu : v ≠ u := Ne.symm huv
  obtain ⟨w, hwu, hwv⟩ := selection_third_index u v
  let eta : (Fin k → Bool) → Fin 16 → Int := fun e j ↦
    if (e, j) = u then 1 else if (e, j) = v then -1 else 0
  refine hnondegenerate ⟨eta, fun z => ?_, ?_, fun A => ?_⟩
  · by_cases hzu : z = u <;> by_cases hzv : z = v <;>
      simp [eta, hzu, hzv, hvu]
  · rintro ⟨q, hq⟩
    have hunit : IsUnit (arrangementParityCoefficient (N := N) (d := 8) w.1 w.2) := by
      unfold arrangementParityCoefficient parityCharacter
      split
      exacts [isUnit_one.neg.pow _, (isUnit_one.neg.pow _).neg]
    have hq0 : q = 0 := hunit.mul_left_eq_zero.mp (by simpa [eta, hwu, hwv] using (hq w).symm)
    simpa [eta, hq0] using hq u
  · have hvert : R.vertex u.1 u.2 = R.vertex v.1 v.2 := huvVertex
    unfold arrangementMoment
    rw [← Fintype.sum_prod_type', Fintype.sum_eq_add u v huv fun z hz => by
      simp [eta, hz.1, hz.2], ← hvert, ← add_mul]
    simp [eta, hvu]

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

end LeanProofs.GowersSzemeredi
