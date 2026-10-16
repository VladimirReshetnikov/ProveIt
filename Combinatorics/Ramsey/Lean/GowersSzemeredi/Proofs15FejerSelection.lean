import GowersSzemeredi.Proofs15Restriction
import GowersSzemeredi.Proofs15DegenerateRange

/-!
# Lemma 15.5 with a single Fejér selection (Notes L.16)

Lemma 15.5 restricts `B` at random so that almost every surviving
8-arrangement is respected. The printed proof (`Proofs15Restriction`) keeps a
point with the Riesz weight `(1 + cos θ)/2 = |1 + e(θ)|²/4` and iterates
`2^(M−1)` independent stages, `M = 2^(k+4)`, because one stage favours a
respected arrangement only by the factor `1 + 2^(1−M)`. Hence the exponent
`arrangementSelectionExponent k = 2^(2^(k+4)+k+3)`.

Here one stage uses the Fejér weight of order `m`,
`|∑_{a ≤ m} e(a θ)|² / (m + 1)²` (the Riesz weight is `m = 1`). Averaging
over the phase (`fejer_oneStage_average`) counts digit pairs `(a, b)` whose
values `a − b` annihilate every feature:
* a respected arrangement has at least `∑_{j<T} (m+1−j)^M` of them, from the
  multiples `j·ε` of the parity pattern (`fejerValidRelations_card_good`);
* a non-respected arrangement without a dependence in `[−m, m]` has only the
  `(m+1)^M` diagonal ones (`fejerValidRelations_subset_diagonal`), by the
  `m`-range Lemma 15.4 of `Proofs15DegenerateRange`.

With `m + 1 = M·⌈6/(αη)⌉` Bernoulli's inequality gives a gain of
`(T+1)/2 ≥ 3/(αη)` in one stage, at the density cost `(m+1)^(−M)`. The result
(`fejer_arrangement_restriction`) is Lemma 15.5 with exponent
`fejerSelectionExponent k = 2^(k+4)·(k+6)`, and it implies the printed one
(`lemma_15_5_of_fejer_restriction`).

The finite Bernoulli averaging uses `Proofs12BernoulliSelection`. The hyperedge
bookkeeping, parity moment and vertex injectivity are copied from
`Proofs15Restriction` (private there). -/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ## Arrangements as finite hyperedges -/

private abbrev fejerIndex (k : Nat) :=
  (Fin k → Bool) × Fin 16

private def fejerVertex {N k : Nat} (R : GeneralArrangement N k 8)
    (z : fejerIndex k) : Point N (k + 1) :=
  R.vertex z.1 z.2

private noncomputable def fejerCarrier {N k : Nat}
    (R : GeneralArrangement N k 8) : Finset (Point N (k + 1)) := by
  classical
  exact Finset.univ.image (fejerVertex R)

private lemma fejerCarrier_subset {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) (R : GeneralArrangement N k 8)
    (hR : R.IsIn B) : fejerCarrier R ⊆ B := by
  classical
  intro z hz
  rw [fejerCarrier, Finset.mem_image] at hz
  obtain ⟨i, -, rfl⟩ := hz
  exact hR.2 i.1 i.2

private lemma fejer_isIn_iff {N k : Nat} [NeZero N]
    (B B' : Finset (Point N (k + 1)))
    (R : GeneralArrangement N k 8) (hR : R.IsIn B) :
    R.IsIn B' ↔ fejerCarrier R ⊆ B' := by
  constructor
  · intro h z hz
    rw [fejerCarrier, Finset.mem_image] at hz
    obtain ⟨i, -, rfl⟩ := hz
    exact h.2 i.1 i.2
  · intro h
    refine ⟨hR.1, ?_⟩
    intro e j
    apply h
    rw [fejerCarrier, Finset.mem_image]
    exact ⟨(e, j), Finset.mem_univ _, rfl⟩

private noncomputable def fejerArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) : Finset (GeneralArrangement N k 8) := by
  classical
  exact Finset.univ.filter fun R ↦ R.IsIn B

private noncomputable def fejerGoodArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (fejerArrangements B).filter fun R ↦ R.IsRespected phi

private noncomputable def fejerBadArrangements {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact fejerArrangements B \ fejerGoodArrangements B phi

private lemma fejerArrangements_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1))) :
    (fejerArrangements B).card = generalArrangementCount 8 B := by
  classical
  unfold fejerArrangements generalArrangementCount countWhere
  rw [Finset.filter_congr_decidable]

private lemma fejerGoodArrangements_card {N k : Nat} [NeZero N]
    (B : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) :
    (fejerGoodArrangements B phi).card =
      respectedGeneralArrangementCount 8 B phi := by
  classical
  unfold fejerGoodArrangements fejerArrangements
    respectedGeneralArrangementCount countWhere
  simp only [Finset.filter_filter]
  rw [Finset.filter_congr_decidable]
  apply congrArg Finset.card
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private lemma fejer_good_restrict_card {N k : Nat} [NeZero N]
    (B B' : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (hB'B : B' ⊆ B) :
    ((fejerGoodArrangements B phi).filter fun R ↦
      fejerCarrier R ⊆ B').card =
        respectedGeneralArrangementCount 8 B' phi := by
  classical
  unfold fejerGoodArrangements fejerArrangements
    respectedGeneralArrangementCount countWhere
  simp only [Finset.filter_filter]
  rw [Finset.filter_congr_decidable]
  apply congrArg Finset.card
  ext R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hRB, hrespect⟩, hcarrier⟩
    exact ⟨(fejer_isIn_iff B B' R hRB).mpr hcarrier, hrespect⟩
  · rintro ⟨hRB', hrespect⟩
    have hRB : R.IsIn B := ⟨hRB'.1, fun e j ↦ hB'B (hRB'.2 e j)⟩
    exact ⟨⟨hRB, hrespect⟩,
      (fejer_isIn_iff B B' R hRB).mp hRB'⟩

private lemma fejer_good_bad_restrict_card {N k : Nat} [NeZero N]
    (B B' : Finset (Point N (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (hB'B : B' ⊆ B) :
    ((fejerGoodArrangements B phi).filter fun R ↦
        fejerCarrier R ⊆ B').card +
      ((fejerBadArrangements B phi).filter fun R ↦
        fejerCarrier R ⊆ B').card =
      generalArrangementCount 8 B' := by
  classical
  let all' := (fejerArrangements B).filter fun R ↦
    fejerCarrier R ⊆ B'
  let good' := (fejerGoodArrangements B phi).filter fun R ↦
    fejerCarrier R ⊆ B'
  let bad' := (fejerBadArrangements B phi).filter fun R ↦
    fejerCarrier R ⊆ B'
  have hdisj : Disjoint good' bad' := by
    apply Finset.disjoint_left.mpr
    intro R hgood hbad
    have hg : R ∈ fejerGoodArrangements B phi :=
      (Finset.mem_filter.mp hgood).1
    have hb : R ∈ fejerBadArrangements B phi :=
      (Finset.mem_filter.mp hbad).1
    exact (Finset.mem_sdiff.mp hb).2 hg
  have hunion : good' ∪ bad' = all' := by
    ext R
    simp only [good', bad', all', fejerBadArrangements,
      fejerGoodArrangements,
      Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hallcard : all'.card = generalArrangementCount 8 B' := by
    unfold all' fejerArrangements generalArrangementCount countWhere
    simp only [Finset.filter_filter]
    rw [Finset.filter_congr_decidable]
    apply congrArg Finset.card
    ext R
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hRB, hcarrier⟩
      exact (fejer_isIn_iff B B' R hRB).mpr hcarrier
    · intro hRB'
      have hRB : R.IsIn B := ⟨hRB'.1, fun e j ↦ hB'B (hRB'.2 e j)⟩
      exact ⟨hRB, (fejer_isIn_iff B B' R hRB).mp hRB'⟩
  rw [← hallcard, ← hunion, Finset.card_union_of_disjoint hdisj]

private def fejerIndexSign {N : Nat} (j : Fin 16) : ZMod N :=
  if (j : Nat) < 8 then 1 else -1

private lemma fejer_additive_iff {N : Nat} (x : Fin 16 → ZMod N) :
    IsAdditiveTuple (k := 8) x ↔
      ∑ j, fejerIndexSign (N := N) j * x j = 0 := by
  classical
  let L := Finset.univ.filter fun j : Fin 16 ↦ (j : Nat) < 8
  let U := Finset.univ.filter fun j : Fin 16 ↦ 8 ≤ (j : Nat)
  have hcomp :
      (Finset.univ.filter fun j : Fin 16 ↦ ¬ (j : Nat) < 8) = U := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, U]
    omega
  have hsum :
      (∑ j, fejerIndexSign (N := N) j * x j) =
        (∑ j ∈ L, x j) - ∑ j ∈ U, x j := by
    dsimp only [L, U]
    simp_rw [fejerIndexSign, ite_mul, one_mul, neg_one_mul]
    rw [Finset.sum_ite, hcomp, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hsum, sub_eq_zero]
  rfl

private abbrev FejerFeature (k : Nat) :=
  Option (Finset (Fin (k + 1)))

private abbrev FejerPhase (N k : Nat) :=
  FejerFeature k → ZMod N

private lemma fejer_index_card (k : Nat) :
    Fintype.card (fejerIndex k) = 2 ^ (k + 4) := by
  simp only [fejerIndex, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_bool]
  rw [show 16 = 2 ^ 4 by norm_num, ← pow_add]

private def fejerFeatureValue {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (F : FejerFeature k)
    (z : Point N (k + 1)) : ZMod N :=
  match F with
  | none => phi z
  | some A => ∏ i ∈ A, z i

private def fejerPhaseValue {N k : Nat} [NeZero N]
    (C : FejerPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : ZMod N :=
  ∑ F, C F * fejerFeatureValue phi F z

attribute [simp] exponential_add

attribute [simp] star_exponential

attribute [simp] exponential_zero

private lemma fejer_expect_phase {N k : Nat} [NeZero N]
    (rel : FejerFeature k → ZMod N) :
    (𝔼 C : FejerPhase N k,
      exponential (∑ F, C F * rel F)) =
      if ∀ F, rel F = 0 then 1 else 0 := by
  classical
  have hexp (C : FejerPhase N k) :
      exponential (∑ F, C F * rel F) =
        ∏ F, exponential (C F * rel F) := by
    exact (fejer_prod_exponential (fun F ↦ C F * rel F)).symm
  simp_rw [hexp]
  rw [selection_expect_pi_prod
    (I := FejerFeature k) (C := ZMod N)
    (f := fun F c ↦ exponential (c * rel F))]
  have hfactor (F : FejerFeature k) :
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

private def fejerEtaZero {k : Nat} (e : Fin k → Bool) (j : Fin 16) : Int :=
  (if (j : Nat) < 8 then 1 else -1) * (-1 : Int) ^ boolWeight e

private lemma fejerEtaZero_cast {N k : Nat} (e : Fin k → Bool)
    (j : Fin 16) :
    (fejerEtaZero e j : ZMod N) =
      arrangementParityCoefficient (N := N) (d := 8) e j := by
  by_cases hj : (j : Nat) < 8 <;>
    simp [fejerEtaZero, arrangementParityCoefficient, parityCharacter, hj]

private lemma fejerEtaZero_cases {k : Nat} (e : Fin k → Bool)
    (j : Fin 16) : fejerEtaZero e j = 1 ∨ fejerEtaZero e j = -1 := by
  by_cases he : Even (boolWeight e)
  · have hp : (-1 : Int) ^ boolWeight e = 1 := he.neg_one_pow
    by_cases hj : (j : Nat) < 8 <;> simp [fejerEtaZero, hp, hj]
  · have hp : (-1 : Int) ^ boolWeight e = -1 :=
      (Nat.not_even_iff_odd.mp he).neg_one_pow
    by_cases hj : (j : Nat) < 8 <;> simp [fejerEtaZero, hp, hj]

private lemma fejerEtaZero_moment {N k : Nat} [NeZero N]
    (R : GeneralArrangement N k 8) (hadd : IsAdditiveTuple R.crossSection)
    (A : Finset (Fin (k + 1))) :
    arrangementMoment R fejerEtaZero A = 0 := by
  classical
  let A₀ : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ i.castSucc ∈ A
  let P : ZMod N := ∏ i : Fin k, if i ∈ A₀ then -R.side i else 0
  have heta (e : Fin k → Bool) (j : Fin 16) :
      (fejerEtaZero e j : ZMod N) =
        fejerIndexSign (N := N) j * parityCharacter (N := N) e := by
    rw [fejerEtaZero_cast]
    by_cases hj : (j : Nat) < 8 <;>
      simp [arrangementParityCoefficient, fejerIndexSign, hj]
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
        (fejerEtaZero e j : ZMod N) * ∏ i ∈ A, R.vertex e j i) =
        ∑ j : Fin 16, fejerIndexSign (N := N) j *
          (P * (if Fin.last k ∈ A then R.crossSection j else 1)) := by
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [heta, selection_vertex_product_split]
      calc
        (∑ e : Fin k → Bool,
            (fejerIndexSign (N := N) j * parityCharacter (N := N) e) *
              ((∏ i : Fin k, if i.castSucc ∈ A then
                (R.base j i + if e i then R.side i else 0) else 1) *
                (if Fin.last k ∈ A then R.crossSection j else 1))) =
            fejerIndexSign (N := N) j *
              ((∑ e : Fin k → Bool, parityCharacter (N := N) e *
                ∏ i : Fin k, if i.castSucc ∈ A then
                  (R.base j i + if e i then R.side i else 0) else 1) *
                (if Fin.last k ∈ A then R.crossSection j else 1)) := by
          rw [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = fejerIndexSign (N := N) j *
            (P * (if Fin.last k ∈ A then R.crossSection j else 1)) := by
          rw [hinner]
    _ = 0 := by
      by_cases hfull : A₀ = Finset.univ
      · by_cases hlast : Fin.last k ∈ A
        · simp only [if_pos hlast]
          have hadd' := (fejer_additive_iff R.crossSection).mp hadd
          calc
            (∑ j : Fin 16, fejerIndexSign (N := N) j *
                (P * R.crossSection j)) =
                P * ∑ j : Fin 16,
                  fejerIndexSign (N := N) j * R.crossSection j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
            _ = 0 := by rw [hadd', mul_zero]
        · simp only [if_neg hlast, mul_one]
          have hsign : (∑ j : Fin 16, fejerIndexSign (N := N) j) = 0 := by
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
              (fejer_additive_iff (N := N) (fun _ : Fin 16 ↦ 1)).mp hconst
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

private lemma fejer_third_index {k : Nat}
    (u v : fejerIndex k) :
    ∃ w : fejerIndex k, w ≠ u ∧ w ≠ v := by
  classical
  let e₀ : Fin k → Bool := fun _ ↦ false
  let z₀ : fejerIndex k := (e₀, (0 : Fin 16))
  let z₁ : fejerIndex k := (e₀, (1 : Fin 16))
  let z₂ : fejerIndex k := (e₀, (2 : Fin 16))
  by_cases h₀ : z₀ ≠ u ∧ z₀ ≠ v
  · exact ⟨z₀, h₀⟩
  by_cases h₁ : z₁ ≠ u ∧ z₁ ≠ v
  · exact ⟨z₁, h₁⟩
  refine ⟨z₂, ?_, ?_⟩ <;>
    push Not at h₀ h₁ <;> aesop

private lemma fejer_injective_of_nondegenerate {N k : Nat} [NeZero N]
    (hN : 2 ≤ N) (R : GeneralArrangement N k 8)
    (hnondegenerate : ¬ R.IsDegenerate) :
    Function.Injective (fejerVertex R) := by
  classical
  letI : Fact (1 < N) := ⟨by omega⟩
  intro u v huvVertex
  by_contra huv
  apply hnondegenerate
  have hvu : v ≠ u := by
    intro h
    exact huv h.symm
  obtain ⟨w, hwu, hwv⟩ := fejer_third_index u v
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
    rw [← Fintype.sum_prod_type (fun z : fejerIndex k ↦
      ((eta z.1 z.2 : Int) : ZMod N) *
        ∏ i ∈ A, R.vertex z.1 z.2 i)]
    let f : fejerIndex k → ZMod N := fun z ↦
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
    have hparityUnit (z : fejerIndex k) :
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

private lemma fejerCarrier_prod_of_nondegenerate {N k : Nat} [NeZero N]
    (hN : 2 ≤ N) (R : GeneralArrangement N k 8)
    (hnondegenerate : ¬ R.IsDegenerate)
    (p : Point N (k + 1) → Real) :
    (∏ z ∈ fejerCarrier R, p z) =
      ∏ i : fejerIndex k, p (fejerVertex R i) := by
  classical
  unfold fejerCarrier
  rw [Finset.prod_image
    (fejer_injective_of_nondegenerate hN R hnondegenerate).injOn]

/-! ## Fejér weights of order `m` -/

/-- A Fejér digit: a pair `(a, b)`, whose value is `a − b`. The Riesz digits
`{0, 0, 1, −1}` of Lemma 15.5 are the case `m = 1`. -/
private abbrev FejerDigit (m : Nat) := Fin (m + 1) × Fin (m + 1)

private def fejerDigitInt {m : Nat} (p : FejerDigit m) : Int :=
  ((p.1 : Nat) : Int) - ((p.2 : Nat) : Int)

private lemma fejerDigitInt_bound {m : Nat} (p : FejerDigit m) :
    -(m : Int) ≤ fejerDigitInt p ∧ fejerDigitInt p ≤ m := by
  unfold fejerDigitInt
  have h1 := p.1.isLt
  have h2 := p.2.isLt
  omega

/-- The relation of an integer coefficient pattern on one feature. -/
private def fejerRelationInt {N k : Nat} [NeZero N]
    (eta : fejerIndex k → Int) (F : FejerFeature k)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) : ZMod N :=
  ∑ z, (eta z : ZMod N) * fejerFeatureValue phi F (fejerVertex R z)

/-- The Fejér selection weight of order `m`,
`|∑_{a ≤ m} e(a·θ)|² / (m + 1)²`. -/
private def fejerKernelWeight {N k : Nat} [NeZero N] (m : Nat)
    (C : FejerPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : Real :=
  Complex.normSq (∑ a : Fin (m + 1),
      exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)) /
    ((m : Real) + 1) ^ 2

private lemma fejerKernelWeight_nonneg {N k : Nat} [NeZero N] (m : Nat)
    (C : FejerPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : 0 ≤ fejerKernelWeight m C phi z := by
  unfold fejerKernelWeight
  exact div_nonneg (Complex.normSq_nonneg _) (by positivity)

private lemma fejerKernelWeight_le_one {N k : Nat} [NeZero N] (m : Nat)
    (C : FejerPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) : fejerKernelWeight m C phi z ≤ 1 := by
  have hn : ‖∑ a : Fin (m + 1),
      exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)‖ ≤ (m : Real) + 1 := by
    calc ‖∑ a : Fin (m + 1),
          exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)‖
        ≤ ∑ a : Fin (m + 1),
          ‖exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)‖ :=
          norm_sum_le _ _
      _ = ∑ _a : Fin (m + 1), (1 : Real) := by
          apply Finset.sum_congr rfl
          intro a _
          exact (ZMod.stdAddChar (N := N)).norm_apply _
      _ = (m : Real) + 1 := by simp
  have hsq : Complex.normSq (∑ a : Fin (m + 1),
      exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)) ≤ ((m : Real) + 1) ^ 2 := by
    rw [← Complex.sq_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  unfold fejerKernelWeight
  rw [div_le_one (by positivity)]
  exact hsq

private lemma fejerKernelWeight_complex {N k : Nat} [NeZero N] (m : Nat)
    (C : FejerPhase N k) (phi : Point N (k + 1) → ZMod N)
    (z : Point N (k + 1)) :
    ((fejerKernelWeight m C phi z : Real) : Complex) =
      (((m : Complex) + 1) ^ 2)⁻¹ * ∑ p : FejerDigit m,
        exponential ((fejerDigitInt p : ZMod N) * fejerPhaseValue C phi z) := by
  have hexp : (∑ a : Fin (m + 1),
        exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)) *
      star (∑ a : Fin (m + 1),
        exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)) =
      ∑ p : FejerDigit m,
        exponential ((fejerDigitInt p : ZMod N) * fejerPhaseValue C phi z) := by
    rw [star_sum, Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [star_exponential, ← exponential_add]
    congr 1
    simp only [fejerDigitInt]
    push_cast
    ring
  have hnorm : ((Complex.normSq (∑ a : Fin (m + 1),
        exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)) : Real) : Complex) =
      (∑ a : Fin (m + 1),
        exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)) *
      star (∑ a : Fin (m + 1),
        exponential (((a : Nat) : ZMod N) * fejerPhaseValue C phi z)) := by
    rw [Complex.normSq_eq_conj_mul_self, mul_comm]
    rfl
  unfold fejerKernelWeight
  rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, hnorm, hexp, div_eq_inv_mul]

private lemma fejer_product_complex {N k : Nat} [NeZero N] (m : Nat)
    (C : FejerPhase N k) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8) :
    ((∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z) : Real) : Complex) =
      ((((m : Complex) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
        ∑ eps : fejerIndex k → FejerDigit m,
          exponential (∑ F, C F *
            fejerRelationInt (fun z => fejerDigitInt (eps z)) F phi R) := by
  rw [Complex.ofReal_prod]
  simp_rw [fejerKernelWeight_complex]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, fejer_index_card]
  rw [Fintype.prod_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro eps _
  rw [fejer_prod_exponential]
  congr 1
  unfold fejerPhaseValue fejerRelationInt
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun F _ => Finset.sum_congr rfl fun z _ => by ring

/-- The digit patterns whose integer values annihilate every feature. -/
private noncomputable def fejerValidRelations {N k : Nat} [NeZero N] (m : Nat)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    Finset (fejerIndex k → FejerDigit m) := by
  classical
  exact Finset.univ.filter fun eps ↦
    ∀ F, fejerRelationInt (fun z => fejerDigitInt (eps z)) F phi R = 0

/-- **The one-stage average**: averaging the product of Fejér weights over
the random phase counts the valid digit patterns. -/
private lemma fejer_oneStage_average {N k : Nat} [NeZero N] (m : Nat)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    (𝔼 C : FejerPhase N k,
      ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) =
      ((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
        (fejerValidRelations m phi R).card := by
  apply Complex.ofReal_injective
  change Complex.ofRealHom
      (𝔼 C : FejerPhase N k,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) =
    Complex.ofRealHom
      (((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
        (fejerValidRelations m phi R).card)
  rw [map_expect Complex.ofRealHom]
  have hrewrite (C : FejerPhase N k) :
      Complex.ofRealHom
          (∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) =
        ((((m : Complex) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
          ∑ eps : fejerIndex k → FejerDigit m,
            exponential (∑ F, C F *
              fejerRelationInt (fun z => fejerDigitInt (eps z)) F phi R) := by
    change ((∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z) : Real) :
      Complex) = _
    exact fejer_product_complex m C phi R
  simp_rw [hrewrite]
  rw [← Finset.mul_expect, Finset.expect_sum_comm]
  simp_rw [fejer_expect_phase]
  unfold fejerValidRelations
  simp_rw [Finset.cast_card, Finset.sum_filter]
  rw [map_mul, map_pow, map_inv₀, map_pow, map_add, map_natCast, map_one, map_sum]
  apply congrArg (((((m : Complex) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) * ·)
  apply Finset.sum_congr rfl
  intro eps _
  by_cases hvalid : ∀ F, fejerRelationInt (fun z => fejerDigitInt (eps z)) F phi R = 0 <;>
    simp [hvalid]

/-! ## Valid patterns: multiples of the parity relation -/

private def fejerEtaZeroIdx {k : Nat} (z : fejerIndex k) : Int :=
  fejerEtaZero z.1 z.2

private lemma fejerRelationInt_smul {N k : Nat} [NeZero N] (c : Int)
    (eta : fejerIndex k → Int) (F : FejerFeature k)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    fejerRelationInt (fun z => c * eta z) F phi R =
      (c : ZMod N) * fejerRelationInt eta F phi R := by
  unfold fejerRelationInt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  push_cast
  ring

private lemma fejerRelationInt_some {N k : Nat} [NeZero N]
    (eta : fejerIndex k → Int) (A : Finset (Fin (k + 1)))
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    fejerRelationInt eta (some A) phi R =
      arrangementMoment R (fun e j => eta (e, j)) A := by
  classical
  unfold fejerRelationInt arrangementMoment fejerFeatureValue
  rw [Fintype.sum_prod_type]
  rfl

private lemma fejerRelationInt_etaZero_none {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    fejerRelationInt fejerEtaZeroIdx none phi R =
      ∑ j : Fin 16, fejerIndexSign (N := N) j * R.cubeValue phi j := by
  classical
  unfold fejerRelationInt fejerFeatureValue GeneralArrangement.cubeValue
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [fejerEtaZeroIdx]
  rw [fejerEtaZero_cast]
  by_cases hj : (j : Nat) < 8 <;>
    simp [arrangementParityCoefficient, parityCharacter, fejerIndexSign, hj, fejerVertex]

private lemma fejerRelationInt_etaZero_none_eq_zero_iff {N k : Nat} [NeZero N]
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8) :
    fejerRelationInt fejerEtaZeroIdx none phi R = 0 ↔ R.IsRespected phi := by
  rw [fejerRelationInt_etaZero_none]
  unfold GeneralArrangement.IsRespected
  exact (fejer_additive_iff (R.cubeValue phi)).symm

/-- The digit patterns with values `j·ε`. -/
private noncomputable def fejerMultiplePatterns {k : Nat} (m j : Nat) :
    Finset (fejerIndex k → FejerDigit m) := by
  classical
  exact Fintype.piFinset fun z => Finset.univ.filter fun p : FejerDigit m =>
    fejerDigitInt p = (j : Int) * fejerEtaZeroIdx z

private lemma fejer_digit_count_pos (m j : Nat) (hj : j ≤ m) :
    (Finset.univ.filter fun p : FejerDigit m => fejerDigitInt p = (j : Int)).card =
      m + 1 - j := by
  classical
  have himg : (Finset.univ.filter fun p : FejerDigit m => fejerDigitInt p = (j : Int)) =
      (Finset.univ : Finset (Fin (m + 1 - j))).image
        (fun a : Fin (m + 1 - j) => ((⟨(a : Nat) + j, by have := a.isLt; omega⟩ : Fin (m + 1)),
          (⟨(a : Nat), by have := a.isLt; omega⟩ : Fin (m + 1)))) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      unfold fejerDigitInt at hp
      refine ⟨⟨(p.2 : Nat), by omega⟩, Prod.ext (Fin.ext ?_) (Fin.ext rfl)⟩
      simp only
      omega
    · rintro ⟨a, rfl⟩
      unfold fejerDigitInt
      simp
  rw [himg, Finset.card_image_of_injective]
  · simp
  · intro a b hab
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hab
    exact Fin.ext hab.2

private lemma fejer_digit_count (m j : Nat) (hj : j ≤ m) (s : Int)
    (hs : s = 1 ∨ s = -1) :
    (Finset.univ.filter fun p : FejerDigit m => fejerDigitInt p = (j : Int) * s).card =
      m + 1 - j := by
  classical
  rcases hs with rfl | rfl
  · simpa using fejer_digit_count_pos m j hj
  · have himg : (Finset.univ.filter fun p : FejerDigit m =>
          fejerDigitInt p = (j : Int) * -1) =
        (Finset.univ.filter fun p : FejerDigit m =>
          fejerDigitInt p = (j : Int)).image Prod.swap := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hp
        refine ⟨p.swap, ?_, Prod.swap_swap p⟩
        unfold fejerDigitInt at hp ⊢
        simp only [Prod.fst_swap, Prod.snd_swap]
        omega
      · rintro ⟨q, hq, rfl⟩
        unfold fejerDigitInt at hq ⊢
        simp only [Prod.fst_swap, Prod.snd_swap]
        omega
    rw [himg, Finset.card_image_of_injective _ Prod.swap_injective]
    exact fejer_digit_count_pos m j hj

private lemma fejerMultiplePatterns_card {k : Nat} (m j : Nat) (hj : j ≤ m) :
    (fejerMultiplePatterns (k := k) m j).card = (m + 1 - j) ^ (2 ^ (k + 4)) := by
  classical
  unfold fejerMultiplePatterns
  rw [Fintype.card_piFinset]
  rw [Finset.prod_congr rfl (fun z _ => fejer_digit_count m j hj (fejerEtaZeroIdx z)
    (fejerEtaZero_cases z.1 z.2))]
  simp only [Finset.prod_const, Finset.card_univ, fejer_index_card]

private lemma fejerMultiplePatterns_valid {N k : Nat} [NeZero N] (m j : Nat)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hadd : IsAdditiveTuple R.crossSection) (hres : R.IsRespected phi) :
    fejerMultiplePatterns (k := k) m j ⊆ fejerValidRelations m phi R := by
  classical
  intro eps heps
  have hval : (fun z => fejerDigitInt (eps z)) = fun z => (j : Int) * fejerEtaZeroIdx z := by
    funext z
    exact (Finset.mem_filter.mp (Fintype.mem_piFinset.mp heps z)).2
  unfold fejerValidRelations
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro F
  rw [hval, fejerRelationInt_smul]
  cases F with
  | none => rw [(fejerRelationInt_etaZero_none_eq_zero_iff phi R).mpr hres, mul_zero]
  | some A =>
    rw [fejerRelationInt_some]
    have hmom := fejerEtaZero_moment R hadd A
    have heq : (fun e j => fejerEtaZeroIdx (k := k) (e, j)) = fejerEtaZero := rfl
    rw [heq, hmom, mul_zero]

private lemma fejerMultiplePatterns_disjoint {k : Nat} (m : Nat) {j j' : Nat}
    (hjj : j ≠ j') :
    Disjoint (fejerMultiplePatterns (k := k) m j) (fejerMultiplePatterns (k := k) m j') := by
  classical
  rw [Finset.disjoint_left]
  intro eps h1 h2
  have e1 := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp h1 (fun _ => false, 0))).2
  have e2 := (Finset.mem_filter.mp (Fintype.mem_piFinset.mp h2 (fun _ => false, 0))).2
  simp only [fejerEtaZeroIdx] at e1 e2
  rcases fejerEtaZero_cases (k := k) (fun _ => false) 0 with h | h <;>
    · rw [h] at e1 e2
      omega

/-- **Respected arrangements have many valid patterns**: at least
`∑_{j<T} (m+1−j)^M`, from the multiples `j·ε`. -/
private lemma fejerValidRelations_card_good {N k : Nat} [NeZero N] (m T : Nat)
    (hT : T ≤ m + 1) (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hadd : IsAdditiveTuple R.crossSection) (hres : R.IsRespected phi) :
    ∑ j ∈ Finset.range T, (m + 1 - j) ^ (2 ^ (k + 4)) ≤
      (fejerValidRelations m phi R).card := by
  classical
  have hsub : (Finset.range T).biUnion (fun j => fejerMultiplePatterns (k := k) m j) ⊆
      fejerValidRelations m phi R :=
    Finset.biUnion_subset.mpr fun j _ => fejerMultiplePatterns_valid m j phi R hadd hres
  have hdisj : ((Finset.range T : Finset Nat) : Set Nat).PairwiseDisjoint
      (fun j => fejerMultiplePatterns (k := k) m j) :=
    fun j _ j' _ hjj => fejerMultiplePatterns_disjoint m hjj
  calc ∑ j ∈ Finset.range T, (m + 1 - j) ^ (2 ^ (k + 4))
      = ∑ j ∈ Finset.range T, (fejerMultiplePatterns (k := k) m j).card := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [fejerMultiplePatterns_card m j (by have := Finset.mem_range.mp hj; omega)]
    _ = ((Finset.range T).biUnion fun j => fejerMultiplePatterns (k := k) m j).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub

/-- **Non-respected, non-degenerate arrangements have only the diagonal
patterns**: a valid pattern is a modular multiple of `ε`, the multiple is
zero because the arrangement is not respected, and a pattern with values in
`[−m, m]` that vanishes modulo `N > m` vanishes. -/
private lemma fejerValidRelations_subset_diagonal {N k : Nat} [NeZero N]
    [Fact N.Prime] (m : Nat) (hmN : m < N)
    (phi : Point N (k + 1) → ZMod N) (R : GeneralArrangement N k 8)
    (hnondeg : ¬ R.IsDegenerateWithin m) (hbad : ¬ R.IsRespected phi) :
    fejerValidRelations m phi R ⊆
      Fintype.piFinset fun _ : fejerIndex k =>
        Finset.univ.filter fun p : FejerDigit m => p.1 = p.2 := by
  classical
  intro eps heps
  have hvalid := (Finset.mem_filter.mp heps).2
  have hmom : ∀ A, arrangementMoment R (fun e j => fejerDigitInt (eps (e, j))) A = 0 := by
    intro A
    have h := hvalid (some A)
    rw [fejerRelationInt_some] at h
    exact h
  have hmult : IsModularMultiple
      (fun z : (Fin k → Bool) × Fin 16 => fejerDigitInt (eps (z.1, z.2)))
      (fun z => arrangementParityCoefficient (N := N) (d := 8) z.1 z.2) := by
    by_contra hnot
    exact hnondeg ⟨fun e j => fejerDigitInt (eps (e, j)),
      fun e j => fejerDigitInt_bound _, hnot, hmom⟩
  obtain ⟨q, hq⟩ := hmult
  have hnone := hvalid none
  have hrel : fejerRelationInt (fun z => fejerDigitInt (eps z)) none phi R =
      q * fejerRelationInt fejerEtaZeroIdx none phi R := by
    unfold fejerRelationInt
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    rintro ⟨e, j⟩ _
    have hz : ((fejerDigitInt (eps (e, j)) : Int) : ZMod N) =
        q * arrangementParityCoefficient (N := N) (d := 8) e j := hq (e, j)
    rw [hz]
    simp only [fejerEtaZeroIdx]
    rw [fejerEtaZero_cast]
    ring
  rw [hrel] at hnone
  have hS : fejerRelationInt fejerEtaZeroIdx none phi R ≠ 0 := fun h =>
    hbad ((fejerRelationInt_etaZero_none_eq_zero_iff phi R).mp h)
  have hq0 : q = 0 := (mul_eq_zero.mp hnone).resolve_right hS
  rw [Fintype.mem_piFinset]
  intro z
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have hz : ((fejerDigitInt (eps (z.1, z.2)) : Int) : ZMod N) =
      q * arrangementParityCoefficient (N := N) (d := 8) z.1 z.2 := hq z
  rw [hq0, zero_mul] at hz
  have hdvd : (N : Int) ∣ fejerDigitInt (eps (z.1, z.2)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hz
  have hb := fejerDigitInt_bound (eps (z.1, z.2))
  have habs : |fejerDigitInt (eps (z.1, z.2))| < (N : Int) := by
    rw [abs_lt]
    constructor <;> omega
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  simp only [Prod.mk.eta] at h0
  unfold fejerDigitInt at h0
  exact Fin.ext (by omega)

private lemma fejer_diagonal_card {k : Nat} (m : Nat) :
    (Fintype.piFinset fun _ : fejerIndex k =>
      Finset.univ.filter fun p : FejerDigit m => p.1 = p.2).card =
      (m + 1) ^ (2 ^ (k + 4)) := by
  classical
  rw [Fintype.card_piFinset]
  have hdiag : (Finset.univ.filter fun p : FejerDigit m => p.1 = p.2) =
      (Finset.univ : Finset (Fin (m + 1))).image fun a => (a, a) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      exact ⟨p.1, Prod.ext rfl hp⟩
    · rintro ⟨a, rfl⟩
      rfl
  rw [hdiag, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.prod_const, fejer_index_card]

/-! ## The averages over good and bad arrangements -/

private lemma fejer_bad_average_upper {N k : Nat} [NeZero N] [Fact N.Prime]
    (m : Nat) (hmN : m < N) (phi : Point N (k + 1) → ZMod N)
    (R : GeneralArrangement N k 8)
    (hnondeg : ¬ R.IsDegenerateWithin m) (hbad : ¬ R.IsRespected phi) :
    (𝔼 C : FejerPhase N k,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) ≤
      (((m : Real) + 1)⁻¹) ^ (2 ^ (k + 4)) := by
  rw [fejer_oneStage_average]
  have hcard : ((fejerValidRelations m phi R).card : Real) ≤
      ((m : Real) + 1) ^ (2 ^ (k + 4)) := by
    have h := Finset.card_le_card
      (fejerValidRelations_subset_diagonal m hmN phi R hnondeg hbad)
    rw [fejer_diagonal_card] at h
    exact_mod_cast h
  calc ((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) * (fejerValidRelations m phi R).card
      ≤ ((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) * ((m : Real) + 1) ^ (2 ^ (k + 4)) :=
        mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = (((m : Real) + 1)⁻¹) ^ (2 ^ (k + 4)) := by
        rw [← mul_pow]
        congr 1
        field_simp

/-- Bernoulli: `∑_{j<T} ((m+1−j)/(m+1))^M ≥ (T+1)/2` when `m + 1 = M·T`. -/
private lemma fejer_ratio_sum_lower (M T : Nat) (hM : 1 ≤ M) (hT : 1 ≤ T) :
    ((T : Real) + 1) / 2 ≤
      ∑ j ∈ Finset.range T,
        (((M * T - j : Nat) : Real) / (M * T : Nat)) ^ M := by
  have hMT : (0 : Real) < (M * T : Nat) := by positivity
  have hterm : ∀ j ∈ Finset.range T,
      1 - (j : Real) / T ≤ (((M * T - j : Nat) : Real) / (M * T : Nat)) ^ M := by
    intro j hj
    have hjT := Finset.mem_range.mp hj
    have hjle : j ≤ M * T := hjT.le.trans (Nat.le_mul_of_pos_left T hM)
    have hcast : ((M * T - j : Nat) : Real) = (M * T : Nat) - j := by
      rw [Nat.cast_sub hjle]
    have hfrac : ((M * T - j : Nat) : Real) / (M * T : Nat) =
        1 + (-((j : Real) / (M * T : Nat))) := by
      rw [hcast]
      field_simp
      ring
    have hge : -2 ≤ -((j : Real) / (M * T : Nat)) := by
      have : (j : Real) / (M * T : Nat) ≤ 1 := by
        rw [div_le_one hMT]
        exact_mod_cast hjle
      linarith
    have hbern := one_add_mul_le_pow hge M
    rw [hfrac]
    have hsimp : (1 : Real) + (M : Real) * -((j : Real) / (M * T : Nat)) =
        1 - (j : Real) / T := by
      push_cast
      have hM0 : (M : Real) ≠ 0 := by positivity
      have hT0 : (T : Real) ≠ 0 := by positivity
      field_simp
      ring
    linarith [hbern, hsimp.symm.le, hsimp.le]
  have hsum : ∑ j ∈ Finset.range T, (1 - (j : Real) / T) = ((T : Real) + 1) / 2 := by
    have hid := Finset.sum_range_id_mul_two T
    have hidR : (∑ j ∈ Finset.range T, (j : Real)) * 2 = (T : Real) * ((T : Real) - 1) := by
      have h1 : ((T - 1 : Nat) : Real) = (T : Real) - 1 := by
        rw [Nat.cast_sub hT]; simp
      have := congrArg (fun n : Nat => (n : Real)) hid
      push_cast at this
      rw [h1] at this
      exact this
    rw [Finset.sum_sub_distrib, ← Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have hT0 : (T : Real) ≠ 0 := by positivity
    field_simp
    linarith
  calc ((T : Real) + 1) / 2 = ∑ j ∈ Finset.range T, (1 - (j : Real) / T) := hsum.symm
    _ ≤ _ := Finset.sum_le_sum hterm

/-! ## Degenerate arrangements and the carrier score -/

private lemma fejer_isDegenerateWithin_of_isDegenerate {N k : Nat} [NeZero N] {m : Nat}
    (hm : 1 ≤ m) (R : GeneralArrangement N k 8) (h : R.IsDegenerate) :
    R.IsDegenerateWithin m := by
  obtain ⟨eta, ht, hn, hmom⟩ := h
  refine ⟨eta, ?_, hn, hmom⟩
  intro e j
  rcases ht (e, j) with h | h | h <;> simp only at h <;> rw [h] <;> constructor <;> omega

private noncomputable def fejerGoodNondegenerate {N k : Nat} [NeZero N] (m : Nat)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (fejerGoodArrangements B phi).filter fun R ↦ ¬ R.IsDegenerateWithin m

private noncomputable def fejerBadNondegenerate {N k : Nat} [NeZero N] (m : Nat)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact (fejerBadArrangements B phi).filter fun R ↦ ¬ R.IsDegenerateWithin m

private noncomputable def fejerDegenerateFinset (N k m : Nat) [NeZero N] :
    Finset (GeneralArrangement N k 8) := by
  classical
  exact Finset.univ.filter fun R ↦
    IsAdditiveTuple R.crossSection ∧ R.IsDegenerateWithin m

private lemma fejerDegenerateFinset_card (N k m : Nat) [NeZero N] :
    (fejerDegenerateFinset N k m).card =
      degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 := by
  classical
  unfold fejerDegenerateFinset degenerateGeneralArrangementCountWithin countWhere
  apply congrArg Finset.card
  ext R
  simp

private lemma fejerGoodNondegenerate_card_lower {N k : Nat} [NeZero N] (m : Nat)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    (fejerGoodArrangements B phi).card ≤
      (fejerGoodNondegenerate m B phi).card +
        degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 := by
  classical
  let goodDeg := (fejerGoodArrangements B phi).filter fun R ↦ R.IsDegenerateWithin m
  have hsplit :
      (fejerGoodNondegenerate m B phi).card + goodDeg.card =
        (fejerGoodArrangements B phi).card := by
    simpa [fejerGoodNondegenerate, goodDeg] using
      (Finset.card_filter_add_card_filter_not
        (s := fejerGoodArrangements B phi) (fun R ↦ ¬ R.IsDegenerateWithin m))
  have hsub : goodDeg ⊆ fejerDegenerateFinset N k m := by
    intro R hR
    have hR' := Finset.mem_filter.mp hR
    have hgoodData : R ∈ fejerArrangements B ∧ R.IsRespected phi := by
      simpa [fejerGoodArrangements] using hR'.1
    have hIsIn : R.IsIn B := by
      simpa [fejerArrangements] using hgoodData.1
    simp [fejerDegenerateFinset, hIsIn.1, hR'.2]
  have hcard : goodDeg.card ≤ degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 := by
    calc goodDeg.card ≤ (fejerDegenerateFinset N k m).card := Finset.card_le_card hsub
      _ = _ := fejerDegenerateFinset_card N k m
  omega

private lemma fejer_carrier_score_lower {N k : Nat} [NeZero N]
    (hN : 2 ≤ N) (m : Nat) (hm : 1 ≤ m) (eta : Real) (heta : 0 ≤ eta)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N)
    (C : FejerPhase N k) :
    eta * (∑ R ∈ fejerGoodNondegenerate m B phi,
      ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) -
      (∑ R ∈ fejerBadNondegenerate m B phi,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) -
      degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 ≤
    eta * (∑ R ∈ fejerGoodArrangements B phi,
      ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z) -
      ∑ R ∈ fejerBadArrangements B phi,
        ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z := by
  classical
  let badDeg := (fejerBadArrangements B phi).filter fun R ↦ R.IsDegenerateWithin m
  have hp0 (z : Point N (k + 1)) : 0 ≤ fejerKernelWeight m C phi z := fejerKernelWeight_nonneg m C phi z
  have hp1 (z : Point N (k + 1)) : fejerKernelWeight m C phi z ≤ 1 := fejerKernelWeight_le_one m C phi z
  have hnd (R : GeneralArrangement N k 8) (h : ¬ R.IsDegenerateWithin m) :
      ¬ R.IsDegenerate := fun hd => h (fejer_isDegenerateWithin_of_isDegenerate hm R hd)
  have hgoodSub : fejerGoodNondegenerate m B phi ⊆ fejerGoodArrangements B phi :=
    fun R hR ↦ (Finset.mem_filter.mp hR).1
  have hgoodSum :
      (∑ R ∈ fejerGoodNondegenerate m B phi,
          ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) ≤
        ∑ R ∈ fejerGoodArrangements B phi,
          ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z := by
    calc
      (∑ R ∈ fejerGoodNondegenerate m B phi,
          ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) =
          ∑ R ∈ fejerGoodNondegenerate m B phi,
            ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z := by
        apply Finset.sum_congr rfl
        intro R hR
        symm
        exact fejerCarrier_prod_of_nondegenerate hN R
          (hnd R (Finset.mem_filter.mp hR).2) _
      _ ≤ ∑ R ∈ fejerGoodArrangements B phi,
          ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hgoodSub
        intro R _ _
        exact Finset.prod_nonneg fun z _ ↦ hp0 z
  have hbadSplit :
      (∑ R ∈ fejerBadArrangements B phi,
          ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z) =
        (∑ R ∈ fejerBadNondegenerate m B phi,
          ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z) +
        ∑ R ∈ badDeg, ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := fejerBadArrangements B phi) (p := fun R ↦ ¬ R.IsDegenerateWithin m)]
    simp [fejerBadNondegenerate, badDeg]
  have hbadNondegenerateEq :
      (∑ R ∈ fejerBadNondegenerate m B phi,
          ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z) =
        ∑ R ∈ fejerBadNondegenerate m B phi,
          ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z) := by
    apply Finset.sum_congr rfl
    intro R hR
    exact fejerCarrier_prod_of_nondegenerate hN R (hnd R (Finset.mem_filter.mp hR).2) _
  have hbadDegenerateSum :
      (∑ R ∈ badDeg, ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z) ≤
        degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 := by
    have hterm :
        (∑ R ∈ badDeg, ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z) ≤
          ∑ _R ∈ badDeg, (1 : Real) := by
      apply Finset.sum_le_sum
      intro R _
      exact Finset.prod_le_one (fun z _ ↦ hp0 z) (fun z _ ↦ hp1 z)
    have hsub : badDeg ⊆ fejerDegenerateFinset N k m := by
      intro R hR
      have hR' := Finset.mem_filter.mp hR
      have hbadMem := Finset.mem_sdiff.mp hR'.1
      have hIsIn : R.IsIn B := by
        simpa [fejerArrangements] using hbadMem.1
      simp [fejerDegenerateFinset, hIsIn.1, hR'.2]
    calc
      (∑ R ∈ badDeg, ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z) ≤
          ∑ _R ∈ badDeg, (1 : Real) := hterm
      _ = (badDeg.card : Real) := by simp
      _ ≤ (fejerDegenerateFinset N k m).card := by
        exact_mod_cast Finset.card_le_card hsub
      _ = degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 := by
        norm_cast
        exact fejerDegenerateFinset_card N k m
  rw [hbadSplit, hbadNondegenerateEq]
  have hgoodScaled := mul_le_mul_of_nonneg_left hgoodSum heta
  nlinarith

/-- The phase average of the score over non-degenerate arrangements. -/
private lemma fejer_phase_score_lower {N k : Nat} [NeZero N] [Fact N.Prime]
    (m T : Nat) (hT : T ≤ m + 1) (hmN : m < N) (eta : Real) (heta : 0 ≤ eta)
    (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N) :
    eta * (fejerGoodNondegenerate m B phi).card *
        (((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
          (∑ j ∈ Finset.range T, ((m + 1 - j : Nat) : Real) ^ (2 ^ (k + 4)))) -
      (fejerBadNondegenerate m B phi).card * (((m : Real) + 1)⁻¹) ^ (2 ^ (k + 4)) ≤
    𝔼 C : FejerPhase N k, (
      eta * (∑ R ∈ fejerGoodNondegenerate m B phi,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) -
      ∑ R ∈ fejerBadNondegenerate m B phi,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) := by
  classical
  rw [Finset.expect_sub_distrib, ← Finset.mul_expect, Finset.expect_sum_comm,
    Finset.expect_sum_comm]
  have hgood : (fejerGoodNondegenerate m B phi).card *
        (((((m : Real) + 1) ^ 2)⁻¹) ^ (2 ^ (k + 4)) *
          (∑ j ∈ Finset.range T, ((m + 1 - j : Nat) : Real) ^ (2 ^ (k + 4)))) ≤
      ∑ R ∈ fejerGoodNondegenerate m B phi, 𝔼 C : FejerPhase N k,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro R hR
    have hR' := Finset.mem_filter.mp hR
    have hgoodData : R ∈ fejerArrangements B ∧ R.IsRespected phi := by
      simpa [fejerGoodArrangements] using hR'.1
    have hIsIn : R.IsIn B := by
      simpa [fejerArrangements] using hgoodData.1
    rw [fejer_oneStage_average]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h := fejerValidRelations_card_good m T hT phi R (hIsIn.1) (hgoodData.2)
    exact_mod_cast h
  have hbad : (∑ R ∈ fejerBadNondegenerate m B phi, 𝔼 C : FejerPhase N k,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) ≤
      (fejerBadNondegenerate m B phi).card * (((m : Real) + 1)⁻¹) ^ (2 ^ (k + 4)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro R hR
    have hR' := Finset.mem_filter.mp hR
    have hbadMem := Finset.mem_sdiff.mp hR'.1
    have hbadR : ¬ R.IsRespected phi := by
      intro hrespect
      apply hbadMem.2
      simp [fejerGoodArrangements, hbadMem.1, hrespect]
    exact fejer_bad_average_upper m hmN phi R hR'.2 hbadR
  have hscaled := mul_le_mul_of_nonneg_left hgood heta
  nlinarith

/-! ## The Fejér restriction -/

/-- The exponent of the single Fejér selection: `2^(k+4)·(k+6)`, against
`2^(2^(k+4)+k+3)` for the iterated Riesz selection. -/
def fejerSelectionExponent (k : Nat) : Nat := 2 ^ (k + 4) * (k + 6)

/-- **Lemma 15.5 with a single Fejér selection.** The statement of
Lemma 15.5 with `fejerSelectionExponent k` in place of
`arrangementSelectionExponent k`. -/
def FejerArrangementRestriction : Prop :=
  ∀ (k : Nat) (alpha beta eta : Real),
    1 ≤ k → 0 < alpha → 0 < beta → 0 < eta → eta ≤ 1 →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1)))
          (phi : Point N (k + 1) → ZMod N),
        (B.card : Real) = beta * (N : Real) ^ (k + 1) →
        alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ fejerSelectionExponent k * beta ^ 15 *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi

/-- The density loss `t = (M·T)^(−M)` dominates `(αη/4)^(M(k+6))`. -/
private lemma fejer_loss_lower (k : Nat) (a : Real) (ha : 0 < a) (ha1 : a ≤ 1) :
    (a / 4) ^ fejerSelectionExponent k ≤
      (((2 ^ (k + 4) * ⌈6 / a⌉₊ : Nat) : Real)⁻¹) ^ (2 ^ (k + 4)) := by
  set M : Nat := 2 ^ (k + 4) with hM
  set T : Nat := ⌈6 / a⌉₊
  have hT : (T : Real) ≤ 7 / a := by
    have h1 : (T : Real) < 6 / a + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : (1 : Real) ≤ 1 / a := by rw [le_div_iff₀ ha]; linarith
    linarith [show 6 / a + 1 ≤ 6 / a + 1 / a by linarith, show (6 : Real) / a + 1 / a = 7 / a by ring]
  have hMR : ((M : Nat) : Real) = 2 ^ (k + 4) := by rw [hM]; push_cast; ring
  have hMT : (((M * T : Nat) : Real)) ≤ 2 ^ (k + 7) / a := by
    push_cast
    rw [hMR]
    calc (2 : Real) ^ (k + 4) * T ≤ 2 ^ (k + 4) * (7 / a) :=
          mul_le_mul_of_nonneg_left hT (by positivity)
      _ ≤ 2 ^ (k + 4) * (8 / a) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_right (by norm_num) ha.le
      _ = 2 ^ (k + 7) / a := by rw [show k + 7 = (k + 4) + 3 by ring, pow_add]; ring
  have hMTpos : (0 : Real) < ((M * T : Nat) : Real) := by
    push_cast; rw [hMR]; positivity
  -- the base comparison: (a/4)^(k+6) ≤ a / 2^(k+7) ≤ 1/(M T)
  have hbase : (a / 4) ^ (k + 6) ≤ (((M * T : Nat) : Real))⁻¹ := by
    have h1 : (a / 4) ^ (k + 6) ≤ (a / 4) * (1 / 4) ^ (k + 5) := by
      rw [show k + 6 = (k + 5) + 1 by ring, pow_succ, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    have h2 : (a / 4) * (1 / 4 : Real) ^ (k + 5) ≤ a / 2 ^ (k + 7) := by
      have h4 : (4 : Real) ^ (k + 5) = 2 ^ (2 * (k + 5)) := by
        rw [pow_mul]; norm_num
      have h5 : (2 : Real) ^ (k + 7) ≤ 4 * 2 ^ (2 * (k + 5)) := by
        calc (2 : Real) ^ (k + 7) ≤ 2 ^ (2 * (k + 5) + 2) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
          _ = 4 * 2 ^ (2 * (k + 5)) := by rw [pow_add]; ring
      rw [one_div_pow, h4]
      rw [div_mul_div_comm, mul_one]
      apply div_le_div_of_nonneg_left ha.le (by positivity) h5
    have h3 : a / 2 ^ (k + 7) ≤ (((M * T : Nat) : Real))⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hMTpos]
      calc ((M * T : Nat) : Real) ≤ 2 ^ (k + 7) / a := hMT
        _ = (a / 2 ^ (k + 7))⁻¹ := by rw [inv_div]
    linarith
  unfold fejerSelectionExponent
  rw [← hM, mul_comm, pow_mul]
  exact pow_le_pow_left₀ (by positivity) hbase M

/-- The order `m` of the Fejér kernel: `m + 1 = 2^(k+4)·⌈6/(min(α,1)·η)⌉`. -/
def fejerOrder (k : Nat) (alpha eta : Real) : Nat :=
  2 ^ (k + 4) * ⌈6 / (min alpha 1 * eta)⌉₊ - 1

/-- The density loss `(m+1)^(−2^(k+4))` of one Fejér stage. -/
def fejerLoss (k : Nat) (alpha eta : Real) : Real :=
  (((fejerOrder k alpha eta : Nat) : Real) + 1)⁻¹ ^ (2 ^ (k + 4))

/-- The constant of the `m`-range degenerate count:
`(2m+1)^(2·8·2^k)·k`. -/
def fejerDegenerateConst (k : Nat) (alpha eta : Real) : Real :=
  (2 * ((fejerOrder k alpha eta : Nat) : Real) + 1) ^ (2 * 8 * 2 ^ k) * k

/-- **The explicit modulus threshold of the Fejér selection**:
`max(m + 1, 3, 2·c₀/(scale·t))`. -/
def fejerExplicitThreshold (k : Nat) (alpha scale eta : Real) : Real :=
  max (((fejerOrder k alpha eta : Nat) : Real) + 1)
    (max 3 (2 * fejerDegenerateConst k alpha eta / (scale * fejerLoss k alpha eta)))

set_option maxHeartbeats 1000000 in
/-- **The Fejér selection at an arbitrary scale**, above the explicit
threshold `fejerExplicitThreshold`: if `B` carries at most
`scale·N^(17k+15)` arrangements, of which at least `α·scale·N^(17k+15)` are
respected, then some `B' ⊆ B` carries at least
`(αη/4)^(2^(k+4)(k+6))·scale·N^(17k+15)` arrangements, of which a
`1 − η` fraction is respected. -/
theorem fejer_scale_estimate_explicit (k : Nat) (alpha scale eta : Real) (hk : 1 ≤ k)
    (halpha : 0 < alpha) (hscale : 0 < scale) (heta : 0 < eta) (heta_one : eta ≤ 1) :
    ∀ (N : Nat) [NeZero N], fejerExplicitThreshold k alpha scale eta ≤ (N : Real) →
      Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        (generalArrangementCount 8 B : Real) ≤ scale * (N : Real) ^ (17 * k + 15) →
        alpha * scale * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ fejerSelectionExponent k * scale *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  -- the order of the Fejér kernel
  set M : Nat := 2 ^ (k + 4) with hM
  have hM1 : 1 ≤ M := Nat.one_le_two_pow
  have hM16 : 16 ≤ M := by
    rw [hM]; calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- `α` may be taken at most one: otherwise the hypothesis is void
  set a : Real := min alpha 1 * eta with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    have h := mul_le_mul (min_le_right alpha 1) heta_one heta.le zero_le_one
    rw [one_mul] at h
    exact h
  set T : Nat := ⌈6 / a⌉₊ with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef, Nat.one_le_ceil_iff]; positivity
  set m : Nat := M * T - 1 with hmdef
  have hm1 : m + 1 = M * T := by
    have : 1 ≤ M * T := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hMT : M ≤ M * T := Nat.le_mul_of_pos_right M hT1
  have hm : 1 ≤ m := by omega
  have hTm : T ≤ m + 1 := by rw [hm1]; exact Nat.le_mul_of_pos_left T hM1
  set t : Real := (((m : Real) + 1)⁻¹) ^ M with htdef
  have ht0 : 0 < t := by positivity
  set c0 : Real := (2 * (m : Real) + 1) ^ (2 * 8 * 2 ^ k) * k with hc0
  intro N _ hN hprime hodd B phi hu hrespected
  letI : Fact N.Prime := ⟨hprime⟩
  have hthr : fejerExplicitThreshold k alpha scale eta =
      max ((m : Real) + 1) (max 3 (2 * c0 / (scale * t))) := rfl
  rw [hthr] at hN
  have hmN : m < N := by
    have h : (m : Real) + 1 ≤ N := (le_max_left _ _).trans hN
    have h' : (m : Real) < N := by linarith
    exact_mod_cast h'
  have hN3 : 3 ≤ N := by
    have h : (3 : Real) ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
    exact_mod_cast h
  have hNbig : 2 * c0 / (scale * t) ≤ (N : Real) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNpos : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
  set G : Real := scale * (N : Real) ^ (17 * k + 15) with hG
  have hG0 : 0 < G := mul_pos hscale (by positivity)
  -- counts
  have hgeneral : (generalArrangementCount 8 B : Real) ≤ G :=
    hu
  have hrespLe : (respectedGeneralArrangementCount 8 B phi : Real) ≤
      generalArrangementCount 8 B := by
    exact_mod_cast selection_respected_le_arrangement B phi
  have halpha1 : alpha ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : alpha * G ≤ G := by
      calc alpha * G = alpha * scale * (N : Real) ^ (17 * k + 15) := by rw [hG]; ring
        _ ≤ _ := hrespected
        _ ≤ _ := hrespLe
        _ ≤ G := hgeneral
    linarith [mul_pos (sub_pos.mpr hlt) hG0]
  have hamin : min alpha 1 = alpha := min_eq_left halpha1
  have haeq : a = alpha * eta := by rw [ha, hamin]
  -- the degenerate count
  set D : Real := ((degenerateGeneralArrangementCountWithin (N := N) (k := k) m 8 : Nat) : Real)
    with hD
  have hD0 : 0 ≤ D := by positivity
  have hDle : D ≤ c0 * (N : Real) ^ (17 * k + 14) := by
    have h := degenerate_count_within_le N m k 8 hprime hodd hk (by norm_num)
    have he : (2 * 8 + 1) * k + 2 * 8 - 2 = 17 * k + 14 := by omega
    rw [he] at h
    calc D ≤ _ := h
      _ = c0 * (N : Real) ^ (17 * k + 14) := by rw [hc0]
  have hDsmall : 2 * D ≤ t * G := by
    have h1 : 2 * c0 ≤ scale * t * N := by
      have := (div_le_iff₀ (by positivity : (0 : Real) < scale * t)).mp hNbig
      linarith
    calc 2 * D ≤ 2 * (c0 * (N : Real) ^ (17 * k + 14)) := by linarith
      _ = (2 * c0) * (N : Real) ^ (17 * k + 14) := by ring
      _ ≤ (scale * t * N) * (N : Real) ^ (17 * k + 14) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = t * G := by rw [hG, show 17 * k + 15 = (17 * k + 14) + 1 by ring, pow_succ]; ring
  -- the ratio
  have hratio : ((T : Real) + 1) / 2 ≤
      ∑ j ∈ Finset.range T, (((M * T - j : Nat) : Real) / (M * T : Nat)) ^ M :=
    fejer_ratio_sum_lower M T hM1 hT1
  have hL : t * (((T : Real) + 1) / 2) ≤
      ((((m : Real) + 1) ^ 2)⁻¹) ^ M *
        (∑ j ∈ Finset.range T, ((m + 1 - j : Nat) : Real) ^ M) := by
    have hmR : ((m : Real) + 1) = ((M * T : Nat) : Real) := by rw [← hm1]; push_cast; ring
    have hrw : ((((m : Real) + 1) ^ 2)⁻¹) ^ M *
          (∑ j ∈ Finset.range T, ((m + 1 - j : Nat) : Real) ^ M) =
        t * ∑ j ∈ Finset.range T, (((M * T - j : Nat) : Real) / (M * T : Nat)) ^ M := by
      rw [htdef, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hm1, ← hmR, div_pow, inv_pow, inv_pow, ← pow_mul]
      field_simp
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hratio ht0.le
  have hTa : 6 / (alpha * eta) ≤ T := by rw [← haeq]; exact Nat.le_ceil _
  have hgain : 3 ≤ eta * alpha * (((T : Real) + 1) / 2) := by
    have h1 : 6 ≤ alpha * eta * T := by
      have := (div_le_iff₀ (by positivity : (0 : Real) < alpha * eta)).mp hTa
      linarith
    linarith [mul_pos halpha heta]
  -- the phase average and the choice of the phase
  have hgoodCard : alpha * G - D ≤ (fejerGoodNondegenerate m B phi).card := by
    have h := fejerGoodNondegenerate_card_lower m B phi
    rw [fejerGoodArrangements_card] at h
    have h' : (respectedGeneralArrangementCount 8 B phi : Real) ≤
        (fejerGoodNondegenerate m B phi).card + D := by
      rw [hD]; exact_mod_cast h
    have : alpha * G ≤ respectedGeneralArrangementCount 8 B phi := by
      calc alpha * G = alpha * scale * (N : Real) ^ (17 * k + 15) := by rw [hG]; ring
        _ ≤ _ := hrespected
    linarith
  have hbadCard : ((fejerBadNondegenerate m B phi).card : Real) ≤ G := by
    have h : (fejerBadNondegenerate m B phi).card ≤ (fejerArrangements B).card := by
      classical
      apply Finset.card_le_card
      intro R hR
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hR).1).1
    rw [fejerArrangements_card] at h
    calc ((fejerBadNondegenerate m B phi).card : Real) ≤ generalArrangementCount 8 B := by
          exact_mod_cast h
      _ ≤ G := hgeneral
  have hphase : eta * (fejerGoodNondegenerate m B phi).card *
        (((((m : Real) + 1) ^ 2)⁻¹) ^ M *
          (∑ j ∈ Finset.range T, ((m + 1 - j : Nat) : Real) ^ M)) -
      (fejerBadNondegenerate m B phi).card * t ≤
    𝔼 C : FejerPhase N k, (
      eta * (∑ R ∈ fejerGoodNondegenerate m B phi,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) -
      ∑ R ∈ fejerBadNondegenerate m B phi,
        ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) :=
    fejer_phase_score_lower (k := k) m T hTm hmN eta heta.le B phi
  have hscore : eta * t * G + D ≤
      𝔼 C : FejerPhase N k, (
        eta * (∑ R ∈ fejerGoodNondegenerate m B phi,
          ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) -
        ∑ R ∈ fejerBadNondegenerate m B phi,
          ∏ z : fejerIndex k, fejerKernelWeight m C phi (fejerVertex R z)) := by
    refine le_trans ?_ hphase
    have hLnn : 0 ≤ t * (((T : Real) + 1) / 2) := by positivity
    have hgoodTerm : eta * (alpha * G - D) * (t * (((T : Real) + 1) / 2)) ≤
        eta * (fejerGoodNondegenerate m B phi).card *
          (((((m : Real) + 1) ^ 2)⁻¹) ^ M *
            (∑ j ∈ Finset.range T, ((m + 1 - j : Nat) : Real) ^ M)) := by
      have h1 : eta * (alpha * G - D) ≤ eta * (fejerGoodNondegenerate m B phi).card :=
        mul_le_mul_of_nonneg_left hgoodCard heta.le
      calc eta * (alpha * G - D) * (t * (((T : Real) + 1) / 2))
          ≤ eta * (fejerGoodNondegenerate m B phi).card * (t * (((T : Real) + 1) / 2)) :=
            mul_le_mul_of_nonneg_right h1 hLnn
        _ ≤ _ := mul_le_mul_of_nonneg_left hL (by positivity)
    have hbadTerm : ((fejerBadNondegenerate m B phi).card : Real) * t ≤ G * t :=
      mul_le_mul_of_nonneg_right hbadCard ht0.le
    have htT : t * (((T : Real) + 1) / 2) ≤ 1 := by
      have hmT : ((m : Real) + 1) = (M : Real) * T := by
        rw [show (M : Real) * T = ((M * T : Nat) : Real) by push_cast; ring, ← hm1]; push_cast; ring
      have h1 : t ≤ ((m : Real) + 1)⁻¹ := by
        rw [htdef]
        exact pow_le_of_le_one (by positivity)
          (inv_le_one_of_one_le₀ (by linarith [show (0 : Real) ≤ m by positivity]))
          (by omega)
      have h2 : ((T : Real) + 1) / 2 ≤ T := by
        have : (1 : Real) ≤ T := by exact_mod_cast hT1
        linarith
      have h3 : ((m : Real) + 1)⁻¹ * T ≤ 1 := by
        rw [hmT, mul_inv, mul_assoc, inv_mul_cancel₀ (by positivity : (T : Real) ≠ 0), mul_one]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast hM1)
      calc t * (((T : Real) + 1) / 2) ≤ ((m : Real) + 1)⁻¹ * T :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ ≤ 1 := h3
    have hmain : eta * t * G + D ≤
        eta * (alpha * G - D) * (t * (((T : Real) + 1) / 2)) - G * t := by
      have e2 : eta * D * (t * (((T : Real) + 1) / 2)) ≤ D := by
        calc eta * D * (t * (((T : Real) + 1) / 2)) ≤ 1 * D * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_right heta_one hD0) htT (by positivity)
                (by positivity)
          _ = D := by ring
      have e3 : 3 * (t * G) ≤ (eta * alpha * (((T : Real) + 1) / 2)) * (t * G) :=
        mul_le_mul_of_nonneg_right hgain (by positivity)
      have e4 : eta * t * G ≤ t * G := by
        have := mul_le_mul_of_nonneg_right heta_one (by positivity : (0 : Real) ≤ t * G)
        linarith
      linarith [mul_comm G t]
    linarith
  obtain ⟨C, -, hC⟩ := Finset.exists_le_of_le_expect
    (Finset.univ_nonempty : (Finset.univ : Finset (FejerPhase N k)).Nonempty) hscore
  have hcarrier := fejer_carrier_score_lower (by omega) m hm eta heta.le B phi C
  have hcarrierAverage :
      eta * t * G ≤
        eta * (∑ R ∈ fejerGoodArrangements B phi,
          ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z) -
          ∑ R ∈ fejerBadArrangements B phi,
            ∏ z ∈ fejerCarrier R, fejerKernelWeight m C phi z := by
    linarith only [hC, hcarrier]
  have hgoodCarrier : ∀ R ∈ fejerGoodArrangements B phi, fejerCarrier R ⊆ B := by
    intro R hR
    have hR' : R ∈ fejerArrangements B ∧ R.IsRespected phi := by
      simpa [fejerGoodArrangements] using hR
    have hIsIn : R.IsIn B := by simpa [fejerArrangements] using hR'.1
    exact fejerCarrier_subset B R hIsIn
  have hbadCarrier : ∀ R ∈ fejerBadArrangements B phi, fejerCarrier R ⊆ B := by
    intro R hR
    have hR' := Finset.mem_sdiff.mp hR
    have hIsIn : R.IsIn B := by simpa [fejerArrangements] using hR'.1
    exact fejerCarrier_subset B R hIsIn
  obtain ⟨S, hSB, hS⟩ := _root_.LeanProofs.GowersSzemeredi.exists_subset_count_score B (fejerKernelWeight m C phi)
    (fun z _ ↦ fejerKernelWeight_nonneg m C phi z) (fun z _ ↦ fejerKernelWeight_le_one m C phi z)
    (fejerGoodArrangements B phi) (fejerBadArrangements B phi) fejerCarrier
    hgoodCarrier hbadCarrier eta (eta * t * G) hcarrierAverage
  rw [fejer_good_restrict_card B S phi hSB] at hS
  have hsplitS := fejer_good_bad_restrict_card B S phi hSB
  rw [fejer_good_restrict_card B S phi hSB] at hsplitS
  set g : Real := ((respectedGeneralArrangementCount 8 S phi : Nat) : Real) with hg
  set b : Real := ((((fejerBadArrangements B phi).filter fun R ↦ fejerCarrier R ⊆ S).card :
    Nat) : Real) with hb
  have hgen : (generalArrangementCount 8 S : Real) = g + b := by
    rw [hg, hb]; exact_mod_cast hsplitS.symm
  have hb0 : 0 ≤ b := by positivity
  have hgLower : t * G ≤ g := by
    have : eta * (t * G) ≤ eta * g := by linarith
    exact le_of_mul_le_mul_left this heta
  refine ⟨S, hSB, ?_, ?_⟩
  · -- the loss
    have hloss := fejer_loss_lower k (alpha * eta) (by positivity) (by rw [← haeq]; exact ha1)
    have hTeq : ⌈6 / (alpha * eta)⌉₊ = T := by rw [hTdef, haeq]
    rw [hTeq, ← hM, ← hm1] at hloss
    have htEq : ((((m + 1 : Nat) : Real))⁻¹) ^ M = t := by rw [htdef]; push_cast; ring
    rw [htEq] at hloss
    calc (alpha * eta / 4) ^ fejerSelectionExponent k * scale * (N : Real) ^ (17 * k + 15)
        = (alpha * eta / 4) ^ fejerSelectionExponent k * G := by rw [hG]; ring
      _ ≤ t * G := mul_le_mul_of_nonneg_right hloss hG0.le
      _ ≤ g := hgLower
      _ ≤ g + b := by linarith
      _ = _ := hgen.symm
  · rw [hgen]
    have hpos : 0 ≤ eta * t * G := by positivity
    have hetab : 0 ≤ eta * b := mul_nonneg heta.le hb0
    linarith

/-- The Fejér selection with an existential threshold. -/
theorem fejer_scale_estimate (k : Nat) (alpha scale eta : Real) (hk : 1 ≤ k)
    (halpha : 0 < alpha) (hscale : 0 < scale) (heta : 0 < eta) (heta_one : eta ≤ 1) :
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N → Nat.Prime N → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        (generalArrangementCount 8 B : Real) ≤ scale * (N : Real) ^ (17 * k + 15) →
        alpha * scale * (N : Real) ^ (17 * k + 15) ≤
            respectedGeneralArrangementCount 8 B phi →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (alpha * eta / 4) ^ fejerSelectionExponent k * scale *
              (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - eta) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi :=
  ⟨⌈fejerExplicitThreshold k alpha scale eta⌉₊, fun N _ hN =>
    fejer_scale_estimate_explicit k alpha scale eta hk halpha hscale heta heta_one N
      ((Nat.le_ceil _).trans (by exact_mod_cast hN))⟩

theorem fejer_arrangement_restriction : FejerArrangementRestriction := by
  intro k alpha beta eta hk halpha hbeta heta heta_one
  obtain ⟨N0, hN0⟩ := fejer_scale_estimate k alpha (beta ^ 15) eta hk halpha
    (pow_pos hbeta 15) heta heta_one
  exact ⟨N0, fun N _ hN hp ho B phi hBcard hl =>
    hN0 N hN hp ho B phi (selection_arrangement_real_upper beta B hBcard) hl⟩

/-- **The Fejér restriction implies the printed Lemma 15.5**, whose
exponent `2^(2^(k+4)+k+3)` is larger. -/
theorem lemma_15_5_of_fejer_restriction (h : FejerArrangementRestriction) : lemma_15_5 := by
  intro k alpha beta eta hk halpha hbeta heta heta_one
  obtain ⟨N0, hN0⟩ := h k alpha beta eta hk halpha hbeta heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN hprime hodd B phi hBcard hrespected
  obtain ⟨B', hB'B, hlower, hdens⟩ := hN0 N hN hprime hodd B phi hBcard hrespected
  refine ⟨B', hB'B, le_trans ?_ hlower, hdens⟩
  have hG : 0 ≤ beta ^ 15 * (N : Real) ^ (17 * k + 15) := by positivity
  have hgeneral := selection_arrangement_real_upper beta B hBcard
  have hrespLe : (respectedGeneralArrangementCount 8 B phi : Real) ≤
      generalArrangementCount 8 B := by
    exact_mod_cast selection_respected_le_arrangement B phi
  rcases eq_or_lt_of_le hG with hG0 | hGpos
  · rw [mul_assoc, mul_assoc, ← hG0, mul_zero, mul_zero]
  have halpha1 : alpha ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have : alpha * (beta ^ 15 * (N : Real) ^ (17 * k + 15)) ≤
        beta ^ 15 * (N : Real) ^ (17 * k + 15) := by
      calc alpha * (beta ^ 15 * (N : Real) ^ (17 * k + 15)) =
          alpha * beta ^ 15 * (N : Real) ^ (17 * k + 15) := by ring
        _ ≤ _ := hrespected
        _ ≤ _ := hrespLe
        _ ≤ _ := hgeneral
    linarith [mul_pos (sub_pos.mpr hlt) hGpos]
  have hbase0 : 0 ≤ alpha * eta / 4 := by positivity
  have hbase1 : alpha * eta / 4 ≤ 1 := by
    have h := mul_le_mul halpha1 heta_one heta.le zero_le_one
    linarith
  have hexp : fejerSelectionExponent k ≤ arrangementSelectionExponent k := by
    unfold fejerSelectionExponent arrangementSelectionExponent
    have h1 : k + 6 ≤ 2 ^ (2 ^ (k + 4) - 1) := by
      have h2 : k + 6 ≤ 2 ^ (k + 4) - 1 := by
        have := Nat.lt_two_pow_self (n := k)
        have e : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
        rw [e]
        omega
      exact h2.trans (Nat.lt_two_pow_self).le
    have h3 : 2 ^ (2 ^ (k + 4) + k + 3) = 2 ^ (k + 4) * 2 ^ (2 ^ (k + 4) - 1) := by
      rw [← pow_add]
      congr 1
      have := Nat.one_le_two_pow (n := k + 4)
      omega
    rw [h3]
    exact Nat.mul_le_mul_left _ h1
  have hpow := pow_le_pow_of_le_one hbase0 hbase1 hexp
  calc (alpha * eta / 4) ^ arrangementSelectionExponent k * beta ^ 15 *
        (N : Real) ^ (17 * k + 15)
      = (alpha * eta / 4) ^ arrangementSelectionExponent k *
          (beta ^ 15 * (N : Real) ^ (17 * k + 15)) := by ring
    _ ≤ (alpha * eta / 4) ^ fejerSelectionExponent k *
          (beta ^ 15 * (N : Real) ^ (17 * k + 15)) :=
        mul_le_mul_of_nonneg_right hpow hG
    _ = _ := by ring

end LeanProofs.GowersSzemeredi
