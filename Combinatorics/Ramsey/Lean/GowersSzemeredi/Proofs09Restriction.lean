import GowersSzemeredi.Proofs09Moments
import GowersSzemeredi.Proofs15Restriction

/-!
# Random restriction for approximate homomorphisms

This module proves Gowers's Lemma 9.3 and Corollary 9.4.  It first records the
counterexample explaining the necessary conventional hypothesis `eta ≤ 1`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Height-zero arrangements are ordinary additive tuples -/

private def restrictionPointEquiv (N : Nat) : Point N 1 ≃ ZMod N :=
  Equiv.funUnique (Fin 1) (ZMod N)

private noncomputable def restrictionPointImage {N : Nat}
    (A : Finset (Point N 1)) : Finset (ZMod N) :=
  A.map (restrictionPointEquiv N).toEmbedding

private noncomputable def restrictionPointPreimage {N : Nat}
    (A : Finset (ZMod N)) : Finset (Point N 1) :=
  A.map (restrictionPointEquiv N).symm.toEmbedding

@[simp] private lemma restrictionPointImage_mem_iff {N : Nat}
    (A : Finset (Point N 1)) (z : Point N 1) :
    restrictionPointEquiv N z ∈ restrictionPointImage A ↔ z ∈ A := by
  simp [restrictionPointImage]

private lemma restrictionPointImage_preimage {N : Nat}
    (A : Finset (ZMod N)) :
    restrictionPointImage (restrictionPointPreimage A) = A := by
  classical
  ext x
  simp [restrictionPointImage, restrictionPointPreimage]

private lemma restrictionPointPreimage_card {N : Nat}
    (A : Finset (ZMod N)) :
    (restrictionPointPreimage A).card = A.card := by
  classical
  simp [restrictionPointPreimage]

private def restrictionZeroArrangementEquiv (N : Nat) :
    GeneralArrangement N 0 8 ≃ (Fin 16 → ZMod N) where
  toFun R := R.crossSection
  invFun x := (default, default, x)
  left_inv R := by
    exact Prod.ext (Subsingleton.elim _ _)
      (Prod.ext (Subsingleton.elim _ _) rfl)
  right_inv _ := rfl

@[simp] private lemma restrictionPointEquiv_vertex {N : Nat}
    (R : GeneralArrangement N 0 8) (e : Fin 0 → Bool) (j : Fin 16) :
    restrictionPointEquiv N (R.vertex e j) = R.crossSection j := by
  simp [restrictionPointEquiv, GeneralArrangement.vertex, appendCoordinate]

private lemma restrictionZero_isIn_iff {N : Nat} [NeZero N]
    (A : Finset (Point N 1)) (R : GeneralArrangement N 0 8) :
    R.IsIn A ↔ IsAdditiveTuple R.crossSection ∧
      ∀ j, R.crossSection j ∈ restrictionPointImage A := by
  constructor
  · rintro ⟨hadd, hvertices⟩
    refine ⟨hadd, ?_⟩
    intro j
    rw [← restrictionPointEquiv_vertex R (default : Fin 0 → Bool) j,
      restrictionPointImage_mem_iff]
    exact hvertices default j
  · rintro ⟨hadd, hcross⟩
    refine ⟨hadd, ?_⟩
    intro e j
    rw [← restrictionPointImage_mem_iff,
      restrictionPointEquiv_vertex]
    exact hcross j

private lemma restriction_generalArrangementCount_zero {N : Nat} [NeZero N]
    (A : Finset (Point N 1)) :
    generalArrangementCount 8 A =
      additiveTupleCount 8 (restrictionPointImage A) := by
  classical
  unfold generalArrangementCount additiveTupleCount countWhere
  apply Finset.card_equiv (restrictionZeroArrangementEquiv N)
  intro R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [restrictionZero_isIn_iff]
  exact and_comm

private def restrictionPointPhi {N : Nat} (phi : ZMod N → ZMod N) :
    Point N 1 → ZMod N :=
  fun z ↦ phi (restrictionPointEquiv N z)

private lemma restrictionZero_cubeValue {N : Nat} [NeZero N]
    (phi : ZMod N → ZMod N) (R : GeneralArrangement N 0 8) (j : Fin 16) :
    R.cubeValue (restrictionPointPhi phi) j = phi (R.crossSection j) := by
  classical
  unfold GeneralArrangement.cubeValue
  rw [Fintype.sum_unique]
  simp [restrictionPointPhi, boolWeight, countWhere]

private lemma restrictionZero_isRespected_iff {N : Nat} [NeZero N]
    (phi : ZMod N → ZMod N) (R : GeneralArrangement N 0 8) :
    R.IsRespected (restrictionPointPhi phi) ↔
      IsAdditiveTuple (fun j ↦ phi (R.crossSection j)) := by
  unfold GeneralArrangement.IsRespected
  simp_rw [restrictionZero_cubeValue]

private lemma restriction_respectedGeneralArrangementCount_zero
    {N : Nat} [NeZero N] (A : Finset (Point N 1))
    (phi : ZMod N → ZMod N) :
    respectedGeneralArrangementCount 8 A (restrictionPointPhi phi) =
      phiAdditiveTupleCount 8 (restrictionPointImage A) phi := by
  classical
  unfold respectedGeneralArrangementCount phiAdditiveTupleCount countWhere
  apply Finset.card_equiv (restrictionZeroArrangementEquiv N)
  intro R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [restrictionZero_isIn_iff, restrictionZero_isRespected_iff]
  tauto

private def restrictionPairEquiv (G : Type*) :
    ((Fin 8 → G) × (Fin 8 → G)) ≃ (Fin (2 * 8) → G) :=
  (Fin.appendEquiv 8 8).trans
    ((finCongr (Nat.two_mul 8).symm).arrowCongr (Equiv.refl G))

private def restrictionLeftIndex (i : Fin 8) : Fin (2 * 8) :=
  Fin.cast (Nat.two_mul 8).symm (Fin.castAdd 8 i)

private def restrictionRightIndex (i : Fin 8) : Fin (2 * 8) :=
  Fin.cast (Nat.two_mul 8).symm (Fin.natAdd 8 i)

@[simp] private lemma restrictionPairEquiv_left (G : Type*)
    (a b : Fin 8 → G) (i : Fin 8) :
    restrictionPairEquiv G (a, b) (restrictionLeftIndex i) = a i := by
  exact Fin.append_left a b i

@[simp] private lemma restrictionPairEquiv_right (G : Type*)
    (a b : Fin 8 → G) (i : Fin 8) :
    restrictionPairEquiv G (a, b) (restrictionRightIndex i) = b i := by
  exact Fin.append_right a b i

private lemma restriction_leftIndex_mem (i : Fin 8) :
    (restrictionLeftIndex i : Nat) < 8 := by
  simp [restrictionLeftIndex]

private lemma restriction_rightIndex_mem (i : Fin 8) :
    8 ≤ (restrictionRightIndex i : Nat) := by
  simp [restrictionRightIndex]

private lemma restriction_leftIndex_injective :
    Function.Injective restrictionLeftIndex := by
  intro i j hij
  apply Fin.ext
  simpa [restrictionLeftIndex] using congrArg Fin.val hij

private lemma restriction_rightIndex_injective :
    Function.Injective restrictionRightIndex := by
  intro i j hij
  apply Fin.ext
  simpa [restrictionRightIndex] using congrArg Fin.val hij

private lemma restriction_leftIndex_surj (j : Fin (2 * 8))
    (hj : (j : Nat) < 8) : ∃ i : Fin 8, restrictionLeftIndex i = j := by
  refine ⟨⟨j, hj⟩, ?_⟩
  apply Fin.ext
  simp [restrictionLeftIndex]

private lemma restriction_rightIndex_surj (j : Fin (2 * 8))
    (hj : 8 ≤ (j : Nat)) : ∃ i : Fin 8, restrictionRightIndex i = j := by
  refine ⟨⟨(j : Nat) - 8, by omega⟩, ?_⟩
  apply Fin.ext
  simp [restrictionRightIndex]
  omega

private lemma restriction_sum_left {G : Type*} [AddCommMonoid G]
    (a b : Fin 8 → G) :
    (Finset.univ.filter (fun j : Fin (2 * 8) ↦ (j : Nat) < 8)).sum
      (fun j ↦ restrictionPairEquiv G (a, b) j) = ∑ i, a i := by
  symm
  apply Finset.sum_bij (fun i _ ↦ restrictionLeftIndex i)
  · intro i _
    simp [restriction_leftIndex_mem]
  · intro i _ j _ hij
    exact restriction_leftIndex_injective hij
  · intro j hj
    have hjlt : (j : Nat) < 8 := (Finset.mem_filter.mp hj).2
    obtain ⟨i, hi⟩ := restriction_leftIndex_surj j hjlt
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    exact (restrictionPairEquiv_left G a b i).symm

private lemma restriction_sum_right {G : Type*} [AddCommMonoid G]
    (a b : Fin 8 → G) :
    (Finset.univ.filter (fun j : Fin (2 * 8) ↦ 8 ≤ (j : Nat))).sum
      (fun j ↦ restrictionPairEquiv G (a, b) j) = ∑ i, b i := by
  symm
  apply Finset.sum_bij (fun i _ ↦ restrictionRightIndex i)
  · intro i _
    simp [restriction_rightIndex_mem]
  · intro i _ j _ hij
    exact restriction_rightIndex_injective hij
  · intro j hj
    have hjge : 8 ≤ (j : Nat) := (Finset.mem_filter.mp hj).2
    obtain ⟨i, hi⟩ := restriction_rightIndex_surj j hjge
    exact ⟨i, Finset.mem_univ i, hi⟩
  · intro i _
    exact (restrictionPairEquiv_right G a b i).symm

private lemma restrictionPairEquiv_additive {G : Type*} [AddCommMonoid G]
    (a b : Fin 8 → G) :
    IsAdditiveTuple (k := 8) (restrictionPairEquiv G (a, b)) ↔
      (∑ i, a i) = ∑ i, b i := by
  unfold IsAdditiveTuple
  rw [restriction_sum_left, restriction_sum_right]

private def restrictionCompleteRight {G : Type*} [AddCommGroup G]
    (a : Fin 8 → G) (c : Fin 7 → G) : Fin 8 → G :=
  Fin.lastCases ((∑ i, a i) - ∑ i, c i) c

private lemma restrictionCompleteRight_sum {G : Type*} [AddCommGroup G]
    (a : Fin 8 → G) (c : Fin 7 → G) :
    ∑ i, restrictionCompleteRight a c i = ∑ i, a i := by
  rw [Fin.sum_univ_castSucc]
  simp only [restrictionCompleteRight, Fin.lastCases_castSucc,
    Fin.lastCases_last]
  abel

private def restrictionEqualSumEquiv {G : Type*} [AddCommGroup G] :
    ((Fin 8 → G) × (Fin 7 → G)) ≃
      {p : (Fin 8 → G) × (Fin 8 → G) //
        (∑ i, p.1 i) = ∑ i, p.2 i} where
  toFun q := ⟨(q.1, restrictionCompleteRight q.1 q.2),
    (restrictionCompleteRight_sum q.1 q.2).symm⟩
  invFun p := (p.1.1, fun i => p.1.2 i.castSucc)
  left_inv q := by
    rcases q with ⟨a, c⟩
    apply Prod.ext
    · rfl
    · funext i
      simp [restrictionCompleteRight]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · have hp := p.2
        have hb := Fin.sum_univ_castSucc p.1.2
        simp only [restrictionCompleteRight, Fin.lastCases_last]
        rw [hp, hb]
        abel
      · simp [restrictionCompleteRight]

private lemma restriction_equalSumPair_count {G : Type*} [Fintype G]
    [AddCommGroup G] :
    countWhere (fun p : (Fin 8 → G) × (Fin 8 → G) =>
      (∑ i, p.1 i) = ∑ i, p.2 i) = (Fintype.card G) ^ 15 := by
  classical
  let P : ((Fin 8 → G) × (Fin 8 → G)) → Prop :=
    fun p => (∑ i, p.1 i) = ∑ i, p.2 i
  calc
    countWhere P = Fintype.card {p // P p} := by
      unfold countWhere
      exact (Fintype.card_subtype P).symm
    _ = Fintype.card ((Fin 8 → G) × (Fin 7 → G)) :=
      Fintype.card_congr restrictionEqualSumEquiv.symm
    _ = (Fintype.card G) ^ 15 := by
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
      rw [← pow_add]

private lemma restriction_additiveTupleCount_univ {G : Type*} [Fintype G]
    [AddCommGroup G] :
    additiveTupleCount 8 (Finset.univ : Finset G) =
      (Fintype.card G) ^ 15 := by
  classical
  change countWhere (fun x : Fin (2 * 8) → G =>
    (∀ i, x i ∈ (Finset.univ : Finset G)) ∧
      IsAdditiveTuple (k := 8) x) = _
  calc
    countWhere (fun x : Fin (2 * 8) → G =>
        (∀ i, x i ∈ (Finset.univ : Finset G)) ∧
          IsAdditiveTuple (k := 8) x) =
        countWhere (fun p : (Fin 8 → G) × (Fin 8 → G) =>
          (∑ i, p.1 i) = ∑ i, p.2 i) := by
      unfold countWhere
      symm
      apply Finset.card_equiv (restrictionPairEquiv G)
      intro p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using (restrictionPairEquiv_additive p.1 p.2).symm
    _ = (Fintype.card G) ^ 15 := restriction_equalSumPair_count

private lemma restriction_additiveTupleCount_le {G : Type*} [Fintype G]
    [AddCommGroup G] (B : Finset G) :
    additiveTupleCount 8 B ≤ (Fintype.card G) ^ 15 := by
  classical
  calc
    additiveTupleCount 8 B ≤
        additiveTupleCount 8 (Finset.univ : Finset G) := by
      unfold additiveTupleCount countWhere
      apply Finset.card_le_card
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simpa using hx.2
    _ = (Fintype.card G) ^ 15 := restriction_additiveTupleCount_univ

private lemma restriction_phiTupleCount_id_univ {G : Type*} [Fintype G]
    [AddCommGroup G] :
    phiAdditiveTupleCount 8 (Finset.univ : Finset G) (fun x => x) =
      additiveTupleCount 8 (Finset.univ : Finset G) := by
  classical
  unfold phiAdditiveTupleCount additiveTupleCount countWhere
  apply congrArg Finset.card
  ext x
  simp

/-! ### The missing upper bound on `eta` -/

/-- The initially transcribed form of Lemma 9.3, before making the paper's
implicit convention `eta ≤ 1` explicit. -/
private def lemma9_3_without_eta_upper_bound : Prop :=
  ∀ (alpha beta eta : Real), 0 < alpha → 0 < beta → 0 < eta →
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N], N0 ≤ N →
      ∀ (B : Finset (ZMod N)) (phi : ZMod N → ZMod N),
        (B.card : Real) = beta * N →
        alpha * beta ^ 15 * (N : Real) ^ 15 ≤
          phiAdditiveTupleCount 8 B phi →
        ∃ B' : Finset (ZMod N), B' ⊆ B ∧
          (alpha * eta / 4) ^ ((2 : Nat) ^ 19) * beta ^ 15 *
              (N : Real) ^ 15 ≤ additiveTupleCount 8 B' ∧
          GammaHomOfOrder 8 B' phi (1 - eta)

/-- Without `eta ≤ 1`, Lemma 9.3 is false: at `alpha = beta = 1` and
`eta = 8`, its requested tuple lower bound is already larger than the total
number of additive tuples in the ambient cyclic group. -/
theorem lemma9_3_unrestricted_eta_counterexample :
    ¬ lemma9_3_without_eta_upper_bound := by
  intro h
  obtain ⟨N0, hN0⟩ := h 1 1 8 (by norm_num) (by norm_num) (by norm_num)
  let N : Nat := N0 + 1
  letI : NeZero N := ⟨by simp [N]⟩
  obtain ⟨B', _hB', hlarge, _hhom⟩ := hN0 N (by simp [N])
    (Finset.univ : Finset (ZMod N)) (fun x => x) (by
      simp [N, ZMod.card]) (by
      rw [restriction_phiTupleCount_id_univ,
        restriction_additiveTupleCount_univ]
      simp [ZMod.card])
  have hupperNat : additiveTupleCount 8 B' ≤ N ^ 15 := by
    simpa [ZMod.card] using restriction_additiveTupleCount_le B'
  have hupper : (additiveTupleCount 8 B' : Real) ≤ (N : Real) ^ 15 := by
    exact_mod_cast hupperNat
  have hNpos : (0 : Real) < (N : Real) ^ 15 := by
    have : (0 : Real) < N := by exact_mod_cast (show 0 < N by simp [N])
    positivity
  have hcoef : (1 : Real) < 2 ^ ((2 : Nat) ^ 19) :=
    one_lt_pow₀ (by norm_num) (by norm_num)
  have hbase : (1 : Real) * 8 / 4 = 2 := by norm_num
  rw [hbase] at hlarge
  simp only [one_pow, mul_one] at hlarge
  have hstrict : (N : Real) ^ 15 <
      2 ^ ((2 : Nat) ^ 19) * (N : Real) ^ 15 :=
    by simpa only [one_mul] using mul_lt_mul_of_pos_right hcoef hNpos
  exact (not_lt_of_ge hupper) (hstrict.trans_le hlarge)

/-! ### Lemma 9.3 and Corollary 9.4 -/

/-- **Lemma 9.3.** Random restriction upgrades a positive proportion of
respected additive 16-tuples to an approximate homomorphism of order eight. -/
theorem lemma_9_3_holds : lemma_9_3 := by
  unfold lemma_9_3
  intro alpha beta eta halpha hbeta heta heta_one
  obtain ⟨N0, hN0⟩ := lemma_15_5_zero_dimensional_holds
    alpha beta eta halpha hbeta heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN B phi hBcard hrespected
  let A := restrictionPointPreimage B
  have hAcard : (A.card : Real) = beta * N := by
    dsimp only [A]
    rw [restrictionPointPreimage_card]
    exact hBcard
  have hrespected' :
      alpha * beta ^ 15 * (N : Real) ^ 15 ≤
        respectedGeneralArrangementCount 8 A (restrictionPointPhi phi) := by
    rw [restriction_respectedGeneralArrangementCount_zero,
      restrictionPointImage_preimage]
    exact hrespected
  obtain ⟨A', hA'A, hlower, hdensity⟩ :=
    hN0 N hN A (restrictionPointPhi phi) hAcard hrespected'
  let B' := restrictionPointImage A'
  have hB'B : B' ⊆ B := by
    rw [← restrictionPointImage_preimage B]
    exact (Finset.map_subset_map).2 hA'A
  have hlower' :
      (alpha * eta / 4) ^ ((2 : Nat) ^ 19) * beta ^ 15 *
          (N : Real) ^ 15 ≤ additiveTupleCount 8 B' := by
    dsimp only [B']
    rw [← restriction_generalArrangementCount_zero]
    exact hlower
  have hdensity' : GammaHomOfOrder 8 B' phi (1 - eta) := by
    unfold GammaHomOfOrder
    dsimp only [B']
    rw [← restriction_generalArrangementCount_zero,
      ← restriction_respectedGeneralArrangementCount_zero]
    exact hdensity
  exact ⟨B', hB'B, hlower', hdensity'⟩

/-- **Corollary 9.4.** Lemma 9.2 supplies the respected-tuples hypothesis in
Lemma 9.3 with `alpha = gamma^7 * beta^6`. -/
theorem corollary_9_4_holds : corollary_9_4 := by
  unfold corollary_9_4
  intro beta gamma eta hbeta hgamma heta heta_one
  let alpha : Real := gamma ^ 7 * beta ^ 6
  have halpha : 0 < alpha := by
    dsimp only [alpha]
    positivity
  obtain ⟨N0, hN0⟩ := lemma_9_3_holds alpha beta eta
    halpha hbeta heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN B phi hBcard hadditive
  have hmoment :
      (gamma * beta ^ 3) ^ 7 * (N : Real) ^ 15 ≤
        (phiAdditiveTupleCount 8 B phi : Real) :=
    lemma_9_2_holds N B phi (gamma * beta ^ 3) hadditive
  have hrespected :
      alpha * beta ^ 15 * (N : Real) ^ 15 ≤
        phiAdditiveTupleCount 8 B phi := by
    calc
      alpha * beta ^ 15 * (N : Real) ^ 15 =
          (gamma * beta ^ 3) ^ 7 * (N : Real) ^ 15 := by
        dsimp only [alpha]
        ring
      _ ≤ (phiAdditiveTupleCount 8 B phi : Real) := hmoment
  obtain ⟨B', hB'B, hlower, hdensity⟩ :=
    hN0 N hN B phi hBcard hrespected
  refine ⟨B', hB'B, ?_, hdensity⟩
  simpa only [alpha] using hlower

end LeanProofs.GowersSzemeredi
