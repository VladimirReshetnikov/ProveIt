import GowersSzemeredi.Proofs16UniformFaceParameter

/-! Theorem 16.2 with a named modulus threshold, and the face restrictions
of Lemma 16.4 with explicit thresholds.

`Theorem162At k` states its modulus threshold existentially, so lemmas that
consume it only ever see an abstract threshold. `Theorem162AtBounded k T`
states the same conclusion for every prime `N ≥ T gamma theta`. It implies
`Theorem162At k` (`Theorem162AtBounded.theorem162At`). The face restrictions
below repeat `Theorem162At.restrict_function`, `restrict_coordinate_face`,
`restrict_parallel_faces`, `restrict_finite_parallel_directions`,
`restrict_all_positive_proper_faces`, `restrict_proper_faces_half_density`
and `restrict_proper_faces_common_parameter` with that hypothesis. Each
returns an explicit threshold: the input threshold itself, or a finite sum
over coordinate directions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Theorem 16.2 in dimension `k` with modulus threshold `T gamma theta`. -/
def Theorem162AtBounded (k : Nat) (T : Real → Real → Real) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], T gamma theta ≤ (N : Real) →
      ∀ Gamma : Finset (Point N k × ZMod N),
        (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ k →
        RelationProductProperty gamma Gamma →
        ∃ J : Finset (Point N k),
          (1 - theta) * (N : Real) ^ k ≤ J.card ∧
          MultiplyLinear gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma k)
            (restrictRelation Gamma J)

theorem Theorem162AtBounded.theorem162At {k : Nat} {T : Real → Real → Real}
    (h : Theorem162AtBounded k T) : Theorem162At k := by
  intro gamma theta hg hg1 ht ht1
  exact ⟨⌈T gamma theta⌉₊, fun N _ _ hN =>
    h gamma theta hg hg1 ht ht1 N ((Nat.le_ceil _).trans (by exact_mod_cast hN))⟩

theorem Theorem162AtBounded.mono {k : Nat} {T T' : Real → Real → Real}
    (h : Theorem162AtBounded k T) (hT : ∀ gamma theta, T gamma theta ≤ T' gamma theta) :
    Theorem162AtBounded k T' := fun gamma theta hg hg1 ht ht1 N _ _ hN =>
  h gamma theta hg hg1 ht ht1 N ((hT gamma theta).trans hN)

/-- `Theorem162At.restrict_function` with the threshold of the hypothesis. -/
theorem Theorem162AtBounded.restrict_function {l : Nat} {T : Real → Real → Real}
    (hth : Theorem162AtBounded l T)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], T gamma theta ≤ (N : Real) →
      ∀ (B : Finset (Point N l)) (phi : Point N l → ZMod N),
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N l), B' ⊆ B ∧
          (B.card : Real) - theta * (N : Real) ^ l ≤ B'.card ∧
          MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma l) B' phi := by
  intro N _ _ hN B phi hprod
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hB : (B.card : Real) ≤ (N : Real) ^ l := by
    exact_mod_cast (show B.card ≤ N ^ l by simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hgraph : ((partialGraph B phi).card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ l := by
    rw [partialGraph_card]
    exact hB.trans (le_mul_of_one_le_left (by positivity) hginv)
  obtain ⟨J, hJ, hcover⟩ := hth gamma theta hg hg1 ht ht1 N hN (partialGraph B phi) hgraph
    (partialGraph_relationProductProperty hprod)
  refine ⟨B ∩ J, Finset.inter_subset_left, ?_, ?_⟩
  · have hsum : ((B ∪ J).card : Real) + (B ∩ J).card = B.card + J.card := by
      exact_mod_cast Finset.card_union_add_card_inter B J
    have hunion : ((B ∪ J).card : Real) ≤ (N : Real) ^ l := by
      exact_mod_cast (show (B ∪ J).card ≤ N ^ l by
        simpa [Point, ZMod.card] using Finset.card_le_univ (B ∪ J))
    linarith
  · rw [restrictRelation_partialGraph] at hcover
    exact hcover

/-- `Theorem162At.restrict_coordinate_face` with the threshold of the hypothesis. -/
theorem Theorem162AtBounded.restrict_coordinate_face {l : Nat} {T : Real → Real → Real}
    (hth : Theorem162AtBounded l T)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N d : Nat) [NeZero N] [Fact N.Prime], T gamma theta ≤ (N : Real) →
      ∀ (B : Finset (Point N d)) (phi : Point N d → ZMod N),
        HasProductProperty B phi gamma → ∀ F : CoordinateFace N d l,
          ∃ B' : Finset (Point N l), B' ⊆ F.domain B ∧
            ((F.domain B).card : Real) - theta * (N : Real) ^ l ≤ B'.card ∧
            MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma l)
              B' (F.pullback phi) :=
  fun N _ _ _ hN B phi hprod F =>
    hth.restrict_function gamma theta hg hg1 ht ht1 N hN (F.domain B) (F.pullback phi)
      (hprod.coordinateFace F)

/-- `Theorem162At.restrict_parallel_faces` with the threshold of the hypothesis. -/
theorem Theorem162AtBounded.restrict_parallel_faces {l : Nat} {T : Real → Real → Real}
    (hth : Theorem162AtBounded l T)
    (gamma theta : Real) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N d r : Nat) [NeZero N] [Fact N.Prime], T gamma theta ≤ (N : Real) →
      ∀ (e : Fin d ≃ Fin l ⊕ Fin r) (B : Finset (Point N d))
        (phi : Point N d → ZMod N), HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N d), B' ⊆ B ∧
          (B.card : Real) - theta * (N : Real) ^ d ≤ B'.card ∧
          ∀ z : Point N r,
            MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma l)
              ((splitCoordinateFace e z).domain B') ((splitCoordinateFace e z).pullback phi) := by
  classical
  intro N d r _ _ hN e B phi hprod
  choose C hCsub hCloss hCcover using
    (fun z : Point N r => hth.restrict_coordinate_face gamma theta hg hg1 ht ht1 N d hN B phi
      hprod (splitCoordinateFace e z))
  refine ⟨parallelFaceUnion e C, parallelFaceUnion_subset e B C hCsub, ?_, ?_⟩
  · have hdim : d = l + r := by
      simpa using Fintype.card_congr e
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun z (_ : z ∈ (Finset.univ : Finset (Point N r))) => hCloss z)
    have hBsum : (∑ z : Point N r, (((splitCoordinateFace e z).domain B).card : Real)) =
        B.card := by
      exact_mod_cast sum_coordinateFace_card e B
    have hCsum : (∑ z : Point N r, ((C z).card : Real)) = (parallelFaceUnion e C).card := by
      exact_mod_cast (parallelFaceUnion_card e C).symm
    rw [Finset.sum_sub_distrib, hBsum, hCsum] at hsum
    have hvol : (∑ _z : Point N r, theta * (N : Real) ^ l) = theta * (N : Real) ^ d := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hc : (Fintype.card (Point N r) : Real) = (N : Real) ^ r := by
        simp [Point, ZMod.card]
      rw [hc, hdim, pow_add]
      ring
    rwa [hvol] at hsum
  · intro z
    rw [splitCoordinateFace_domain_union]
    exact hCcover z

/-- `restrict_finite_parallel_directions` with threshold
`∑ i, max 0 (T i gamma theta)`. -/
theorem restrict_finite_parallel_directions_bounded {I : Type*} [Fintype I]
    (d : Nat) (l r : I → Nat) (e : ∀ i, Fin d ≃ Fin (l i) ⊕ Fin (r i))
    (T : I → Real → Real → Real)
    (hth : ∀ i, Theorem162AtBounded (l i) (T i)) (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], (∑ i, max 0 (T i gamma theta)) ≤ (N : Real) →
      ∀ (B : Finset (Point N d)) (phi : Point N d → ZMod N),
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N d), B' ⊆ B ∧
          (B.card : Real) - (Fintype.card I : Real) * theta * (N : Real) ^ d ≤ B'.card ∧
          ∀ (i : I) (z : Point N (r i)),
            MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma (l i))
              ((splitCoordinateFace (e i) z).domain B')
              ((splitCoordinateFace (e i) z).pullback phi) := by
  classical
  intro N _ _ hN B phi hprod
  let P := fun i (C : Finset (Point N d)) => ∀ z : Point N (r i),
    MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma (l i))
      ((splitCoordinateFace (e i) z).domain C) ((splitCoordinateFace (e i) z).pullback phi)
  have hmono : ∀ i, ∀ C D, D ⊆ C → P i C → P i D := by
    intro i C D hDC hC z
    exact (hC z).mono ((splitCoordinateFace (e i) z).domain_mono hDC)
  have hstep : ∀ i ∈ (Finset.univ : Finset I), ∀ C, HasProductProperty C phi gamma →
      ∃ D, D ⊆ C ∧ (C.card : Real) - theta * (N : Real) ^ d ≤ D.card ∧ P i D := by
    intro i _ C hC
    have hi : T i gamma theta ≤ (N : Real) :=
      (le_max_right 0 _).trans ((Finset.single_le_sum
        (fun j _ => le_max_left 0 (T j gamma theta)) (Finset.mem_univ i)).trans hN)
    exact (hth i).restrict_parallel_faces gamma theta hg hg1 ht ht1 N d (r i) hi (e i) C phi hC
  obtain ⟨C, hCB, hcard, hC⟩ := hprod.restrict_finite_family Finset.univ P
    (fun _ => theta * (N : Real) ^ d) hmono hstep
  refine ⟨C, hCB, ?_, fun i => hC i (Finset.mem_univ i)⟩
  simpa [mul_assoc] using hcard

/-- The face threshold: one summand per proper coordinate direction, each
the threshold of the face dimension at the face parameter. -/
def section16FaceThreshold (d : Nat) (T : Nat → Real → Real → Real)
    (gamma eps : Real) : Real :=
  ∑ s : ProperCoordinateDirection d, max 0 (T s.val.card gamma eps)

/-- `restrict_all_positive_proper_faces` with an explicit threshold. -/
theorem restrict_all_positive_proper_faces_bounded (d : Nat)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l, 0 < l → l < d → Theorem162AtBounded l (T l)) (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime], section16FaceThreshold d T gamma theta ≤ (N : Real) →
      ∀ (B : Finset (Point N d)) (phi : Point N d → ZMod N),
        HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N d), B' ⊆ B ∧
          (B.card : Real) - (2 : Real) ^ d * theta * (N : Real) ^ d ≤ B'.card ∧
          ∀ (l : Nat), 0 < l → l < d → ∀ F : CoordinateFace N d l,
            MultiplyLinearFunction gamma (gamma ^ (-(2 : Int)) * multipleS theta gamma l)
              (F.domain B') (F.pullback phi) := by
  classical
  intro N _ _ hN B phi hprod
  obtain ⟨B', hsub, hcard, hfaces⟩ := restrict_finite_parallel_directions_bounded
    (I := ProperCoordinateDirection d) d (fun s => s.val.card) (fun s => s.valᶜ.card)
    (fun s => coordinateDirectionSplit s.val) (fun s => T s.val.card)
    (fun s => hth s.val.card s.property.1 s.property.2) gamma theta hg hg1 ht ht1 N hN
    B phi hprod
  refine ⟨B', hsub, ?_, ?_⟩
  · have hcost : (Fintype.card (ProperCoordinateDirection d) : Real) * theta * (N : Real) ^ d ≤
        (2 : Real) ^ d * theta * (N : Real) ^ d := by
      gcongr
      exact_mod_cast properCoordinateDirection_card_le d
    linarith
  · intro l hl hld F
    let s : ProperCoordinateDirection d := ⟨F.direction, by simpa using And.intro hl hld⟩
    obtain ⟨e, z, hmap⟩ := F.parallel_reparametrization
    have hh := F.multiplyLinear_of_reparametrization
      (splitCoordinateFace (coordinateDirectionSplit F.direction) z) e hmap (hfaces s z)
    simpa only [s, CoordinateFace.direction_card] using hh

/-- `restrict_proper_faces_half_density` with an explicit threshold. -/
theorem restrict_proper_faces_half_density_bounded (k : Nat)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l)) (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      section16FaceThreshold (k + 1) T gamma ((2 : Real) ^ (-(k + 2 : Real)) * theta) ≤
        (N : Real) →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        theta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (theta / 2) * (N : Real) ^ (k + 1) ≤ B'.card ∧
          ∀ l, 1 ≤ l → l ≤ k → ∀ F : CoordinateFace N (k + 1) l,
            MultiplyLinearFunction gamma
              (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma l)
              (F.domain B') (F.pullback phi) := by
  let eps := (2 : Real) ^ (-(k + 2 : Real)) * theta
  have hpow : (2 : Real) ^ (-(k + 2 : Real)) = ((2 : Real) ^ (k + 2))⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    congr 1
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (Real.rpow_natCast (2 : Real) (k + 2))
  have heps : 0 < eps := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) ht
  have heps1 : eps ≤ 1 := by
    have hfac : (2 : Real) ^ (-(k + 2 : Real)) ≤ 1 := by
      rw [hpow]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    exact (mul_le_of_le_one_left ht.le hfac).trans ht1
  have hbudget : (2 : Real) ^ (k + 1) * eps = theta / 2 := by
    dsimp [eps]
    rw [hpow, show k + 2 = (k + 1) + 1 by omega, pow_succ]
    field_simp
    simp [pow_succ, mul_assoc]
  intro N _ _ hN B phi hB hprod
  obtain ⟨B', hsub, hcard, hfaces⟩ := restrict_all_positive_proper_faces_bounded (k + 1) T
    (fun l hl hlk => hth l hl (by omega)) gamma eps hg hg1 heps heps1 N hN B phi hprod
  refine ⟨B', hsub, ?_, fun l hl hlk F => hfaces l hl (by omega) F⟩
  rw [hbudget] at hcard
  linarith

/-- `restrict_proper_faces_common_parameter` with an explicit threshold. -/
theorem restrict_proper_faces_common_parameter_bounded (k : Nat)
    (T : Nat → Real → Real → Real)
    (hth : ∀ l, 1 ≤ l → l ≤ k → Theorem162AtBounded l (T l)) (gamma theta : Real)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (N : Nat) [NeZero N] [Fact N.Prime],
      section16FaceThreshold (k + 1) T gamma ((2 : Real) ^ (-(k + 2 : Real)) * theta) ≤
        (N : Real) →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        theta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (theta / 2) * (N : Real) ^ (k + 1) ≤ B'.card ∧
          ProperCrossSectionsMultiplyLinear gamma
            (gamma ^ (-(2 : Int)) * multipleS ((2 : Real) ^ (-(k + 2 : Real)) * theta) gamma k)
            B' phi := by
  let eps := (2 : Real) ^ (-(k + 2 : Real)) * theta
  obtain ⟨heps, heps1⟩ := section16_face_error_range k ht ht1
  have hginv : 1 ≤ gamma ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    exact (one_le_inv₀ (pow_pos hg 2)).mpr (pow_le_one₀ hg.le hg1)
  have hr : ∀ l, 1 ≤ gamma ^ (-(2 : Int)) * multipleS eps gamma l := by
    intro l
    exact one_le_mul_of_one_le_of_one_le hginv (one_le_multipleS l heps heps1 hg hg1)
  intro N _ _ hN B phi hB hprod
  obtain ⟨B', hsub, hcard, hfaces⟩ :=
    restrict_proper_faces_half_density_bounded k T hth gamma theta hg hg1 ht ht1 N hN
      B phi hB hprod
  refine ⟨B', hsub, hcard, ?_⟩
  intro l hl F
  by_cases hl0 : l = 0
  · subst l
    exact multiplyLinearFunction_dimension_zero (F.domain B') (F.pullback phi) hg hg1 (hr k)
  · have hl1 : 1 ≤ l := by omega
    have hlk : l ≤ k := by omega
    apply (hfaces l hl1 hlk F).mono_parameter hg hg1 (hr l)
    exact mul_le_mul_of_nonneg_left (multipleS_mono_dimension heps heps1 hg hg1 hlk)
      (by positivity)

end LeanProofs.GowersSzemeredi
