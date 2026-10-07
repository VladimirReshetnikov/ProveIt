/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerCommonSideInitializationUniform
import OAI.Combinatorics.Progressions.Estimates.CommonSideExponentialAbsorption
import OAI.Combinatorics.Progressions.Estimates.EmptyLayerPrescribedScale
import OAI.Combinatorics.Progressions.Nilpotent.UnconditionedScalarScaleNiltestBase
import OAI.Combinatorics.Progressions.Polynomial.AllocatedZeroLayerDegreeScalarConclusion
import OAI.Combinatorics.Progressions.Probability.AllocatedZeroLayerInitializationMassLoss

namespace OAI

section

namespace Erdos3

theorem exists_allocatedZeroLayerInitialization_power_budget
    (s n₀ Cinit : ℕ) (extra : ℝ) (hextra : 0 ≤ extra) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (p : ℝ), 2 ≤ p →
      let q := p + extra + (n₀ : ℝ) + 2
      let b := (p + 2) ^ C
      p + extra ≤ b ∧ (q + 2) ^ Cinit ≤ b ∧
      Real.exp (-b) ≤ Real.exp (-((q + 2) ^ Cinit)) ∧
      ∀ D : ℕ, D ≤ ⌊p + extra⌋₊ →
        (D : ℝ) ≤ b ∧
        Real.exp (-b) ≤
          ((Real.exp (-p) / 4) / (((D + 1) * (s + 1) ^ D : ℕ) : ℝ)) *
            Real.exp (-((q + 2) ^ Cinit)) := by
  let E : ℕ := ⌈extra⌉₊
  let rankPoly : Polynomial ℕ := Polynomial.X + Polynomial.C E
  let depth : Polynomial ℕ := (Polynomial.X + Polynomial.C (E + n₀ + 4)) ^ Cinit
  let massLog : Polynomial ℕ :=
    depth + Polynomial.X + rankPoly + 5 + rankPoly * Polynomial.C (s + 1)
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_fixed_power_budget (rankPoly + depth + massLog)
  refine ⟨C, hC, ?_⟩
  intro p hp q b
  let r : ℝ := p + E
  let L : ℝ := (p + E + n₀ + 4) ^ Cinit
  let T : ℝ := L + p + r + 5 + r * (s + 1)
  have hp0 : 0 ≤ p := by linarith
  have hE : extra ≤ (E : ℝ) := Nat.le_ceil extra
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hbudget' : r + L + T ≤ b := by
    simpa [rankPoly, depth, massLog, Polynomial.eval₂_pow, r, L, T, b,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc] using hbudget p hp0
  have hrb : r ≤ b := by linarith
  have hLb : L ≤ b := by linarith
  have hTb : T ≤ b := by linarith
  have hcost : p + extra ≤ r := by dsimp only [r]; linarith
  have hnorm : (q + 2) ^ Cinit ≤ L := by
    apply pow_le_pow_left₀
      (by dsimp only [q]; positivity)
      (by dsimp only [q]; linarith)
  have hnormalization : (q + 2) ^ Cinit ≤ b := hnorm.trans hLb
  refine ⟨hcost.trans hrb, hnormalization,
    Real.exp_le_exp.mpr (neg_le_neg hnormalization), ?_⟩
  intro D hD
  have hDr : (D : ℝ) ≤ p + extra :=
    (Nat.cast_le.mpr hD).trans (Nat.floor_le (add_nonneg hp0 hextra))
  refine ⟨hDr.trans (hcost.trans hrb), ?_⟩
  have hmassLog : (q + 2) ^ Cinit + p + (p + extra) + 5 +
      (p + extra) * (s + 1) ≤ T := by
    have hmul := mul_le_mul_of_nonneg_right hcost (show (0 : ℝ) ≤ s + 1 by positivity)
    dsimp only [T]
    linarith
  exact (Real.exp_le_exp.mpr (neg_le_neg (hmassLog.trans hTb))).trans
    (allocatedZeroLayerInitialization_mass_loss s D p (p + extra)
      ((q + 2) ^ Cinit) hDr)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

def unconditionedCommonSide {n : ℕ} (P : Fin n → ℕ) : ℕ := 1 + ∑ i, P i

theorem unconditionedCommonSide_pos {n : ℕ} (P : Fin n → ℕ) :
    0 < unconditionedCommonSide P := by
  unfold unconditionedCommonSide
  omega

theorem le_unconditionedCommonSide {n : ℕ} (P : Fin n → ℕ) (j : Fin n) :
    P j ≤ unconditionedCommonSide P := by
  have hsum : P j ≤ ∑ i, P i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold unconditionedCommonSide
  omega

theorem unconditionedCommonSide_le {n : ℕ} (P : Fin n → ℕ)
    (hpos : ∀ i, 0 < P i) (hcompare : ∀ i j, P i ≤ 2 ^ (n + 1) * P j)
    (j : Fin n) :
    unconditionedCommonSide P ≤ (1 + n * 2 ^ (n + 1)) * P j := by
  have hsum : (∑ i, P i) ≤ n * (2 ^ (n + 1) * P j) := by
    calc
      _ ≤ ∑ _i : Fin n, 2 ^ (n + 1) * P j := Finset.sum_le_sum (fun i _ => hcompare i j)
      _ = _ := by simp
  calc
    unconditionedCommonSide P = 1 + ∑ i, P i := rfl
    _ ≤ P j + n * (2 ^ (n + 1) * P j) := Nat.add_le_add (hpos j) hsum
    _ = _ := by ring

@[simp] theorem unconditionedCommonSide_cast {n : ℕ} (P : Fin n → ℕ) :
    (unconditionedCommonSide P : ℝ) = 1 + unconditionedResidueSiteBound P := by
  simp [unconditionedCommonSide, unconditionedResidueSiteBound]

theorem unconditionedCommonSide_density {n : ℕ} (P : Fin n → ℕ)
    (hpos : ∀ i, 0 < P i) (hcompare : ∀ i j, P i ≤ 2 ^ (n + 1) * P j) :
    1 / ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) ^ n ≤
      (∏ i, (P i : ℝ)) / (unconditionedCommonSide P : ℝ) ^ n := by
  have hside : 0 < (unconditionedCommonSide P : ℝ) :=
    Nat.cast_pos.mpr (unconditionedCommonSide_pos P)
  have hfactor : 0 < ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) := by positivity
  have hprod : (unconditionedCommonSide P : ℝ) ^ n ≤
      ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) ^ n * ∏ i, (P i : ℝ) := by
    calc
      _ = ∏ _i : Fin n, (unconditionedCommonSide P : ℝ) := by simp
      _ ≤ ∏ i : Fin n, ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) * (P i : ℝ) := by
        apply Finset.prod_le_prod₀ (fun _ _ => hside.le)
        intro i _
        exact_mod_cast unconditionedCommonSide_le P hpos hcompare i
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  apply (div_le_div_iff₀ (pow_pos hfactor _) (pow_pos hside _)).mpr
  simpa only [one_mul, mul_one, mul_comm] using hprod

theorem unconditionedCommonSide_root_budget {n : ℕ} (P : Fin n → ℕ) :
    1 + (n : ℝ) * (unconditionedCommonSide P : ℝ) ≤
      ((n : ℝ) + 1) * (1 + unconditionedResidueSiteBound P) := by
  rw [unconditionedCommonSide_cast]
  have hB : 0 ≤ unconditionedResidueSiteBound P :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  nlinarith

theorem unconditionedSpatialWidthCutoff_common_side_le {n : ℕ} (P : Fin n → ℕ)
    {τ L : ℝ} (hτ : 0 < τ) :
    unconditionedSpatialWidthCutoff ((n : ℝ) * (unconditionedCommonSide P : ℝ)) τ L ≤
      ((n : ℝ) + 1) *
        unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P) τ L := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hfactor : 0 ≤ (n : ℝ) + 1 := by positivity
  have hmax : 0 ≤ max (8 * (probabilityProfileLipschitz : ℝ)) L :=
    (by positivity : 0 ≤ 8 * (probabilityProfileLipschitz : ℝ)).trans (le_max_left _ _)
  unfold unconditionedSpatialWidthCutoff
  apply max_le
  · calc
      4 / τ ≤ ((n : ℝ) + 1) * (4 / τ) := by
        nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hτ.le,
          mul_nonneg hn (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hτ.le)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) hfactor
  · calc
      _ ≤ 8 * (((n : ℝ) + 1) * (1 + unconditionedResidueSiteBound P)) *
          max (8 * (probabilityProfileLipschitz : ℝ)) L / τ := by
        apply div_le_div_of_nonneg_right _ hτ.le
        apply mul_le_mul_of_nonneg_right _ hmax
        exact mul_le_mul_of_nonneg_left (unconditionedCommonSide_root_budget P) (by norm_num)
      _ = ((n : ℝ) + 1) * (8 * (1 + unconditionedResidueSiteBound P) *
          max (8 * (probabilityProfileLipschitz : ℝ)) L / τ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right _ _) hfactor

theorem exists_unconditioned_late_prime_common_side_budget (n : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (p t : ℝ), 2 ≤ p → p ≤ t →
      ∃ (P : Fin n → ℕ) (hprime : ∀ i, (P i).Prime) (S : ℕ),
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n + 1) * P j) ∧
        (∀ i, Real.exp t ≤ (P i : ℝ) ∧ (P i : ℝ) ≤ Real.exp (t + (n : ℝ) + 2)) ∧
        (∀ i, Real.exp p ≤ (P i : ℝ)) ∧
        S = 1 + ∑ i, P i ∧ 0 < S ∧ (∀ i, P i ≤ S) ∧
        (∀ i, S ≤ (1 + n * 2 ^ (n + 1)) * P i) ∧
        1 / ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) ^ n ≤
          (∏ i, (P i : ℝ)) / (S : ℝ) ^ n ∧
        ∀ d : ℕ, (d : ℝ) ≤ p →
          let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
          unconditionedSpatialWidthCutoff ((n : ℝ) * (S : ℝ))
            (unconditionedSpatialTrimFraction d (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((t + 2) ^ E) := by
  obtain ⟨E, hE, hchoose⟩ := exists_unconditioned_late_prime_side_budget n
  refine ⟨E + n + 3, by omega, ?_⟩
  intro p t hp hpt
  obtain ⟨P, hprime, hinj, hcompare, hrange, hearly, hcutoff⟩ := hchoose p t hp hpt
  refine ⟨P, hprime, unconditionedCommonSide P, hinj, hcompare, hrange, hearly, rfl,
    unconditionedCommonSide_pos P, le_unconditionedCommonSide P,
    unconditionedCommonSide_le P (fun i => (hprime i).pos) hcompare,
    unconditionedCommonSide_density P (fun i => (hprime i).pos) hcompare, ?_⟩
  intro d hd
  let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
  have hτ : 0 < unconditionedSpatialTrimFraction d (Real.exp (-p)) := by
    unfold unconditionedSpatialTrimFraction
    positivity
  exact (unconditionedSpatialWidthCutoff_common_side_le P hτ).trans
    ((mul_le_mul_of_nonneg_left (hcutoff d hd) (by positivity)).trans
      (commonSide_exp_absorption n E (by linarith : 0 ≤ t)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def unconditionedCommonSideScalarRatio (n : ℕ) : ℕ :=
  1 + n * unconditionedScalarPrimeRatio n

theorem unconditionedCommonSide_scalar_bound {n : ℕ} (P : Fin n → ℕ)
    {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ j, (P j : ℝ) ≤ (unconditionedScalarPrimeRatio n : ℝ) * Real.exp t) :
    (unconditionedCommonSide P : ℝ) ≤
      (unconditionedCommonSideScalarRatio n : ℝ) * Real.exp t := by
  have hsum : unconditionedResidueSiteBound P ≤
      (n : ℝ) * ((unconditionedScalarPrimeRatio n : ℝ) * Real.exp t) := by
    calc
      _ ≤ ∑ _j : Fin n, (unconditionedScalarPrimeRatio n : ℝ) * Real.exp t :=
        Finset.sum_le_sum (fun j _ => hP j)
      _ = _ := by simp
  rw [unconditionedCommonSide_cast]
  unfold unconditionedCommonSideScalarRatio
  push_cast
  nlinarith [Real.one_le_exp_iff.mpr ht]

theorem unconditionedCommonSide_scalar_bound_of_range {n : ℕ} (P : Fin n → ℕ)
    {t : ℝ} (ht : 0 ≤ t)
    (hP : ∀ j, (P j : ℝ) ≤ Real.exp (t + (n : ℝ) + 2)) :
    (unconditionedCommonSide P : ℝ) ≤
      (unconditionedCommonSideScalarRatio n : ℝ) * Real.exp t :=
  unconditionedCommonSide_scalar_bound P ht
    (fun j => (hP j).trans (unconditionedScalarPrimeRatio_exp_bound n t))

noncomputable def unconditionedCommonSideExtra (n : ℕ) : ℝ :=
  Real.log ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ)

theorem unconditionedCommonSideExtra_nonneg (n : ℕ) :
    0 ≤ unconditionedCommonSideExtra n := by
  apply Real.log_nonneg
  exact_mod_cast (by omega : 1 ≤ 1 + n * 2 ^ (n + 1))

@[simp] theorem exp_unconditionedCommonSideExtra (n : ℕ) :
    Real.exp (unconditionedCommonSideExtra n) = ((1 + n * 2 ^ (n + 1) : ℕ) : ℝ) := by
  exact Real.exp_log (by positivity)

theorem unconditionedCommonSide_le_exp_extra_mul {n : ℕ} (P : Fin n → ℕ)
    (hpos : ∀ j, 0 < P j) (hcompare : ∀ i j, P i ≤ 2 ^ (n + 1) * P j)
    (j : Fin n) :
    (unconditionedCommonSide P : ℝ) ≤
      Real.exp (unconditionedCommonSideExtra n) * (P j : ℝ) := by
  rw [exp_unconditionedCommonSideExtra]
  exact_mod_cast unconditionedCommonSide_le P hpos hcompare j

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_allocatedZeroLayer_budgeted_initialization (s n₀ : ℕ) :
    ∃ Cshape Cinput : ℕ, 2 ≤ Cshape ∧ Cshape ≤ Cinput ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∀ (S : LayerSamplerScale (G := G) B U b R σ)
      (_eG : G ≃ Fin n₀)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : X)
      {p a Λ : ℝ},
      2 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      (∀ j, P j ≤ S.value) →
      (∀ j, (S.value : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n₀) * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
      (∀ x, unconditionedSpatialWidthCutoff
        ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
        (unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p)))
        (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N x : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + (Real.exp (-p)) ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) (Real.exp (-p))
      let shape := (p + 2) ^ Cshape
      let input := (p + 2) ^ Cinput
      ∃ (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
          N poly hm τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
        d ≤ d₀ ∧ (d : ℝ) ≤ shape ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp shape ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ shape) ∧
        letI := polynomialShearIndexFintype patch.weight patch.weight_pos
        ∀ [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
          [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)],
        ∃ M : ℝ≥0, patch.ExternalObservableRegularity M input ∧
        ∃ Q : AllocatedExternalCandidateProblem (E := E) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          input (Real.exp (-input)) (Real.exp (-input)),
          Q.centerLift = allocatedZeroLayerCenterLift U ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  obtain ⟨Cinit, _, hinit⟩ := exists_allocatedZeroLayer_commonSide_initialization_uniform s
  obtain ⟨Cshape, hCshape, hbudget⟩ := exists_allocatedZeroLayerInitialization_power_budget
    s n₀ Cinit (unconditionedCommonSideExtra n₀) (unconditionedCommonSideExtra_nonneg n₀)
  obtain ⟨Cobs, hCobs, hobs⟩ := exists_polynomialPatch_external_observable_budget s
  let Cinput := (Cshape + 1) * Cobs
  have hshapeInput : Cshape ≤ Cinput := by
    dsimp only [Cinput]
    exact (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ (by omega))
  refine ⟨Cshape, Cinput, hCshape, hshapeInput, ?_⟩
  intro G X _ _ I E J _ _ n B _ U b R σ hb o hR hσ poly hm _ S eG P _ i
    p a Λ hp ha hΛ hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff
    N hN f hf hfree hmean τ shape input
  have hp0 : 0 ≤ p := by linarith
  have hsurplus1 : Real.exp (-p) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hvars : Fintype.card (LayerSamplerVariables G I n B) = n₀ := by
    rw [zeroLayerVariables_card]
    exact (Fintype.card_congr eG).trans (Fintype.card_fin n₀)
  have hsource := hinit (E := E) B U b hb o hR hσ poly hm S n₀ eG P i hp0 ha hΛ
    (Real.exp_pos _) hsurplus1 (unconditionedCommonSideExtra_nonneg n₀)
    hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  dsimp only at hsource
  rw [hvars] at hsource
  obtain ⟨A, d, patch, hd, hdD, hLip, hcenter, hproblem⟩ := hsource
  let : Fintype (PolynomialShearIndex patch.weight) := polynomialShearIndexFintype patch.weight patch.weight_pos
  obtain ⟨Pinit, hcenterLift, hkeep⟩ := hproblem
  have hb := hbudget p hp
  dsimp only at hb
  have hdFloor : d ≤ ⌊p + unconditionedCommonSideExtra n₀⌋₊ := hdD.trans (Nat.min_le_right _ _)
  have hrank : (d : ℝ) ≤ shape := (hb.2.2.2 d hdFloor).1
  have hshape0 : 0 ≤ shape := pow_nonneg (by linarith) _
  have hshape1 : 1 ≤ shape := one_le_pow₀ (by linarith : 1 ≤ p + 2)
  have hshapeLe : shape ≤ input := pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hshapeInput
  have hshift : shape + 2 ≤ (p + 2) ^ (Cshape + 1) := by
    rw [pow_succ']
    change shape + 2 ≤ (p + 2) * shape
    nlinarith
  have hobsLe : (shape + 2) ^ Cobs ≤ input := by
    calc
      _ ≤ ((p + 2) ^ (Cshape + 1)) ^ Cobs := pow_le_pow_left₀ (by positivity) hshift _
      _ = input := by dsimp only [input, Cinput]; rw [pow_mul]
  have hLipShape : (patch.kernel.lip : ℝ) ≤ Real.exp shape :=
    hLip.trans (Real.exp_le_exp.mpr hb.2.1)
  have hcenterShape : ∀ j, realPolynomialMass (patch.form.center j) ≤ shape :=
    fun j => (hcenter j).trans hb.2.1
  refine ⟨A, d, patch, hd, hrank, hLipShape, hcenterShape, ?_⟩
  intro _ _ _ _
  have hregularity := PolynomialPatch.ExternalObservableRegularity.mono patch
    (hobs patch shape hshape0 hrank hcenterShape hLipShape) hobsLe
  let D := min d₀ ⌊p + unconditionedCommonSideExtra n₀⌋₊
  have hmass := (hb.2.2.2 D (Nat.min_le_right _ _)).2
  have he : Real.exp (-input) ≤ Real.exp (-shape) := Real.exp_le_exp.mpr (neg_le_neg hshapeLe)
  let ref := Pinit.budgetRefinement (hb.1.trans hshapeLe) (he.trans hmass) (he.trans hb.2.2.1)
  refine ⟨⟨shape, hshape0⟩, hregularity, ref.problem, ?_, ?_⟩
  · exact hcenterLift
  · exact hkeep

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

namespace CanonicalEmptyLayerGeometry

noncomputable def zeroLayerScale (G : Type) [Fintype G] (side : ℕ) (hside : 0 < side) :
    LayerSamplerScale (G := G) (B 0) (U 0) (b 0) (fun _ => 1) (fun _ => 1) :=
  emptyLayerSamplerScale (B 0) (U 0) (b 0) side hside (fun j => Fin.elim0 j)

@[simp] theorem zeroLayerScale_value (G : Type) [Fintype G] (side : ℕ) (hside : 0 < side) :
    (zeroLayerScale G side hside).value = side := rfl

theorem zeroLayer_one_pos (j : Fin 0) : (0 : ℝ) < 1 := Fin.elim0 j

end CanonicalEmptyLayerGeometry

local notation "C0" => CanonicalEmptyLayerGeometry.B 0
local notation "U0" => CanonicalEmptyLayerGeometry.U 0
local notation "b0" => CanonicalEmptyLayerGeometry.b 0
local notation "hb0" => CanonicalEmptyLayerGeometry.hb 0
local notation "o0" => CanonicalEmptyLayerGeometry.o 0
local notation "pos0" => CanonicalEmptyLayerGeometry.zeroLayer_one_pos

theorem exists_canonicalZeroLayer_budgeted_initialization (s n₀ : ℕ) :
    ∃ Cshape Cinput : ℕ, 2 ≤ Cshape ∧ Cshape ≤ Cinput ∧
    ∀ (nX side : ℕ) (hside : 0 < side)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : Fin nX)
      {p a Λ : ℝ},
      2 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      (∀ j, P j ≤ side) →
      (∀ j, (side : ℝ) ≤ Real.exp (unconditionedCommonSideExtra n₀) * (P j : ℝ)) →
      ∀ d₀ : ℕ, RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ N : Fin nX → ℕ,
      (∀ x, unconditionedSpatialWidthCutoff ((n₀ : ℝ) * side)
        (unconditionedSpatialTrimFraction nX (Real.exp (-p)))
        (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N x : ℝ)) →
      ∀ f : (Fin nX → ℤ) → ℝ,
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + Real.exp (-p) ≤ (𝔼 x ∈ integerBox N, f x) →
      let S := CanonicalEmptyLayerGeometry.zeroLayerScale (Fin n₀) side hside
      let τ := unconditionedSpatialTrimFraction (Fintype.card (Fin nX)) (Real.exp (-p))
      let shape := (p + 2) ^ Cshape
      let input := (p + 2) ^ Cinput
      ∃ (A : AllocatedExternalCandidateSampler C0 U0 b0 S hb0 o0 pos0 pos0
          N (CanonicalEmptyLayerGeometry.poly 0 (Fin nX))
          (CanonicalEmptyLayerGeometry.poly_mem 0 (Fin nX)) τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables (Fin n₀)
          (CanonicalEmptyLayerGeometry.I 0) (CanonicalEmptyLayerGeometry.n 0) C0) s d),
        d ≤ d₀ ∧ (d : ℝ) ≤ shape ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp shape ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ shape) ∧
        let := polynomialShearIndexFintype patch.weight patch.weight_pos
        let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
        let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
        let := realification_moduleTopology_t2 (polynomialShearOrderedBasis patch.weight)
        ∃ M : ℝ≥0, patch.ExternalObservableRegularity M input ∧
        ∃ Q : AllocatedExternalCandidateProblem (E := CanonicalEmptyLayerGeometry.I 0) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          input (Real.exp (-input)) (Real.exp (-input)),
          Q.centerLift = allocatedZeroLayerCenterLift U0 ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  obtain ⟨Cshape, Cinput, hshape, hinput, hinit⟩ :=
    exists_allocatedZeroLayer_budgeted_initialization s n₀
  refine ⟨Cshape, Cinput, hshape, hinput, ?_⟩
  intro nX side hside P _ i p a Λ hp ha hΛ hPS hratio d₀ habsolute
    hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean S τ shape input
  have hsize : ∀ x, unconditionedSpatialWidthCutoff
      ((Fintype.card (LayerSamplerVariables (Fin n₀) (CanonicalEmptyLayerGeometry.I 0)
        (CanonicalEmptyLayerGeometry.n 0) C0) : ℝ) * S.value)
      (unconditionedSpatialTrimFraction (Fintype.card (Fin nX)) (Real.exp (-p)))
      (unconditionedCollisionWidth P (Real.exp (-p))) ≤ (N x : ℝ) := by
    simpa only [S, zeroLayerVariables_card, Fintype.card_fin, CanonicalEmptyLayerGeometry.zeroLayerScale_value]
      using hN
  have hdec : instDecidableEqFin nX = (fun a b : Fin nX => Classical.propDecidable (a = b)) :=
    Subsingleton.elim _ _
  rw [hdec] at hmean
  have hsource := hinit (E := CanonicalEmptyLayerGeometry.I 0) C0 U0 b0 hb0 o0 pos0 pos0
      (CanonicalEmptyLayerGeometry.poly 0 (Fin nX))
      (CanonicalEmptyLayerGeometry.poly_mem 0 (Fin nX)) S (Equiv.refl _) P i
      hp ha hΛ hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hsize
      f (by simpa using hf) (by simpa using hfree) hmean
  obtain ⟨A, d, patch, hd, hrank, hLip, hcenter, hrest⟩ := hsource
  refine ⟨A, d, patch, hd, hrank, hLip, hcenter, ?_⟩
  let := polynomialShearIndexFintype patch.weight patch.weight_pos
  let := moduleTopology ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)
  let := realification_moduleTopology_t2 (polynomialShearOrderedBasis patch.weight)
  dsimp only
  simpa only [input] using hrest

end Erdos3.VectorPolynomial

end

end OAI
