/-
Modified for ProveIt: use explicit reducible rewriting for translated niltest
evaluation across equivalent quotient-dimension subtype descriptions on
Lean 4.32. The theorem statements and quantitative bounds are unchanged.
-/
import OAI.Combinatorics.Progressions.Estimates.CommonIntegralModelEquivalences
import OAI.Combinatorics.Progressions.Estimates.ShiftedVerticalExpansion
import OAI.Combinatorics.Progressions.Geometry.BoxOverlapSize
import OAI.Combinatorics.Progressions.Nilpotent.StepOneGradedNiltestSplitting

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem norm_finiteCorrelation_one {A : Type*} (Q : Finset A) (u : A → ℂ) :
    ‖finiteCorrelation Q (fun _ => 1) u‖ = ‖𝔼 x ∈ Q, u x‖ := by
  have he : (𝔼 x ∈ Q, star (u x)) = star (𝔼 x ∈ Q, u x) := by
    simp [Finset.expect, star_sum]
  simp only [finiteCorrelation, one_mul, he, norm_star]

theorem finiteCorrelation_one_derivative {A : Type*} [AddCommGroup A]
    (Q : Finset A) (u : A → ℂ) (h : A) :
    finiteCorrelation Q (multiplicativeDerivative (fun _ : A => 1) h) (multiplicativeDerivative u h) =
      𝔼 x ∈ Q, u (x + h) * star (u x) := by
  simp only [finiteCorrelation, multiplicativeDerivative, star_one, one_mul, star_mul, star_star]

theorem exists_many_biased_box_shifts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (T : ι → ℕ) (hT : ∀ i, 0 < T i) (u : (ι → ℤ) → ℂ)
    {p : ℝ} (_hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hu : ∀ x ∈ translatedIntegerBox a T, ‖u x‖ ≤ Real.exp p)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox a T, u x‖) :
    ∃ H : Finset (ι → ℤ), H.Nonempty ∧
      Real.exp (-(4 * p + 6)) * (∏ i, (T i : ℝ)) ≤ H.card ∧
      ∀ h ∈ H,
        (∀ i, |(h i : ℝ)| ≤ T i) ∧
        (∀ i, Real.exp (-(5 * p + 6)) * T i < (((T i : ℤ) - |h i|).toNat : ℝ)) ∧
        Real.exp (-(2 * p + 1)) ≤
          ‖𝔼 x ∈ derivativeSupport (translatedIntegerBox a T) h, u (x + h) * star (u x)‖ := by
  classical
  let : ∀ i, NeZero (T i) := fun i => ⟨(hT i).ne'⟩
  let Q := translatedIntegerBox a T
  let δ := Real.exp (-(5 * p + 6))
  let P := fun h : ι → ℤ =>
    Real.exp (-p) ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative (fun _ : ι → ℤ => 1) h) (multiplicativeDerivative u h)‖ ∧
    δ * Q.card < ((derivativeSupport Q h).card : ℝ)
  let H := (cubeDifferenceSupport Q).filter P
  have hQ : Q.Nonempty := translatedIntegerBox_nonempty T a
  have hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Q (fun _ => 1) u‖ := by
    rw [norm_finiteCorrelation_one]
    exact hbias
  have hw := weight_correlating_large_box_overlaps a T (fun _ => 1) u
    (Real.exp_nonneg (-p)) (Real.exp_pos (p + 1)) (Real.exp_nonneg (-(5 * p + 6)))
    (fun _ _ => by norm_num) (fun x hx => (hu x hx).trans (Real.exp_le_exp.mpr (by linarith))) hcorr
  have hret := retained_exponential_weight (Fintype.card ι) (r := p) hι
  have hμ : Real.exp (-(4 * p + 6)) ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if P h then (1 : ℝ) else 0) := by
    have he₁ : 2 * p + 2 * p + 6 = 4 * p + 6 := by ring
    have he₂ : 4 * p + 6 + p = 5 * p + 6 := by ring
    have hret' : Real.exp (-(4 * p + 6)) ≤
        Real.exp (-p) ^ 2 / (2 * Real.exp (p + 1) ^ 2) -
          (2 : ℝ) ^ Fintype.card ι * Real.exp (-(5 * p + 6)) := by
      simpa only [he₁, he₂] using hret
    exact hret'.trans hw
  have hcount : Real.exp (-(4 * p + 6)) * (∏ i, (T i : ℝ)) ≤ H.card := by
    have hc := cardinality_ge_overlap_weight hQ (cubeDifferenceSupport Q) P hμ
    simpa only [H, Q, translatedIntegerBox, card_translateSupport, card_integerBox, Nat.cast_prod] using hc
  have hnonempty : H.Nonempty := by
    apply Finset.card_pos.mp
    have hpos : (0 : ℝ) < H.card :=
      (mul_pos (Real.exp_pos _) (Finset.prod_pos (fun i _ => by exact_mod_cast hT i))).trans_le hcount
    exact_mod_cast hpos
  refine ⟨H, hnonempty, hcount, ?_⟩
  intro h hh
  obtain ⟨hsupport, hc, hlarge⟩ := Finset.mem_filter.mp hh
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hi := box_overlap_length_pos a T hsupport i
    have habs : |h i| ≤ (T i : ℤ) := by omega
    exact_mod_cast habs
  · exact box_overlap_side_gt_of_card_gt a T hT h hlarge
  · have he : Real.exp (-p) ^ 2 = Real.exp (-2 * p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hsmall : Real.exp (-(2 * p + 1)) ≤ Real.exp (-p) ^ 2 / 2 := by
      have he' : -(2 * p + 1) = -2 * p - 1 := by ring
      rw [he, he']
      exact exp_sub_one_le_half_exp (-2 * p)
    rw [finiteCorrelation_one_derivative] at hc
    exact hsmall.trans hc

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_correlating_vertical_mode_preserving_characters (T : D.Niltest w)
    {p ρ : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
      U.ComplexityLE p ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
        ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
      (∀ (z : D.RealGroup) (c : ℂ),
        (∀ x, T.observable (z • x) = c * T.observable x) →
          ∀ x, U.observable (z • x) = c * U.observable x) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation Q f U.eval‖ := by
  obtain ⟨J, inst, hdecomp⟩ := T.exists_controlled_vertical_decomposition hp hT
    (ρ / 2) (by linarith) hρp
  let := inst
  obtain ⟨η, U, hcard, hheight, hU, hchar, hint, hpres, _, herr⟩ := hdecomp
  obtain ⟨j, hj⟩ := exists_correlating_summand hQ f T.eval (fun j => (U j).eval)
    hρ (Real.exp_pos _) hcard hf (fun x _ => herr x) hcorr
  have hne : ∃ x, (U j).observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, (U j).eval x = 0 := fun x => hzero _
    have hc0 : finiteCorrelation Q f (U j).eval = 0 := by simp [finiteCorrelation, heval]
    rw [hc0, norm_zero] at hj
    exact (not_le_of_gt (div_pos hρ (by positivity))) hj
  exact ⟨η j, U j, (hU j).1, (hU j).2, hheight j, hchar j, hint j hne,
    (fun z c hz x => hpres z c hz j x), hj⟩

theorem exists_correlating_vertical_mode (T : D.Niltest w)
    {p ρ : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w),
      U.ComplexityLE p ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (η (D.basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x) ∧
      (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
        ∃ n : ℤ, realifyFunctional η z.coord = n) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation Q f U.eval‖ := by
  obtain ⟨η, U, hU, hOrbit, hheight, hchar, hint, _, hCorr⟩ :=
    T.exists_correlating_vertical_mode_preserving_characters hp hT hρ hρp hQ f hf hcorr
  exact ⟨η, U, hU, hOrbit, hheight, hchar, hint, hCorr⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_detection_vertical_mode (a : ℕ)
    (ha : ∀ q : ℝ, 0 ≤ q → verticalDecompositionBudget q ≤ (q + a) ^ a)
    (T : D.Niltest w) {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    {Q : Finset (σ → ℤ)} (hQ : Q.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hcorr : Real.exp (-p) ≤ ‖finiteCorrelation Q f T.eval‖) :
    ∃ (η : L →ₗ[ℚ] ℚ) (U : D.Niltest w), U.ComplexityLE (p + 1) ∧
      Real.exp (-boxModeBudget a p) ≤ ‖finiteCorrelation Q f U.eval‖ ∧
      ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) =
          character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * U.observable x := by
  have hp1 : 0 ≤ p + 1 := by linarith
  have herror : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div]; simp [Real.exp_neg]
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg p)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨η, U, hU, _, _, hvert, _, hcorrU⟩ :=
    T.exists_correlating_vertical_mode hp1 (hT.mono (by linarith)) (Real.exp_pos (-p))
      herror hQ f hf hcorr
  refine ⟨η, U, hU, ?_, hvert⟩
  apply le_trans _ hcorrU
  have hv := ha (p + 1) hp1
  calc
    _ ≤ Real.exp ((-p - verticalDecompositionBudget (p + 1)) - 1) := by
      apply Real.exp_le_exp.mpr
      unfold boxModeBudget
      linarith
    _ ≤ Real.exp (-p - verticalDecompositionBudget (p + 1)) / 2 := exp_sub_one_le_half_exp _
    _ = _ := by rw [Real.exp_sub]; ring

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def TranslatedStepDropSpec (s C : ℕ) : Prop :=
  ∀ {σ : Type uσ} {L : Type uL} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (_hvertical : ∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
      T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x)
    (origin : σ → ℤ) (lengths : σ → ℕ) (_hlengths : ∀ i, 0 < lengths i)
    (_hlarge : ∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ))
    (_hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖),
    D.filtration.ControlledSymbolFactorization D.basis ω _hF η (fun i => (lengths i : ℝ))
      (T.symbol D.basis ω _hF) ((p + C) ^ C)

namespace RationalFilteredNilmanifold

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L 1 d)

theorem stepOne_controlled_symbol_factorization (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) (η : L →ₗ[ℚ] ℚ)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hvertical : ∀ z ∈ D.filtration.realification.subgroup 1, ∀ x,
      T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x)
    (origin : σ → ℤ) (lengths : σ → ℕ) (hlengths : ∀ i, 0 < lengths i)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖) :
    D.filtration.ControlledSymbolFactorization D.basis ω hF η (fun i => (lengths i : ℝ))
      (T.symbol D.basis ω hF) ((p + 2) ^ 4) := by
  let U := T.translate (fun _ => Nat.zero_lt_one) origin
  have hUbias : Real.exp (-p) ≤ ‖𝔼 x ∈ integerBox lengths, U.eval x‖ := by
    rw [T.mean_translate_box (fun _ => Nat.zero_lt_one) origin lengths]
    exact hbias
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hheight, hη, hfast⟩ :=
    D.exists_stepOne_graded_niltest_splitting ω hF U η hp hT hηheight hvertical
      lengths hlengths hUbias
  refine ⟨m, E, P, R, W, v, hm, hmp, ?_, hE, hR, hv, hW, hheight, ?_, ?_⟩
  · exact hprod.trans (T.symbol_translate D.basis ω hF (fun _ => Nat.zero_lt_one) origin)
  · intro x hx _
    change D.filtration.stepOneGradedFrequency D.basis ω hF η x = 0
    exact hη x hx
  · exact (D.filtration.mem_real_symbolPointwiseSubalgebra_iff_values D.basis ω hF
      (fun _ => 1) W P.coord).mpr hfast

end RationalFilteredNilmanifold

theorem translatedStepDropSpec_one : TranslatedStepDropSpec.{uσ, uL} 1 4 := by
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p hp _ T hT η hη hvertical origin lengths hlengths _ hbias
  have h := D.stepOne_controlled_symbol_factorization ω hF T η hp hT hη hvertical
    origin lengths hlengths hbias
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono D.filtration D.basis ω hF h
    (pow_le_pow_left₀ (by linarith) (by norm_num) 4)
    (fun i => by exact_mod_cast hlengths i)

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s m : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (Γ : Subgroup F.Group)
  [TopologicalSpace (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)))]
  (bs : Basis (Fin m) ℚ F.squareLieSubalgebra) (ω : Fin m → ℕ)
  (hls : ∀ j, F.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ ω i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (F.squareLattice Γ))
  (hout : bchSubgroupCoordinates bs (F.squareLattice Γ) ⊆ denominatorGrid N)

local notation "Dq" => F.squareFiltration.topQuotientModel bs ω hls (F.squareLattice Γ) N hN hin hout

theorem exists_correlating_square_vertical_mode (hs : 1 ≤ s) (w : σ → ℕ)
    (ε : F.realification.Group) (η : L →ₗ[ℚ] ℚ)
    (u : F.realification.Group ⧸ Γ.map realificationHom → ℂ)
    (hu : ∀ z ∈ F.realification.subgroup (s + 1), ∀ x,
      u (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * u x)
    (r : F.squareFiltration.RealAdaptedPolynomialGroup w) (S : (Dq).Niltest w)
    (hOrbit : S.orbit = F.squareFiltration.nativeReducedPolynomialOrbit w r)
    (hObs : ∀ z : F.squareFiltration.realification.Group,
      S.observable (QuotientGroup.mk (F.squareFiltration.realQuotientStepHom
        (F.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
        F.realSquareObservable Γ ε u (QuotientGroup.mk z))
    {p ρ : ℝ} (hp : 0 ≤ p) (hS : S.ComplexityLE p)
    (hρ : 0 < ρ) (hρp : (ρ / 2)⁻¹ ≤ Real.exp p)
    {A : Finset (σ → ℤ)} (hA : A.Nonempty) (f : (σ → ℤ) → ℂ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ 1) (hcorr : ρ ≤ ‖finiteCorrelation A f S.eval‖) :
    ∃ (ξ : (F.squareLieSubalgebra ⧸ F.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
      (V : (Dq).Niltest w),
      V.ComplexityLE p ∧ V.orbit = F.squareFiltration.nativeReducedPolynomialOrbit w r ∧
      (∀ i, rationalLogHeight (ξ ((Dq).basis i)) ≤ verticalDecompositionBudget p) ∧
      (∀ z ∈ F.squareFiltration.quotientTop.realification.subgroup s, ∀ x,
        V.observable (z • x) =
          character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
      (∀ z : (Dq).RealGroup, z ∈ F.squareFiltration.quotientTop.realification.subgroup s →
        z ∈ (Dq).realLattice → ∃ n : ℤ, realifyFunctional ξ z.coord = n) ∧
      (∀ x : F.layer (s + 1), ξ (lieQuotientMap (F.squareFiltration.layerIdeal (s + 1))
        (F.squareRelativeLayer s hs x).val) = η x) ∧
      ρ / (2 * Real.exp (verticalDecompositionBudget p)) ≤ ‖finiteCorrelation A f V.eval‖ := by
  obtain ⟨ξ, V, hV, hVO, hheight, hchar, hint, hpres, hCorr⟩ :=
    S.exists_correlating_vertical_mode_preserving_characters hp hS hρ hρp hA f hf hcorr
  have hne : ∃ x, V.observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, V.eval x = 0 := fun _ => hzero _
    have hc0 : finiteCorrelation A f V.eval = 0 := by simp [finiteCorrelation, heval]
    rw [hc0, norm_zero] at hCorr
    exact (not_le_of_gt (div_pos hρ (by positivity))) hCorr
  refine ⟨ξ, V, hV, hVO.trans hOrbit, hheight, hchar, hint, ?_, hCorr⟩
  exact F.descended_square_mode_frequency_restriction hs Γ ε η u hu
    S.observable V.observable hObs ξ hchar hne hpres

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uι uL

namespace RationalFilteredNilmanifold

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

def HasNativeBiasedSquare (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (A : Finset (σ → ℤ)) (h : σ → ℤ) (q : ℝ) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp q) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
      ∃ (m : ℕ) (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
        (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
        (N : ℕ) (hN : 0 < N)
        (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
        (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
        let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
          (D.filtration.squareLattice D.lattice) N hN hin hout
        ∃ (ξ : (D.filtration.squareLieSubalgebra ⧸
            D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
          (V : Q.Niltest (fun _ : σ => 1)),
          V.orbit = D.filtration.squareFiltration.nativeReducedPolynomialOrbit (fun _ => 1) r ∧
          V.ComplexityLE q ∧
          (∀ i, rationalLogHeight (ξ (Q.basis i)) ≤ q) ∧
          (∀ z ∈ D.filtration.squareFiltration.quotientTop.realification.subgroup s, ∀ x,
            V.observable (z • x) =
              character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
          (∀ z : Q.RealGroup, z ∈ D.filtration.squareFiltration.quotientTop.realification.subgroup s →
            z ∈ Q.realLattice → ∃ n : ℤ, realifyFunctional ξ z.coord = n) ∧
          (∀ x : D.filtration.layer (s + 1),
            ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
              (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
          Real.exp (-q) ≤ ‖𝔼 x ∈ A, V.eval x‖

end RationalFilteredNilmanifold

def NativeBiasedSquareSpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (_hg : D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit)
    (η : L →ₗ[ℚ] ℚ)
    (_hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x)
    (h : σ → ℤ) (A : Finset (σ → ℤ)) (_hA : A.Nonempty)
    (_hbias : Real.exp (-(2 * p + 1)) ≤ ‖𝔼 x ∈ A, T.eval (x + h) * star (T.eval x)‖),
    D.HasNativeBiasedSquare hs g η A h ((p + C) ^ C)

theorem exists_native_biased_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeBiasedSquareSpec.{uσ, uι, uL} s C := by
  obtain ⟨a, _, hsquare⟩ := exists_native_square_niltest.{uσ, uι, uL} s
  obtain ⟨b, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + 2 * Polynomial.X + 2
  let P : Polynomial ℕ := Q + (Q + Polynomial.C b) ^ b + 2 * Polynomial.X + 2
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ ι L _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ e ω hF p hp T hT g hg η hvert h A hA hbias
  let q := (p + a) ^ a + 2 * p + 2
  have hqa : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hbasepow : 0 ≤ (p + a) ^ a := by positivity
  have hqp : 2 * p + 2 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hv := hvertical q hq
  have hfinal' : q + (q + b) ^ b + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [P, Q, q, Polynomial.eval₂_pow] using hfinal p hp
  have hpow : 0 ≤ (q + b) ^ b := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hvC : verticalDecompositionBudget q ≤ (p + C) ^ C := by linarith
  have hbC : 2 * p + 2 + verticalDecompositionBudget q ≤ (p + C) ^ C := by linarith
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, m, bs, v, hls, N, hN, hin, hout,
    S, hOrbit, hObs, _, hS, hSval⟩ :=
    hsquare D e ω hF p hp T hT g hg
      (fun z => ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle)) hvert h
  have herror : (Real.exp (-(2 * p + 1)) / 2)⁻¹ ≤ Real.exp q := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp (2 * p + 1) := by rw [inv_div, Real.exp_neg, div_inv_eq_mul]
      _ ≤ Real.exp 1 * Real.exp (2 * p + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hqp
  have hc : Real.exp (-(2 * p + 1)) ≤ ‖finiteCorrelation A (fun _ => 1) S.eval‖ := by
    rw [norm_finiteCorrelation_one]
    have he : (𝔼 x ∈ A, S.eval x) = 𝔼 x ∈ A, T.eval (x + h) * star (T.eval x) := by
      apply Finset.expect_congr rfl
      intro x _
      exact hSval x
    rw [he]
    exact hbias
  obtain ⟨ξ, V, hV, hVO, hheight, hchar, hint, hrestriction, hCorr⟩ :=
    D.filtration.exists_correlating_square_vertical_mode D.lattice bs v hls N hN hin hout
      hs (fun _ : σ => 1) ε η T.observable hvert r S hOrbit hObs hq (hS.mono hqa)
      (Real.exp_pos _) herror hA (fun _ => 1) (fun _ _ => by norm_num) hc
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr (hqa.trans hqC))),
    r, hf, hsecond, hderivative, m, bs, v, hls, N, hN, hin, hout, ξ, V,
    hVO, hV.mono hqC, (fun i => (hheight i).trans hvC), hchar, hint, hrestriction, ?_⟩
  rw [norm_finiteCorrelation_one] at hCorr
  apply le_trans _ hCorr
  calc
    _ ≤ Real.exp ((-(2 * p + 1) - verticalDecompositionBudget q) - 1) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ ≤ Real.exp (-(2 * p + 1) - verticalDecompositionBudget q) / 2 := exp_sub_one_le_half_exp _
    _ = _ := by rw [Real.exp_sub]; ring

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uι uL

namespace RationalFilteredNilmanifold

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
theorem HasNativeBiasedSquare.mono {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {A : Finset (σ → ℤ)} {h : σ → ℤ} {p q : ℝ}
    (hdata : D.HasNativeBiasedSquare hs g η A h p) (hpq : p ≤ q) :
    D.HasNativeBiasedSquare hs g η A h q := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, m, bs, v, hls, N, hN, hin, hout,
    ξ, V, hOrbit, hV, hheight, hchar, hint, hrestriction, hbias⟩ := hdata
  exact ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpq)),
    r, hf, hsecond, hderivative, m, bs, v, hls, N, hN, hin, hout, ξ, V, hOrbit,
    hV.mono hpq, (fun i => (hheight i).trans hpq), hchar, hint, hrestriction,
    (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias⟩

end RationalFilteredNilmanifold

def NativeBiasedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {ι : Type uι} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (_hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (_hg : D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit)
    (η : L →ₗ[ℚ] ℚ)
    (_hvert : ∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
      T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
        T.observable x)
    (a : σ → ℤ) (N : σ → ℕ) (_hN : ∀ i, 0 < N i)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox a N, T.eval x‖),
    ∃ H : Finset (σ → ℤ), H.Nonempty ∧
      Real.exp (-((p + C) ^ C)) * (∏ i, (N i : ℝ)) ≤ H.card ∧
      ∀ h ∈ H,
        (∀ i, |(h i : ℝ)| ≤ N i) ∧
        (∀ i, Real.exp (-((p + C) ^ C)) * N i < (((N i : ℤ) - |h i|).toNat : ℝ)) ∧
        D.HasNativeBiasedSquare hs g η (derivativeSupport (translatedIntegerBox a N) h) h ((p + C) ^ C)

theorem exists_native_biased_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ NativeBiasedSquareFamilySpec.{uσ, uι, uL} s C := by
  obtain ⟨a, _, hsingle⟩ := exists_native_biased_square.{uσ, uι, uL} s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + 5 * Polynomial.X + 6
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ ι L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ b ω hF p hp T hT g hg η hvert origin N hN hσ hbias
  have hbound : (p + a) ^ a + 5 * p + 6 ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hfinal p hp
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have haC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  have h5 : 5 * p + 6 ≤ (p + C) ^ C := by linarith
  have h4 : 4 * p + 6 ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hcount, hgood⟩ := exists_many_biased_box_shifts origin N hN T.eval hp hσ
    (fun x _ => T.eval_budget hT x) hbias
  refine ⟨H, hH, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h4))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (N i)))).trans hcount
  · intro h hh
    obtain ⟨hbox, hsides, hmean⟩ := hgood h hh
    refine ⟨hbox, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h5))
        (Nat.cast_nonneg (N i))).trans_lt (hsides i)
    · have hA : (derivativeSupport (translatedIntegerBox origin N) h).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.expect_empty, norm_zero] at hmean
        exact (not_le_of_gt (Real.exp_pos _)) hmean
      exact RationalFilteredNilmanifold.HasNativeBiasedSquare.mono D
        (hsingle hs D b ω hF p hp T hT g hg η hvert h
          (derivativeSupport (translatedIntegerBox origin N) h) hA hmean) haC

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

def HasNativeBiasedSquareInModel {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (A : Finset (σ → ℤ)) (h : σ → ℤ) (q : ℝ) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp q) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
        let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
          (D.filtration.squareLattice D.lattice) N hN hin hout
        ∃ (ξ : (D.filtration.squareLieSubalgebra ⧸
            D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
          (V : Q.Niltest (fun _ : σ => 1)),
          V.orbit = D.filtration.squareFiltration.nativeReducedPolynomialOrbit (fun _ => 1) r ∧
          V.ComplexityLE q ∧
          (∀ i, rationalLogHeight (ξ (Q.basis i)) ≤ q) ∧
          (∀ z ∈ D.filtration.squareFiltration.quotientTop.realification.subgroup s, ∀ x,
            V.observable (z • x) =
              character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) * V.observable x) ∧
          (∀ z : Q.RealGroup, z ∈ D.filtration.squareFiltration.quotientTop.realification.subgroup s →
            z ∈ Q.realLattice → ∃ n : ℤ, realifyFunctional ξ z.coord = n) ∧
          (∀ x : D.filtration.layer (s + 1),
            ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
              (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
          Real.exp (-q) ≤ ‖𝔼 x ∈ A, V.eval x‖

variable {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
theorem HasNativeBiasedSquareInModel.mono {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {A : Finset (σ → ℤ)} {h : σ → ℤ} {p q : ℝ}
    (hdata : D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η A h p) (hpq : p ≤ q) :
    D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η A h q := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative,
    ξ, V, hOrbit, hV, hheight, hchar, hint, hrestriction, hbias⟩ := hdata
  exact ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpq)),
    r, hf, hsecond, hderivative, ξ, V, hOrbit,
    hV.mono hpq, (fun i => (hheight i).trans hpq), hchar, hint, hrestriction,
    (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias⟩

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
theorem HasNativeBiasedSquareInModel.forget {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {A : Finset (σ → ℤ)} {h : σ → ℤ} {p : ℝ}
    (hdata : D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η A h p) :
    D.HasNativeBiasedSquare hs g η A h p := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, hmode⟩ := hdata
  exact ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, m, bs, v, hls, N, hN, hin, hout, hmode⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct BigOperators

namespace NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis (Fin d) ℚ L) (w : Fin d → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

theorem topQuotientModel_basis_layers (Γ : Subgroup F.Group) (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates b Γ)
    (hout : bchSubgroupCoordinates b Γ ⊆ denominatorGrid N) (j : ℕ) :
    (F.topQuotientModel b w hF Γ N hN hin hout).filtration.layer j =
      Submodule.span ℚ ((F.topQuotientModel b w hF Γ N hN hin hout).basis ''
        {i | j ≤ quotientFinWeight w {i | s + 1 ≤ w i} i}) :=
  F.quotientFinBasis_layers b w hF (F.layerIdeal (s + 1)) le_rfl
    {i | s + 1 ≤ w i} (hF (s + 1)) j

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold

universe uσ uL

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

variable {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

def HasNativeFactoredSquareInModel (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (h : σ → ℤ) (p q : ℝ) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
      ∃ ξ : (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ,
        (∀ i, rationalLogHeight (ξ ((Q).basis i)) ≤ p) ∧
        (∀ x : D.filtration.layer (s + 1),
          ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
            (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
        (Q).filtration.ControlledSymbolFactorization (Q).basis
          (quotientFinWeight v {i | s + 1 ≤ v i}) hQ ξ S
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) q

variable [DecidableEq σ]
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

theorem HasNativeBiasedSquareInModel.factorization {c : ℕ}
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {origin h : σ → ℤ} {lengths : σ → ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p) (hlengths : ∀ i, 0 < lengths i)
    (hlarge : ∀ i, Real.exp ((p + c) ^ c) ≤ (lengths i : ℝ))
    (hdata : D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η
      (translatedIntegerBox origin lengths) h p) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h p ((p + c) ^ c) := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative,
    ξ, V, hOrbit, hV, hheight, hchar, _, hrestriction, hbias⟩ := hdata
  have hfactor := hI Q (quotientFinWeight v {i | s + 1 ≤ v i}) hQ p hp hσ V hV ξ hheight hchar
    origin lengths hlengths hlarge hbias
  have hsymbol : V.symbol (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ =
      D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r := by
    have he := congrArg (fun a : (Q).filtration.realification.PolynomialOrbit (fun _ : σ => 1) =>
      (Q).filtration.realPolynomialSymbolHom (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i})
        hQ (fun _ => 1) ⟨⟨a.log, a.property⟩⟩) hOrbit
    exact he.trans (D.filtration.squareFiltration.nativeReducedPolynomialOrbit_symbol
      (fun _ => 1) (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ r)
  rw [hsymbol] at hfactor
  exact ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_adapted_uniform_two_shift_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (p : ℝ), 0 ≤ p → ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : D.Niltest w), T.ComplexityLE p →
      ∃ (n : ℕ) (Q : RationalFilteredNilmanifold (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) s n) (weight : Fin n → ℕ),
        (∀ j, Q.filtration.layer j = Submodule.span ℚ (Q.basis '' {i | j ≤ weight i})) ∧
        Q.GeometryComplexityLE (squareGeometryBudget p) ∧
        ∀ (χ : D.RealGroup → CircleFourier.Circle),
          (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
            T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ a b : σ → ℤ, ∃ S : Q.Niltest w,
          S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
          ∀ x : σ → ℤ, S.eval x = T.eval (x + a) * star (T.eval (x + b)) := by
  obtain ⟨a, _, hnorm⟩ := exists_bounded_realified_square_orbit (s + 1)
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨C, hC, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp w hw T hT
  obtain ⟨e, ω, hF, N, hN, hin, hout, _, hgeom, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  refine ⟨_, _, NilpotentLieFiltration.quotientFinWeight (NilpotentLieFiltration.squareFinWeight ω)
    {i | s + 1 ≤ NilpotentLieFiltration.squareFinWeight ω i}, ?_, hgeom, ?_⟩
  · exact D.filtration.squareFiltration.topQuotientModel_basis_layers
      (D.filtration.squareFinBasis e ω (hF 2)) (NilpotentLieFiltration.squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF)
      (D.filtration.squareLattice D.lattice) N hN hin hout
  · intro χ hvert h k
    obtain ⟨ε, γ, hγ, hε, q, hq⟩ := hnorm D p hp hT.1 w hw (h - k) T.orbit
    obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
    obtain ⟨S, _, _, hSB, hS, hSval⟩ := hconstruct ε q χ hvert A hA (hALip ε hε)
    have hval (x : σ → ℤ) : S.eval x = T.eval (x + (h - k)) * star (T.eval x) := by
      exact (hSval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice ε γ
        (D.filtration.realification.polynomialOrbitEval w (fun i => x i + (h - k) i) T.orbit)
        (D.filtration.realification.polynomialOrbitEval w x T.orbit) hγ T.observable
        (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q) (hq x).1 (hq x).2)
    refine ⟨S.translate hw k, hSB, hS.mono (hbudget p hp), ?_⟩
    intro x
    erw [RationalFilteredNilmanifold.Niltest.eval_translate, hval]
    congr 2
    abel

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

def HasFixedNativeSquareFactors (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (h : σ → ℤ) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded) : Prop :=
  ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
    (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
    ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
      ∃ ξ : (D.filtration.squareLieSubalgebra ⧸
          D.filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ,
        (∀ i, rationalLogHeight (ξ ((Q).basis i)) ≤ p) ∧
        (∀ x : D.filtration.layer (s + 1),
          ξ (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
            (D.filtration.squareRelativeLayer s hs x).val) = η x) ∧
        (∀ x ∈ W, basisGradeProjection
            ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
            (quotientFinWeight v {i | s + 1 ≤ v i}) s x = x →
          (Q).filtration.gradedFrequency (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ ξ x = 0) ∧
        (Q).filtration.SymbolFactorizationIn (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ S
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) p l W

theorem HasNativeFactoredSquareInModel.exists_fixed {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) → (Q).filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
        (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ).repr
          (u i) j) ≤ p) ∧
      D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  obtain ⟨l, W, u, hl, hlp, hu, hW, hcoordinates, hη, hfixed⟩ :=
    ControlledSymbolFactorization.exists_in (Q).filtration (Q).basis
      (quotientFinWeight v {i | s + 1 ≤ v i}) hQ hfactor
  refine ⟨l, W, u, hl, hlp, hu, hW, hcoordinates, ?_⟩
  exact ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hη, hfixed⟩

theorem HasFixedNativeSquareFactors.mono {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p q : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W)
    (hpq : p ≤ q) (hS : ∀ i, 0 < S i) :
    D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h q l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hη, hfixed⟩ := hdata
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpq)), r,
    hf, hsecond, hderivative, ξ, (fun i => (hheight i).trans hpq), hrestriction, hη, ?_⟩
  exact SymbolFactorizationIn.mono (Q).filtration (Q).basis
    (quotientFinWeight v {i | s + 1 ≤ v i}) hQ hfixed hpq hS

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

theorem exists_common_native_square_factors (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (H : Finset (σ → ℤ)) (hH : H.Nonempty)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i} : ℝ) ≤ p)
    (hdata : ∀ h ∈ H, D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) → (Q).filtration.AssociatedGraded)
      (H' : Finset (σ → ℤ)),
      H' ⊆ H ∧ H'.Nonempty ∧
      Real.exp (-((p + 2) ^ 5 + p)) * H.card ≤ (H'.card : ℝ) ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
        (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ).repr
          (u i) j) ≤ p) ∧
      ∀ h ∈ H', D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W := by
  classical
  let J := Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i})
  let bG := (Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ
  obtain ⟨h₀, hh₀⟩ := hH
  have htags : ∀ h : σ → ℤ, ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : J → (Q).filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule bG (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight (bG.repr (u i) j) ≤ p) ∧
      (h ∈ H → D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W) := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨l, W, u, hl, hlp, hu, hW, hhgt, hfixed⟩ :=
        HasNativeFactoredSquareInModel.exists_fixed D bs v hls N hN hin hout (hdata h hh)
      exact ⟨l, W, u, hl, hlp, hu, hW, hhgt, fun _ => hfixed⟩
    · obtain ⟨l, W, u, hl, hlp, hu, hW, hhgt, _⟩ :=
        HasNativeFactoredSquareInModel.exists_fixed D bs v hls N hN hin hout (hdata h₀ hh₀)
      exact ⟨l, W, u, hl, hlp, hu, hW, hhgt, fun he => False.elim (hh he)⟩
  choose l W u hl hlp hu hW hhgt hfixed using htags
  have hdim : (Fintype.card J : ℝ) ≤ p := by simpa only [J, Fintype.card_fin] using hd
  obtain ⟨a₀, _, H', hsub, ha, hsame, hlarge⟩ :=
    exists_common_fast_subalgebra_and_denominator bG H ⟨h₀, hh₀⟩ W l
      (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) hp hd hdim
      (fun h _ => ⟨u h, hu h, hhgt h⟩) (fun h _ => ⟨hl h, hlp h⟩)
  refine ⟨l a₀, W a₀, u a₀, H', hsub, ⟨a₀, ha⟩, hlarge,
    hl a₀, hlp a₀, hu a₀, hW a₀, hhgt a₀, ?_⟩
  intro h hh
  simpa only [(hsame h hh).1, (hsame h hh).2] using hfixed h (hsub hh)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
