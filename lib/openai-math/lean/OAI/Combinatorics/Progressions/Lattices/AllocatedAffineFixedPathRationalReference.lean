import OAI.Combinatorics.Progressions.Sampling.AllocatedForecastShortRawDependence
import OAI.Combinatorics.Progressions.Sampling.ForecastNativeJointTestBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {L V Short Out : Type*} [Fintype L] [Fintype V]
  [Fintype Out] [DecidableEq Out]

local instance arbitraryStepForecastModulusNeZero (p e : L → ℕ) [∀ l, NeZero (p l)] :
    NeZero (∏ l, p l ^ e l) :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩

theorem rationalInactivePolynomialForecast_arbitraryStepCRT_tsum_marginal
    {I Z : Type*} [Fintype I]
    (inactive : FiniteProbabilityWeights I) (gridPoint : I → Z)
    (p e : L → ℕ) [∀ l, NeZero (p l)] (step : ℕ)
    (hp : ∀ l, (p l).Prime) (hstep : step ≠ 0)
    (hcoprime : Pairwise (fun l k => (p l ^ e l).Coprime (p k ^ e k)))
    (cLong : V → ℤ)
    (poly : Out → MvPolynomial (V ⊕ Short) ℤ) (inactiveCoord : I → Short → ℤ)
    {q : ℕ} [NeZero q] (hdiv : q ∣ ∏ l, p l ^ e l)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (Out → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : Out → ZMod (∏ l, p l ^ e l),
      ((rationalInactiveForecast inactive
        (fun _ => crtPolynomialInputLaw p e (fun l => padicValNat (p l) step) hcoprime
          (fun l v => (cLong v : ZMod (p l ^ e l)))) gridPoint
        (fun i => integerLongPolynomialOutput poly (inactiveCoord i) (∏ l, p l ^ e l))
        (∏ l, p l ^ e l) gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hdiv (ZMod q) (b j))) =
      inactive.complexMean (fun i =>
        (FiniteProbabilityWeights.uniform (V → ZMod q)).complexMean (fun r =>
          test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
            (Sum.elim (fun v => (cLong v : ZMod q) + (step : ZMod q) * r v)
              (fun a => (inactiveCoord i a : ZMod q))) (poly j)))) := by
  rw [rationalInactiveForecast_divisor_tsum_test _ _ _ _ hdiv hV]
  apply congrArg inactive.complexMean
  funext i
  simp_rw [integerLongPolynomialOutput_reduce poly (inactiveCoord i) hdiv]
  exact crtPolynomialInputLaw_arbitrary_step_divisor_complexMean p e step hp hstep
    hcoprime cLong hdiv
    (fun r => test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim r (fun a => (inactiveCoord i a : ZMod q))) (poly j)))

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
variable (hH : ∀ j, 0 < H j)

noncomputable def allocatedInactiveAffineIntervalLaw
    (H step : (PrincipalTupleIndex B (layerSamplerDegree I n)) → ℕ) (start : (PrincipalTupleIndex B (layerSamplerDegree I n)) → ℤ)
    (hinside : ∀ j (t : Fin (H j)),
      0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
    (hH : ∀ j, 0 < H j) : FiniteProbabilityWeights (PrincipalAxisTuples (α := Empty) (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)) :=
  principalAffineIntervalAxisLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH (allocatedShortAxis (I := I) U basis S.value)

include hinside hH in
theorem allocatedInactiveAffineIntervalLaw_complexMean (f : (PrincipalAxisTuples (α := Empty) (allocatedShortAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)) → ℂ) :
    (allocatedInactiveAffineIntervalLaw B U basis S H step start hinside hH).complexMean f =
      𝔼 t : (∀ j, Fin (H j)), f (principalAxisRestrict (allocatedShortAxis (I := I) U basis S.value)
        (principalAffineIntervalPoint B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside t)) :=
  principalAffineIntervalAxisLaw_complexMean B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH (allocatedShortAxis (I := I) U basis S.value) f

include hinside hH in
theorem allocatedInactiveAffineIntervalLaw_total :
    ∑ u, (allocatedInactiveAffineIntervalLaw B U basis S H step start hinside hH).weight u = 1 :=
  (allocatedInactiveAffineIntervalLaw B U basis S H step start hinside hH).total

variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)

include hinside hH in

theorem allocatedInactiveAffineIntervalLaw_fixed_grid_mean
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (f : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) → ℂ) :
    (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH).complexMean (fun y => f (forecastInactiveFixedOutput B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) x y)) =
      (allocatedInactiveAffineIntervalLaw B U basis S H step start hinside hH).complexMean
        (fun u => f (forecastInactiveShortGrid B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) u)) := by
  rw [allocatedInactiveAffineIntervalLaw, principalAffineIntervalAxisLaw,
    FiniteProbabilityWeights.complexMean_finitePushforward]
  apply congrArg (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH).complexMean
  funext y
  rw [forecastInactiveFixedOutput_eq_shortGrid B U basis S hR hσ selected hshort (allocatedOriginalSampleInactiveCoefficients B selected sample)
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs) x y]

include hinside hH in

theorem allocatedInactiveAffineIntervalLaw_fixed_grid_law
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hshort : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j) (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j)) :
    (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH).toPMF.map (forecastInactiveFixedOutput B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) x) =
      (allocatedInactiveAffineIntervalLaw B U basis S H step start hinside hH).toPMF.map
        (forecastInactiveShortGrid B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample)) := by
  ext z
  apply ENNReal.ofReal_toReal (PMF.apply_ne_top _ _) |>.symm.trans
  apply Eq.trans _ (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _))
  congr 1
  rw [FiniteProbabilityWeights.toPMF_map_toReal, FiniteProbabilityWeights.toPMF_map_toReal]
  have he := congrArg Complex.re
    (allocatedInactiveAffineIntervalLaw_fixed_grid_mean B U basis S H step start hinside hH
      selected sample x hR hσ hshort hs (fun w => if w = z then 1 else 0))
  simpa only [FiniteProbabilityWeights.complexMean_re, apply_ite, Complex.one_re, Complex.zero_re] using he

variable {Ω Out : Type*} [Fintype Ω] [Fintype Out] [DecidableEq Out]
variable (active : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) → FiniteProbabilityWeights Ω) (Y : (PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S)) → Ω → Out → ℤ)

noncomputable def allocatedAffineIntervalInactiveForecast
    (H step : (PrincipalTupleIndex B (layerSamplerDegree I n)) → ℕ) (start : (PrincipalTupleIndex B (layerSamplerDegree I n)) → ℤ)
    (hinside : ∀ j (t : Fin (H j)),
      0 ≤ start j + (step j : ℤ) * t.val ∧ start j + (step j : ℤ) * t.val < (allocatedPrincipalSides B U basis S) j)
    (hH : ∀ j, 0 < H j) (N : ℕ) [NeZero N] (volume : ℝ)
    (grid : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ)) (out : Out → ZMod N) : ℝ :=
  rationalInactiveForecast (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH) active (forecastInactiveFixedOutput B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) x)
    Y N volume grid out

include hinside hH in
theorem allocatedAffineIntervalInactiveForecast_mass_one
    (N : ℕ) [NeZero N] {volume : ℝ} (hV : volume ≠ 0) :
    (∑' grid, 𝔼 out : Out → ZMod N,
      ((allocatedAffineIntervalInactiveForecast B U basis S selected sample x active Y
        H step start hinside hH N volume grid out / volume : ℝ) : ℂ)) = 1 :=
  rationalInactiveForecast_complexTsumMass_one
    (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step start hinside hH) active
    (forecastInactiveFixedOutput B U basis S selected (allocatedOriginalSampleInactiveCoefficients B selected sample) x) Y N hV

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "FullInput" => PrincipalTupleIndex B degree
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "AI" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)
local notation "sides" => allocatedPrincipalSides B U basis S

variable (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (deck : ∀ j : Fin m,
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
variable (projection : ∀ j, AllocatedDegreeActiveAxis short j →
  BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)

noncomputable def allocatedJointResidueOutput
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (rG : G → ZMod q)
    (r : FullInput → Option Empty → ZMod q) : Out → ZMod q :=
  fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
    (Sum.elim (Sum.elim rG (fun j : AI => r ⟨j.1.val, j.2⟩ none))
      (fun k => r k.1 k.2)) (allocatedForecastPolynomial short base noise deck projection o)

theorem allocatedJointResidueOutput_join
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ) (rG : G → ZMod q)
    (u : PrincipalAxisTuples (α := Empty) short sides) (ar : AI → ZMod q) :
    allocatedJointResidueOutput B U basis S base noise deck projection q rG
        (allocatedPrincipalResidueJoin B U basis S q u ar) =
      fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
        (Sum.elim (Sum.elim rG ar)
          (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q)))
        (allocatedForecastPolynomial short base noise deck projection o) := by
  funext o
  have hlong : (fun j : AI => allocatedPrincipalResidueJoin B U basis S q u ar
      ⟨j.1.val, j.2⟩ none) = ar := by
    funext j
    simp only [allocatedPrincipalResidueJoin, principalAxisResidueJoin, j.1.property, dite_false]
  unfold allocatedJointResidueOutput
  rw [hlong]
  apply allocatedForecastPolynomial_eval₂_raw_congr
  intro j hj
  simp only [allocatedPrincipalResidueJoin, principalAxisResidueJoin,
    allocatedShortPrincipalRaw, hj, dite_true]

theorem allocatedJointResidueOutput_actual
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (q : ℕ)
    (x : G → IntegerScalarCubeBox Empty S.value)
    (v : PrincipalIntegerTuples B degree Empty sides) :
    allocatedJointResidueOutput B U basis S base noise deck projection q
        (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q v) =
      fun o => ((MvPolynomial.eval (Sum.elim (fun g => (x g none : ℤ))
        (fun j => (v j none : ℤ)))
        (allocatedUnconditionedCongruenceIntegerPolynomial short o.1 base noise deck
          (projection o.1) o.2) : ℤ) : ZMod q) := by
  funext o
  rw [integerPolynomial_eval_residue]
  unfold allocatedJointResidueOutput allocatedForecastPolynomial allocatedSeparatedCongruencePolynomial
  rw [MvPolynomial.eval₂_rename]
  congr 1
  funext k
  cases k with
  | inl g => rfl
  | inr j =>
    by_cases hj : short j.1
    · simp only [Function.comp_apply, samplerSeparatedVariable_inactive short degree _ _ _ hj,
        Sum.elim_inr, principalResidueLabel]
      rfl
    · simp only [Function.comp_apply, samplerSeparatedVariable_active short degree _ _ _ hj,
        Sum.elim_inl, Sum.elim_inr, principalResidueLabel]
      rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

private theorem affineReference_uniform_sum_flip
    {G A R : Type*} [Fintype G] [Fintype A] [Fintype R] [Nonempty R]
    [DecidableEq G] [DecidableEq A] [DecidableEq (G ⊕ A)]
    (f : (G ⊕ A → R) → ℂ) :
    (FiniteProbabilityWeights.uniform (A → R)).complexMean (fun a =>
      (FiniteProbabilityWeights.uniform (G → R)).complexMean (fun g => f (Sum.elim g a))) =
        (FiniteProbabilityWeights.uniform (G ⊕ A → R)).complexMean f := by
  simp only [FiniteProbabilityWeights.uniform_complexMean]
  calc
    _ = 𝔼 ga : (G → R) × (A → R), f (Sum.elim ga.1 ga.2) := by
      rw [Finset.expect_comm]
      simpa only [Finset.univ_product_univ] using
        (Finset.expect_product' (Finset.univ : Finset (G → R))
          (Finset.univ : Finset (A → R)) (fun g a => f (Sum.elim g a))).symm
    _ = _ := by
      apply Fintype.expect_equiv (Equiv.sumPiEquivProdPi (fun _ : G ⊕ A => R)).symm
      intro ga
      rfl

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "Input" => PrincipalTupleIndex B degree
local notation "Long" => LayerSamplerLongVariables short G B
local notation "Active" => PrincipalTupleIndex
  (fun a : {a // ¬short a} => B (Subtype.val a))
  (fun a : {a // ¬short a} => degree (Subtype.val a))
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E short)

variable (H parameterStep : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (start : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ)
variable (hinside : ∀ j (t : Fin (H j)),
  0 ≤ start j + (parameterStep j : ℤ) * t.val ∧
    start j + (parameterStep j : ℤ) * t.val < allocatedPrincipalSides B U basis S j)
variable (hH : ∀ j, 0 < H j)

variable {PrimeIndex : Type*} [Fintype PrimeIndex]
variable (primes exponent : PrimeIndex → ℕ) [∀ l, NeZero (primes l)]
local notation "N" => (∏ l, primes l ^ exponent l)
local instance affineFixedPathCRTModulusNeZero : NeZero N :=
  ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (primes l)))⟩

theorem allocatedAffineFixedPath_crtRationalForecast_reference
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (commonStep : ℕ) (hstep : commonStep ≠ 0) (cLong : Long → ℤ)
    (hp : ∀ l, (primes l).Prime)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    {q : ℕ} [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    let c := allocatedOriginalSampleInactiveCoefficients B selected sample
    (allocatedInactiveAffineIntervalLaw B U basis S H parameterStep start hinside hH).complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Long → ZMod q)).complexMean (fun r =>
        test (forecastInactiveShortGrid B U basis S selected c u)
          (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
            (Sum.elim (fun v => (cLong v : ZMod q) + (commonStep : ZMod q) * r v)
              (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q))) (poly o)))) =
      ∑' z, 𝔼 b : Out → ZMod N,
        ((rationalInactiveForecast (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH)
          (fun _ => crtPolynomialInputLaw primes exponent
            (fun l => padicValNat (primes l) commonStep) hcoprime
            (fun l v => (cLong v : ZMod (primes l ^ exponent l))))
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test z (fun j => ZMod.castHom hq (ZMod q) (b j)) := by
  intro poly c
  symm
  rw [rationalInactivePolynomialForecast_arbitraryStepCRT_tsum_marginal (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH)
    (forecastInactiveFixedOutput B U basis S selected c xref)
    primes exponent commonStep hp hstep hcoprime cLong poly
    (fun v k => (v k.1 k.2 : ℤ)) hq hV test]
  change _ = ((principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH).finitePushforward (principalAxisRestrict short)).complexMean _
  rw [FiniteProbabilityWeights.complexMean_finitePushforward]
  apply congrArg (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH).complexMean
  funext v
  rw [forecastInactiveFixedOutput_eq_shortGrid B U basis S hR hσ selected hsmall c
    (allocatedOriginalSampleInactiveCoefficients_supported B selected U basis hR hσ S sample hs)
    xref v]
  apply congrArg (FiniteProbabilityWeights.uniform (Long → ZMod q)).complexMean
  funext r
  congr 1
  funext o
  exact allocatedForecastPolynomial_short_raw B U basis S base noise deck projection q
    (fun k => (cLong k : ZMod q) + (commonStep : ZMod q) * r k) v o

theorem allocatedAffineFixedPath_joint_crtRationalForecast_reference
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
    (hsmall : ∀ a, basisAxisScale (basis (selected a).1) (selected a).2 ≤
      S.value ^ ((selected a).1.val + 1))
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (xref : G → IntegerScalarCubeBox Empty S.value)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis short j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (commonStep : ℕ) (hstep : commonStep ≠ 0) (cLong : Long → ℤ)
    (hp : ∀ l, (primes l).Prime)
    (hcoprime : Pairwise (fun l k => (primes l ^ exponent l).Coprime (primes k ^ exponent k)))
    {q : ℕ} [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (test : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) →
      (Out → ZMod q) → ℂ) :
    let poly := allocatedForecastPolynomial short base noise deck projection
    let c := allocatedOriginalSampleInactiveCoefficients B selected sample
    (allocatedInactiveAffineIntervalLaw B U basis S H parameterStep start hinside hH).complexMean (fun u =>
      (FiniteProbabilityWeights.uniform (Active → ZMod q)).complexMean (fun ar =>
        (FiniteProbabilityWeights.uniform (G → ZMod q)).complexMean (fun rG =>
          test (forecastInactiveShortGrid B U basis S selected c u)
            (allocatedJointResidueOutput B U basis S base noise deck projection q
              (fun g => (cLong (Sum.inl g) : ZMod q) + (commonStep : ZMod q) * rG g)
              (allocatedPrincipalResidueJoin B U basis S q u
                (fun a => (cLong (Sum.inr a) : ZMod q) + (commonStep : ZMod q) * ar a)))))) =
      ∑' z, 𝔼 b : Out → ZMod N,
        ((rationalInactiveForecast (principalAffineIntervalLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S)
      H parameterStep start hinside hH)
          (fun _ => crtPolynomialInputLaw primes exponent
            (fun l => padicValNat (primes l) commonStep) hcoprime
            (fun l v => (cLong v : ZMod (primes l ^ exponent l))))
          (forecastInactiveFixedOutput B U basis S selected c xref)
          (fun v => integerLongPolynomialOutput poly (fun k => (v k.1 k.2 : ℤ)) N)
          N gridVolume z b / gridVolume : ℝ) : ℂ) *
            test z (fun j => ZMod.castHom hq (ZMod q) (b j)) := by
  intro poly c
  rw [← allocatedAffineFixedPath_crtRationalForecast_reference B U basis S H parameterStep
    start hinside hH primes exponent hR hσ selected hsmall sample hs xref
    base noise deck projection commonStep hstep cLong hp hcoprime hq hV test]
  apply congrArg (allocatedInactiveAffineIntervalLaw B U basis S H parameterStep start hinside hH).complexMean
  funext u
  simp_rw [allocatedJointResidueOutput_join]
  have hlong (ar : Active → ZMod q) (rG : G → ZMod q) :
      Sum.elim
        (fun g => (cLong (Sum.inl g) : ZMod q) + (commonStep : ZMod q) * rG g)
        (fun a => (cLong (Sum.inr a) : ZMod q) + (commonStep : ZMod q) * ar a) =
      (fun v => (cLong v : ZMod q) + (commonStep : ZMod q) * Sum.elim rG ar v) := by
    funext v
    cases v <;> rfl
  simp_rw [hlong]
  exact affineReference_uniform_sum_flip
    (fun r : Long → ZMod q =>
      test (forecastInactiveShortGrid B U basis S selected c u)
        (fun o => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
          (Sum.elim (fun v => (cLong v : ZMod q) + (commonStep : ZMod q) * r v)
            (fun k => (allocatedShortPrincipalRaw B U basis S u k : ZMod q))) (poly o)))

end Erdos3.VectorPolynomial

end

end OAI
