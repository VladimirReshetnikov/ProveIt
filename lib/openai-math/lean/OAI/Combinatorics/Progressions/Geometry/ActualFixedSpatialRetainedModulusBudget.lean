import OAI.Combinatorics.Progressions.Lattices.ActualFixedSpatialGoodPrimeDeletion

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem crtPolynomialInputLaw_integerLong_density_of_output
    {L V Inactive Out : Type*} [Fintype L] [Fintype V] [Fintype Out] [DecidableEq Out]
    (p A e : L → ℕ) [∀ l, NeZero (p l)]
    (hq : Pairwise (fun l k => (p l ^ A l).Coprime (p k ^ A k)))
    (origin : ∀ l, V → ZMod (p l ^ A l))
    (poly : Out → MvPolynomial (V ⊕ Inactive) ℤ) (inactive : Inactive → ℤ)
    (Y : (∀ l, V → ZMod (p l ^ A l)) → Out → ℤ)
    (hY : ∀ x j, Y x j = MvPolynomial.eval
      (Sum.elim (fun v => ((prescribedCRTPolynomialInput p A e hq origin x v).val : ℤ))
        inactive) (poly j))
    (β : Out → ZMod (∏ l, p l ^ A l)) :
    letI : NeZero (∏ l, p l ^ A l) :=
      ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
    rationalOutputDensity (crtPolynomialInputLaw p A e hq origin)
      (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l)) (∏ l, p l ^ A l) β =
    rationalOutputDensity (crtPrimePowerPolynomialLaw (V := V) p A) Y (∏ l, p l ^ A l) β := by
  let : NeZero (∏ l, p l ^ A l) :=
    ⟨Finset.prod_ne_zero_iff.mpr (fun l _ => pow_ne_zero _ (NeZero.ne (p l)))⟩
  unfold rationalOutputDensity finiteImageMass crtPolynomialInputLaw
  rw [FiniteProbabilityWeights.fiberLaw_mean]
  congr 1
  apply congrArg (crtPrimePowerPolynomialLaw (V := V) p A).mean
  funext x
  have heq : (fun j => (integerLongPolynomialOutput poly inactive (∏ l, p l ^ A l)
      (prescribedCRTPolynomialInput p A e hq origin x) j : ZMod (∏ l, p l ^ A l))) =
      fun j => (Y x j : ZMod (∏ l, p l ^ A l)) := by
    funext j
    exact congrArg (fun a : ℤ => (a : ZMod (∏ l, p l ^ A l))) (hY x j).symm
  dsimp only
  simp only [heq]

namespace VectorPolynomial
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

@[instance_reducible] noncomputable def retainedLabelDecidableEq (cutoff : ℕ) :
    DecidableEq (path.referenceRetainedPrimes cutoff) := Classical.decEq _

attribute [local instance] retainedLabelDecidableEq

noncomputable def referenceRetainedCRTModulus (cutoff : ℕ) : ℕ :=
  ∏ p : path.referenceRetainedPrimes cutoff, p.val.val ^ path.exponent p.val.val

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_eq (cutoff : ℕ) :
    path.referenceRetainedCRTModulus cutoff = path.referenceRetainedModulus cutoff := by
  exact Finset.prod_coe_sort (path.referenceRetainedPrimes cutoff)
    (fun p : path.primes => p.val ^ path.exponent p.val)

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_dvd (cutoff : ℕ) :
    path.referenceRetainedCRTModulus cutoff ∣ path.referenceModulus := by
  rw [path.referenceRetainedCRTModulus_eq]
  exact path.referenceRetainedModulus_dvd cutoff

local instance smallReferencePrimeNeZero : ∀ p : path.primes, NeZero p.val :=
  path.primeNeZero

local instance smallReferenceModulusNeZero (cutoff : ℕ) :
    NeZero (path.referenceRetainedCRTModulus cutoff) :=
  ⟨by rw [path.referenceRetainedCRTModulus_eq]; exact (path.referenceRetainedModulus_pos cutoff).ne'⟩

noncomputable def referenceRetainedCRTInputLaw (cutoff : ℕ) : FiniteProbabilityWeights
    (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod (path.referenceRetainedCRTModulus cutoff)) :=
  crtPolynomialInputLaw (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
    (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
    (fun p : path.referenceRetainedPrimes cutoff => path.prescribed p.val.val)
    (primePower_crt_coprime (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
      (fun p => path.prime p.val.val p.val.property)
      (Subtype.val_injective.comp Subtype.val_injective)) (fun p => path.origin p.val)

omit [Fintype Tsp] in

theorem referenceRetainedCRT_density_eq (cutoff : ℕ)
    (raw : PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod (path.referenceRetainedCRTModulus cutoff)) :
    rationalOutputDensity (path.referenceRetainedCRTInputLaw cutoff)
      (integerLongPolynomialOutput path.referencePolynomial raw
        (path.referenceRetainedCRTModulus cutoff)) (path.referenceRetainedCRTModulus cutoff) β =
    rationalOutputDensity
      (crtPrimePowerPolynomialLaw
        (V := LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B)
        (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val))
      (crtPrimePowerIntegerPolynomialOutput
        (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.prescribed p.val.val)
        (primePower_crt_coprime (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
          (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
          (fun p => path.prime p.val.val p.val.property)
          (Subtype.val_injective.comp Subtype.val_injective))
        (path.localReferencePolynomial raw) (fun p => path.origin p.val))
      (path.referenceRetainedCRTModulus cutoff) β := by
  apply crtPolynomialInputLaw_integerLong_density_of_output
  intro x o
  simpa only [crtPrimePowerIntegerPolynomialOutput, prescribedCRTPolynomialInput,
    localReferencePolynomial, referencePolynomial, allocatedForecastPolynomial] using
    (allocatedSeparatedCongruencePolynomial_eval (allocatedShortAxis (I := I) U b S.value)
      o.1 path.base path.noise (allocatedReadDeck path.read)
      (fun a => allocatedReadProjection path.read ⟨o.1, a.val⟩) o.2 _ raw).symm

noncomputable def retainedCRTReferenceForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  rationalInactiveForecast inactive (fun _ => path.referenceRetainedCRTInputLaw cutoff) gridPoint
    (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i)
      (path.referenceRetainedCRTModulus cutoff))
    (path.referenceRetainedCRTModulus cutoff) gridVolume z
    (fun j => ZMod.castHom (path.referenceRetainedCRTModulus_dvd cutoff)
      (ZMod (path.referenceRetainedCRTModulus cutoff)) (β j))

noncomputable def retainedCRTIndependentForecast {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) : ℝ :=
  rationalInactiveForecast inactive
    (fun _ => crtPrimePowerPolynomialLaw
      (V := LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B)
      (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)) gridPoint
    (fun i => crtPrimePowerIntegerPolynomialOutput
      (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
      (fun p : path.referenceRetainedPrimes cutoff => path.prescribed p.val.val)
      (primePower_crt_coprime (fun p : path.referenceRetainedPrimes cutoff => p.val.val)
        (fun p : path.referenceRetainedPrimes cutoff => path.exponent p.val.val)
        (fun p => path.prime p.val.val p.val.property)
        (Subtype.val_injective.comp Subtype.val_injective))
      (path.localReferencePolynomial (raw i)) (fun p => path.origin p.val))
    (path.referenceRetainedCRTModulus cutoff) gridVolume z
    (fun j => ZMod.castHom (path.referenceRetainedCRTModulus_dvd cutoff)
      (ZMod (path.referenceRetainedCRTModulus cutoff)) (β j))

omit [Fintype Tsp] in
theorem retainedCRTIndependentForecast_eq {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    path.retainedCRTIndependentForecast inactive gridPoint raw cutoff gridVolume z β =
      path.retainedReferenceForecast inactive gridPoint raw cutoff gridVolume z β := by
  dsimp only [retainedCRTIndependentForecast, retainedReferenceForecast,
    referenceLocalDensity, referenceRetainedCRTModulus]
  have h := crt_integer_polynomial_retained_inactive_density_product inactive gridPoint
    (fun p : path.primes => p.val) (fun p : path.primes => path.exponent p.val)
    (fun p : path.primes => path.prescribed p.val)
    (primePower_crt_coprime (fun p : path.primes => p.val)
      (fun p : path.primes => path.exponent p.val)
      (fun p => path.prime p.val p.property) Subtype.val_injective)
    (fun i => path.localReferencePolynomial (raw i)) (fun _ => path.origin)
    (path.referenceRetainedPrimes cutoff) gridVolume z β
  dsimp only at h
  simp only [rationalInactiveForecast, rationalOutputDensity, ← Nat.card_eq_fintype_card] at h ⊢
  exact h

omit [Fintype Tsp] in
theorem retainedCRTReferenceForecast_eq_independent {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    path.retainedCRTReferenceForecast inactive gridPoint raw cutoff gridVolume z β =
      path.retainedCRTIndependentForecast inactive gridPoint raw cutoff gridVolume z β := by
  unfold retainedCRTReferenceForecast retainedCRTIndependentForecast rationalInactiveForecast
  congr 1
  apply congrArg (inactive.fiberMean gridPoint z)
  funext i
  exact path.referenceRetainedCRT_density_eq cutoff (raw i) _

omit [Fintype Tsp] in

theorem retainedCRTReferenceForecast_eq {Ω Z : Type*} [Fintype Ω]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (gridVolume : ℝ) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    path.retainedCRTReferenceForecast inactive gridPoint raw cutoff gridVolume z β =
      path.retainedReferenceForecast inactive gridPoint raw cutoff gridVolume z β :=
  (path.retainedCRTReferenceForecast_eq_independent inactive gridPoint raw cutoff gridVolume z β).trans
    (path.retainedCRTIndependentForecast_eq inactive gridPoint raw cutoff gridVolume z β)

omit [Fintype Tsp] in
theorem referenceRetainedCRTModulus_pos (cutoff : ℕ) :
    0 < path.referenceRetainedCRTModulus cutoff := by
  rw [path.referenceRetainedCRTModulus_eq]
  exact path.referenceRetainedModulus_pos cutoff

local instance retainedFullReferenceModulusNeZero : NeZero path.referenceModulus :=
  ⟨path.referenceModulus_pos.ne'⟩

omit [Fintype Tsp] in

theorem reference_inactive_goodPrimeDeletion_retainedCRT {Ω Z : Type*} [Fintype Ω]
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ Dmod)
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (raw : Ω → PrincipalTupleIndex B (layerSamplerDegree I n) × Option Empty → ℤ)
    (cutoff : ℕ) (hcutoff : 0 < cutoff) (hsmall : 2 / (cutoff : ℝ) ≤ 1 / 2)
    {δ : ℝ} (hδ : 0 ≤ δ) (haccuracy : 4 / (cutoff : ℝ) ≤ δ)
    (gridVolume : ℝ) (hvolume : 0 ≤ gridVolume) (z : Z)
    (β : Sigma (AllocatedCongruenceRankOutput X Eout
      (allocatedShortAxis (I := I) U b S.value)) → ZMod path.referenceModulus) :
    let full := rationalInactiveForecast inactive (fun _ => path.referenceInputLaw) gridPoint
      (fun i => integerLongPolynomialOutput path.referencePolynomial (raw i) path.referenceModulus)
      path.referenceModulus gridVolume z β
    let truncated := path.retainedCRTReferenceForecast inactive gridPoint raw cutoff gridVolume z β
    (1 - δ) * truncated ≤ full ∧ full ≤ (1 + δ) * truncated := by
  dsimp only
  rw [path.retainedCRTReferenceForecast_eq]
  exact path.reference_inactive_goodPrimeDeletion hm hD inactive gridPoint raw
    cutoff hcutoff hsmall hδ haccuracy gridVolume hvolume z β

end ActualFixedSpatialForecastPath
end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in

theorem referenceRetainedCRTModulus_log_le_tested (cutoff : ℕ)
    {Ptest : ℝ} (hPtest : 0 ≤ Ptest)
    (hexponent : ∀ p : path.primes,
      path.exponent p.val ≤ Nat.log p.val ⌈Real.exp (2 * Ptest)⌉₊) :
    Real.log (path.referenceRetainedCRTModulus cutoff : ℝ) ≤
      (4 * Ptest + 2) *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1)) := by
  obtain ⟨depth, hdepth, hprime⟩ := exists_testedPrimeDepth hPtest
  rw [path.referenceRetainedCRTModulus_eq]
  exact path.referenceRetainedModulus_log_le cutoff depth
    (fun p => (hexponent p).trans (hprime p.val (path.prime p.val p.property)))
    (4 * Ptest + 2) hdepth

omit [Fintype Tsp] in

theorem referenceRetainedCRTModulus_le_exp_tested (cutoff : ℕ)
    {Ptest : ℝ} (hPtest : 0 ≤ Ptest)
    (hexponent : ∀ p : path.primes,
      path.exponent p.val ≤ Nat.log p.val ⌈Real.exp (2 * Ptest)⌉₊) :
    (path.referenceRetainedCRTModulus cutoff : ℝ) ≤
      Real.exp ((4 * Ptest + 2) *
        (Pbad + Ppres + ((cutoff + 1 : ℕ) : ℝ) * Real.log (cutoff + 1))) := by
  exact (Real.log_le_iff_le_exp
    (Nat.cast_pos.mpr (path.referenceRetainedCRTModulus_pos cutoff))).mp
      (path.referenceRetainedCRTModulus_log_le_tested cutoff hPtest hexponent)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
