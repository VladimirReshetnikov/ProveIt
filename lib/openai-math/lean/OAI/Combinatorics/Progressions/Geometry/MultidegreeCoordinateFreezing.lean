/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

def retainedCoordinateWeight (S : Finset σ) (i : σ) : ℕ := if i ∈ S then 1 else 0

def freezeCoordinates (S : Finset σ) (b : σ → ℤ) (x : S → ℤ) (i : σ) : ℤ :=
  if h : i ∈ S then x ⟨i, h⟩ else b i

noncomputable def freezingPolynomial (S : Finset σ) (b : σ → ℤ) (i : σ) :
    MvPolynomial S ℚ :=
  if h : i ∈ S then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i : ℚ)

theorem freezingPolynomial_support (S : Finset σ) (b : σ → ℤ) (i : σ) :
    freezingPolynomial S b i ∈ weightedSupportLE (fun _ : S => 1) (retainedCoordinateWeight S i) := by
  by_cases hi : i ∈ S
  · simp only [freezingPolynomial, retainedCoordinateWeight, dite_eq_left hi, ite_eq_left hi]
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : S => 1) (Finsupp.single (⟨i, hi⟩ : S) 1) (1 : ℚ)
  · simp only [freezingPolynomial, retainedCoordinateWeight, dite_eq_right hi, ite_eq_right hi]
    exact weightedSupportLE_C _ _ _

theorem freezingPolynomial_eval (S : Finset σ) (b : σ → ℤ) (x : S → ℤ) (i : σ) :
    MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (freezingPolynomial S b i) =
      (freezeCoordinates S b x i : ℚ) := by
  by_cases hi : i ∈ S <;> simp [freezingPolynomial, freezeCoordinates, hi]

theorem retainedCoordinate_degree [Fintype σ] (S : Finset σ) (bound : σ → ℕ) :
    multidegreeWeight (retainedCoordinateWeight S) bound = ∑ i ∈ S, bound i := by
  simp [multidegreeWeight, retainedCoordinateWeight]

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_normalized_frozen_orbit (S : Finset σ) (b : σ → ℤ)
    (p : F.PolynomialOrbit) (a γ : F.Group)
    (hzero : F.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ) :
    ∃ q : (F.weightedFiltration (retainedCoordinateWeight S)).PolynomialOrbit (fun _ : S => 1),
      (F.weightedFiltration (retainedCoordinateWeight S)).polynomialOrbitEval _ 0 q = 1 ∧
      ∀ x : S → ℤ, F.weightedGroupInclusion (retainedCoordinateWeight S)
        ((F.weightedFiltration (retainedCoordinateWeight S)).polynomialOrbitEval _ x q) =
          a⁻¹ * F.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
  let r := VectorPolynomial.substitute (freezingPolynomial S b) (p.log F)
  have hr : F.WeightedAdapted (retainedCoordinateWeight S) (fun _ : S => 1) r :=
    F.weightedAdapted_substitute _ _ _ (freezingPolynomial_support S b) (p.adapted F)
  have heval (x : S → ℤ) : (⟨eval (fun i => (x i : ℚ)) r⟩ : F.Group) =
      F.polynomialOrbitEval (freezeCoordinates S b x) p := by
    apply NilpotentLieBCHGroup.ext
    change eval (fun i => (x i : ℚ)) r = _
    simp only [r, eval_substitute, freezingPolynomial_eval, F.polynomialOrbitEval_coord]
  have hz : (⟨eval (fun _ => 0) r⟩ : F.Group) = a * γ := by
    simpa only [Pi.zero_apply, Int.cast_zero] using (heval 0).trans hzero
  refine ⟨F.normalizedWeightedOrbit _ _ (fun _ => by decide) r hr a γ hz,
    F.normalizedWeightedOrbit_zero _ _ (fun _ => by decide) r hr a γ hz, ?_⟩
  intro x
  rw [F.normalizedWeightedOrbit_eval, heval]

theorem exists_frozen_orbit (S : Finset σ) (b : σ → ℤ) (p : F.PolynomialOrbit) :
    ∃ q : (F.weightedFiltration (retainedCoordinateWeight S)).PolynomialOrbit (fun _ : S => 1),
      (F.weightedFiltration (retainedCoordinateWeight S)).polynomialOrbitEval _ 0 q = 1 ∧
      ∀ x : S → ℤ, F.weightedGroupInclusion (retainedCoordinateWeight S)
        ((F.weightedFiltration (retainedCoordinateWeight S)).polynomialOrbitEval _ x q) =
          (F.polynomialOrbitEval (freezeCoordinates S b 0) p)⁻¹ *
            F.polynomialOrbitEval (freezeCoordinates S b x) p := by
  obtain ⟨q, hq, hval⟩ := F.exists_normalized_frozen_orbit S b p
    (F.polynomialOrbitEval (freezeCoordinates S b 0) p) 1 (by rw [mul_one])
  exact ⟨q, hq, fun x => by simpa only [inv_one, mul_one] using hval x⟩

end MultidegreeLieFiltration

end Erdos3

end

end OAI
