import OAI.Combinatorics.Progressions.Estimates.ActiveProfileNoise
import OAI.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R σ : Fin m → ℝ)

theorem allocatedContinuousProfileCenters_dilation (j : Fin m) (i : I j)
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
    allocatedContinuousProfileCenters B R j i e =
      nonprincipalDilation Subtype.val
        (canonicalPrincipalExponent (layerSamplerDegree I n) ⟨j, Sum.inl i⟩) (σ j) e *
      allocatedContinuousProfileCenters B R j i e :=
  boundedProfileCenter_dilation (layerSamplerDegree I n) ⟨j, Sum.inl i⟩ _ (σ j) e

theorem allocatedContinuousProfileWidths_dilation (j : Fin m) (i : I j)
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
    allocatedContinuousProfileWidths B R σ j i e =
      nonprincipalDilation Subtype.val
        (canonicalPrincipalExponent (layerSamplerDegree I n) ⟨j, Sum.inl i⟩) (σ j) e *
      allocatedContinuousProfileWidths B R (fun _ => 1) j i e := by
  have ht (N : ℕ) : tailProfileSize (R j) (σ j) N = σ j * tailProfileSize (R j) 1 N := by
    unfold tailProfileSize
    ring
  unfold allocatedContinuousProfileWidths
  rw [ht]
  exact boundedProfileWidth_dilation (layerSamplerDegree I n) ⟨j, Sum.inl i⟩ _ _ _ _ e

theorem allocatedIntegerProfileCenters_dilation (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
    allocatedIntegerProfileCenters B R j i e =
      nonprincipalDilation Subtype.val
        (canonicalPrincipalExponent (layerSamplerDegree I n) ⟨j, Sum.inr i⟩) (σ j) e *
      allocatedIntegerProfileCenters B R j i e :=
  boundedProfileCenter_dilation (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ _ (σ j) e

theorem allocatedIntegerProfileWidths_dilation (j : Fin m) (i : Fin (n j))
    (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
    allocatedIntegerProfileWidths B R σ j i e =
      nonprincipalDilation Subtype.val
        (canonicalPrincipalExponent (layerSamplerDegree I n) ⟨j, Sum.inr i⟩) (σ j) e *
      allocatedIntegerProfileWidths B R (fun _ => 1) j i e := by
  have ht (N : ℕ) : tailProfileSize (R j) (σ j) N = σ j * tailProfileSize (R j) 1 N := by
    unfold tailProfileSize
    ring
  unfold allocatedIntegerProfileWidths
  rw [ht]
  exact boundedProfileWidth_dilation (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ _ _ _ _ e

theorem allocatedContinuousProfile_polynomial_split (j : Fin m) (i : I j)
    (r : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ) :
    let γ := principalProfileSize (R j) (layerContinuousPrincipalSlots (G := G) B j i).card
    let ε := tailProfileSize (R j) 1
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)))
    monomialArrayPolynomial Subtype.val (fun e =>
      allocatedContinuousProfileCenters B R j i e + allocatedContinuousProfileWidths B R σ j i e * r e) =
      MvPolynomial.C (R j / 4 * r (constantCoefficientSlot _ _)) +
      (∑ b, MvPolynomial.monomial (canonicalPrincipalExponent (layerSamplerDegree I n) ⟨j, Sum.inl i⟩ b)
        (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inl i⟩ b))) +
      ∑ e ∈ nonprincipalCoefficientSlots Subtype.val
          (canonicalPrincipalExponent (layerSamplerDegree I n) ⟨j, Sum.inl i⟩),
        MvPolynomial.monomial e.val (σ j * (ε * r e)) := by
  have ht (N : ℕ) : tailProfileSize (R j) (σ j) N = σ j * tailProfileSize (R j) 1 N := by
    unfold tailProfileSize
    ring
  dsimp only
  unfold allocatedContinuousProfileCenters allocatedContinuousProfileWidths
  rw [ht]
  exact boundedProfile_polynomial_split (layerSamplerDegree I n) ⟨j, Sum.inl i⟩
    (Nat.zero_lt_succ _) _ _ _ _ r

theorem allocatedIntegerProfile_polynomial_split (j : Fin m) (i : Fin (n j))
    (r : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ) :
    let γ := principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card
    let ε := tailProfileSize (R j) 1
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)))
    monomialArrayPolynomial Subtype.val (fun e =>
      allocatedIntegerProfileCenters B R j i e + allocatedIntegerProfileWidths B R σ j i e * r e) =
      MvPolynomial.C (R j / 4 * r (constantCoefficientSlot _ _)) +
      (∑ b, MvPolynomial.monomial (canonicalPrincipalExponent (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b)
        (3 * γ / 2 + γ / 2 * r (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))) +
      ∑ e ∈ nonprincipalCoefficientSlots Subtype.val
          (canonicalPrincipalExponent (layerSamplerDegree I n) ⟨j, Sum.inr i⟩),
        MvPolynomial.monomial e.val (σ j * (ε * r e)) := by
  have ht (N : ℕ) : tailProfileSize (R j) (σ j) N = σ j * tailProfileSize (R j) 1 N := by
    unfold tailProfileSize
    ring
  dsimp only
  unfold allocatedIntegerProfileCenters allocatedIntegerProfileWidths
  rw [ht]
  exact boundedProfile_polynomial_split (layerSamplerDegree I n) ⟨j, Sum.inr i⟩
    (Nat.zero_lt_succ _) _ _ _ _ r

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedAxisProfilePolynomial (R σ : Fin m → ℝ) :
    (a : LayerSamplerAxis I n) → (SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) →
    MvPolynomial (LayerSamplerVariables G I n B) ℝ
  | ⟨j, .inl i⟩, r => monomialArrayPolynomial Subtype.val (fun e =>
      allocatedContinuousProfileCenters B R j i e + allocatedContinuousProfileWidths B R σ j i e * r e)
  | ⟨j, .inr i⟩, r => monomialArrayPolynomial Subtype.val (fun e =>
      allocatedIntegerProfileCenters B R j i e + allocatedIntegerProfileWidths B R σ j i e * r e)

theorem allocatedAxisProfilePolynomial_eq (R σ : Fin m → ℝ) (a : LayerSamplerAxis I n)
    (r : SamplerCoefficientSlot G B (layerSamplerDegree I n) a → ℝ) :
    allocatedAxisProfilePolynomial B R σ a r =
      monomialArrayPolynomial Subtype.val (fun e =>
        coefficientProfileCenter (principalCoefficientSlots (layerSamplerDegree I n) a)
          (principalProfileSize (R a.1) (Fintype.card (B a))) e +
        coefficientProfileWidth (principalCoefficientSlots (layerSamplerDegree I n) a)
          (constantCoefficientSlot _ _) (R a.1 / 4)
          (principalProfileSize (R a.1) (Fintype.card (B a)))
          (tailProfileSize (R a.1) (σ a.1)
            (Fintype.card (SamplerCoefficientSlot G B (layerSamplerDegree I n) a))) e * r e) := by
  rcases a with ⟨j, i⟩
  cases i with
  | inl i =>
    simp only [allocatedAxisProfilePolynomial, allocatedContinuousProfileCenters,
      allocatedContinuousProfileWidths, layerContinuousPrincipalSlots_card]
    rfl
  | inr i =>
    simp only [allocatedAxisProfilePolynomial, allocatedIntegerProfileCenters,
      allocatedIntegerProfileWidths, layerIntegerPrincipalSlots_card]
    rfl

theorem allocatedPartitionedProfileJet_eq {Z α : Type*} [Fintype α] [DecidableEq α]
    (P : LayerSamplerAxis I n → Prop) [DecidablePred P] (extra : G → Option α → Z)
    {O : {a // ¬P a} → Type*} (sets : ∀ a, O a → Finset α) (R : Fin m → ℝ) (t : ℝ)
    (y : PartitionedProfileNoiseIndex G Z α B (layerSamplerDegree I n) P → ℝ)
    (x : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬P a) → ℝ)
    (o : Σ a, O a) :
    partitionedAllocatedProfileJet (layerSamplerDegree I n) P extra sets (fun a => R a.1) t y x o =
      booleanCoefficient (fun s => MvPolynomial.eval
        (normalizedCubeTuple (partitionedPrincipalInput P extra) (fun j => y (.inl j)) x s)
        (allocatedAxisProfilePolynomial B R (fun _ => t) o.1.val
          (fun e => y (.inr ⟨o.1.val, e⟩)))) (sets o.1 o.2) := by
  have ht (j : Fin m) (N : ℕ) : tailProfileSize (R j) t N = t * tailProfileSize (R j) 1 N := by
    unfold tailProfileSize
    ring
  have hs (s : Finset α) : normalizedCubeTuple (partitionedProfileInput P extra) y x s =
      normalizedCubeTuple (partitionedPrincipalInput P extra) (fun j => y (.inl j)) x s :=
    funext (fun k => partitionedProfileInput_source P extra y x s k)
  unfold partitionedAllocatedProfileJet partitionedProfileJet
  simp only [allocatedAxisProfilePolynomial_eq, ht, hs]

end Erdos3.VectorPolynomial

end

end OAI
