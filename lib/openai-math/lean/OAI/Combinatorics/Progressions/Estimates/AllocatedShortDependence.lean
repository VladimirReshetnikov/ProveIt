import OAI.Combinatorics.Progressions.Lattices.AllocatedIntegerJet
import OAI.Combinatorics.Progressions.Lattices.AllocatedIntegerTailZero
import OAI.Combinatorics.Progressions.Lattices.WeightedIntegerGridInversion

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def integerArrayJetImage {X J V α O : Type*} [Fintype J] [DecidableEq α]
    (e : J → V →₀ ℕ) (a : X → J → ℤ) (vertices : X → Finset α → V → ℤ)
    (rows : O → Finset α) (center : O → ℤ) (x : X) : O → ℤ :=
  center+integerJetMatrix (fun j => MvPolynomial.monomial (e j) (1 : ℤ)) (vertices x) rows *ᵥ a x

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (hσ1 : ∀ j, σ j ≤ 1)
variable (j : Fin m) (i : Fin (n j))
variable {X α O : Type} [Fintype X] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (p : FiniteProbabilityWeights X)
variable (a : X → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1) → ℤ)
variable (ha : ∀ x, p.weight x ≠ 0 → ∀ d,
  a x d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
variable (vertices : X → Finset α → LayerSamplerVariables G I n B → ℤ)
variable (rows : O → Finset α) (q : ℕ) (hrows : ∀ o, (rows o).card ≤ q)
variable (hx : ∀ x, p.weight x ≠ 0 → ∀ o t, t ∈ (rows o).powerset →
  ∀ v, |(vertices x t v : ℝ)| ≤ layerSamplerBox B U basis S v)

include hR hσ S hσ1 ha hrows hx

omit [Fintype O] [DecidableEq O] in
theorem allocatedLayerIntegerImage_support (center : O → ℤ) (x : X) (hp : p.weight x ≠ 0) (o : O) :
    |(integerArrayJetImage Subtype.val a vertices rows center x o : ℝ)-center o| ≤
      (allocatedIntegerJetRadius q (R j) : ℝ)*(basisAxisScale (basis j) i : ℝ) := by
  simp only [integerArrayJetImage, Pi.add_apply, Int.cast_add, add_sub_cancel_left]
  apply (allocatedLayerIntegerJet_bound B U basis hR hσ S hσ1 j i (a x) (ha x hp)
    (vertices x) rows o q (hrows o) (hx x hp o)).trans
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg _)

theorem allocatedLayerIntegerImage_weighted_inversion (w : X → ℂ) (M : ℕ) [NeZero M]
    (hM : M = (2*allocatedIntegerJetRadius q (R j)+1)*basisAxisScale (basis j) i)
    (center z : O → ℤ)
    (hz : centeredFundamentalBox (allocatedIntegerJetRadius q (R j))
      (basisAxisScale (basis j) i) center z) :
    (∑ k : O → Fin M, weightedIntegerGridCoefficient p
      (integerArrayJetImage Subtype.val a vertices rows center) w M k *
        star (rectangularGridCharacter M k z)) =
      (M : ℂ)^Fintype.card O * p.complexMean
        (fun x => if integerArrayJetImage Subtype.val a vertices rows center x = z then w x else 0) := by
  exact weightedIntegerGrid_image_on_centered_box p
    (integerArrayJetImage Subtype.val a vertices rows center) w M center z hM
    (basisAxisScale_pos (basis j) i)
    (allocatedLayerIntegerImage_support B U basis hR hσ S hσ1 j i p a ha vertices rows q hrows hx center) hz

variable {T : ℕ} (hT : 0 < T) (hTS : T ≤ S.value)
variable (hshort : integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value
  (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) < T)

include hT hTS hshort

noncomputable def allocatedLayerShortIntegerImageAxis : IntegerFourierAxis := by
  letI : NeZero (basisAxisScale (basis j) i) := ⟨(basisAxisScale_pos (basis j) i).ne'⟩
  exact shortIntegerImageAxis p (integerArrayJetImage Subtype.val a vertices rows)
    (allocatedIntegerJetRadius q (R j)) (Nat.zero_lt_succ _) hT hTS hshort
    (allocatedLayerIntegerImage_support B U basis hR hσ S hσ1 j i p a ha vertices rows q hrows hx)

theorem allocatedLayerShortIntegerImageAxis_exact :
    let A := allocatedLayerShortIntegerImageAxis B U basis hR hσ S hσ1 j i p a ha
      vertices rows q hrows hx hT hTS hshort
    A.law = p ∧ A.image = integerArrayJetImage Subtype.val a vertices rows ∧
      A.scale = basisAxisScale (basis j) i ∧ A.countExponent = 0 ∧
      ∀ ε, A.residualBound ε = 0 := ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem allocatedLayerShortIntegerImageAxis_log_bounds {u t r : ℝ}
    (hu : 0 ≤ u) (hr : 0 ≤ r)
    (hγu : (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card)⁻¹ ≤ Real.exp u)
    (hTt : (T : ℝ) ≤ Real.exp t) (hRr : R j ≤ Real.exp r) :
    let A := allocatedLayerShortIntegerImageAxis B U basis hR hσ S hσ1 j i p a ha
      vertices rows q hrows hx hT hTS hshort
    let V := (q+r+1)+u+4+((j.val+1 : ℕ) : ℝ)*(t+1)
    (A.period : ℝ) ≤ Real.exp V ∧
      A.countConstant ≤ Real.exp (Fintype.card O*V) ∧
      A.coefficientCap ≤ Real.exp (Fintype.card O*V) ∧
      ∀ ε, A.denominatorBound ε ≤ Real.exp V := by
  let : NeZero (basisAxisScale (basis j) i) := ⟨(basisAxisScale_pos (basis j) i).ne'⟩
  exact shortIntegerImageAxis_log_bounds p (integerArrayJetImage Subtype.val a vertices rows)
    (allocatedIntegerJetRadius q (R j)) (Nat.zero_lt_succ _) hT hTS hshort
    (allocatedLayerIntegerImage_support B U basis hR hσ S hσ1 j i p a ha vertices rows q hrows hx)
    (principalProfileSize_pos (hR j) _) hu hγu hTt (by positivity)
    (allocatedIntegerJetRadius_le_exp q (hR j).le hr hRr)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)

theorem allocatedLayerInteger_moderate_tail_zero
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (d : Slots) (hd₀ : d ≠ constantCoefficientSlot _ _)
    (hdP : d ∉ layerIntegerPrincipalSlots B j i) : a d = 0 := by
  exact allocatedIntegerCoordinate_tail_zero (layerIntegerPrincipalSlots B j i)
    (constantCoefficientSlot _ _) (j.val+1) (basisAxisScale (basis j) i) S.value (layerTailDegree m)
    (Nat.zero_lt_succ _) (basisAxisScale_pos (basis j) i) S.positive
    (layerSamplerBox B U basis S)
    (fun v => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S v))
    (layerSamplerBox_le B U basis S) Subtype.val
    (fun e => e.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j i) (S.width j) hmoderate d hd₀ hdP (ha d)

theorem allocatedLayerInteger_moderate_eval
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (x : LayerSamplerVariables G I n B → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) + ∑ b : B ⟨j, Sum.inr i⟩,
        a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) *
          ∏ v : Fin (j.val+1), x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) := by
  exact integerPrincipalPolynomial_eval (layerSamplerDegree I n) ⟨j, Sum.inr i⟩
    (Nat.zero_lt_succ _) a
    (allocatedLayerInteger_moderate_tail_zero B U basis hR hσ S j i hmoderate a ha) x

theorem allocatedLayerInteger_moderate_eval_congr
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a a' : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (ha' : ∀ d, a' d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (hconstant : a (constantCoefficientSlot _ _) = a' (constantCoefficientSlot _ _))
    (hcoeff : ∀ b : B ⟨j, Sum.inr i⟩,
      a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        a' (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
    (x x' : LayerSamplerVariables G I n B → ℤ)
    (hprincipal : ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
      x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) = x' (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      MvPolynomial.eval x' (integerMonomialArrayPolynomial Subtype.val a') := by
  rw [allocatedLayerInteger_moderate_eval B U basis hR hσ S j i hmoderate a ha x,
    allocatedLayerInteger_moderate_eval B U basis hR hσ S j i hmoderate a' ha' x', hconstant]
  simp only [hcoeff, hprincipal]

theorem allocatedLayerInteger_moderateJet_congr
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    (a a' : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (ha' : ∀ d, a' d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (hconstant : a (constantCoefficientSlot _ _) = a' (constantCoefficientSlot _ _))
    (hcoeff : ∀ b : B ⟨j, Sum.inr i⟩,
      a (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        a' (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
    {α O : Type*} [DecidableEq α]
    (vertices vertices' : Finset α → LayerSamplerVariables G I n B → ℤ)
    (rows : O → Finset α)
    (hprincipal : ∀ o t, t ∈ (rows o).powerset →
      ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
        vertices t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) =
          vertices' t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ)) vertices rows *ᵥ a =
      integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ)) vertices' rows *ᵥ a' := by
  funext o
  simp only [integerJetMatrix_apply_coefficients, MvPolynomial.C_mul_monomial, mul_one]
  change booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
      (integerMonomialArrayPolynomial Subtype.val a)) (rows o) =
    booleanCoefficient (fun t => MvPolynomial.eval (vertices' t)
      (integerMonomialArrayPolynomial Subtype.val a')) (rows o)
  unfold booleanCoefficient
  apply Finset.sum_congr rfl
  intro t ht
  exact congrArg (fun v : ℤ => (-1) ^ (rows o \ t).card * v)
    (allocatedLayerInteger_moderate_eval_congr B U basis hR hσ S j i hmoderate
      a a' ha ha' hconstant hcoeff (vertices t) (vertices' t) (hprincipal o t ht))

theorem allocatedLayerModerateIntegerImage_freeze
    (hmoderate : basisAxisScale (basis j) i ≤ S.value^(layerTailDegree m+1))
    {X α O : Type*} [DecidableEq α]
    (a : X → Slots → ℤ)
    (vertices : X → Finset α → LayerSamplerVariables G I n B → ℤ)
    (rows : O → Finset α) (center : O → ℤ) (x x' : X)
    (ha : ∀ d, a x d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (ha' : ∀ d, a x' d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (hconstant : a x (constantCoefficientSlot _ _) = a x' (constantCoefficientSlot _ _))
    (hcoeff : ∀ b : B ⟨j, Sum.inr i⟩,
      a x (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b) =
        a x' (principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b))
    (hprincipal : ∀ o t, t ∈ (rows o).powerset →
      ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
        vertices x t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) =
          vertices x' t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    integerArrayJetImage Subtype.val a vertices rows center x =
      integerArrayJetImage Subtype.val a vertices rows center x' := by
  unfold integerArrayJetImage
  rw [allocatedLayerInteger_moderateJet_congr B U basis hR hσ S j i hmoderate
    (a x) (a x') ha ha' hconstant hcoeff (vertices x) (vertices x') rows hprincipal]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))

local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)

theorem allocatedLayerInteger_inactive_eval
    (hsmall : basisAxisScale (basis j) i ≤ S.value^(j.val+1))
    (a : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (x : LayerSamplerVariables G I n B → ℤ) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      a (constantCoefficientSlot _ _) +
        inactivePrincipalCoefficient (basisAxisScale (basis j) i)
          (inactiveDenominator (principalProfileSize (R j)
            (layerIntegerPrincipalSlots (G := G) B j i).card)) * ∑ b : B ⟨j, Sum.inr i⟩,
        ∏ v : Fin (j.val+1), x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) := by
  classical
  obtain ⟨htail, hprincipal⟩ :=
    allocatedLayerInteger_inactive_structure B U basis hR hσ S j i hsmall a ha
  erw [integerPrincipalPolynomial_eval (layerSamplerDegree I n) ⟨j, Sum.inr i⟩
    (Nat.zero_lt_succ _) a htail x, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  have hb : principalCoefficientSlot (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ b ∈
      layerIntegerPrincipalSlots (G := G) B j i :=
    (mem_principalCoefficientSlots _ _ _).mpr ⟨b, rfl⟩
  rw [hprincipal _ hb]
  rfl

theorem allocatedLayerInteger_inactive_eval_congr
    (hsmall : basisAxisScale (basis j) i ≤ S.value^(j.val+1))
    (a a' : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (ha' : ∀ d, a' d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (hconstant : a (constantCoefficientSlot _ _) = a' (constantCoefficientSlot _ _))
    (x x' : LayerSamplerVariables G I n B → ℤ)
    (hprincipal : ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
      x (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) = x' (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    MvPolynomial.eval x (integerMonomialArrayPolynomial Subtype.val a) =
      MvPolynomial.eval x' (integerMonomialArrayPolynomial Subtype.val a') := by
  rw [allocatedLayerInteger_inactive_eval B U basis hR hσ S j i hsmall a ha x,
    allocatedLayerInteger_inactive_eval B U basis hR hσ S j i hsmall a' ha' x', hconstant]
  simp only [hprincipal]

theorem allocatedLayerInteger_inactiveJet_congr
    (hsmall : basisAxisScale (basis j) i ≤ S.value^(j.val+1))
    (a a' : Slots → ℤ)
    (ha : ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (ha' : ∀ d, a' d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (hconstant : a (constantCoefficientSlot _ _) = a' (constantCoefficientSlot _ _))
    {α O : Type*} [DecidableEq α]
    (vertices vertices' : Finset α → LayerSamplerVariables G I n B → ℤ)
    (rows : O → Finset α)
    (hprincipal : ∀ o t, t ∈ (rows o).powerset →
      ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
        vertices t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) =
          vertices' t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ)) vertices rows *ᵥ a =
      integerJetMatrix (fun d : Slots => MvPolynomial.monomial d.val (1 : ℤ)) vertices' rows *ᵥ a' := by
  funext o
  simp only [integerJetMatrix_apply_coefficients, MvPolynomial.C_mul_monomial, mul_one]
  change booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
      (integerMonomialArrayPolynomial Subtype.val a)) (rows o) =
    booleanCoefficient (fun t => MvPolynomial.eval (vertices' t)
      (integerMonomialArrayPolynomial Subtype.val a')) (rows o)
  unfold booleanCoefficient
  apply Finset.sum_congr rfl
  intro t ht
  exact congrArg (fun v : ℤ => (-1) ^ (rows o \ t).card * v)
    (allocatedLayerInteger_inactive_eval_congr B U basis hR hσ S j i hsmall
      a a' ha ha' hconstant (vertices t) (vertices' t) (hprincipal o t ht))

theorem allocatedLayerShortIntegerImage_freeze {T : ℕ} (hTS : T ≤ S.value)
    (hshort : integerAxisSideLength (j.val+1) (basisAxisScale (basis j) i) S.value
      (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) < T)
    {X α O : Type*} [DecidableEq α]
    (a : X → Slots → ℤ)
    (vertices : X → Finset α → LayerSamplerVariables G I n B → ℤ)
    (rows : O → Finset α) (center : O → ℤ) (x x' : X)
    (ha : ∀ d, a x d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (ha' : ∀ d, a x' d ∈ (allocatedLayerIntegerPMFs B U basis hR hσ S j i d).support)
    (hconstant : a x (constantCoefficientSlot _ _) = a x' (constantCoefficientSlot _ _))
    (hprincipal : ∀ o t, t ∈ (rows o).powerset →
      ∀ (b : B ⟨j, Sum.inr i⟩) (v : Fin (j.val+1)),
        vertices x t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩) =
          vertices x' t (.inr ⟨⟨j, Sum.inr i⟩, b, v⟩)) :
    integerArrayJetImage Subtype.val a vertices rows center x =
      integerArrayJetImage Subtype.val a vertices rows center x' := by
  unfold integerArrayJetImage
  rw [allocatedLayerInteger_inactiveJet_congr B U basis hR hσ S j i
    (integerAxisSideLength_inactive_of_short hTS hshort).1
    (a x) (a x') ha ha' hconstant (vertices x) (vertices x') rows hprincipal]

end Erdos3.VectorPolynomial

end

end OAI
