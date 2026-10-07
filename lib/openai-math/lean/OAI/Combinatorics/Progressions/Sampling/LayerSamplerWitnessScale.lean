import OAI.Combinatorics.Progressions.Lattices.ShortIntegerCubeBudget
import OAI.Combinatorics.Progressions.Polynomial.LayerTailDegree
import OAI.Combinatorics.Progressions.Probability.EmptyCoefficientDensity

namespace OAI

section

namespace Erdos3

noncomputable def heterogeneousSamplerSides {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : D → ℝ) : SamplerTupleIndex G B h → ℕ
  | .inl _ => L
  | .inr ⟨d, _, _⟩ => match K d with
    | none => L
    | some k => integerAxisSideLength (h d) k L (γ d)

theorem heterogeneousSamplerSides_pos {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) {L : ℕ} (hL : 0 < L) (γ : D → ℝ)
    (v : SamplerTupleIndex G B h) : 0 < heterogeneousSamplerSides h K L γ v := by
  rcases v with g | ⟨d, b, v⟩
  · exact hL
  · simp only [heterogeneousSamplerSides]
    cases K d with
    | none => exact hL
    | some k => exact integerAxisSideLength_pos (hh d) hL (γ d)

theorem heterogeneousSamplerSides_le {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (hh : ∀ d, 0 < h d) (K : D → Option ℕ) {L : ℕ} (hL : 0 < L) (γ : D → ℝ)
    (v : SamplerTupleIndex G B h) : heterogeneousSamplerSides h K L γ v ≤ L := by
  rcases v with g | ⟨d, b, v⟩
  · exact le_rfl
  · simp only [heterogeneousSamplerSides]
    cases K d with
    | none => exact le_rfl
    | some k => exact integerAxisSideLength_le (hh d) hL (γ d)

theorem heterogeneousSamplerSides_integer_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : D → ℝ) (d : D) [Fintype (B d)]
    {k : ℕ} (hk : K d = some k) (e) (he : e ∈ principalCoefficientSlots (G := G) (B := B) h d) :
    monomialScale (fun v : SamplerTupleIndex G B h => (heterogeneousSamplerSides h K L γ v : ℝ)) e.val =
      (integerAxisSideLength (h d) k L (γ d) : ℝ) ^ h d := by
  obtain ⟨b, rfl⟩ := (mem_principalCoefficientSlots h d e).mp he
  change monomialScale _ (canonicalPrincipalExponent h d b) = _
  rw [monomialScale_canonicalPrincipal]
  simp only [heterogeneousSamplerSides, hk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem heterogeneousSamplerSides_continuous_principal {D G : Type*} {B : D → Type*}
    (h : D → ℕ) (K : D → Option ℕ) (L : ℕ) (γ : D → ℝ) (d : D) [Fintype (B d)]
    (hk : K d = none) (e) (he : e ∈ principalCoefficientSlots (G := G) (B := B) h d) :
    monomialScale (fun v : SamplerTupleIndex G B h => (heterogeneousSamplerSides h K L γ v : ℝ)) e.val =
      (L : ℝ) ^ h d := by
  obtain ⟨b, rfl⟩ := (mem_principalCoefficientSlots h d e).mp he
  change monomialScale _ (canonicalPrincipalExponent h d b) = _
  rw [monomialScale_canonicalPrincipal]
  simp only [heterogeneousSamplerSides, hk, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ}

abbrev LayerSamplerAxis (I : Fin m → Type*) (n : Fin m → ℕ) :=
  Σ j : Fin m, I j ⊕ Fin (n j)

def layerSamplerDegree (I : Fin m → Type*) (n : Fin m → ℕ) : LayerSamplerAxis I n → ℕ :=
  fun a => a.1.val + 1

abbrev LayerSamplerVariables (G : Type*) (I : Fin m → Type*) (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) := SamplerTupleIndex G B (layerSamplerDegree I n)

variable {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def layerContinuousPrincipalSlots (j : Fin m) (i : I j) :
    Finset (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
  principalCoefficientSlots (layerSamplerDegree I n) ⟨j, Sum.inl i⟩

noncomputable def layerIntegerPrincipalSlots (j : Fin m) (i : Fin (n j)) :
    Finset (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :=
  principalCoefficientSlots (layerSamplerDegree I n) ⟨j, Sum.inr i⟩

theorem layerContinuousPrincipalSlots_card (j : Fin m) (i : I j) :
    (layerContinuousPrincipalSlots (G := G) B j i).card = Fintype.card (B ⟨j, Sum.inl i⟩) :=
  principalCoefficientSlots_card _ _ (Nat.zero_lt_succ _)

theorem layerIntegerPrincipalSlots_card (j : Fin m) (i : Fin (n j)) :
    (layerIntegerPrincipalSlots (G := G) B j i).card = Fintype.card (B ⟨j, Sum.inr i⟩) :=
  principalCoefficientSlots_card _ _ (Nat.zero_lt_succ _)

theorem layerContinuousPrincipalSlots_not_constant (j : Fin m) (i : I j) :
    constantCoefficientSlot _ (j.val + 1) ∉ layerContinuousPrincipalSlots (G := G) B j i :=
  constantCoefficientSlot_not_principal _ _ (Nat.zero_lt_succ _)

theorem layerIntegerPrincipalSlots_not_constant (j : Fin m) (i : Fin (n j)) :
    constantCoefficientSlot _ (j.val + 1) ∉ layerIntegerPrincipalSlots (G := G) B j i :=
  constantCoefficientSlot_not_principal _ _ (Nat.zero_lt_succ _)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerDenominators : LayerSamplerAxis I n → Option ℕ :=
  fun a => Sum.elim (fun _ => none) (fun i => some (basisAxisScale (b a.1) i)) a.2

noncomputable def layerSamplerWidths (R : Fin m → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a => principalProfileSize (R a.1) (Fintype.card (B a))

noncomputable def layerSamplerSides (R : Fin m → ℝ) (L : ℕ) : LayerSamplerVariables G I n B → ℕ :=
  heterogeneousSamplerSides (layerSamplerDegree I n) (layerSamplerDenominators U b) L
    (layerSamplerWidths B R)

theorem layerSamplerSides_pos (R : Fin m → ℝ) {L : ℕ} (hL : 0 < L)
    (v : LayerSamplerVariables G I n B) : 0 < layerSamplerSides B U b R L v :=
  heterogeneousSamplerSides_pos _ (fun _ => Nat.zero_lt_succ _) _ hL _ v

theorem layerSamplerSides_le (R : Fin m → ℝ) {L : ℕ} (hL : 0 < L)
    (v : LayerSamplerVariables G I n B) : layerSamplerSides B U b R L v ≤ L :=
  heterogeneousSamplerSides_le _ (fun _ => Nat.zero_lt_succ _) _ hL _ v

theorem layerSamplerSides_integer_principal (R : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : Fin (n j)) (e) (he : e ∈ layerIntegerPrincipalSlots (G := G) B j i) :
    monomialScale (fun v : LayerSamplerVariables G I n B => (layerSamplerSides B U b R L v : ℝ)) e.val =
      (integerAxisSideLength (j.val + 1) (basisAxisScale (b j) i) L
        (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) : ℝ) ^ (j.val + 1) := by
  rw [layerIntegerPrincipalSlots_card]
  exact heterogeneousSamplerSides_integer_principal _ _ L (layerSamplerWidths B R)
    ⟨j, Sum.inr i⟩ rfl e he

theorem layerSamplerSides_continuous_principal (R : Fin m → ℝ) (L : ℕ)
    (j : Fin m) (i : I j) (e) (he : e ∈ layerContinuousPrincipalSlots (G := G) B j i) :
    monomialScale (fun v : LayerSamplerVariables G I n B => (layerSamplerSides B U b R L v : ℝ)) e.val =
      (L : ℝ) ^ (j.val + 1) :=
  heterogeneousSamplerSides_continuous_principal _ _ L (layerSamplerWidths B R)
    ⟨j, Sum.inl i⟩ rfl e he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerTailWidth (R σ : Fin m → ℝ) (j : Fin m) : ℝ :=
  tailProfileSize (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)))

noncomputable def layerSamplerGapWidth (R : Fin m → ℝ) (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  principalProfileSize (R a.1) (layerIntegerPrincipalSlots (G := G) B a.1 a.2).card

noncomputable def layerSamplerScaleBound (R σ : Fin m → ℝ) (L₀ : ℕ) : ℕ :=
  commonPolynomialInitialScale L₀ (layerSamplerTailWidth (G := G) B R σ) *
    commonPolynomialGapRatio (layerSamplerGapWidth (G := G) B R) ^ Fintype.card (Σ j, Fin (n j))

structure LayerSamplerScale (R σ : Fin m → ℝ) where
  value : ℕ
  positive : 0 < value
  width : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) ≤ layerSamplerTailWidth (G := G) B R σ j * value
  gap : ∀ j i, value ^ (j.val + 1) < basisAxisScale (b j) i →
    (principalSamplingGapRatio (layerSamplerGapWidth (G := G) B R ⟨j, i⟩) * value) ^ (j.val + 1) ≤
      basisAxisScale (b j) i

theorem exists_layerSamplerScale (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (L₀ : ℕ) : ∃ S : LayerSamplerScale (G := G) B U b R σ,
      L₀ ≤ S.value ∧ S.value ≤ layerSamplerScaleBound (G := G) B R σ L₀ := by
  obtain ⟨L, hL, hlo, hhi, hw, hg⟩ := exists_common_polynomial_scale
    (fun a : Σ j, Fin (n j) => basisAxisScale (b a.1) a.2) (fun a => a.1.val + 1)
    (layerSamplerGapWidth (G := G) B R) (layerSamplerTailWidth (G := G) B R σ)
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) L₀
  exact ⟨⟨L, hL, hw, fun j i => hg ⟨j, i⟩⟩, hlo, hhi⟩

noncomputable def selectedLayerSamplerScale (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (hσ : ∀ j, 0 < σ j) (L₀ : ℕ) : LayerSamplerScale (G := G) B U b R σ :=
  (exists_layerSamplerScale (G := G) B U b R σ hR hσ L₀).choose

theorem selectedLayerSamplerScale_bounds (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j)
    (hσ : ∀ j, 0 < σ j) (L₀ : ℕ) :
    L₀ ≤ (selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀).value ∧
      (selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀).value ≤
        layerSamplerScaleBound (G := G) B R σ L₀ :=
  (exists_layerSamplerScale (G := G) B U b R σ hR hσ L₀).choose_spec

noncomputable def layerSamplerBox {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : ℝ := layerSamplerSides B U b R S.value v

theorem layerSamplerBox_one_le {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : 1 ≤ layerSamplerBox B U b S v := by
  have h : 1 ≤ layerSamplerSides B U b R S.value v :=
    Nat.succ_le_of_lt (layerSamplerSides_pos B U b R S.positive v)
  unfold layerSamplerBox
  exact_mod_cast h

theorem layerSamplerBox_le {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (v : LayerSamplerVariables G I n B) : layerSamplerBox B U b S v ≤ S.value := by
  unfold layerSamplerBox
  exact_mod_cast layerSamplerSides_le B U b R S.positive v

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem principalSamplingGapRatio_antitone {γ δ : ℝ}
    (hγ : 0 < γ) (hγδ : γ ≤ δ) :
    principalSamplingGapRatio δ ≤ principalSamplingGapRatio γ := by
  apply Nat.ceil_mono
  apply max_le_max le_rfl
  exact div_le_div_of_nonneg_left (by positivity) hγ hγδ

namespace VectorPolynomial
open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

noncomputable def layerSamplerWitnessScaleBound (R σ : Fin m → ℝ) (L₀ : ℕ) (W : ℝ) : ℕ :=
  commonPolynomialInitialScale L₀ (layerSamplerTailWidth (G := G) B R σ) *
    commonPolynomialGapRatio (fun a => layerSamplerGapWidth (G := G) B R a / W) ^
      Fintype.card (Σ j, Fin (n j))

theorem exists_layerSamplerWitnessScale
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (L₀ : ℕ) {W : ℝ} (hW : 1 ≤ W) :
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      L₀ ≤ S.value ∧ S.value ≤ layerSamplerWitnessScaleBound (G := G) B R σ L₀ W ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := G) B R ⟨j,i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  let γ := layerSamplerGapWidth (G := G) B R
  have hγ (a : Σ j, Fin (n j)) : 0 < γ a := principalProfileSize_pos (hR a.1) _
  obtain ⟨L, hL, hlo, hhi, hw, hg⟩ := exists_common_polynomial_scale
    (fun a : Σ j, Fin (n j) => basisAxisScale (b a.1) a.2) (fun a => a.1.val + 1)
    (fun a => γ a / W) (layerSamplerTailWidth (G := G) B R σ)
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) L₀
  have hgap (j : Fin m) (i : Fin (n j)) (ha : L ^ (j.val + 1) < basisAxisScale (b j) i) :
      (principalSamplingGapRatio (γ ⟨j,i⟩) * L) ^ (j.val + 1) ≤ basisAxisScale (b j) i := by
    have hm := principalSamplingGapRatio_antitone (div_pos (hγ ⟨j,i⟩) hW0)
      (div_le_self (hγ ⟨j,i⟩).le hW)
    exact (Nat.pow_le_pow_left (Nat.mul_le_mul_right L hm) _).trans (hg ⟨j,i⟩ ha)
  let S : LayerSamplerScale (G := G) B U b R σ := ⟨L, hL, hw, hgap⟩
  refine ⟨S, hlo, hhi, ?_⟩
  intro j i ha
  have hh := integerAxisPrincipal_width (Nat.zero_lt_succ _) hL
    (div_pos (hγ ⟨j,i⟩) hW0) (hg ⟨j,i⟩ ha)
  have hmul := mul_le_mul_of_nonneg_right hh hW0.le
  have he : ((γ ⟨j,i⟩ / W / 2) *
      ((basisAxisScale (b j) i : ℝ) / (L : ℝ) ^ (j.val + 1))) * W =
      (γ ⟨j,i⟩ / 2) * ((basisAxisScale (b j) i : ℝ) / (L : ℝ) ^ (j.val + 1)) := by
    field_simp
  exact hmul.trans_eq he

theorem layerSamplerWitnessScaleBound_exp_bound
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (L₀ : ℕ) {W P Qt Qg Qw : ℝ}
    (hW : 0 < W) (hP : 0 ≤ P) (hQt : 0 ≤ Qt) (hQg : 0 ≤ Qg) (hQw : 0 ≤ Qw)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hL : (L₀ : ℝ) ≤ Real.exp P)
    (ht : ∀ j, (layerSamplerTailWidth (G := G) B R σ j)⁻¹ ≤ Real.exp Qt)
    (hg : ∀ a, (layerSamplerGapWidth (G := G) B R a)⁻¹ ≤ Real.exp Qg)
    (hw : W ≤ Real.exp Qw) :
    (layerSamplerWitnessScaleBound (G := G) B R σ L₀ W : ℝ) ≤
      Real.exp ((P + Qt + 17) + (Fintype.card (Σ j, Fin (n j)) : ℝ) *
        (P + (Qg + Qw) + 17)) := by
  let γ := layerSamplerGapWidth (G := G) B R
  have hγ (a : Σ j, Fin (n j)) : 0 < γ a := principalProfileSize_pos (hR a.1) _
  have hi := commonPolynomialInitialScale_exp_bound
    (layerSamplerTailWidth (G := G) B R σ) L₀
    (fun j => tailProfileSize_pos (hR j) (hσ j) _) hP hQt hA ht hL
  have hginv (a : Σ j, Fin (n j)) : (γ a / W)⁻¹ ≤ Real.exp (Qg + Qw) := by
    rw [inv_div, div_eq_mul_inv, Real.exp_add]
    calc
      _ ≤ Real.exp Qw * Real.exp Qg := mul_le_mul hw (hg a) (inv_nonneg.mpr (hγ a).le)
        (Real.exp_nonneg _)
      _ = _ := mul_comm _ _
  have hgap := commonPolynomialGapRatio_exp_bound (fun a => γ a / W)
    (fun a => div_pos (hγ a) hW) hP (add_nonneg hQg hQw) hA hginv
  unfold layerSamplerWitnessScaleBound
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    _ ≤ Real.exp (P + Qt + 17) *
        (Real.exp (P + (Qg + Qw) + 17)) ^ Fintype.card (Σ j, Fin (n j)) := by
      apply mul_le_mul hi (pow_le_pow_left₀ (Nat.cast_nonneg _) hgap _) (by positivity)
        (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

end VectorPolynomial
end Erdos3

end

end OAI
