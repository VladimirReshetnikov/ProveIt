import OAI.Combinatorics.Progressions.Geometry.AllocatedInactiveSupport

namespace OAI

section

namespace Erdos3

theorem inactiveDenominator_normalized_bounds {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    1 ≤ γ * inactiveDenominator γ ∧ γ * inactiveDenominator γ ≤ 2 := by
  have hd : (0 : ℝ) < inactiveDenominator γ := Nat.cast_pos.mpr (inactiveDenominator_pos γ)
  have hlo := (div_le_iff₀ hd).mp (inactiveDenominator_bound hγ)
  have hu : (inactiveDenominator γ : ℝ) ≤ γ⁻¹ + 1 := by
    simp only [inactiveDenominator, Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith only [inv_nonneg.mpr hγ.le])
      (Nat.ceil_lt_add_one (inv_nonneg.mpr hγ.le)).le
  refine ⟨hlo, ?_⟩
  calc
    _ ≤ γ * (γ⁻¹ + 1) := mul_le_mul_of_nonneg_left hu hγ.le
    _ = 1 + γ := by rw [mul_add, mul_inv_cancel₀ hγ.ne', mul_one]
    _ ≤ 2 := by linarith only [hγ1]

theorem inactiveNaturalScale_bounds {h K : ℕ} {γ : ℝ}
    (hh : 0 < h) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 2 * inactiveDenominator γ ≤ K) :
    (inactiveSideLength h K (inactiveDenominator γ) : ℝ) ^ h ≤ (⌈γ * K⌉₊ : ℝ) ∧
      (⌈γ * K⌉₊ : ℝ) ≤ (2 : ℝ) ^ (h + 1) *
        (inactiveSideLength h K (inactiveDenominator γ) : ℝ) ^ h := by
  let d := inactiveDenominator γ
  let T := inactiveSideLength h K d
  have hd := inactiveDenominator_normalized_bounds hγ hγ1
  have hlow : d * T ^ h ≤ K :=
    (Nat.mul_le_mul_left d (inactiveSideLength_power hh hlarge)).trans
      (by simpa only [Nat.mul_comm] using Nat.div_mul_le_self K d)
  have hlowr : (d : ℝ) * (T : ℝ) ^ h ≤ K := by exact_mod_cast hlow
  have hupr : (K : ℝ) ≤ (d : ℝ) * 2 ^ h * (T : ℝ) ^ h := by
    exact_mod_cast (inactiveSideLength_lower_power hh (inactiveDenominator_pos γ) hlarge).le
  have hT0 : 0 ≤ (T : ℝ) ^ h := pow_nonneg (Nat.cast_nonneg _) _
  constructor
  · calc
      _ ≤ (γ * d) * (T : ℝ) ^ h := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hd.1 hT0
      _ = γ * ((d : ℝ) * (T : ℝ) ^ h) := by ring
      _ ≤ γ * K := mul_le_mul_of_nonneg_left hlowr hγ.le
      _ ≤ _ := Nat.le_ceil _
  · have hup : ⌈γ * K⌉₊ ≤ 2 ^ (h + 1) * T ^ h := by
      apply Nat.ceil_le.mpr
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      calc
        _ ≤ γ * ((d : ℝ) * 2 ^ h * (T : ℝ) ^ h) := mul_le_mul_of_nonneg_left hupr hγ.le
        _ = (γ * d) * (2 ^ h * (T : ℝ) ^ h) := by ring
        _ ≤ 2 * (2 ^ h * (T : ℝ) ^ h) :=
          mul_le_mul_of_nonneg_right hd.2 (mul_nonneg (pow_nonneg (by norm_num) _) hT0)
        _ = _ := by rw [pow_succ]; ring
    exact_mod_cast hup

theorem inactiveNaturalScale_short_bound {h K T : ℕ} {γ : ℝ}
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hT : 0 < T)
    (hK : K ≤ max (2 * inactiveDenominator γ) (integerAxisShortBound h T γ)) :
    ⌈γ * K⌉₊ ≤ 4 * (2 * T) ^ h := by
  have hp : 0 < (2 * T) ^ h := pow_pos (Nat.mul_pos (by norm_num) hT) _
  have hc : K ≤ 2 * inactiveDenominator γ * (2 * T) ^ h := hK.trans
    (max_le (Nat.le_mul_of_pos_right _ hp) (by rfl))
  have hcr : (K : ℝ) ≤ 2 * (inactiveDenominator γ : ℝ) * (2 * (T : ℝ)) ^ h := by exact_mod_cast hc
  have hd := (inactiveDenominator_normalized_bounds hγ hγ1).2
  apply Nat.ceil_le.mpr
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  calc
    _ ≤ γ * (2 * (inactiveDenominator γ : ℝ) * (2 * (T : ℝ)) ^ h) :=
      mul_le_mul_of_nonneg_left hcr hγ.le
    _ = 2 * (γ * inactiveDenominator γ) * (2 * (T : ℝ)) ^ h := by ring
    _ ≤ 2 * 2 * (2 * (T : ℝ)) ^ h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hd (by norm_num)) (pow_nonneg (by positivity) _)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "source" => allocatedLocalResidueSources B U b S j i q hq r hsize

local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedInactiveResidueSources_natural_scale
    (hR : ∀ j, 0 < R j) (hgamma : gamma ≤ 1)
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height) :
    (∀ a, (∏ v, ((source a v).length : ℝ)) ≤ scale) ∧
    (∀ a, (scale : ℝ) ≤ (2 : ℝ) ^ (degree + 1) * ∏ v, ((source a v).length : ℝ)) ∧
    (∀ a v, (scale : ℝ) ≤ (2 : ℝ) ^ (degree + 1) * ((source a v).length : ℝ) ^ degree) := by
  let T := inactiveSideLength degree height denom
  have hlen (a : B ⟨j, Sum.inr i⟩) (v : Fin degree) : (source a v).length = T := by
    rw [allocatedLocalResidueSources_length]
    simp only [integerAxisSideLength, Nat.not_lt.mpr hsmall, ite_false, T]
  have hprod (a : B ⟨j, Sum.inr i⟩) : (∏ v, ((source a v).length : ℝ)) = (T : ℝ) ^ degree := by
    simp only [hlen, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hb := inactiveNaturalScale_bounds (Nat.zero_lt_succ j.val)
    (principalProfileSize_pos (hR j) _) hgamma hlarge
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [hprod]
    exact hb.1
  · intro a
    rw [hprod]
    exact hb.2
  · intro a v
    rw [hlen]
    exact hb.2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "Slots" => BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree
local notation "radius" => (Fintype.card Slots : ℝ) *
  ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j

local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "constantLaw" => allocatedLayerIntegerPMFs B U b hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
theorem allocatedGridSide_natural_normalizable_or_bounded (hq : 0 < q)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1) :
    (2 * inactiveDenominator gamma ≤ height ∧
      ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin degree),
        (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩) ∨
      scale ≤ 4 * (2 * ((Fintype.card α + 1) * q)) ^ degree := by
  rcases allocatedGridSide_normalizable_or_bounded B U b S q j i hq hsize with hl | hs
  · exact Or.inl hl
  · exact Or.inr (inactiveNaturalScale_short_bound (principalProfileSize_pos (hR j) _) hgamma
      (Nat.mul_pos (Nat.succ_pos _) hq) hs)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedConstantLaw_natural_bound (c : ℤ) (hc : c ∈ (constantLaw).support) :
    |(c : ℝ)| / scale ≤ 2 * ((layerIntegerPrincipalSlots (G := G) B j i).card + 1 : ℝ) := by
  have hscale : (0 : ℝ) < scale := Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
  apply (div_le_iff₀ hscale).mpr
  have hN : gamma * height ≤ (scale : ℝ) := Nat.le_ceil _
  calc
    _ ≤ (R j / 4) * height := allocatedConstantLaw_height_bound B U b S j i hR hσ c hc
    _ = (2 * ((layerIntegerPrincipalSlots (G := G) B j i).card + 1 : ℝ)) * (gamma * height) := by
      unfold principalProfileSize
      have hn : (0 : ℝ) < (layerIntegerPrincipalSlots (G := G) B j i).card + 1 := by positivity
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hN (by positivity)

end Erdos3.VectorPolynomial

end

end OAI
