/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Lattices.RoundedAffineLifts

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {X Y R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def subtractConstant (c : V) (p : VectorPolynomial X R V) :
    VectorPolynomial X R V := p - monomial 0 c

theorem coefficients_subtractConstant (c : V) (p : VectorPolynomial X R V) (d : X →₀ ℕ) :
    coefficients (subtractConstant c p) d = coefficients p d - if d = 0 then c else 0 := by
  classical
  simp [subtractConstant, Finsupp.single_apply, eq_comm]

theorem eval_subtractConstant (c : V) (p : VectorPolynomial X R V) (x : X → R) :
    eval x (subtractConstant c p) = eval x p - c := by
  simp [subtractConstant]

theorem substitute_subtractConstant (f : X → MvPolynomial Y R) (c : V)
    (p : VectorPolynomial X R V) :
    substitute f (subtractConstant c p) = subtractConstant c (substitute f p) := by
  simp [subtractConstant, monomial]

theorem DegreeLE.subtractConstant {w : X → ℕ} {h : ℕ} {p : VectorPolynomial X R V}
    (hp : DegreeLE w h p) (c : V) : DegreeLE w h (subtractConstant c p) := by
  intro d hd
  have hd0 : d ≠ 0 := by
    intro he
    subst d
    simp at hd
  rw [coefficients_subtractConstant, hp d hd, ite_eq_right hd0, sub_zero]

theorem coefficients_subtractConstant_mem (U : Submodule R V) (c : U)
    (p : VectorPolynomial X R V) (hp : ∀ d, coefficients p d ∈ U) (d : X →₀ ℕ) :
    coefficients (subtractConstant c.val p) d ∈ U := by
  classical
  rw [coefficients_subtractConstant]
  split_ifs
  · exact U.sub_mem (hp d) c.property
  · simpa using hp d

theorem homogeneousPart_subtractConstant {h : ℕ} (hh : 0 < h) (c : V)
    (p : VectorPolynomial X R V) :
    homogeneousPart h (subtractConstant c p) = homogeneousPart h p := by
  classical
  apply coefficients.injective
  ext d
  by_cases hd : d.degree = h
  · have hd0 : d ≠ 0 := by
      intro he
      subst d
      have : h = 0 := by simpa using hd.symm
      omega
    simp only [coefficients_homogeneousPart, hd, ite_true, coefficients_subtractConstant,
      hd0, ite_false, sub_zero]
  · simp only [coefficients_homogeneousPart, hd, ite_false]

theorem hasLayerSamplingRank_subtractConstant_iff {I J : Type*} [Fintype J]
    {h : ℕ} (hh : 0 < h) (T : I → ℝ) (R : ℝ) (U : Submodule ℝ (J → ℝ))
    (c : J → ℝ) (p : VectorPolynomial I ℝ (J → ℝ)) :
    HasLayerSamplingRank h T R U (subtractConstant c p) ↔ HasLayerSamplingRank h T R U p := by
  rw [← hasLayerSamplingRank_homogeneousPart_iff h T R U (subtractConstant c p),
    homogeneousPart_subtractConstant hh, hasLayerSamplingRank_homogeneousPart_iff]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem AffinePolynomialLiftProperties.of_subtractConstant {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*}
    {p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {c : ∀ j, J j → ℝ}
    {frame : Option K → X → ℝ} {T : K → ℝ}
    {Y : ∀ j, J j → MvPolynomial K ℝ} {β : ∀ j, J j → MvPolynomial K ℤ}
    (h : AffinePolynomialLiftProperties (fun j => subtractConstant (c j) (p j))
      (fun _ => 0) frame T Y β) :
    AffinePolynomialLiftProperties p c frame T Y β := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  intro j i x
  simpa only [eval_subtractConstant, Pi.sub_apply, Pi.zero_apply, sub_zero] using h.2.2.2.2 j i x

theorem HasQuarterAffinePolynomialLifts.of_subtractConstant {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*}
    {p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {c : ∀ j, J j → ℝ}
    {frame : Option K → X → ℝ} {T : K → ℝ}
    (h : HasQuarterAffinePolynomialLifts (fun j => subtractConstant (c j) (p j))
      (fun _ => 0) frame T) :
    HasQuarterAffinePolynomialLifts p c frame T := by
  obtain ⟨Y, β, hYβ, hquarter⟩ := h
  exact ⟨Y, β, hYβ.of_subtractConstant, hquarter⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

theorem centeredAffineCoefficientTorus_zero {K X : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (frame : Option K → X → ℝ) :
    centeredAffineCoefficientTorus U p hm (fun _ => 0) frame =
      affineSampleCoefficientTorus U p hm frame := by
  change QuotientAddGroup.mk' (coefficientIntegerLattice U)
      (affineSampleCoefficientArray U p hm frame - constantCoefficientArray U 0) = _
  rw [map_zero, sub_zero]
  rfl

variable {m : ℕ} {G X : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

theorem selectedPhysicalDensity_quarter_lifts
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hz : selectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm z ≠ 0) :
    HasQuarterAffinePolynomialLifts p (fun _ => 0) (fun k x => (z (k,x) : ℝ))
      (layerSamplerBox B U b (selectedLayerSamplerScale B U b R σ hR hσ L₀)) := by
  apply allocatedAffineDensity_quarter_lifts B U b hb o hR hσ
    (selectedLayerSamplerScale B U b R σ hR hσ L₀) p hm (fun _ => 0)
    hσ1 C hC hchart hsmall hp
  simpa only [allocatedAffineDensity, centeredAffineCoefficientTorus_zero,
    selectedPhysicalDensity, selectedCoefficientDensity] using hz

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

theorem affineSampleCoefficientArray_subtractConstant {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : ∀ j, U j) (frame : Option K → X → ℝ) :
    affineSampleCoefficientArray U (fun j => subtractConstant (c j).val (p j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)) frame =
      centeredAffineCoefficientArray U p hm c frame := by
  funext s
  apply Subtype.ext
  simp only [centeredAffineCoefficientArray, Pi.sub_apply, Submodule.coe_sub,
    affineSampleCoefficientArray_val, substitute_subtractConstant, coefficients_subtractConstant]
  by_cases hs : s.2.val = 0
  · simp [constantCoefficientArray, hs]
  · simp [constantCoefficientArray, hs]

theorem affineSampleCoefficientTorus_subtractConstant {K X : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : ∀ j, U j) (frame : Option K → X → ℝ) :
    affineSampleCoefficientTorus U (fun j => subtractConstant (c j).val (p j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)) frame =
      centeredAffineCoefficientTorus U p hm c frame := by
  exact congrArg (QuotientAddGroup.mk' (coefficientIntegerLattice U))
    (affineSampleCoefficientArray_subtractConstant U p hm c frame)

variable {m : ℕ} {G X : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

theorem selectedPhysicalDensity_subtractConstant
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : ∀ j, U j)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    selectedPhysicalDensity B U b hb o R σ hR hσ L₀ (fun j => subtractConstant (c j).val (p j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)) z =
      translatedSelectedPhysicalDensity B U b hb o R σ hR hσ L₀
        (-(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c s.1)))) p hm z := by
  rw [selectedPhysicalDensity, affineSampleCoefficientTorus_subtractConstant,
    centeredAffineCoefficientTorus_eq_subtractive]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G X : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)

theorem exists_constant_center_uniform_lifts
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    ∃ c : ∀ j, U j, coefficientConstantCenter U x =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U) (constantCoefficientArray U (fun s => c s.1))) ∧
      ∀ z : Option (LayerSamplerVariables G I n B) × X → ℤ,
        translatedSelectedPhysicalDensity B U b hb o R σ hR hσ L₀
          (coefficientConstantCenter U x) p hm z ≠ 0 →
        HasQuarterAffinePolynomialLifts p (fun j => (c j).val) (fun k v => (z (k,v) : ℝ))
          (layerSamplerBox B U b (selectedLayerSamplerScale B U b R σ hR hσ L₀)) := by
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center (K := LayerSamplerVariables G I n B) U x
  refine ⟨c, hc, ?_⟩
  intro z hz
  let p' := fun j => subtractConstant (c j).val (p j)
  let hm' := fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)
  have hp' (j) : DegreeLE (1 : X → ℕ) (j.val+1) (p' j) := (hp j).subtractConstant _
  have hz' : selectedPhysicalDensity B U b hb o R σ hR hσ L₀ p' hm' z ≠ 0 := by
    change selectedPhysicalDensity B U b hb o R σ hR hσ L₀
      (fun j => subtractConstant (c j).val (p j))
      (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)) z ≠ 0
    rw [selectedPhysicalDensity_subtractConstant, ← hc]
    exact hz
  exact HasQuarterAffinePolynomialLifts.of_subtractConstant
    (selectedPhysicalDensity_quarter_lifts B U b hb o R σ hR hσ L₀ hσ1 C hC hchart hsmall p' hp' hm' z hz')

end Erdos3.VectorPolynomial

end

end OAI
