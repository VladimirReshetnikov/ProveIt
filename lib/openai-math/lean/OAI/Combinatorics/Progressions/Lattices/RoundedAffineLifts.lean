import Mathlib.Algebra.Order.Round
import OAI.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity
import OAI.Combinatorics.Progressions.Polynomial.AffinePolynomialLiftData
import OAI.Combinatorics.Progressions.Polynomial.AllocatedPolynomialQuarter

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

def jointIntegerFrame {K I : Type*}
    (z : (I → ℤ) × (Option K × I → ℤ)) : Option K → I → ℤ :=
  fun k i => match k with
    | none => z.1 i + z.2 (none,i)
    | some k => z.2 (some k,i)

theorem integerAffineMap_jointIntegerFrame {K I : Type*} [Fintype K]
    (z : (I → ℤ) × (Option K × I → ℤ)) (root : K → ℤ) :
    integerAffineMap (fun i k => jointIntegerFrame z (some k) i) (jointIntegerFrame z none) root =
      jointIntegerPhysicalSite root z := by
  funext i
  simp only [integerAffineMap, jointIntegerFrame, jointIntegerPhysicalSite,
    integerPhysicalSite, Pi.add_apply]
  rw [add_assoc]
  congr 2
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end Erdos3.BooleanCubeKernel

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators

theorem AffinePolynomialLiftProperties.joint_frame {K V : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*}
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    {T : K → ℝ} (a : V → ℤ) (z : Option K × V → ℤ)
    {Y : ∀ j, J j → MvPolynomial K ℝ} {β : ∀ j, J j → MvPolynomial K ℤ}
    (h : AffinePolynomialLiftProperties (fun j => translate (fun v => (a v : ℝ)) (p j))
      center (fun k v => (z (k,v) : ℝ)) T Y β) :
    AffinePolynomialLiftProperties p center (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) T Y β := by
  obtain ⟨hY, hβ, hcoeff, hbox, heq⟩ := h
  refine ⟨hY, hβ, hcoeff, hbox, ?_⟩
  intro j i x
  have he := heq j i x
  rw [eval_translate] at he
  have hx :
      (fun v => (z (none,v) : ℝ) + ∑ k, (z (some k,v) : ℝ) * x k + (a v : ℝ)) =
      (fun v => (jointIntegerFrame (a,z) none v : ℝ) +
        ∑ k, (jointIntegerFrame (a,z) (some k) v : ℝ) * x k) := by
    funext v
    simp only [jointIntegerFrame, Int.cast_add]
    ring
  rwa [hx] at he

theorem HasAffinePolynomialLifts.joint_frame {K V : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*}
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    {T : K → ℝ} (a : V → ℤ) (z : Option K × V → ℤ)
    (h : HasAffinePolynomialLifts (fun j => translate (fun v => (a v : ℝ)) (p j))
      center (fun k v => (z (k,v) : ℝ)) T) :
    HasAffinePolynomialLifts p center (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) T := by
  obtain ⟨Y, β, hYβ⟩ := h
  exact ⟨Y, β, hYβ.joint_frame a z⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G V : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j) (center : ∀ j, U j)

noncomputable def allocatedAffineDensity
    (frame : Option (LayerSamplerVariables G I n B) → V → ℝ) : ℝ :=
  allocatedCoefficientDensity B U b hb o hR hσ S (centeredAffineCoefficientTorus U p hm center frame)

theorem allocatedAffineDensity_lifts
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (frame : Option (LayerSamplerVariables G I n B) → V → ℝ)
    (hframe : allocatedAffineDensity B U b hb o hR hσ S p hm center frame ≠ 0) :
    HasAffinePolynomialLifts p (fun j => (center j).val) frame (layerSamplerBox B U b S) := by
  obtain ⟨Y, β, heq, hY, hβ, hcoeff, hbox⟩ :=
    allocatedCoefficientDensity_polynomial_decomposition B U b hb o hR hσ S hσ1 C hC hchart hsmall
      (centeredAffineCoefficientArray U p hm center frame) hframe
  refine ⟨Y, β, hY, hβ, hcoeff, hbox, ?_⟩
  intro j i x
  rw [← coefficientRowPolynomial_centered_affine_eval U p hm hp center frame j i x, heq j i, map_add]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedAffineDensity_nonneg (frame : Option (LayerSamplerVariables G I n B) → V → ℝ) :
    0 ≤ allocatedAffineDensity B U b hb o hR hσ S p hm center frame :=
  canonicalCoefficientDensity_nonneg U b hb o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerPMFs B U b hR hσ S)
    (allocatedLayerWidths_pos B U b hR hσ S) _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G V : Type*} [Fintype G] [Fintype V]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j) (center : ∀ j, U j)

noncomputable def allocatedAffineSpatialDensity
    (frame : Option (LayerSamplerVariables G I n B) × V → ℤ) : ℝ :=
  allocatedAffineDensity B U b hb o hR hσ S p hm center (fun k v => (frame (k, v) : ℝ))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype V] in
theorem allocatedAffineSpatialDensity_nonneg (frame : Option (LayerSamplerVariables G I n B) × V → ℤ) :
    0 ≤ allocatedAffineSpatialDensity B U b hb o hR hσ S p hm center frame :=
  allocatedAffineDensity_nonneg B U b hb o hR hσ S p hm center _

variable (modulus : V → ℕ)
variable (Γ : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) V modulus))
variable (width : Option (LayerSamplerVariables G I n B) × V → ℝ) (hwidth : ∀ z, 0 < width z)
variable (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus Γ width x)
variable (hD : 0 < selectedResidueDensityMass modulus Γ width
  (allocatedAffineSpatialDensity B U b hb o hR hσ S p hm center))

noncomputable def allocatedAffineSpatialPMF : PMF (Option (LayerSamplerVariables G I n B) × V → ℤ) :=
  selectedResidueDensityPMF modulus Γ width hwidth hZ
    (allocatedAffineSpatialDensity B U b hb o hR hσ S p hm center)
    (allocatedAffineSpatialDensity_nonneg B U b hb o hR hσ S p hm center) hD

theorem allocatedAffineSpatialPMF_toReal (frame : Option (LayerSamplerVariables G I n B) × V → ℤ) :
    (allocatedAffineSpatialPMF B U b hb o hR hσ S p hm center modulus Γ width hwidth hZ hD frame).toReal =
      (selectedResidueSmoothPMF modulus Γ width hwidth hZ frame).toReal *
        allocatedAffineSpatialDensity B U b hb o hR hσ S p hm center frame /
          selectedResidueDensityMass modulus Γ width
            (allocatedAffineSpatialDensity B U b hb o hR hσ S p hm center) :=
  selectedResidueDensityPMF_toReal modulus Γ width hwidth hZ _ _ hD frame

variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
variable (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))

include hσ1 C hC hchart hsmall hp

theorem allocatedAffineSpatialPMF_support_lifts
    (frame : Option (LayerSamplerVariables G I n B) × V → ℤ)
    (hframe : frame ∈ (allocatedAffineSpatialPMF B U b hb o hR hσ S p hm center
      modulus Γ width hwidth hZ hD).support) :
    HasAffinePolynomialLifts p (fun j => (center j).val)
      (fun k v => (frame (k, v) : ℝ)) (layerSamplerBox B U b S) := by
  have hn : (allocatedAffineSpatialPMF B U b hb o hR hσ S p hm center
      modulus Γ width hwidth hZ hD frame).toReal ≠ 0 :=
    (ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hframe) (PMF.apply_ne_top _ _)).ne'
  have hd : allocatedAffineSpatialDensity B U b hb o hR hσ S p hm center frame ≠ 0 := by
    intro hz
    apply hn
    rw [allocatedAffineSpatialPMF_toReal, hz, mul_zero, zero_div]
  exact allocatedAffineDensity_lifts B U b hb o hR hσ S p hm center hσ1 C hC hchart hsmall hp _ hd

theorem allocatedAffineSpatialPMF_ae_lifts :
    ∀ᵐ frame ∂(allocatedAffineSpatialPMF B U b hb o hR hσ S p hm center
      modulus Γ width hwidth hZ hD).toMeasure,
      HasAffinePolynomialLifts p (fun j => (center j).val)
        (fun k v => (frame (k, v) : ℝ)) (layerSamplerBox B U b S) := by
  apply (pmf_support_ae _).mono
  intro frame hframe
  exact allocatedAffineSpatialPMF_support_lifts B U b hb o hR hσ S p hm center
    modulus Γ width hwidth hZ hD hσ1 C hC hchart hsmall hp frame hframe

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel

def HasQuarterAffinePolynomialLifts {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)) (center : ∀ j, J j → ℝ)
    (frame : Option K → V → ℝ) (T : K → ℝ) : Prop :=
  ∃ Y β, AffinePolynomialLiftProperties p center frame T Y β ∧
    ∀ j (x : K → ℝ), (∀ v, |x v| ≤ T v) → ∀ i, |MvPolynomial.eval x (Y j i)| < 1/4

theorem HasQuarterAffinePolynomialLifts.to_hasAffinePolynomialLifts
    {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    {frame : Option K → V → ℝ} {T : K → ℝ}
    (h : HasQuarterAffinePolynomialLifts p center frame T) :
    HasAffinePolynomialLifts p center frame T := by
  obtain ⟨Y, β, hYβ, _⟩ := h
  exact ⟨Y, β, hYβ⟩

theorem HasQuarterAffinePolynomialLifts.joint_frame {K V : Type*} [Fintype K]
    {m : ℕ} {J : Fin m → Type*}
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    {T : K → ℝ} (a : V → ℤ) (z : Option K × V → ℤ)
    (h : HasQuarterAffinePolynomialLifts (fun j => translate (fun v => (a v : ℝ)) (p j))
      center (fun k v => (z (k,v) : ℝ)) T) :
    HasQuarterAffinePolynomialLifts p center (fun k v => (jointIntegerFrame (a,z) k v : ℝ)) T := by
  obtain ⟨Y, β, hYβ, hquarter⟩ := h
  exact ⟨Y, β, hYβ.joint_frame a z, hquarter⟩

variable {m : ℕ} {G V : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (p j) d ∈ U j) (center : ∀ j, U j)

theorem allocatedAffineDensity_quarter_lifts
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hp : ∀ j, DegreeLE (1 : V → ℕ) (j.val + 1) (p j))
    (frame : Option (LayerSamplerVariables G I n B) → V → ℝ)
    (hframe : allocatedAffineDensity B U b hb o hR hσ S p hm center frame ≠ 0) :
    HasQuarterAffinePolynomialLifts p (fun j => (center j).val) frame (layerSamplerBox B U b S) := by
  obtain ⟨Y, β, heq, hY, hβ, hcoeff, hquarter⟩ :=
    allocatedCoefficientDensity_quarter_decomposition B U b hR hσ S hσ1 o C hC hchart hsmall hb
      (centeredAffineCoefficientArray U p hm center frame) hframe
  refine ⟨Y, β, ⟨hY, hβ, hcoeff, ?_, ?_⟩, hquarter⟩
  · intro j x hx i
    exact (hquarter j x hx i).trans (by norm_num)
  · intro j i x
    rw [← coefficientRowPolynomial_centered_affine_eval U p hm hp center frame j i x, heq j i, map_add]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel

variable {K V : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}

noncomputable def roundedPolynomialIntegerLift
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)) (center : ∀ j, J j → ℝ)
    (u : V → ℤ) (j : Fin m) (i : J j) : ℤ :=
  round (eval (fun v => (u v : ℝ)) (p j) i - center j i)

noncomputable def roundedPolynomialSmallLift
    (p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)) (center : ∀ j, J j → ℝ)
    (u : V → ℤ) (j : Fin m) (i : J j) : ℝ :=
  eval (fun v => (u v : ℝ)) (p j) i - center j i - roundedPolynomialIntegerLift p center u j i

theorem AffinePolynomialLiftProperties.rounded_evaluation
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    {frame : Option K → V → ℤ} {T : K → ℝ}
    {Y : ∀ j, J j → MvPolynomial K ℝ} {β : ∀ j, J j → MvPolynomial K ℤ}
    (h : AffinePolynomialLiftProperties p center (fun k v => (frame k v : ℝ)) T Y β)
    (x : K → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ T k) (j : Fin m) :
    let u := integerAffineMap (fun v k => frame (some k) v) (frame none) x
    (fun i => MvPolynomial.eval (fun k => (x k : ℝ)) (Y j i)) = roundedPolynomialSmallLift p center u j ∧
    (fun i => MvPolynomial.eval x (β j i)) = roundedPolynomialIntegerLift p center u j := by
  let u := integerAffineMap (fun v k => frame (some k) v) (frame none) x
  have he (i : J j) := h.integer_evaluation j i x
  have hr (i : J j) : roundedPolynomialIntegerLift p center u j i = MvPolynomial.eval x (β j i) := by
    apply round_eq_iff.mpr
    have hy := abs_lt.mp (h.2.2.2.1 j (fun k => (x k : ℝ)) hx i)
    constructor <;> linarith [he i]
  constructor
  · funext i
    change MvPolynomial.eval (fun k => (x k : ℝ)) (Y j i) =
      eval (fun v => (u v : ℝ)) (p j) i - center j i - roundedPolynomialIntegerLift p center u j i
    rw [hr i]
    linarith [he i]
  · exact funext (fun i => (hr i).symm)

theorem HasQuarterAffinePolynomialLifts.rounded_joint
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    (z : (V → ℤ) × (Option K × V → ℤ)) {T : K → ℝ}
    (h : HasQuarterAffinePolynomialLifts p center (fun k v => (jointIntegerFrame z k v : ℝ)) T) :
    ∃ Y β, AffinePolynomialLiftProperties p center (fun k v => (jointIntegerFrame z k v : ℝ)) T Y β ∧
      (∀ j (x : K → ℝ), (∀ k, |x k| ≤ T k) → ∀ i, |MvPolynomial.eval x (Y j i)| < 1/4) ∧
      ∀ x : K → ℤ, (∀ k, |(x k : ℝ)| ≤ T k) → ∀ j,
        (fun i => MvPolynomial.eval (fun k => (x k : ℝ)) (Y j i)) =
          roundedPolynomialSmallLift p center (jointIntegerPhysicalSite x z) j ∧
        (fun i => MvPolynomial.eval x (β j i)) =
          roundedPolynomialIntegerLift p center (jointIntegerPhysicalSite x z) j := by
  obtain ⟨Y, β, hYβ, hquarter⟩ := h
  refine ⟨Y, β, hYβ, hquarter, ?_⟩
  intro x hx j
  simpa only [integerAffineMap_jointIntegerFrame] using hYβ.rounded_evaluation x hx j

theorem HasQuarterAffinePolynomialLifts.rounded_joint_residue
    {p : ∀ j, VectorPolynomial V ℝ (J j → ℝ)} {center : ∀ j, J j → ℝ}
    (z : (V → ℤ) × (Option K × V → ℤ)) {T : K → ℝ}
    (h : HasQuarterAffinePolynomialLifts p center (fun k v => (jointIntegerFrame z k v : ℝ)) T)
    (q : ℕ) (x x' : K → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ T k) (hx' : ∀ k, |(x' k : ℝ)| ≤ T k)
    (hmod : integerResidueMap K q x = integerResidueMap K q x') (j : Fin m) (i : J j) :
    (roundedPolynomialIntegerLift p center (jointIntegerPhysicalSite x z) j i : ZMod q) =
      (roundedPolynomialIntegerLift p center (jointIntegerPhysicalSite x' z) j i : ZMod q) := by
  obtain ⟨Y, β, _, _, heval⟩ := h.rounded_joint z
  rw [← congrFun (heval x hx j).2 i, ← congrFun (heval x' hx' j).2 i]
  exact integerPolynomial_eval_congr (β j i) q hmod

end Erdos3.VectorPolynomial

end

end OAI
