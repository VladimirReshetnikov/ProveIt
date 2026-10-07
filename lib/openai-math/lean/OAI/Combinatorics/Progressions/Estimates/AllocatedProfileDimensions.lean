import OAI.Combinatorics.Progressions.Estimates.PhysicalJetCoverCancellation
import OAI.Combinatorics.Progressions.Linear.KernelScalarEnvelope

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

theorem allocatedGoodKernel_prescribed_comparison {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedJointLengthLog (G := G) B α O P E) ≤ S.value) :
    ∃ (modulus : ℕ) (hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*modulus ≤ lengths d,
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus),
      ∃ residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus),
        (∀ v, (allocatedLongResidueWeights B U basis S modulus hm r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) ∧
        ∀ z : AllocatedLongJetRows B U basis S O,
        |(allocatedLongResidueWeights B U basis S modulus hm r hsize).mean
            (fun v => (∏ a, allocatedLongJetOutputScale B U basis S (O := O) a) *
              allocatedLongJetDensity B U basis hR hσ S x u v rows s hA hσ1 z) -
          (∏ a, allocatedLongJetMask B U basis S x rows modulus residue a (z a)) *
            (∫ y, (∏ a, allocatedLongJetTarget B U basis S x u rows s hA y a (z a))
              ∂jointBooleanSource (fun a : {a // ¬grid a} => layerSamplerDegree I n a.val))| ≤ η := by
  obtain ⟨hcoefficient, htuple⟩ := allocatedJointLengthLog_spec (G := G) B α O hP hE hMP hη hηE hlarge
  obtain ⟨hε, _, hεe⟩ := allocatedJointAccuracy_spec (G := G) B α O hP hMP hη hη1 hηE
  have he := allocatedJointAccuracyLog_nonneg (G := G) B α O hP hE
  obtain ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, hcompare⟩ :=
    allocatedGoodKernel_principal_comparison B U basis hR hσ S x rows hM selection hx hq hinj hrows hσ1
      hP he hε hMP hRP hRi hσi hcount hεe hcoefficient
  obtain ⟨hsize, hsmall, herror⟩ :=
    allocatedJointTupleCutoff_spec B U basis S O hP hM hη hη1 hmB htuple
  refine ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, hsize, ?_⟩
  intro u r
  obtain ⟨residue, hr, hz⟩ := hcompare u r hsize hsmall
  exact ⟨residue, hr, fun z => (hz z).trans herror⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedJetTestLog (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (P E : ℝ) : ℝ :=
  E + Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
    (allocatedJetSupportLog (G := G) B α O P + 2)

theorem allocatedJetTestLog_nonneg (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 ≤ allocatedJetTestLog (G := G) B α O P E := by
  have hS := (allocatedJetSupportLog_bounds (G := G) B α O hP).1
  unfold allocatedJetTestLog
  positivity

theorem allocatedJetTestAccuracy_spec (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] {P E η : ℝ}
    (hP : 0 ≤ P) (hη : 0 < η) (hη1 : η ≤ 1) (hηE : η⁻¹ ≤ Real.exp E) :
    let V := (2*Real.exp (allocatedJetSupportLog (G := G) B α O P)+1)^
      Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    0 < η/V ∧ η/V ≤ 1 ∧ (η/V)⁻¹ ≤ Real.exp (allocatedJetTestLog (G := G) B α O P E) ∧ V*(η/V) = η := by
  dsimp only
  let b := allocatedJetSupportLog (G := G) B α O P
  let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
  have hb : 0 ≤ b := (allocatedJetSupportLog_bounds (G := G) B α O hP).1
  have hT : (1 : ℝ) ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hV : (1 : ℝ) ≤ (2*Real.exp b+1)^D := one_le_pow₀ (by linarith)
  have hVp : (0 : ℝ) < (2*Real.exp b+1)^D := zero_lt_one.trans_le hV
  have hvexp : (2*Real.exp b+1)^D ≤ Real.exp (D*(b+2)) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    calc
      _ ≤ 3*Real.exp b := by linarith
      _ ≤ Real.exp 2*Real.exp b :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, add_comm]
  refine ⟨div_pos hη hVp, (div_le_one hVp).mpr (hη1.trans hV), ?_, ?_⟩
  · rw [inv_div, div_eq_mul_inv]
    calc
      _ ≤ Real.exp (D*(b+2))*Real.exp E :=
        mul_le_mul hvexp hηE (inv_nonneg.mpr hη.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; unfold allocatedJetTestLog; dsimp [D, b]; ring
  · change (2*Real.exp b+1)^D * (η/(2*Real.exp b+1)^D) = η
    field_simp [hVp.ne']

variable [DecidableEq G] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides
local notation "scale" => ∏ a, allocatedLongJetOutputScale B U basis S (O := O) a

theorem allocatedGoodKernel_prescribed_test {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedJointLengthLog (G := G) B α O P
      (allocatedJetTestLog (G := G) B α O P E)) ≤ S.value) :
    ∃ (modulus : ℕ) (hm : 0 < modulus), modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*modulus ≤ lengths d,
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod modulus),
      let w := allocatedLongResidueWeights B U basis S modulus hm r hsize
      ∃ residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus),
        (∀ v, w.weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue j) ∧
        ∀ (φ : AllocatedLongJetRows B U basis S O → ℂ), Measurable φ → (∀ z, ‖φ z‖ ≤ 1) →
        ‖(∫ c, w.complexMean (fun v => φ (allocatedLongJetMap B U basis S x u v rows c))
            ∂allocatedLongCoefficientSource B U basis hR hσ S) -
          ∫ z, ((allocatedLongJetProxy B U basis S x u rows s hA modulus residue z/scale : ℝ) : ℂ)*φ z
            ∂allocatedLongJetReference B U basis S O‖ ≤ η := by
  obtain ⟨hδ, hδ1, hδE, hVδ⟩ := allocatedJetTestAccuracy_spec (G := G) B α O hP hη hη1 hηE
  obtain ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, hsize, hcompare⟩ :=
    allocatedGoodKernel_prescribed_comparison B U basis hR hσ S x rows hM selection hx hq hinj hrows hσ1
      hP (allocatedJetTestLog_nonneg (G := G) B α O hP hE) hδ hδ1 hMP hRP hRi hσi hcount hδE hlarge
  refine ⟨modulus, hm, hmB, hspatial, hperiod, s, hA, hi, hsize, ?_⟩
  intro u r
  obtain ⟨residue, hr, hpoint⟩ := hcompare u r
  refine ⟨residue, hr, ?_⟩
  intro φ hφ hb
  have ht := allocatedLongJet_test_comparison B U basis hR hσ S x u rows s hA
    hM hi hP hMP hRP hRi hσi hcount hσ1
    (allocatedLongResidueWeights B U basis S modulus hm r hsize) modulus residue hδ.le hpoint φ hφ hb
  exact ht.trans_eq hVδ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

structure AllocatedComparisonDimensions (α : Type*) [Fintype α]
    (O : Fin m → Type*) [∀ j, Fintype (O j)] (D : ℝ) : Prop where
  nonneg : 0 ≤ D
  degree : (m : ℝ) ≤ D
  kernel_variables : (Fintype.card G : ℝ) ≤ D
  cube : (Fintype.card α : ℝ) ≤ D
  axes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D
  tuples : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ D
  parameters : (Fintype.card (JointBlockParameter B (layerSamplerDegree I n) α) : ℝ) ≤ D
  outputs : (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) : ℝ) ≤ D
  rows : ∀ j, (Fintype.card (O j) : ℝ) ≤ D
  coefficients : ∀ j : Fin m,
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ D
  profile : (probabilityProfileLipschitz : ℝ) ≤ D

variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)] {D : ℝ}

theorem AllocatedComparisonDimensions.kernel_coefficients
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    (Fintype.card (BoundedIntegerExponent G (j.val+1)) : ℝ) ≤ D := by
  have hc := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  rw [Fintype.card_sum] at hc
  exact (Nat.cast_le.mpr (by omega)).trans (h.coefficients j)

theorem AllocatedComparisonDimensions.nonkernel_coefficients
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) : ℝ) ≤ D := by
  have hc := Fintype.card_congr (allocatedKernelCoefficientEquiv (G := G) B j)
  rw [Fintype.card_sum] at hc
  exact (Nat.cast_le.mpr (by omega)).trans (h.coefficients j)

theorem AllocatedComparisonDimensions.layer_degree
    (h : AllocatedComparisonDimensions (G := G) B α O D) (j : Fin m) :
    ((j.val+1 : ℕ) : ℝ) ≤ D :=
  (Nat.cast_le.mpr (Nat.succ_le_of_lt j.isLt)).trans h.degree

section Envelopes

variable {A : Type*} [Semiring A]

def allocatedKernelEnvelope (m : ℕ) (D p : A) : A :=
  p+(m*2^(m+1) : ℕ)*p+D*(m+1)+m*kernelInverseEnvelope D p

def allocatedDensityEnvelope (m : ℕ) (D p : A) : A :=
  1+m*kernelOutputEnvelope D (4*(p+8))+p+m*(D+3*D*D+D*(D+1))

def allocatedSupportEnvelope (m : ℕ) (D p : A) : A :=
  allocatedDensityEnvelope m D p+p+m*(D+D*(D+1))

def allocatedTestEnvelope (m : ℕ) (D p e : A) : A :=
  e+D*(allocatedSupportEnvelope m D p+2)

def allocatedAccuracyEnvelope (m : ℕ) (D p e : A) : A :=
  e+D+3+D*(2+(m*2^(m+1) : ℕ)*p+allocatedDensityEnvelope m D p)

def allocatedFrontEnvelope (m : ℕ) (D p e : A) : A :=
  let C := allocatedKernelEnvelope m D p+D+(D+D+(D+1)*(4*(p+8)))
  2*D^2+(2*D+4)*C+(D+2*D)*(C+4)+4+e+1

def allocatedTupleEnvelope (m : ℕ) (D p e : A) : A :=
  let R := (D+1)^2+4*D+3
  R+D+D+(m+1)*p+
    (D*((m*2^(m+1) : ℕ)*p+allocatedDensityEnvelope m D p)+R+D+
      allocatedDensityEnvelope m D p+1)+(e+2)+1

def allocatedJointLengthEnvelope (m : ℕ) (D p e : A) : A :=
  m*allocatedFrontEnvelope m D p (allocatedAccuracyEnvelope m D p e)+
    allocatedTupleEnvelope m D p e

def allocatedTestLengthEnvelope (m : ℕ) (D p e : A) : A :=
  allocatedJointLengthEnvelope m D p (allocatedTestEnvelope m D p e)

end Envelopes

theorem allocatedDensityEnvelope_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedDensityEnvelope m D p := by
  have ho := kernelOutputEnvelope_nonneg hD (show 0 ≤ 4*(p+8) by positivity)
  unfold allocatedDensityEnvelope
  positivity

theorem allocatedSupportEnvelope_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedSupportEnvelope m D p := by
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  unfold allocatedSupportEnvelope
  positivity

theorem allocatedTestEnvelope_nonneg (m : ℕ) {D p e : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) : 0 ≤ allocatedTestEnvelope m D p e := by
  have hs := allocatedSupportEnvelope_nonneg m hD hp
  unfold allocatedTestEnvelope
  positivity

theorem allocatedTestLengthEnvelope_nonneg (m : ℕ) {D p e : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) : 0 ≤ allocatedTestLengthEnvelope m D p e := by
  have hi := kernelInverseEnvelope_nonneg hD hp
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  have ht := allocatedTestEnvelope_nonneg m hD hp he
  dsimp only [allocatedTestLengthEnvelope, allocatedJointLengthEnvelope, allocatedFrontEnvelope,
    allocatedKernelEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope]
  positivity

variable (h : AllocatedComparisonDimensions (G := G) B α O D) {p e : ℝ} (hp : 0 ≤ p)

include h hp

theorem allocatedKernelLog_le_envelope :
    allocatedKernelLog G α O p ≤ allocatedKernelEnvelope m D p := by
  have hi (j : Fin m) := kernelInverseLog_le_envelope h.nonneg hp h.cube h.kernel_variables
    (h.rows j) (h.layer_degree B j)
  have hs : (∑ j : Fin m, kernelInverseLog (Fintype.card α) (Fintype.card G)
      (Fintype.card (O j)) (j.val+1) p) ≤ (m : ℝ)*kernelInverseEnvelope D p := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hi j)
  unfold allocatedKernelLog allocatedKernelEnvelope
  gcongr
  exact h.cube

theorem allocatedDensityLog_le_envelope :
    allocatedDensityLog (G := G) B α O p ≤ allocatedDensityEnvelope m D p := by
  have hD := h.nonneg
  have ht : 0 ≤ 4*(p+8) := by positivity
  have hk (j : Fin m) := kernelRowOutputLog_le_envelope h.nonneg ht h.cube h.kernel_variables
    (h.rows j) (h.kernel_coefficients B j) (h.nonkernel_coefficients B j)
    (h.layer_degree B j) h.profile
  have hsum : (∑ j : Fin m, kernelRowOutputLog (Fintype.card α) (Fintype.card G)
      (Fintype.card (O j)) (Fintype.card (BoundedIntegerExponent G (j.val+1)))
      (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j)) (j.val+1) (4*(p+8))) ≤
      (m : ℝ)*kernelOutputEnvelope D (4*(p+8)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hk j)
  have hc (j : Fin m) : allocatedDensityColumnLog (G := G) B α j ≤ D+3*D*D+D*(D+1) := by
    have hd := h.layer_degree B j
    have hn := h.nonkernel_coefficients B j
    have hparam := h.parameters
    have hq := h.cube
    have hplus : (j.val : ℝ)+2 ≤ D+1 := by
      push_cast at hd
      linarith
    unfold allocatedDensityColumnLog
    push_cast at hd ⊢
    gcongr
  have hcols : (∑ j : Fin m, allocatedDensityColumnLog (G := G) B α j) ≤
      (m : ℝ)*(D+3*D*D+D*(D+1)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  unfold allocatedDensityLog allocatedDensityEnvelope kernelFamilyOutputLog
  linarith

theorem allocatedJetSupportLog_le_envelope :
    allocatedJetSupportLog (G := G) B α O p ≤ allocatedSupportEnvelope m D p := by
  have hD := h.nonneg
  have hden := allocatedDensityLog_le_envelope B h hp
  have hc (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1) ≤ D+D*(D+1) := by
    have hd := h.layer_degree B j
    have hn := h.coefficients j
    have hq := h.cube
    gcongr
  have hs : (∑ j : Fin m,
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+
        (Fintype.card α : ℝ)*((j.val+1 : ℕ)+1))) ≤ (m : ℝ)*(D+D*(D+1)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hc j)
  unfold allocatedJetSupportLog allocatedSupportEnvelope
  linarith

theorem allocatedJetTestLog_le_envelope :
    allocatedJetTestLog (G := G) B α O p e ≤ allocatedTestEnvelope m D p e := by
  have hD := h.nonneg
  have hs := allocatedJetSupportLog_le_envelope B h hp
  have hs0 := (allocatedJetSupportLog_bounds (G := G) B α O hp).1
  have ho := h.outputs
  unfold allocatedJetTestLog allocatedTestEnvelope
  gcongr

theorem allocatedJointAccuracyLog_le_envelope :
    allocatedJointAccuracyLog (G := G) B α O p e ≤ allocatedAccuracyEnvelope m D p e := by
  have hD := h.nonneg
  have hd := allocatedDensityLog_le_envelope B h hp
  have hd0 := (allocatedDensityLog_bounds (G := G) B α O hp).1
  have ha := h.axes
  unfold allocatedJointAccuracyLog allocatedAccuracyEnvelope
  gcongr

theorem allocatedCoefficientFrontLog_le_envelope (j : Fin m) :
    coefficientFrontLog (Fintype.card (O j))
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (allocatedKernelLog G α O p) (4*(p+8)) e ≤ allocatedFrontEnvelope m D p e := by
  have hD := h.nonneg
  have hk := allocatedKernelLog_le_envelope B h hp
  have hk0 := (allocatedKernelLog_bounds G α O hp).1
  have hn := h.coefficients j
  have hj := h.rows j
  have hf := h.profile
  have ht : 0 ≤ 4*(p+8) := by positivity
  have hc : affineCoefficientCommonBudget
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
      (allocatedKernelLog G α O p) (4*(p+8)) ≤
      allocatedKernelEnvelope m D p+D+(D+D+(D+1)*(4*(p+8))) := by
    unfold affineCoefficientCommonBudget affineProfileLogBound
    gcongr
  have hc0 := affineCoefficientCommonBudget_nonneg
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1))) hk0 ht
  dsimp only [coefficientFrontLog, allocatedFrontEnvelope, coefficientLogAllowance]
  gcongr

theorem allocatedKernelReplacementLog_le_envelope :
    allocatedKernelReplacementLog (G := G) B α O p e ≤ (m : ℝ)*allocatedFrontEnvelope m D p e := by
  unfold allocatedKernelReplacementLog
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
      allocatedCoefficientFrontLog_le_envelope B h hp j (e := e))

theorem allocatedTupleLog_le_envelope :
    scalarTupleToleranceLog (Fintype.card α) (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)))
      ((m+1 : ℕ)*p)
      (maskedJointTupleLog (Fintype.card α) (Fintype.card (LayerSamplerAxis I n))
        ((m*2^(m+1) : ℕ)*p) (allocatedDensityLog (G := G) B α O p)) (e+2) ≤
      allocatedTupleEnvelope m D p e := by
  have hD := h.nonneg
  have hd := allocatedDensityLog_le_envelope B h hp
  have hd0 := (allocatedDensityLog_bounds (G := G) B α O hp).1
  have ha := h.axes
  have hc := h.cube
  have ht := h.tuples
  dsimp only [scalarTupleToleranceLog, maskedJointTupleLog, scalarCubeGridRatioLog,
    allocatedTupleEnvelope]
  push_cast
  gcongr

theorem allocatedJointLengthLog_le_envelope (he : 0 ≤ e) :
    allocatedJointLengthLog (G := G) B α O p e ≤ allocatedJointLengthEnvelope m D p e := by
  have ha := allocatedJointAccuracyLog_le_envelope B h hp (e := e)
  have hf := allocatedKernelReplacementLog_le_envelope B h hp
    (e := allocatedJointAccuracyLog (G := G) B α O p e)
  have hl : allocatedKernelReplacementLog (G := G) B α O p
      (allocatedJointAccuracyLog (G := G) B α O p e) ≤
      (m : ℝ)*allocatedFrontEnvelope m D p (allocatedAccuracyEnvelope m D p e) := by
    apply hf.trans
    dsimp only [allocatedFrontEnvelope]
    gcongr
  have hr := allocatedTupleLog_le_envelope B h hp (e := e)
  have hD := h.nonneg
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  have hi := kernelInverseEnvelope_nonneg hD hp
  have hf0 : 0 ≤ (m : ℝ)*allocatedFrontEnvelope m D p (allocatedAccuracyEnvelope m D p e) := by
    dsimp only [allocatedFrontEnvelope, allocatedKernelEnvelope, allocatedAccuracyEnvelope]
    positivity
  have ht0 : 0 ≤ allocatedTupleEnvelope m D p e := by
    dsimp only [allocatedTupleEnvelope]
    positivity
  unfold allocatedJointLengthLog allocatedJointLengthEnvelope
  exact max_le (hl.trans (le_add_of_nonneg_right ht0)) (hr.trans (le_add_of_nonneg_left hf0))

theorem allocatedTestLengthLog_le_envelope (he : 0 ≤ e) :
    allocatedJointLengthLog (G := G) B α O p (allocatedJetTestLog (G := G) B α O p e) ≤
      allocatedTestLengthEnvelope m D p e := by
  have ht := allocatedJetTestLog_le_envelope B h hp (e := e)
  have hj := allocatedJointLengthLog_le_envelope B h hp
    (allocatedJetTestLog_nonneg (G := G) B α O hp he)
  apply hj.trans
  dsimp only [allocatedTestLengthEnvelope, allocatedJointLengthEnvelope, allocatedFrontEnvelope,
    allocatedAccuracyEnvelope, allocatedTupleEnvelope]
  gcongr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

noncomputable def comparisonProfileBound : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊+1

noncomputable def allocatedComparisonDimension {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  (m+1 : ℕ)+p+((m+1 : ℕ)*(p+1)^(m+1)+1)+(2^(m+1) : ℕ)+
    (m+2 : ℕ)*p+(2*m : ℕ)*p+(2*m : ℕ)*p*(2^(m+1) : ℕ)+comparisonProfileBound

theorem allocatedComparisonDimension_bounds (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let D := allocatedComparisonDimension m p
    0 ≤ D ∧ ((m+1 : ℕ) : ℝ) ≤ D ∧ p ≤ D ∧ ((2^(m+1) : ℕ) : ℝ) ≤ D ∧
      geometricSiteBudget m 0 p ≤ D ∧ ((m+2 : ℕ) : ℝ)*p ≤ D ∧
      ((2*m : ℕ) : ℝ)*p ≤ D ∧ ((2*m : ℕ) : ℝ)*p*(2^(m+1) : ℕ) ≤ D ∧
      (comparisonProfileBound : ℝ) ≤ D := by
  have hC : 0 ≤ ((m+1 : ℕ) : ℝ)*(p+1)^(m+1)+1 := by positivity
  have hpa : 0 ≤ ((m+2 : ℕ) : ℝ)*p := by positivity
  have ha : 0 ≤ ((2*m : ℕ) : ℝ)*p := by positivity
  have ho : 0 ≤ ((2*m : ℕ) : ℝ)*p*(2^(m+1) : ℕ) := by positivity
  have hm : (0 : ℝ) ≤ (m+1 : ℕ) := Nat.cast_nonneg _
  have hq : (0 : ℝ) ≤ (2^(m+1) : ℕ) := Nat.cast_nonneg _
  have hf : (0 : ℝ) ≤ comparisonProfileBound := Nat.cast_nonneg _
  dsimp only [allocatedComparisonDimension]
  simp only [geometricSiteBudget, pow_zero]
  push_cast at *
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedPrincipalIndex_card_le_variables :
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) ≤
      Fintype.card (LayerSamplerVariables G I n B) := by
  change _ ≤ Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))
  rw [Fintype.card_sum]
  omega

theorem allocatedKernelVariables_card_le_variables :
    Fintype.card G ≤ Fintype.card (LayerSamplerVariables G I n B) := by
  change _ ≤ Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))
  rw [Fintype.card_sum]
  omega

theorem allocatedJointParameter_card (α : Type*) [Fintype α] :
    Fintype.card (JointBlockParameter B (layerSamplerDegree I n) α) =
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n))*(Fintype.card α+1) := by
  simp only [JointBlockParameter, BlockParameter, PrincipalTupleIndex, Fintype.card_sigma,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_option]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem allocatedAxes_card_le {p : ℝ}
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ ((2*m : ℕ) : ℝ)*p := by
  calc
    _ = ∑ j : Fin m, ((Fintype.card (I j) : ℝ)+(n j : ℝ)) := by
      simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin,
        Nat.cast_sum, Nat.cast_add]
    _ ≤ ∑ _ : Fin m, (p+p) := Finset.sum_le_sum (fun j _ => add_le_add (hI j) (hn j))
    _ = _ := by simp; ring

theorem allocatedComparisonDimensions_of_primitive
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ m+1)
    (hinj : ∀ j, Function.Injective (rows j)) {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    AllocatedComparisonDimensions (G := G) B α O (allocatedComparisonDimension m p) := by
  obtain ⟨hD, hm, hpD, hqD, hCD, hpaD, haD, hoD, hfD⟩ := allocatedComparisonDimension_bounds m hp
  have hqreal : (Fintype.card α : ℝ) ≤ (m+1 : ℕ) := Nat.cast_le.mpr hq
  have hrow (j : Fin m) : Fintype.card (O j) ≤ 2^(m+1) := by
    have hc := Fintype.card_le_of_injective (rows j) (hinj j)
    rw [Fintype.card_finset] at hc
    exact hc.trans (Nat.pow_le_pow_right (by omega) hq)
  have htuple : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hK
  have haxes := allocatedAxes_card_le (I := I) (n := n) hI hn
  refine ⟨hD, (Nat.cast_le.mpr (Nat.le_succ m)).trans hm,
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hK.trans hpD),
    hqreal.trans hm, haxes.trans haD, htuple.trans hpD, ?_, ?_,
    fun j => (Nat.cast_le.mpr (hrow j)).trans hqD, ?_, ?_⟩
  · rw [allocatedJointParameter_card, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply le_trans _ hpaD
    calc
      _ ≤ p*((m+1 : ℕ)+1) :=
        mul_le_mul htuple (by linarith) (by positivity) hp
      _ = _ := by push_cast; ring
  · apply le_trans _ hoD
    calc
      _ = ∑ a : LayerSamplerAxis I n, (Fintype.card (O a.1) : ℝ) := by
        simp only [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _ : LayerSamplerAxis I n, ((2^(m+1) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun a _ => Nat.cast_le.mpr (hrow a.1))
      _ = (Fintype.card (LayerSamplerAxis I n) : ℝ)*(2^(m+1) : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right haxes (Nat.cast_nonneg _)
  · intro j
    exact (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
      (Nat.succ_le_of_lt j.isLt) hp hK).trans hCD
  · apply le_trans _ hfD
    exact (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators

def allocatedWitnessScaleLog (P Qw : ℝ) : ℝ :=
  allocatedScaleLog P + P ^ 2 * Qw

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem exists_allocatedWitnessScale_of_bounded_source
    (R σ : Fin m → ℝ) (S0 : LayerSamplerScale (G := G) B U b R σ)
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D P W Qw : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hDQ : D ≤ P) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hS0 : (S0.value : ℝ) ≤ Real.exp P)
    (hW : 1 ≤ W) (hQw : 0 ≤ Qw) (hWexp : W ≤ Real.exp Qw) :
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      S0.value ≤ S.value ∧
      (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog P Qw) ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDQ
  have hm : (m : ℝ) ≤ P := hdim.degree.trans hDQ
  have hn (j : Fin m) : (n j : ℝ) ≤ P := by
    have hi : Function.Injective (fun i : Fin (n j) =>
        (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) := by
      intro a b hab
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Sum.inr.injEq] using hab
    have hc := Fintype.card_le_of_injective _ hi
    exact (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hc)).trans
      (hdim.axes.trans hDQ)
  have haxes : (Fintype.card (Σ j : Fin m, Fin (n j)) : ℝ) ≤ P ^ 2 := by
    calc
      _ = ∑ j : Fin m, (n j : ℝ) := by simp [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hn j)
      _ = (m : ℝ) * P := by simp
      _ ≤ P ^ 2 := by nlinarith
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P :=
    (hdim.profile.trans hDQ).trans (by linarith [Real.add_one_le_exp P])
  obtain ⟨ht, hg⟩ := layerSamplerWidths_inverse_exp_bounds B R σ hP hR hσ hRi hσi
    (fun j => (hdim.coefficients j).trans hDQ)
  have hbound := layerSamplerWitnessScaleBound_exp_bound B R σ hR hσ S0.value
    (lt_of_lt_of_le zero_lt_one hW) hP (show 0 ≤ 4 * (P + 8) by positivity)
    (show 0 ≤ 4 * (P + 8) by positivity) hQw hA hS0 ht hg hWexp
  obtain ⟨S, hle, hS, hwidth⟩ :=
    exists_layerSamplerWitnessScale (G := G) B U b R σ hR hσ S0.value hW
  refine ⟨S, hle, (Nat.cast_le.mpr hS).trans (hbound.trans ?_), hwidth⟩
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (P + 4 * (P + 8) + 17) + P ^ 2 * (P + (4 * (P + 8) + Qw) + 17) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right haxes
        (show 0 ≤ P + (4 * (P + 8) + Qw) + 17 by positivity))
    _ = allocatedWitnessScaleLog P Qw := by
      unfold allocatedWitnessScaleLog allocatedScaleLog
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedComparisonDimensions_of_primitive_with_cutoff_unboosted
    (d : ℕ) {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ d+1)
    (hinj : ∀ j, Function.Injective (rows j)) {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    AllocatedComparisonDimensions (G := G) B α O
      (allocatedComparisonDimension (max m d) p) := by
  let M := max m d
  have hmM : m ≤ M := Nat.le_max_left _ _
  have hdM : d ≤ M := Nat.le_max_right _ _
  have hqM : Fintype.card α ≤ M+1 := hq.trans (Nat.add_le_add_right hdM 1)
  obtain ⟨hD, hM, hpD, hqD, hCD, hpaD, haD, hoD, hfD⟩ :=
    allocatedComparisonDimension_bounds M hp
  have hqreal : (Fintype.card α : ℝ) ≤ (M+1 : ℕ) := Nat.cast_le.mpr hqM
  have hrow (j : Fin m) : Fintype.card (O j) ≤ 2^(M+1) := by
    have hc := Fintype.card_le_of_injective (rows j) (hinj j)
    rw [Fintype.card_finset] at hc
    exact hc.trans (Nat.pow_le_pow_right (by omega) hqM)
  have htuple : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hK
  have haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ ((2*M : ℕ) : ℝ)*p := by
    apply (allocatedAxes_card_le (I := I) (n := n) hI hn).trans
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.mul_le_mul_left 2 hmM)) hp
  refine ⟨hD, (Nat.cast_le.mpr (hmM.trans (Nat.le_succ M))).trans hM,
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans (hK.trans hpD),
    hqreal.trans hM, haxes.trans haD, htuple.trans hpD, ?_, ?_,
    fun j => (Nat.cast_le.mpr (hrow j)).trans hqD, ?_, ?_⟩
  · rw [allocatedJointParameter_card, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    apply le_trans _ hpaD
    calc
      _ ≤ p*((M+1 : ℕ)+1) :=
        mul_le_mul htuple (by linarith) (by positivity) hp
      _ = _ := by push_cast; ring
  · apply le_trans _ hoD
    calc
      _ = ∑ a : LayerSamplerAxis I n, (Fintype.card (O a.1) : ℝ) := by
        simp only [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _ : LayerSamplerAxis I n, ((2^(M+1) : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun a _ => Nat.cast_le.mpr (hrow a.1))
      _ = (Fintype.card (LayerSamplerAxis I n) : ℝ)*(2^(M+1) : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right haxes (Nat.cast_nonneg _)
  · intro j
    exact (boundedCoefficientExponent_card_le_geometricSiteBudget M 0
      ((Nat.succ_le_of_lt j.isLt).trans hmM) hp hK).trans hCD
  · apply le_trans _ hfD
    exact (Nat.le_ceil _).trans (by unfold comparisonProfileBound; push_cast; linarith)

theorem allocatedComparisonDimensions_of_primitive_with_cutoff
    (d : ℕ) {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ d+1)
    (hinj : ∀ j, Function.Injective (rows j)) {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    AllocatedComparisonDimensions (G := G) B α O
      (allocatedComparisonDimension (max m d) (p+(d+1 : ℕ))) := by
  have hpp : p ≤ p+(d+1 : ℕ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  exact allocatedComparisonDimensions_of_primitive_with_cutoff_unboosted B d rows hq hinj
    (hp.trans hpp) (hK.trans hpp) (fun j => (hI j).trans hpp) (fun j => (hn j).trans hpp)

theorem allocatedComparisonDimensions_of_primitive_withCutoff
    {d : ℕ} {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ d+1)
    (hinj : ∀ j, Function.Injective (rows j)) {p : ℝ} (hp : 0 ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    AllocatedComparisonDimensions (G := G) B α O
      (allocatedComparisonDimension (max m d) p) :=
  allocatedComparisonDimensions_of_primitive_with_cutoff_unboosted B d rows hq hinj hp hK hI hn

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, IsEmpty (I j)]
variable {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem emptyLayerSamplerVariables_card :
    Fintype.card (LayerSamplerVariables G I n B) = Fintype.card G := by
  simp only [LayerSamplerVariables, SamplerTupleIndex, Fintype.card_sum]
  have hzero : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) = 0 := by
    let : IsEmpty (PrincipalTupleIndex B (layerSamplerDegree I n)) :=
      ⟨fun a => a.1.2.elim isEmptyElim isEmptyElim⟩
    exact Fintype.card_eq_zero
  rw [hzero, Nat.add_zero]

theorem emptyLayerCoefficientCount_le (j : Fin m) :
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) ≤ allocatedComparisonDimension m (Fintype.card G : ℝ) := by
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      (Fintype.card G : ℝ) := by rw [emptyLayerSamplerVariables_card B]
  exact (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
    (Nat.succ_le_of_lt j.isLt) (Nat.cast_nonneg _) hvars).trans
    (allocatedComparisonDimension_bounds m (Nat.cast_nonneg (Fintype.card G))).2.2.2.2.1

theorem emptyLayerCoefficientCount_le_exp (j : Fin m) :
    4 * ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) + 1) ≤
        Real.exp (allocatedComparisonDimension m (Fintype.card G : ℝ) + 4) := by
  have hcount := emptyLayerCoefficientCount_le (G := G) B j
  have hcountExp : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      (j.val + 1)) : ℝ) + 1 ≤
        Real.exp (allocatedComparisonDimension m (Fintype.card G : ℝ)) := by
    linarith [Real.add_one_le_exp (allocatedComparisonDimension m (Fintype.card G : ℝ))]
  calc
    _ ≤ 4 * Real.exp (allocatedComparisonDimension m (Fintype.card G : ℝ)) := by
      gcongr
    _ ≤ Real.exp 4 * Real.exp (allocatedComparisonDimension m (Fintype.card G : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (4 : ℝ)])
        (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem exists_allocatedWitnessScale_with_late_floor
    (R σ : Fin m → ℝ) (S0 : LayerSamplerScale (G := G) B U b R σ) (Lmin : ℕ)
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D P W Qw Pmin : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hDP : D ≤ P) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hS0 : (S0.value : ℝ) ≤ Real.exp P)
    (hW : 1 ≤ W) (hQw : 0 ≤ Qw) (hWexp : W ≤ Real.exp Qw)
    (hPmin : 0 ≤ Pmin) (hLmin : (Lmin : ℝ) ≤ Real.exp Pmin) :
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      S0.value ≤ S.value ∧ Lmin ≤ S.value ∧
      (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog P Qw + (1 + P ^ 2) * Pmin) ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hm : (m : ℝ) ≤ P := hdim.degree.trans hDP
  have hn (j : Fin m) : (n j : ℝ) ≤ P := by
    have hi : Function.Injective (fun i : Fin (n j) =>
        (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n)) := by
      intro a b hab
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Sum.inr.injEq] using hab
    have hc := Fintype.card_le_of_injective _ hi
    exact (Nat.cast_le.mpr (by simpa only [Fintype.card_fin] using hc)).trans
      (hdim.axes.trans hDP)
  have haxes : (Fintype.card (Σ j : Fin m, Fin (n j)) : ℝ) ≤ P ^ 2 := by
    calc
      _ = ∑ j : Fin m, (n j : ℝ) := by simp [Fintype.card_sigma, Nat.cast_sum]
      _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hn j)
      _ = (m : ℝ) * P := by simp
      _ ≤ P ^ 2 := by nlinarith
  have hA0 : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P :=
    (hdim.profile.trans hDP).trans (by linarith [Real.add_one_le_exp P])
  have hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (P + Pmin) :=
    hA0.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hPmin))
  have hL : ((max S0.value Lmin : ℕ) : ℝ) ≤ Real.exp (P + Pmin) := by
    rw [Nat.cast_max]
    exact max_le
      (hS0.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hPmin)))
      (hLmin.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hP)))
  obtain ⟨ht, hg⟩ := layerSamplerWidths_inverse_exp_bounds B R σ hP hR hσ hRi hσi
    (fun j => (hdim.coefficients j).trans hDP)
  have hbound := layerSamplerWitnessScaleBound_exp_bound B R σ hR hσ (max S0.value Lmin)
    (lt_of_lt_of_le zero_lt_one hW) (add_nonneg hP hPmin)
    (show 0 ≤ 4 * (P + 8) by positivity)
    (show 0 ≤ 4 * (P + 8) by positivity) hQw hA hL ht hg hWexp
  obtain ⟨S, hlo, hhi, hprincipal⟩ :=
    exists_layerSamplerWitnessScale (G := G) B U b R σ hR hσ (max S0.value Lmin) hW
  refine ⟨S, (le_max_left _ _).trans hlo, (le_max_right _ _).trans hlo,
    (Nat.cast_le.mpr hhi).trans (hbound.trans ?_), hprincipal⟩
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (P + Pmin + 4 * (P + 8) + 17) +
        P ^ 2 * (P + Pmin + (4 * (P + 8) + Qw) + 17) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right haxes (by positivity))
    _ = allocatedWitnessScaleLog P Qw + (1 + P ^ 2) * Pmin := by
      unfold allocatedWitnessScaleLog allocatedScaleLog
      ring

theorem exists_allocatedWitnessScale_with_exponential_floor
    (R σ : Fin m → ℝ) (S0 : LayerSamplerScale (G := G) B U b R σ)
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D P W Qw Pmin : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (hDP : D ≤ P) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hS0 : (S0.value : ℝ) ≤ Real.exp P)
    (hW : 1 ≤ W) (hQw : 0 ≤ Qw) (hWexp : W ≤ Real.exp Qw)
    (hPmin : 0 ≤ Pmin) :
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      S0.value ≤ S.value ∧ Real.exp Pmin ≤ (S.value : ℝ) ∧
      (S.value : ℝ) ≤ Real.exp (allocatedWitnessScaleLog P Qw + (1 + P ^ 2) * (Pmin + 1)) ∧
      ∀ j i, S.value ^ (j.val + 1) < basisAxisScale (b j) i →
        8 * (probabilityProfileLipschitz : ℝ) * W ≤
          (layerSamplerGapWidth (G := G) B R ⟨j, i⟩ / 2) *
            ((basisAxisScale (b j) i : ℝ) / (S.value : ℝ) ^ (j.val + 1)) := by
  obtain ⟨S, hS0S, hfloor, hS, hprincipal⟩ :=
    exists_allocatedWitnessScale_with_late_floor B U b R σ S0 ⌈Real.exp Pmin⌉₊
      hdim hDP hR hσ hRi hσi hS0 hW hQw hWexp
      (show 0 ≤ Pmin + 1 by linarith)
      (natCeil_le_exp_succ (Real.exp_nonneg Pmin) hPmin le_rfl)
  exact ⟨S, hS0S, (Nat.le_ceil _).trans (Nat.cast_le.mpr hfloor), hS, hprincipal⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

include U b o

theorem allocatedAmbientDimension_eq (j : Fin m) :
    Fintype.card (I j) + n j = Fintype.card (J j) := by
  have h := (euclideanSubspace (U j)).finrank_add_finrank_orthogonal
  rw [finrank_eq_card_basis (o j).toBasis, finrank_eq_card_basis (b j), finrank_euclideanSpace] at h
  simpa only [Fintype.card_fin] using h

theorem allocatedAmbientDimension_le_axes (j : Fin m) :
    Fintype.card (J j) ≤ Fintype.card (LayerSamplerAxis I n) := by
  rw [← allocatedAmbientDimension_eq U b o j]
  have h := Finset.single_le_sum (f := fun i : Fin m => Fintype.card (I i ⊕ Fin (n i)))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  simpa only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin] using h

theorem allocatedLatticeDimension_eq
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (j : Fin m) : Fintype.card (Q j) = Fintype.card (I j) := by
  have h := standardLatticeCoordinates_card (euclideanSubspace (U j)) (bW j) (b j) (hb j)
  rw [Fintype.card_sum, Fintype.card_fin, ← allocatedAmbientDimension_eq U b o j] at h
  omega

theorem allocatedProfile_dimensions
    {G : Type*} [Fintype G] (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    {D : ℝ} (hd : AllocatedComparisonDimensions (G := G) B α O D)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))) :
    (∀ j, (Fintype.card (J j) : ℝ) ≤ D) ∧ (∀ j, (Fintype.card (Q j) : ℝ) ≤ D) := by
  have hJ (j) : (Fintype.card (J j) : ℝ) ≤ D :=
    (Nat.cast_le.mpr (allocatedAmbientDimension_le_axes U b o j)).trans hd.axes
  exact ⟨hJ, fun j => (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans (hJ j)⟩

end Erdos3.VectorPolynomial

end

end OAI
