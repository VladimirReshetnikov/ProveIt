import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionLatticeGeometry
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionReversedWeights
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionNearbyKernel
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionDensityPrecision
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitKernel.GaussianEulerUnitKernelLatticeSum
import IPRADerivations.Analysis.RationalArithmetic.Distances.RationalSandwichRadius

/-!
# Compare the original unit-lattice rows with the reversed Euler rows

The entire block lies between two actual integer floor cuts. Its scalar
distance to the original right image endpoint is at most the original
decay mesh plus the node displacement. The original Euler power
and rational unit kernel retain their independent output queries.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionLatticeGeometry (source disk start cuts_source denominator_positive)
open GaussianEulerUnitSubstitutionFloorCuts (cut cutF data)
open GaussianEulerUnitDecayInput (clock compactDenominator)
open GaussianEulerUnitSubstitutionTiltedNodes (reverseNode)
open GaussianEulerUnitSubstitutionImageGrid (meshNumerator meshDenominator)
open GaussianEulerUnitSubstitutionReversedDensity (leftIndex coarsePowerBody)
open GaussianEulerUnitKernelLatticeSum (body)
open GaussianPartitionedFiniteSumDistance (blockLength blockAgreement)
open GaussianRationalRiemannRefinement (termsDistance constantBody)
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def displacementNumerator (p N M : PTm n) : PTm n := two*N*M+unit p
def displacementDenominator (p M : PTm n) : PTm n := M*unit p
def pointNumerator (p N C E M : PTm n) : PTm n :=
  meshNumerator p N C E*displacementDenominator p M+displacementNumerator p N M*meshDenominator p N E
def pointDenominator (p N E M : PTm n) : PTm n := meshDenominator p N E*displacementDenominator p M
def anchorNumerator (k q N R C E T M : PTm n) : PTm n :=
  let p := clock k E T
  rateNumerator (GaussianEulerUnitSubstitutionNearbyKernel.leadingNumerator k R E T (disk E T)
    (pointNumerator p N C E M) (pointDenominator p N E M))
    (GaussianEulerUnitSubstitutionNearbyKernel.leadingDenominator k (pointDenominator p N E M)) p q
def anchorDenominator (k q N E T M : PTm n) : PTm n :=
  let p := clock k E T
  rateDenominator (GaussianEulerUnitSubstitutionNearbyKernel.leadingDenominator k (pointDenominator p N E M)) p q

@[simp] theorem subst_anchorNumerator {m : ℕ} (σ : Fin n → PTm m) (k q N R C E T M : PTm n) :
    Syn.subst σ (anchorNumerator k q N R C E T M) = anchorNumerator (Syn.subst σ k) (Syn.subst σ q)
      (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by
  simp [anchorNumerator,pointNumerator,pointDenominator,displacementNumerator,displacementDenominator]
@[simp] theorem subst_anchorDenominator {m : ℕ} (σ : Fin n → PTm m) (k q N E T M : PTm n) :
    Syn.subst σ (anchorDenominator k q N E T M) = anchorDenominator (Syn.subst σ k) (Syn.subst σ q)
      (Syn.subst σ N) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by
  simp [anchorDenominator,pointDenominator,displacementDenominator]

theorem point_denominator_positive (k N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] le one (pointDenominator (clock k E T) N E M) := by
  have hu := unit_positive (Γ := Γ) (clock k E T)
  have hE := h.andE₁.andE₁.andE₁.andE₂.andE₁
  have hN := h.andE₁.andE₂.andE₁
  have hM := denominator_positive _ _ _ _ _ _ _ _ _ _ h
  exact positive_product _ _ (positive_product _ _ (positive_product _ _ hE hN) hu) (positive_product _ _ hM hu)

theorem anchor_denominator_positive (k q N z R B a C E T M : PTm n) (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] le one (anchorDenominator k q N E T M) :=
  GaussianNamedInverseRate.denominator_positive _ _ _
    (positive_product _ _ (point_denominator_positive _ _ _ _ _ _ _ _ _ _ h) (unit_positive k))

theorem original_point_distance (i v k N z R B a C E T M : PTm n)
    (h : Γ ⊢[PRAAx] source k N z R B a C E T M) (hi : Γ ⊢[PRAAx] lt i N)
    (lo : Γ ⊢[PRAAx] le (cut i k N a C E T M) v) (up : Γ ⊢[PRAAx] le v (cut (succ i) k N a C E T M)) :
    Γ ⊢[PRAAx] RationalValueBounds.radius (reverseNode (succ i) (clock k E T) N a C E) (fraction v M)
      (pointNumerator (clock k E T) N C E M) (pointDenominator (clock k E T) N E M) := by
  have hM := denominator_positive _ _ _ _ _ _ _ _ _ _ h
  have lower : Γ ⊢[PRAAx] le (M*cut i k N a C E T M) (v*M) :=
    le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right M lo)
  have upper : Γ ⊢[PRAAx] le (M*v) (cut (succ i) k N a C E T M*M) :=
    le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right M up)
  have lu := fraction_order _ _ _ _ hM hM lower
  have uv := fraction_order _ _ _ _ hM hM upper
  have mesh := GaussianEulerUnitSubstitutionReversedWeights.original_reversed_mesh i (clock k E T) N a C E
    (GaussianEulerUnitSubstitutionDensityPrecision.geometry_source z R B a C E T N h.andE₁) hi
  exact RationalValueBounds.radius_symmetric _ _ _ _
    (RationalSandwichRadius.perturbed_endpoints _ _ _ _ _ _ _ _ _ lu uv
      (GaussianEulerUnitSubstitutionFloorCuts.original_displacement i k N a C E T M (cuts_source _ _ _ _ _ _ _ _ _ _ h) (le_of_lt hi))
      (GaussianEulerUnitSubstitutionFloorCuts.original_displacement (succ i) k N a C E T M (cuts_source _ _ _ _ _ _ _ _ _ _ h) hi) mesh)

theorem original_lattice_row (i v k q N z R B a C E T M : PTm n)
    (h : Γ ⊢[PRAAx] source k N z R B a C E T M) (hi : Γ ⊢[PRAAx] lt i N)
    (lo : Γ ⊢[PRAAx] le (cut i k N a C E T M) v) (up : Γ ⊢[PRAAx] le v (cut (succ i) k N a C E T M)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 GaussianEulerUnitSubstitutionKernel.nameF q (GaussianEulerUnitSubstitutionKernel.data z B v M))
      (inst2 coarsePowerBody i (GaussianEulerUnitSubstitutionReversedDensity.data (clock k E T) N z B a C E))
      (anchorNumerator k q N R C E T M) (anchorDenominator k q N E T M) := by
  let p := clock k E T
  let a' := a*N+C*leftIndex N i
  let b' := E*N
  have hz := h.andE₁.andE₁.andE₁
  have chart := GaussianEulerUnitSubstitutionReversedDensity.reversed_unit_source i N z R B a C E T h.andE₁
  have range := GaussianEulerUnitSubstitutionFloorCuts.original_block_source i v k N a C E T M (cuts_source _ _ _ _ _ _ _ _ _ _ h) lo up
  have close := original_point_distance i v k N z R B a C E T M h hi lo up
  have hd := point_denominator_positive k N z R B a C E T M h
  have hs : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionNearbyKernel.source k z R B a' b' E T v M (disk E T)
      (pointNumerator p N C E M) (pointDenominator p N E M) :=
    .andI chart (.andI (.andI hz.andE₁ (.andI (GaussianEulerUnitSubstitutionLatticeGeometry.disk_positive E T) hz.andE₂.andE₂))
      (.andI (GaussianEulerUnitSubstitutionLatticeGeometry.disk_widens E T) (.andI range (.andI hd close))))
  have row := GaussianEulerUnitSubstitutionNearbyKernel.original_observations p q k z R B a' b' E T v M (disk E T) _ _ hs
  exact distance_congr (.eqRefl _)
    (GaussianEulerUnitSubstitutionReversedDensity.power_row_at i p N z B a C E).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ (anchor_denominator_positive k q N z R B a C E T M h) row)

def latticeData (k q N z B a C E T M : PTm n) : PTm n :=
  GaussianEulerUnitKernelLatticeSum.data q z B (start k N a C E T M) M
def powerData (k N z B a C E T : PTm n) : PTm n :=
  GaussianEulerUnitSubstitutionReversedDensity.data (clock k E T) N z B a C E

@[simp] theorem subst_latticeData {m : ℕ} (σ : Fin n → PTm m) (k q N z B a C E T M : PTm n) :
    Syn.subst σ (latticeData k q N z B a C E T M) = latticeData (Syn.subst σ k) (Syn.subst σ q) (Syn.subst σ N)
      (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ M) := by
  simp [latticeData]
@[simp] theorem subst_powerData {m : ℕ} (σ : Fin n → PTm m) (k N z B a C E T : PTm n) :
    Syn.subst σ (powerData k N z B a C E T) = powerData (Syn.subst σ k) (Syn.subst σ N) (Syn.subst σ z)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [powerData]

private theorem shifted_lattice_row (j p z B L M I : PTm n) : Γ ⊢[PRAAx]
    inst2 (offB body) j (pairT I (GaussianEulerUnitKernelLatticeSum.data p z B L M)) ≐
      GaussianEulerUnitKernelLatticeSum.row (I+j) p z B L M := by
  rw [inst2_offB]
  exact (congrInst2 body (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
    (GaussianEulerUnitKernelLatticeSum.row_at _ _ _ _ _ _)

private theorem constant_at (i y : PTm n) : inst2 constantBody i y = y := by
  simp [constantBody,inst2]

theorem original_block_rows (i k q N z R B a C E T M : PTm n)
    (h : Γ ⊢[PRAAx] source k N z R B a C E T M)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    termsDistance (offB body) constantBody (blockLength cutF i (data k N a C E T M))
      (pairT (ap2 cutF i (data k N a C E T M)) (latticeData k q N z B a C E T M))
      (inst2 coarsePowerBody i (powerData k N z B a C E T))
      (anchorNumerator k q N R C E T M) (anchorDenominator k q N E T M) := by
  let s (u : PTm n) := Syn.shift u
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s k) (s N) (s z) (s R) (s B) (s a) (s C) (s E) (s T) (s M) :=
    by simpa [Fm.shift,Syn.shift,s] using h.shift
  have is : Γ.map Fm.shift ⊢[PRAAx] lt (s i) (s N) := by simpa [Fm.shift,Syn.shift,s] using hi.shift
  refine .allI (.impI ?_)
  let I := ap2 cutF (s i) (data (s k) (s N) (s a) (s C) (s E) (s T) (s M))
  let L := start (s k) (s N) (s a) (s C) (s E) (s T) (s M)
  have near := GaussianEulerUnitSubstitutionLatticeGeometry.original_positions (s i) (var 0) (s k) (s N) (s a) (s C) (s E) (s T) (s M)
    (cuts_source _ _ _ _ _ _ _ _ _ _ hs.wk) Prf.hyp0
  have raw := original_lattice_row (s i) (L+(I+var 0)) (s k) (s q) (s N) (s z) (s R) (s B)
    (s a) (s C) (s E) (s T) (s M) hs.wk is.wk near.andE₁ (le_of_lt near.andE₂)
  simp only [Syn.shift,GaussianPartitionedFiniteSumDistance.subst_blockLength,GaussianEulerUnitSubstitutionFloorCuts.subst_data,
    subst_pairT,subst_ap2,subst_inst2,subst_latticeData,subst_powerData,subst_anchorNumerator,subst_anchorDenominator,
    constant_at]
  change _ ⊢[PRAAx] distanceBounded
    (inst2 (offB body) (var 0) (pairT I (GaussianEulerUnitKernelLatticeSum.data (s q) (s z) (s B) L (s M))))
    (inst2 coarsePowerBody (s i) (powerData (s k) (s N) (s z) (s B) (s a) (s C) (s E) (s T)))
    (anchorNumerator (s k) (s q) (s N) (s R) (s C) (s E) (s T) (s M))
    (anchorDenominator (s k) (s q) (s N) (s E) (s T) (s M))
  exact distance_congr (shifted_lattice_row (var 0) (s q) (s z) (s B) L (s M) I).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) raw

theorem original_block_agreement (k q N z R B a C E T M : PTm n)
    (h : Γ ⊢[PRAAx] source k N z R B a C E T M) :
    Γ ⊢[PRAAx] blockAgreement cutF body coarsePowerBody N (data k N a C E T M) (latticeData k q N z B a C E T M)
      (powerData k N z B a C E T) (anchorNumerator k q N R C E T M) (anchorDenominator k q N E T M) := by
  let s (u : PTm n) := Syn.shift u
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s k) (s N) (s z) (s R) (s B) (s a) (s C) (s E) (s T) (s M) :=
    by simpa [Fm.shift,Syn.shift,s] using h.shift
  refine .allI (.impI ?_)
  simpa only [blockAgreement,GaussianEulerUnitSubstitutionFloorCuts.subst_data,subst_latticeData,subst_powerData,
    subst_anchorNumerator,subst_anchorDenominator,Syn.shift,s] using
    original_block_rows (var 0) (s k) (s q) (s N) (s z) (s R) (s B) (s a) (s C) (s E) (s T) (s M) hs.wk Prf.hyp0

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionLatticeRows
