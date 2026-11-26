import IPRADerivations.Analysis.Euler.QuadraticSubstitution.GaussianEulerSquareFactorExtraction
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# Original compact quadratic Jacobian and its factored kernel name

Both actual compact samplers meet on one product refinement of their
original meshes. The original factor query is fixed at the requested
output precision, using the independent finite observation estimate.
A later row query pays only the auxiliary quadrature observations.
The fixed finite envelope gives exact name equivalence.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareFactorCompact

open_ipra
open GaussianEulerSquareIntegrand (factorF factorData)
open GaussianEulerSquareFactorObservation (factorBound kernelBound leadingNumerator leadingDenominator)
open GaussianCompactRiemannName (quadrature mesh precision mesh_positive quadrature_index_congr)
open GaussianCompactMeshIndependence (arbitrary_refinement)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "J" => GaussianEulerSquareJacobianCompactName.evaluatorF
local notation "JD" => GaussianEulerSquareJacobianCompactName.fixedData
local notation "JN" => GaussianEulerSquareJacobianCompactName.nameF
local notation "JData" => GaussianEulerSquareJacobianCompactName.data
local notation "K" => GaussianEulerQuadraticKernelCompactName.evaluatorF
local notation "KD" => GaussianEulerPositiveScalingIntegrand.fixedData
local notation "KN" => GaussianEulerQuadraticKernelCompactName.nameF
local notation "KData" => GaussianEulerQuadraticKernelCompactName.data

abbrev source (z R B c d a C E T : PTm n) : Fm PTm n := GaussianEulerQuadraticKernelCompactName.source z R B c d a C E T
abbrev factoredF : PR 2 := multiplyF factorF KN
def factoredData (z R B c d a C E T : PTm n) : PTm n := multiplyData factorF KN (factorData z B c d) (KData z R B c d a C E T)
def diagonalCost (z R B c d a C E T : PTm n) : PTm n := num 4+T*kernelBound R E T c+num 3*factorBound z B c d+
  (multiplyModulus factorF KN (factorData z B c d) (KData z R B c d a C E T)+one)

ipra_subst factoredData
ipra_subst diagonalCost

theorem factor_regular (z R B c d a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN factorF (factorData z B c d) :=
  GaussianEulerSquareFactorObservation.factor_regular z R B E c d (.andI hs.andE₁.andE₁ hs.andE₂)

theorem factored_regular (z R B c d a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN factoredF (factoredData z R B c d a C E T) :=
  GaussianNameArithmetic.multiply_fast factorF KN _ _ (factor_regular z R B c d a C E T hs)
    (GaussianEulerQuadraticKernelCompactName.name_regular z R B c d a C E T hs)

theorem original_diagonal (t z R B c d a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 JN t (JData z R B c d a C E T)) (ap2 factoredF t (factoredData z R B c d a C E T))
      (diagonalCost z R B c d a C E T) (unit t) := by
  let LJ := GaussianEulerSquareJacobianRate.lipschitz R E T c d
  let LK := GaussianEulerQuadraticKernelCompactName.lipschitz R E T c d
  let O := mesh t LJ T
  let V := mesh t LK T
  let N := O*V
  let F := factorBound z B c d
  let H := kernelBound R E T c
  let s := precision t T+GaussianFastValueCut.exponent (T*(one+F)) t
  let P := unit t
  let Q := unit s
  let x := JD z B c d T
  let y := KD z B c d
  let u := factorData z B c d
  let v := KData z R B c d a C E T
  have hp := unit_positive (Γ := Γ) t
  have hq := unit_positive (Γ := Γ) s
  have hE := hs.andE₁.andE₁.andE₂.andE₁
  have width : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left C a) hs.andE₁.andE₂.andE₂
  have hO := mesh_positive (Γ := Γ) t LJ T
  have hV := mesh_positive (Γ := Γ) t LK T
  have hN := positive_product _ _ hO hV
  have later : Γ ⊢[PRAAx] le (precision t T) s := le_add_right _ _
  have pays : Γ ⊢[PRAAx] le (T*(one+F)*P) Q := le_trans (GaussianFastValueCut.query_budget _ _)
    (GaussianExponentialReference.unit_monotone (le_add_left _ _))
  have grow : Γ ⊢[PRAAx] le P (unit (t+num 6)) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have payThree : Γ ⊢[PRAAx] le (num 3*P) (num 3*unit (t+num 6)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (num 3) grow)
  have jr := GaussianEulerSquareJacobianCompactName.compact_input z R B c d a C E T hs
  have kr := GaussianEulerQuadraticKernelCompactName.compact_input z R B c d a C E T hs
  have hfactor := factor_regular z R B c d a C E T hs
  have hkernel := GaussianEulerQuadraticKernelCompactName.name_regular z R B c d a C E T hs
  have old := arbitrary_refinement J t s V a C E LJ T x jr hV later
  have oldRead := distance_congr (quadrature_index_congr J s _ N a C E x (by dsimp only [N]; ipra_ring))
    (GaussianEulerSquareJacobianCompactName.name_at t z R B c d a C E T).eqSymm (.eqRefl _) (.eqRefl _) old
  have first := distance_radius_mono _ _ _ _ (num 3) P (unit_positive (t+num 6)) hp payThree
    (distance_symmetric _ _ _ _ (unit_positive (t+num 6)) oldRead)
  have finite := GaussianEulerSquareFactorExtraction.original_same_grid_bound s t s z R B c d a C E T N (.andI hs hN)
  have middle : Γ ⊢[PRAAx] distanceBounded (quadrature J s N a C E x)
      (GaussianRationalHorner.qmul (ap2 factorF t u) (quadrature K s N a C E y)) (one+T*H) P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE (GaussianEulerSquareFactorObservation.denominator_positive s t s)) hp
      (by dsimp only [leadingNumerator,leadingDenominator,H,F,P,Q]
          ipra_le (𝔞(unit t)*𝔞(unit s)*(𝔞(kernelBound R E T c)*𝔞(unit s)+(1+𝔞(factorBound z B c d))*𝔞(unit t)))*sl width+
            (𝔞(E)*𝔞(unit s)*𝔞(unit t))*sl pays) finite
  have refined := arbitrary_refinement K t s O a C E LK T y kr hO later
  have refinedRead := distance_congr (.eqRefl _) (GaussianEulerQuadraticKernelCompactName.name_at t z R B c d a C E T).eqSymm (.eqRefl _) (.eqRefl _) refined
  have kernelNear := distance_radius_mono _ _ _ _ (num 3) P (unit_positive (t+num 6)) hp payThree refinedRead
  have third := GaussianNamedDifferenceQuotient.scale_distance (ap2 factorF t u) _ _ F (num 3) P hp
    (GaussianNameBounds.sample_bound factorF u t hfactor) kernelNear
  have fourth := distance_symmetric _ _ _ _ hp (GaussianNameRingLaws.multiply_sample_error factorF KN u v t hfactor hkernel)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalCost,H,F,u,v]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp first (distance_triangle_same _ _ _ _ _ _ hp middle
      (distance_triangle_same _ _ _ _ _ _ hp third fourth)))

/-- Original compact Jacobian equals the literal normalized product of
one original scale factor with the original unfactored kernel integral. -/
theorem original_compact_cross (z R B c d a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent JN factoredF (JData z R B c d a C E T) (factoredData z R B c d a C E T) := by
  refine GaussianNameRingLaws.equivalent_of_envelope JN factoredF _ _ (diagonalCost z R B c d a C E T)
    (GaussianEulerSquareJacobianCompactName.name_regular z R B c d a C E T hs) (factored_regular z R B c d a C E T hs) ?_
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift c) (Syn.shift d) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using hs.shift
  refine .allI ?_
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianEulerSquareJacobianCompactName.subst_data,
    subst_factoredData,subst_diagonalCost,Syn.shift] using
    original_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) ss

theorem factored_to_Jacobian (z R B c d a C E T : PTm n) (hs : Γ ⊢[PRAAx] source z R B c d a C E T) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent factoredF JN (factoredData z R B c d a C E T) (JData z R B c d a C E T) :=
  GaussianNameEquivalence.cross_symm _ _ _ _ (original_compact_cross z R B c d a C E T hs)

theorem actual_original_quadratic_Jacobian_factored_compact_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      GaussianNameEquivalence.crossEquivalent JN factoredF (JData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (factoredData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (original_compact_cross _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareFactorCompact
