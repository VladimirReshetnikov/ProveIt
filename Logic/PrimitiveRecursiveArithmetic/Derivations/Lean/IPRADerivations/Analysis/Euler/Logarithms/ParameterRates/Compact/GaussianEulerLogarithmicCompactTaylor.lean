import IPRADerivations.Analysis.Euler.Logarithms.ParameterRates.Compact.GaussianEulerLogarithmicTaylorGrid
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Euler.Logarithms.Compact.GaussianEulerLogarithmicIntervalName
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedAffineRemainderRate

/-!
# Taylor error for the original logarithmic compact integral names

The three original compact programs keep their own computed meshes and
the same physical interval. Their actual common product mesh and the
original evaluator precision lift the pointwise parameter remainder.
This is a fixed-interval estimate; no improper limit is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCompactTaylor

open_ipra
open GaussianEulerLogarithmicTaylorGrid (source perturbedClient baseClient linearClient rowNumerator rowDenominator)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianEulerLogarithmicParameterIncrement (curvature)
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData)
open GaussianEulerLogarithmicIntervalName (nameF data name_at name_regular compact_input)
open GaussianEulerLogarithmicMultiplier (lipschitz)
open GaussianCompactRiemannName (mesh precision quadrature)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalHorner (ofGaussian qadd qmul positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def point (p j z R B a C E T : PTm n) : PTm n := ap2 nameF p (data j z R B a C E T)
def actualLinear (q r j z R B a C E T h D : PTm n) : PTm n :=
  qadd (point q j z R B a C E T) (qmul (ofGaussian h D) (point r (succ j) z R B a C E T))
def commonMesh (p j R E T : PTm n) : PTm n :=
  mesh p (lipschitz j (R+one) E T) T*mesh p (lipschitz j R E T) T*mesh p (lipschitz (succ j) R E T) T
def quadraticNumerator (j R C E T X : PTm n) : PTm n := C*curvature j R E T*X*X
def quadraticDenominator (E Y : PTm n) : PTm n := E*(Y*Y)
def diagonalNumerator (p j R C E T X Y : PTm n) : PTm n :=
  quadraticNumerator j R C E T X*unit (p+num 6)+num 12*quadraticDenominator E Y
def diagonalDenominator (p E Y : PTm n) : PTm n := quadraticDenominator E Y*unit (p+num 6)

ipra_subst point
ipra_subst actualLinear

theorem parameter_source (z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicParameterIncrement.source z R B E T a E h D X Y := by
  have ha := hs.andE₁.andE₂.andE₁
  have he := hs.andE₁.andE₁.andE₂.andE₁
  have lower : Γ ⊢[PRAAx] le E (E*a) :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right E ha)
  have upper : Γ ⊢[PRAAx] le a (T*E) :=
    le_congr (.eqRefl _) (mul_comm _ _) (le_trans (le_add_right a C) hs.andE₁.andE₂.andE₂)
  exact .andI (.andI hs.andE₁.andE₁ (.andI (.andI ha he) (.andI lower upper))) hs.andE₂

theorem parameter_bound (z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx] bounded (ofGaussian h D) one one :=
  GaussianEulerParameterIncrementObservation.parameter_unit_bound z R B E T a E h D X Y
    (parameter_source z R B a C E T h D X Y hs)

theorem shifted_source (z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.intervalSource (shifted z B h D) (R+one) (B*D) a C E T :=
  .andI (.andI (positive_product _ _ hs.andE₁.andE₁.andE₁ hs.andE₂.andE₁)
    (.andI hs.andE₁.andE₁.andE₂.andE₁
      (GaussianEulerLogarithmicParameterTaylor.shifted_disk z R B E T a E h D X Y
        (parameter_source z R B a C E T h D X Y hs)))) hs.andE₁.andE₂

theorem common_mesh_positive (p j R E T : PTm n) : Γ ⊢[PRAAx] le one (commonMesh p j R E T) :=
  positive_product _ _ (positive_product _ _ (GaussianCompactRiemannName.mesh_positive _ _ _)
    (GaussianCompactRiemannName.mesh_positive _ _ _)) (GaussianCompactRiemannName.mesh_positive _ _ _)

theorem common_refinement (p j R a C E T L x : PTm n)
    (hi : Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF a C E L T x)
    (factor : PTm n) (hf : Γ ⊢[PRAAx] le one factor)
    (heq : Γ ⊢[PRAAx] factor*mesh p L T ≐ commonMesh p j R E T) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF (precision p T) (commonMesh p j R E T) a C E x)
      (GaussianCompactRiemannName.sample evaluatorF p a C E L T x) (num 3) (unit (p+num 6)) :=
  distance_congr (GaussianCompactRiemannName.quadrature_index_congr evaluatorF _ _ _ a C E x heq)
    (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF p (precision p T) factor a C E L T x hi hf (le_refl _))

theorem perturbed_refinement (p j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF (precision p T) (commonMesh p j R E T) a C E (perturbedClient j z R B E T h D))
      (point p j (shifted z B h D) (R+one) (B*D) a C E T) (num 3) (unit (p+num 6)) :=
  distance_congr (.eqRefl _) (name_at p j (shifted z B h D) (R+one) (B*D) a C E T).eqSymm (.eqRefl _) (.eqRefl _)
    (common_refinement p j R a C E T _ _
      (compact_input j _ _ _ _ _ _ _ (shifted_source z R B a C E T h D X Y hs))
      (mesh p (lipschitz j R E T) T*mesh p (lipschitz (succ j) R E T) T)
      (positive_product _ _ (GaussianCompactRiemannName.mesh_positive _ _ _) (GaussianCompactRiemannName.mesh_positive _ _ _))
      (by unfold commonMesh; ipra_ring))

theorem sampling_budget (C E Y K U V : PTm n) (h : Γ ⊢[PRAAx] le (C*U) (E*V)) : Γ ⊢[PRAAx]
    le ((C*(K*V+num 3*(Y*Y)))*(E*(Y*Y)*U))
      ((C*K*U+num 3*(E*(Y*Y)))*(E*((Y*Y)*V))) := by
  ipra_le 3*𝔞 E*𝔞 Y*𝔞 Y*𝔞 Y*𝔞 Y*sl h

theorem base_refinement (p j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF (precision p T) (commonMesh p j R E T) a C E (baseClient j z R B E T))
      (point p j z R B a C E T) (num 3) (unit (p+num 6)) :=
  distance_congr (.eqRefl _) (name_at p j z R B a C E T).eqSymm (.eqRefl _) (.eqRefl _)
    (common_refinement p j R a C E T _ _ (compact_input j _ _ _ _ _ _ _ hs.andE₁)
      (mesh p (lipschitz j (R+one) E T) T*mesh p (lipschitz (succ j) R E T) T)
      (positive_product _ _ (GaussianCompactRiemannName.mesh_positive _ _ _) (GaussianCompactRiemannName.mesh_positive _ _ _))
      (by unfold commonMesh; ipra_ring))

theorem linear_refinement (p j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (quadrature evaluatorF (precision p T) (commonMesh p j R E T) a C E (linearClient j z R B E T))
      (point p (succ j) z R B a C E T) (num 3) (unit (p+num 6)) :=
  distance_congr (.eqRefl _) (name_at p (succ j) z R B a C E T).eqSymm (.eqRefl _) (.eqRefl _)
    (common_refinement p j R a C E T _ _ (compact_input (succ j) _ _ _ _ _ _ _ hs.andE₁)
      (mesh p (lipschitz j (R+one) E T) T*mesh p (lipschitz j R E T) T)
      (positive_product _ _ (GaussianCompactRiemannName.mesh_positive _ _ _) (GaussianCompactRiemannName.mesh_positive _ _ _))
      (.eqRefl _))

theorem original_diagonal (p j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (point p j (shifted z B h D) (R+one) (B*D) a C E T)
      (actualLinear p p j z R B a C E T h D)
      (diagonalNumerator p j R C E T X Y) (diagonalDenominator p E Y) := by
  let U := unit (p+num 6)
  let V := unit (precision p T)
  let Q := quadraticDenominator E Y
  let DD := Q*U
  have hu := unit_positive (Γ := Γ) (p+num 6)
  have hv := unit_positive (Γ := Γ) (precision p T)
  have yy := positive_product _ _ hs.andE₂.andE₂.andE₁ hs.andE₂.andE₂.andE₁
  have he := hs.andE₁.andE₁.andE₂.andE₁
  have hq : Γ ⊢[PRAAx] le one Q := positive_product _ _ he yy
  have hd : Γ ⊢[PRAAx] le one DD := positive_product _ _ hq hu
  have first := distance_radius_mono _ _ _ _ (num 3*Q) DD hu hd
    (le_of_eq_add (d := zero) (by dsimp only [DD,Q]; ipra_ring))
    (distance_symmetric _ _ _ _ hu (perturbed_refinement p j z R B a C E T h D X Y hs))
  have actual := GaussianEulerLogarithmicTaylorGrid.original_grid_bound (precision p T) (commonMesh p j R E T)
    j z R B a C E T h D X Y hs (common_mesh_positive p j R E T)
  have width := le_trans (le_add_left C a) hs.andE₁.andE₂.andE₂
  have budget : Γ ⊢[PRAAx] le (C*U) (E*V) := by
    have prec := GaussianCompactRiemannName.precision_lower (Γ := Γ) p T
    ipra_le 𝔞 U*sl width+𝔞 E*sl prec
  have oldDen : Γ ⊢[PRAAx] le one (E*rowDenominator (precision p T) Y) :=
    positive_product _ _ he (positive_product _ _ yy hv)
  have middleBudget : Γ ⊢[PRAAx]
      le ((C*rowNumerator (precision p T) j R E T X Y)*DD)
        ((quadraticNumerator j R C E T X*U+num 3*Q)*(E*rowDenominator (precision p T) Y)) :=
    le_congr (by dsimp only [rowNumerator,rowDenominator,quadraticNumerator,quadraticDenominator,DD,Q]; ipra_ring)
      (by dsimp only [rowNumerator,rowDenominator,quadraticNumerator,quadraticDenominator,DD,Q]; ipra_ring)
      (sampling_budget C E Y (curvature j R E T*X*X) U V budget)
  have middle := distance_radius_mono _ _ (C*rowNumerator (precision p T) j R E T X Y)
    (E*rowDenominator (precision p T) Y) (quadraticNumerator j R C E T X*U+num 3*Q) DD oldDen hd middleBudget actual
  have product := GaussianApproximateInverseDistance.multiply_distance _ _ _ one _ _ hu
    (parameter_bound z R B a C E T h D X Y hs) (linear_refinement p j z R B a C E T h D X Y hs)
  have rawRight : Γ ⊢[PRAAx] distanceBounded
      (qadd (quadrature evaluatorF (precision p T) (commonMesh p j R E T) a C E (baseClient j z R B E T))
        (qmul (ofGaussian h D) (quadrature evaluatorF (precision p T) (commonMesh p j R E T) a C E (linearClient j z R B E T))))
      (actualLinear p p j z R B a C E T h D) (num 6) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNameArithmetic.sum_distance _ _ _ _ (num 3) (one*num 3) U hu
        (base_refinement p j z R B a C E T h D X Y hs) product)
  have right := distance_radius_mono _ _ (num 6) U (num 6*Q) DD hu hd
    (le_of_eq_add (d := zero) (by dsimp only [DD,Q]; ipra_ring))
    rawRight
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalNumerator,DD,Q]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd first (distance_triangle_same _ _ _ _ _ _ hd middle right))

theorem quadratic_denominator_positive (E Y : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hY : Γ ⊢[PRAAx] le one Y) : Γ ⊢[PRAAx]
    le one (quadraticDenominator E Y) := positive_product _ _ hE (positive_product _ _ hY hY)

theorem diagonal_envelope (j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    GaussianNamedAffineRemainderRate.diagonalEnvelope nameF nameF nameF
      (data j (shifted z B h D) (R+one) (B*D) a C E T)
      (data j z R B a C E T) (data (succ j) z R B a C E T) (ofGaussian h D)
      (quadraticNumerator j R C E T X) (quadraticDenominator E Y) (num 12) := by
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a)
      (Syn.shift C) (Syn.shift E) (Syn.shift T) (Syn.shift h) (Syn.shift D) (Syn.shift X) (Syn.shift Y) :=
    by simpa only [Fm.shift,Syn.shift,GaussianEulerLogarithmicTaylorGrid.subst_source] using hs.shift
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  let Q := quadraticDenominator (sh E) (sh Y)
  let A := quadraticNumerator (sh j) (sh R) (sh C) (sh E) (sh T) (sh X)
  have hQ : Γ.map Fm.shift ⊢[PRAAx] le one Q := quadratic_denominator_positive _ _ ss.andE₁.andE₁.andE₂.andE₁ ss.andE₂.andE₂.andE₁
  have old := original_diagonal (var 0) (sh j) (sh z) (sh R) (sh B) (sh a) (sh C) (sh E) (sh T) (sh h) (sh D) (sh X) (sh Y) ss
  have increase := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ.map Fm.shift) (var 0) (var 0+num 6) (le_add_right _ _)
  have native : Γ.map Fm.shift ⊢[PRAAx]
      le ((A*unit (var 0+num 6)+num 12*Q)*(Q*unit (var 0)))
        ((A*unit (var 0)+num 12*Q)*(Q*unit (var 0+num 6))) := by
    ipra_le 12*Groth.ι (IPRA.Q.mk (Γ.map Fm.shift) Q)*Groth.ι (IPRA.Q.mk (Γ.map Fm.shift) Q)*sl increase
  have converted := distance_radius_mono _ _ _ _ (A*unit (var 0)+num 12*Q) (Q*unit (var 0))
    (positive_product _ _ hQ (unit_positive _)) (positive_product _ _ hQ (unit_positive _)) native old
  simpa only [GaussianNamedAffineRemainderRate.diagonalEnvelope,GaussianNamedAffineRemainderRate.affine,
    GaussianNamedLipschitzRate.diagonalNumerator,GaussianNamedLipschitzRate.diagonalDenominator,
    GaussianEulerLogarithmicIntervalName.subst_data,GaussianEulerParameterExponentialIncrement.subst_shifted,
    GaussianRationalHorner.subst_ofGaussian,PTm.subst_add,PTm.subst_mul,PTm.subst_num,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,point,actualLinear,quadraticNumerator,quadraticDenominator,
    GaussianEulerLogarithmicParameterIncrement.subst_curvature,Syn.shift,sh,A,Q] using converted

def numerator (p q r j R C E T X Y : PTm n) : PTm n :=
  GaussianNamedAffineRemainderRate.numerator (quadraticNumerator j R C E T X) (quadraticDenominator E Y) p q r
def denominator (p q r E Y : PTm n) : PTm n := GaussianNamedAffineRemainderRate.denominator (quadraticDenominator E Y) p q r

/-- The three actual original compact observations are independent;
the only non-observation error is the integrated quadratic remainder. -/
theorem original_observations (p q r j z R B a C E T h D X Y : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C E T h D X Y) : Γ ⊢[PRAAx]
    distanceBounded (point p j (shifted z B h D) (R+one) (B*D) a C E T)
      (actualLinear q r j z R B a C E T h D) (numerator p q r j R C E T X Y) (denominator p q r E Y) :=
  GaussianNamedAffineRemainderRate.independent_at nameF nameF nameF
    (data j (shifted z B h D) (R+one) (B*D) a C E T) (data j z R B a C E T)
    (data (succ j) z R B a C E T) (ofGaussian h D) (quadraticNumerator j R C E T X) (quadraticDenominator E Y)
    (num 12) p q r (quadratic_denominator_positive E Y hs.andE₁.andE₁.andE₂.andE₁ hs.andE₂.andE₂.andE₁)
    (parameter_bound z R B a C E T h D X Y hs)
    (name_regular _ _ _ _ _ _ _ _ (shifted_source z R B a C E T h D X Y hs))
    (name_regular _ _ _ _ _ _ _ _ hs.andE₁) (name_regular _ _ _ _ _ _ _ _ hs.andE₁)
    (diagonal_envelope j z R B a C E T h D X Y hs)

theorem actual_original_compact_logarithmic_parameter_Taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 15
    (source (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) ⟶
      distanceBounded (point (var 0) (var 3) (shifted (var 4) (var 6) (var 11) (var 12))
        (var 5+one) (var 6*var 12) (var 7) (var 8) (var 9) (var 10))
        (actualLinear (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12))
        (numerator (var 0) (var 1) (var 2) (var 3) (var 5) (var 8) (var 9) (var 10) (var 13) (var 14))
        (denominator (var 0) (var 1) (var 2) (var 9) (var 14))) :=
  closeUniv 15 (.impI (original_observations _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCompactTaylor
