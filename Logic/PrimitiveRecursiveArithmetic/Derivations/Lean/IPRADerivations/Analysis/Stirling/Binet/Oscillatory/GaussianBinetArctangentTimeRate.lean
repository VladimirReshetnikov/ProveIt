import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetArctangentQuadratureBound
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripCutoff
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant

/-!
# Time variation of the original arctangent quadrature

Compare same-count grids at corresponding unit tags. The original
quadrature is its width times the unit-weighted resolvent sum. A
common refinement compares the actual cofinal meshes while retaining
the tag and width variation bounds.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentTimeRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (nameF data evaluatorF fixedData evaluator_at)
open GaussianBinetLaplaceStrip (tagNumerator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (grid sampleBody sampleData sample_body_at quadrature precision mesh mesh_positive)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRiemannRefinement (leftSum termsDistance constantBody constant_entry)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open GaussianRightHalfPlaneLogarithm (source)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def gain (D T : PTm n) : PTm n := D+T*(D*D)
def gridData (p M X Y D sign A B : PTm n) : PTm n :=
  sampleData p M (B+zero) A B (fixedData X Y D sign)
def average (p M X Y D sign A B : PTm n) : PTm n :=
  leftSum (sampleBody evaluatorF) M (gridData p M X Y D sign A B) one one

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (D T : PTm n) :
    Syn.subst σ (gain D T) = gain (Syn.subst σ D) (Syn.subst σ T) := by simp [gain]
@[simp] theorem subst_gridData {m : ℕ} (σ : Fin n → PTm m) (p M X Y D sign A B : PTm n) :
    Syn.subst σ (gridData p M X Y D sign A B) = gridData (Syn.subst σ p) (Syn.subst σ M) (Syn.subst σ X)
      (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B) := by simp [gridData]

private theorem factor (p M X Y D sign A B : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] quadrature evaluatorF p M (B+zero) A B (fixedData X Y D sign) ≐
      qmul (fraction A B) (average p M X Y D sign A B) := by
  let w := GaussianRationalRiemannRefinement.weight one one M
  let s := GaussianRationalFiniteSum.sum (sampleBody evaluatorF) M (gridData p M X Y D sign A B)
  have ew : Γ ⊢[PRAAx] w ≐ fraction one M :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl _) (one_mul M)
  have ew' : Γ ⊢[PRAAx] qmul (fraction A B) w ≐ GaussianRationalRiemannRefinement.weight A B M :=
    (qmul_congr (.eqRefl _) ew).eqTrans ((GaussianEulerDampedTimeRate.fraction_product A B one M hB hM).eqTrans
      (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (.eqRefl _)))
  exact ((GaussianReciprocalHorner.qmul_associative (fraction A B) w s).eqSymm.eqTrans
    (qmul_congr ew' (.eqRefl s))).eqSymm

private theorem row_at (i p M X Y D sign A B : PTm n) :
    Γ ⊢[PRAAx] inst2 (sampleBody evaluatorF) i (gridData p M X Y D sign A B) ≐
      GaussianBinetArctangentResolvent.value X Y D sign (tagNumerator (grid i M (B+zero) A B)) (sndT (grid i M (B+zero) A B)) :=
  (sample_body_at evaluatorF i p M (B+zero) A B (fixedData X Y D sign)).eqTrans
    (evaluator_at p (grid i M (B+zero) A B) X Y D sign)

private theorem tag_fraction (i M A B : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] fraction (tagNumerator (grid i M (B+zero) A B)) (sndT (grid i M (B+zero) A B)) ≐
      qmul (fraction i M) (fraction A B) := by
  have e := GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Γ) i M zero A B
  have n := e.andE₁.eqTrans (by ipra_ring : Γ ⊢[PRAAx] zero*M+A*i ≐ i*A)
  exact (GaussianCompactRiemannName.fraction_congr _ _ _ _ n (e.andE₂.eqTrans (mul_comm B M))).eqTrans
    (GaussianEulerDampedTimeRate.fraction_product i M A B hM hB).eqSymm

private theorem tag_denominator (i M A B : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (sndT (grid i M (B+zero) A B)) :=
  le_congr (.eqRefl _) (GaussianBinetLaplaceStripCutoff.grid_tag (Γ := Γ) i M zero A B).andE₂.eqSymm (positive_product _ _ hB hM)

private theorem row_distance (i p q M X Y D sign A B C E H Q : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hM : Γ ⊢[PRAAx] le one M) (hi : Γ ⊢[PRAAx] le i M)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction A B) (fraction C E) H Q) :
    Γ ⊢[PRAAx] distanceBounded (inst2 (sampleBody evaluatorF) i (gridData p M X Y D sign A B))
      (inst2 (sampleBody evaluatorF) i (gridData q M X Y D sign C E)) (D*D*H) Q := by
  let t := grid i M (B+zero) A B
  let u := grid i M (E+zero) C E
  have x := tag_denominator i M A B hM hB
  have y := tag_denominator i M C E hM hE
  have iBd := GaussianEulerExponentCompactBounds.fraction_bound i M one hM (le_congr (.eqRefl _) (one_mul M).eqSymm hi)
  have near := GaussianRationalRoundedPower.multiply_distance_bound (fraction i M) _ _ H Q hQ iBd h
  have cells := GaussianBinetArctangentResolventRate.time_distance X Y D sign (tagNumerator t) (sndT t) (tagNumerator u) (sndT u)
    H Q hz x y hQ (distance_congr (tag_fraction i M A B hM hB).eqSymm (tag_fraction i M C E hM hE).eqSymm
      (.eqRefl _) (.eqRefl _) near)
  have hX := hz.andE₁.andE₁
  have hX2 := positive_product _ _ hX hX
  have widened := distance_radius_mono _ _ _ _ (D*D*H) Q (positive_product _ _ hX2 hQ) hQ
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (D*D*H*Q) hX2)) cells
  exact distance_congr (row_at i p M X Y D sign A B).eqSymm (row_at i q M X Y D sign C E).eqSymm
    (.eqRefl _) (.eqRefl _) widened

theorem average_bound (p M X Y D sign A B : PTm n) (hz : Γ ⊢[PRAAx] source X D sign)
    (hM : Γ ⊢[PRAAx] le one M) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (average p M X Y D sign A B) D one := by
  let f := sampleBody evaluatorF
  let d := gridData p M X Y D sign A B
  have rows : Γ ⊢[PRAAx] termsDistance f constantBody M d qzero D one := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    let t := grid (var 0) (s M) (s B+zero) (s A) (s B)
    have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) :=
      by simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hM.shift.wk
    have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift.wk
    have x := tag_denominator (var 0) (s M) (s A) (s B) ms bs
    have b := GaussianBinetArctangentResolventRate.uniform_bound (s X) (s Y) (s D) (s sign) (tagNumerator t) (sndT t) zs x
    have widened := GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ (s D) one zs.andE₁.andE₁ (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (s D) zs.andE₁.andE₁)) b
    rw [constant_entry]
    simpa only [f,d,Δ,s,Syn.shift,subst_gridData,GaussianRationalHorner.subst_qzero,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      (GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_refl one)).iffMpr
        (GaussianRationalReciprocal.bound_congr (row_at (var 0) (s p) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B)).eqSymm
          (.eqRefl _) (.eqRefl _) widened)
  have zeroSum : Γ ⊢[PRAAx] GaussianRationalFiniteSum.sum constantBody M qzero ≐ qzero :=
    (GaussianRationalRiemannRefinement.constant_sum qzero M).eqTrans (GaussianRationalFactorialEulerSums.scale_zero_value M)
  have zeroAvg : Γ ⊢[PRAAx] leftSum constantBody M qzero one one ≐ qzero :=
    (qmul_congr (.eqRefl _) zeroSum).eqTrans (qmul_zero_right _)
  have close := GaussianCompactScalarMajorant.common_mesh_distance f constantBody M d qzero one one D one
    hM (le_refl one) (le_refl one) rows
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_refl one)).iffMp
    (distance_congr (.eqRefl _) zeroAvg (one_mul D) (one_mul one) close)

theorem quadrature_rate (p q M X Y D sign A B C E T H Q : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hM : Γ ⊢[PRAAx] le one M)
    (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) (hc : Γ ⊢[PRAAx] le C (T*E))
    (hQ : Γ ⊢[PRAAx] le one Q) (h : Γ ⊢[PRAAx] distanceBounded (fraction A B) (fraction C E) H Q) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p M (B+zero) A B (fixedData X Y D sign))
      (quadrature evaluatorF q M (E+zero) C E (fixedData X Y D sign)) (gain D T*H) Q := by
  let f := sampleBody evaluatorF
  let x := gridData p M X Y D sign A B
  let y := gridData q M X Y D sign C E
  have rows : Γ ⊢[PRAAx] termsDistance f f M x y (D*D*H) Q := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) :=
      by simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hM.shift.wk
    have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift.wk
    have es : Δ ⊢[PRAAx] le one (s E) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hE.shift.wk
    have ds : Δ ⊢[PRAAx] le one (s Q) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hQ.shift.wk
    have near : Δ ⊢[PRAAx] distanceBounded (fraction (s A) (s B)) (fraction (s C) (s E)) (s H) (s Q) :=
      by simpa [Δ,s,Fm.shift,Syn.shift] using h.shift.wk
    simpa only [f,x,y,Δ,s,Syn.shift,subst_gridData,PTm.subst_mul] using
      row_distance (var 0) (s p) (s q) (s M) (s X) (s Y) (s D) (s sign) (s A) (s B) (s C) (s E)
        (s H) (s Q) zs ms (le_of_lt Prf.hyp0) bs es ds near
  have midd := GaussianCompactScalarMajorant.common_mesh_distance f f M x y one one (D*D*H) Q
    hM (le_refl one) hQ rows
  have av := distance_congr (.eqRefl _) (.eqRefl _) (one_mul (D*D*H)) (one_mul Q) midd
  have bd := average_bound p M X Y D sign A B hz hM hB
  have cf := GaussianEulerExponentCompactBounds.fraction_bound C E T hE hc
  exact distance_congr (factor p M X Y D sign A B hM hB).eqSymm (factor q M X Y D sign C E hM hE).eqSymm
    (by unfold gain; ipra_ring) (.eqRefl _) (GaussianNameArithmetic.product_distance _ _ _ _ H _ Q D T hQ h av bd cf)

private theorem diagonal_error (p X Y D sign A B C E T H Q : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] le C (T*E)) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction A B) (fraction C E) H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign A B)) (ap2 nameF p (data X Y D sign C E))
      (diagonalNumerator (gain D T*H) Q two p) (diagonalDenominator Q p) := by
  let F := evaluatorF
  let L := D*D
  let x := fixedData X Y D sign
  let M := mesh p L A
  let N := mesh p L C
  let r := precision p A+precision p C
  let U := unit p
  let V := unit (p+num 6)
  let Z := Q*U
  have m := mesh_positive (Γ := Γ) p L A
  have n' := mesh_positive (Γ := Γ) p L C
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) (p+num 6)
  have hZ := positive_product _ _ hQ hU
  have grow := GaussianCompactRiemannName.dyadic_six_lower (Γ := Γ) p
  have left := GaussianCompactMeshIndependence.arbitrary_refinement F p r N (B+zero) A B L A x
    (GaussianBinetArctangentQuadrature.compact_input X Y D sign A B hz hB) n' (le_add_right _ _)
  have right := GaussianCompactMeshIndependence.arbitrary_refinement F p r M (E+zero) C E L C x
    (GaussianBinetArctangentQuadrature.compact_input X Y D sign C E hz hE) m (le_add_left _ _)
  have left' := distance_congr (GaussianCompactRiemannName.quadrature_index_congr F r (N*M) (M*N) (B+zero) A B x (mul_comm N M))
    (GaussianCompactRiemannName.name_at F p (B+zero) A B L A x).eqSymm (.eqRefl _) (.eqRefl _) left
  have right' := distance_congr (.eqRefl _) (GaussianCompactRiemannName.name_at F p (E+zero) C E L C x).eqSymm (.eqRefl _) (.eqRefl _) right
  have ha := distance_radius_mono _ _ _ _ Q Z hV hZ (by dsimp only [Z,U,V]; ipra_le 𝔞(Q)*sl grow)
    (distance_symmetric _ _ _ _ hV left')
  have hb := distance_radius_mono _ _ _ _ Q Z hV hZ (by dsimp only [Z,U,V]; ipra_le 𝔞(Q)*sl grow) right'
  have raw := quadrature_rate r r (M*N) X Y D sign A B C E T H Q hz (positive_product _ _ m n') hB hE hc hQ h
  have mid := distance_radius_mono _ _ _ _ (gain D T*H*U) Z hQ hZ
    (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) raw
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold diagonalNumerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hZ (distance_triangle_same _ _ _ _ _ _ hZ ha mid) hb)

theorem independent_rate (X Y D sign A B C E T H Q : PTm n)
    (hz : Γ ⊢[PRAAx] source X D sign) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (hc : Γ ⊢[PRAAx] le C (T*E)) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction A B) (fraction C E) H Q) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data X Y D sign A B) (data X Y D sign C E) (gain D T*H) Q := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two hQ
    (GaussianBinetArctangentQuadrature.regular X Y D sign A B hz hB)
    (GaussianBinetArctangentQuadrature.regular X Y D sign C E hz hE)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have zs : Δ ⊢[PRAAx] source (s X) (s D) (s sign) :=
    by simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using hz.shift
  have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift
  have es : Δ ⊢[PRAAx] le one (s E) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hE.shift
  have cs : Δ ⊢[PRAAx] le (s C) (s T*s E) := by simpa [Δ,s,Fm.shift,Syn.shift] using hc.shift
  have qs : Δ ⊢[PRAAx] le one (s Q) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hQ.shift
  have near : Δ ⊢[PRAAx] distanceBounded (fraction (s A) (s B)) (fraction (s C) (s E)) (s H) (s Q) :=
    by simpa [Δ,s,Fm.shift,Syn.shift] using h.shift
  simpa only [diagonalEnvelope,Δ,s,Syn.shift,GaussianBinetArctangentQuadrature.subst_data,subst_gain,PTm.subst_mul,two,one,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using diagonal_error (var 0) (s X) (s Y) (s D) (s sign) (s A) (s B)
      (s C) (s E) (s T) (s H) (s Q) zs bs es cs qs near

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentTimeRate
