import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.FrozenKernels.GaussianBinetFrozenKernelRectangle
import IPRADerivations.Analysis.Stirling.Binet.Kernel.FrequencyGrids.GaussianBinetKernelFrequencyRadius
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Exhaustion.GaussianBinetLaplaceFrequencySuffix

/-!
# Frozen kernel rectangle and the original Laplace suffix

Finite interchange puts the geometric prefix inside each frequency
column. The original damping and mesh weight then give a uniform
comparison with the cofinal kernel on the same retained grid.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetFrozenKernelLaplace

open_ipra
open GaussianBinetFrozenKernelRectangle (matrix column_at)
open GaussianBinetKernelFrequencyGrid (cofinalBody originalData physical_weight)
open GaussianBinetKernelFrozenIndependent (errorDenominator error_denominator_positive)
open GaussianBinetLaplaceOrderedPrefixes (width)
open GaussianBinetLaplaceFrequencySuffix (suffixValue)
open GaussianCoefficientNameBounds (unit)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFiniteSum (sum)
open GaussianRationalFubini (columnSumBody column_sum_at)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rectData" => GaussianBinetFrozenKernelRectangle.data
local notation "rectValue" => GaussianBinetFrozenKernelRectangle.value
local notation "cellError" => GaussianBinetKernelFrequencyRadius.errorNumerator

def errorNumerator (p q I D L : PTm n) : PTm n := (D*L)*cellError p q I

ipra_subst errorNumerator

private theorem column_error (j s p q k I N X Y D sign Ra R L J : PTm n)
    (hAngle : Γ ⊢[PRAAx] source X Y D sign Ra) (hR : Γ ⊢[PRAAx] source X Y D sign R)
    (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le (J+j) N) (hI : Γ ⊢[PRAAx] le one I)
    (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k)) (hp : Γ ⊢[PRAAx] le p (s+N)) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (columnSumBody matrix) j (pairT I (rectData s k N (D*L) J X Y D sign Ra)))
      (inst2 (offB cofinalBody) j (pairT J (originalData q N X Y D sign R (width D L) (width D L))))
      (cellError p q I) (errorDenominator p q I) := by
  let W := D*L
  let C := width D L
  have hw : Γ ⊢[PRAAx] C ≐ W := by dsimp only [C,W,width]; ipra_ring
  have left := (column_sum_at (Γ := Γ) matrix j I (rectData s k N W J X Y D sign Ra)).eqTrans
    (column_at j s k I N W J X Y D sign Ra)
  exact distance_congr left.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianBinetKernelFrequencyRadius.damping_suffix_error j J s p q k I N X Y D sign Ra R C C W
      hAngle hR hN hj hI hk hw hw hp)

/-- Both sums use the full mesh weight. The bound contains the physical
width and the per-column error, with no growth in the angular count. -/
theorem suffix_error (s p q k I N X Y D sign Ra R L J : PTm n)
    (hAngle : Γ ⊢[PRAAx] source X Y D sign Ra) (hR : Γ ⊢[PRAAx] source X Y D sign R)
    (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le J N) (hI : Γ ⊢[PRAAx] le one I)
    (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k)) (hp : Γ ⊢[PRAAx] le p (s+N)) :
    Γ ⊢[PRAAx] distanceBounded (rectValue s k I N (D*L) J X Y D sign Ra)
      (suffixValue q N X Y D sign R L J) (errorNumerator p q I D L) (errorDenominator p q I) := by
  let W := D*L
  let C := width D L
  let M := monus N J
  let A := cellError p q I
  let H := errorDenominator p q I
  let d := rectData s k N W J X Y D sign Ra
  let x := pairT I d
  let y := pairT J (originalData q N X Y D sign R C C)
  let f := columnSumBody matrix
  let g := offB cofinalBody
  have rows : Γ ⊢[PRAAx] termsDistance f g M x y A H := by
    refine .allI (.impI ?_)
    let t (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (t M) :: Γ.map Fm.shift
    have angles : Δ ⊢[PRAAx] source (t X) (t Y) (t D) (t sign) (t Ra) := by
      simpa [Δ,t,Fm.shift,Syn.shift] using hAngle.shift.wk
    have rs : Δ ⊢[PRAAx] source (t X) (t Y) (t D) (t sign) (t R) := by
      simpa [Δ,t,Fm.shift,Syn.shift] using hR.shift.wk
    have ns : Δ ⊢[PRAAx] le one (t N) := by simpa [Δ,t,Fm.shift,Syn.shift] using hN.shift.wk
    have is : Δ ⊢[PRAAx] le one (t I) := by simpa [Δ,t,Fm.shift,Syn.shift] using hI.shift.wk
    have ks : Δ ⊢[PRAAx] le (t I*unit (t p)) (unit (t k)) := by
      simpa [Δ,t,Fm.shift,Syn.shift] using hk.shift.wk
    have ps : Δ ⊢[PRAAx] le (t p) (t s+t N) := by simpa [Δ,t,Fm.shift,Syn.shift] using hp.shift.wk
    have js : Δ ⊢[PRAAx] le (t J) (t N) := by simpa [Δ,t,Fm.shift,Syn.shift] using hJ.shift.wk
    have jlt : Δ ⊢[PRAAx] lt (var 0) (monus (t N) (t J)) := by
      simpa [Δ,t,M,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (t M))
    have jnd : Δ ⊢[PRAAx] le (t J+var 0) (t N) :=
      le_congr (.eqRefl _) (eq_add_of_le js).eqSymm (add_le_add₂ (le_refl (t J)) (le_of_lt jlt))
    simpa only [f,g,d,x,y,A,H,W,C,t,Δ,originalData,width,Syn.shift,subst_pairT,
      GaussianBinetFrozenKernelRectangle.subst_data,GaussianCompactRiemannName.subst_sampleData,
      GaussianBinetKernelFrequencyRadius.subst_errorNumerator,GaussianBinetKernelFrozenIndependent.subst_errorDenominator,
      PTm.subst_add,PTm.subst_mul,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      column_error (var 0) (t s) (t p) (t q) (t k) (t I) (t N) (t X) (t Y) (t D) (t sign) (t Ra) (t R)
        (t L) (t J) angles rs ns jnd is ks ps
  let w := weight W one N
  have hH := error_denominator_positive p q I hI
  have hW := positive_product _ _ (le_refl (Γ := Γ) one) hN
  have diff := sum_distance f g M x y A H hH rows
  have bound := bounded_product w _ W (one*N) (M*A) H hW hH (weight_bound W one N (le_refl one) hN) diff
  have raw := bound_congr (GaussianRationalRoundedPower.multiplication_difference w (sum f M x) (sum g M y)).eqSymm
    (.eqRefl _) (.eqRefl _) bound
  have leN : Γ ⊢[PRAAx] le M N :=
    le_congr (.eqRefl _) (eq_add_of_le hJ).eqSymm (le_add_left M J)
  have compare : Γ ⊢[PRAAx] le ((W*(M*A))*H) ((W*A)*((one*N)*H)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (W*A*H) leN)
  have scaled := distance_radius_mono _ _ _ _ (W*A) H (positive_product _ _ hW hH) hH compare raw
  have interchange : Γ ⊢[PRAAx] GaussianRationalFubini.rowFirst matrix I M d ≐ sum f M x :=
    GaussianRationalFubini.fubini matrix I M d
  have left : Γ ⊢[PRAAx] qmul w (sum f M x) ≐ rectValue s k I N W J X Y D sign Ra :=
    qmul_congr (.eqRefl w) interchange.eqSymm
  have hw : Γ ⊢[PRAAx] C ≐ W := by dsimp only [C,W,width]; ipra_ring
  have right : Γ ⊢[PRAAx] qmul w (sum g M y) ≐ suffixValue q N X Y D sign R L J :=
    qmul_congr (physical_weight N C W hw).eqSymm (.eqRefl (sum g M y))
  exact distance_congr left right (.eqRefl _) (.eqRefl _) scaled

theorem sine_suffix_error (s p q k I N X Y D sign Ra R L E : PTm n)
    (hAngle : Γ ⊢[PRAAx] source X Y D sign Ra) (hR : Γ ⊢[PRAAx] source X Y D sign R)
    (hN : Γ ⊢[PRAAx] le one N) (hL : Γ ⊢[PRAAx] le one L) (hE : Γ ⊢[PRAAx] le one E)
    (hI : Γ ⊢[PRAAx] le one I) (hk : Γ ⊢[PRAAx] le (I*unit p) (unit k)) (hp : Γ ⊢[PRAAx] le p (s+N)) :
    let J := GaussianBinetSineStripCut.cutoff N (D*L) E
    Γ ⊢[PRAAx] distanceBounded (rectValue s k I N (D*L) J X Y D sign Ra)
      (suffixValue q N X Y D sign R L J) (errorNumerator p q I D L) (errorDenominator p q I) :=
  suffix_error s p q k I N X Y D sign Ra R L _ hAngle hR hN
    (GaussianBinetSineStripCut.prefix_admission N (D*L) E (positive_product _ _ hR.andE₁.andE₂ hL) hE).andE₁
    hI hk hp

end LeanProofs.IPRA.Analysis.GaussianBinetFrozenKernelLaplace
