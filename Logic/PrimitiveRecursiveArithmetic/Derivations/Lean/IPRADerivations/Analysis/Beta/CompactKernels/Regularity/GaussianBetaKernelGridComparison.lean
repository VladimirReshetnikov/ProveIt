import IPRADerivations.Analysis.Beta.CompactKernels.Factors.GaussianBetaKernelExponential
import IPRADerivations.Analysis.Euler.CompactExhaustion.ParameterBounds.GaussianEulerCompactProductComparison
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianCompactScalarMajorant
import IPRADerivations.Analysis.Euler.CompactExhaustion.Names.GaussianEulerImproperName

/-!
# The original compact Euler grid with the finite beta kernel

At each row, preserve the original power query and replace the decay
factor with the literal finite beta kernel. On the same grid the
difference is bounded by the interval width times a uniform bound
on the row errors. The compact time bound T must satisfy 2T <= N;
the number of cells is independent of the beta degree. The fixed-cutoff
comparison lets the observation precision grow on a single interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelGridComparison

open_ipra
open GaussianBetaKernelExponential (kernel coefficient errorNumerator errorDenominator)
open GaussianEulerCompactProductComparison (clock replacement replacement_error)
open GaussianEulerCompactPowerMajorant (majorant)
open GaussianEulerExponentCompactBounds (source)
open GaussianCompactLogarithmBounds (domain)
open GaussianEulerIntegrandName (fixedData sample_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody sampleData sample_body_at quadrature)
open GaussianRationalRiemannRefinement (termsDistance)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianEulerVaryingCutoffName (cells evaluationPrecision)
open GaussianGammaEulerCompactQuadrature (conservativeCells)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def sampleDataBeta (z B N : PTm n) : PTm n := pairT (fixedData z B) N
def betaTerm (p t x : PTm n) : PTm n :=
  replacement p (fstT (fstT x)) (sndT (fstT x)) (fstT t) (sndT t) (kernel (fstT t) (sndT t) (sndT x))
def evaluatorF : PR 3 := PTm.toPR (betaTerm (var 0) (var 1) (var 2))
def row (p z B a b N : PTm n) : PTm n := replacement p z B a b (kernel a b N)

ipra_subst sampleDataBeta [fixedData]
ipra_subst row [kernel, GaussianBetaKernelExponential.base]
ipra_subst betaTerm [kernel, GaussianBetaKernelExponential.base]

theorem row_at (p z B a b N : PTm n) : Γ ⊢[PRAAx]
    ap3 evaluatorF p (pairT a b) (sampleDataBeta z B N) ≐ row p z B a b N := by
  let x := sampleDataBeta z B N
  let t := pairT a b
  have program : Γ ⊢[PRAAx] ap3 evaluatorF p t x ≐ betaTerm p t x := by
    simpa [evaluatorF,ap3] using toPR_eq (Γ := Γ) (betaTerm (var 0) (var 1) (var 2) : PTm 3) ![p,t,x]
  have zarg : Γ ⊢[PRAAx] fstT (fstT x) ≐ z :=
    (congrFst (fst_pair (fixedData z B) N)).eqTrans (fst_pair z B)
  have barg : Γ ⊢[PRAAx] sndT (fstT x) ≐ B :=
    (congrSnd (fst_pair (fixedData z B) N)).eqTrans (snd_pair z B)
  have lastInput : ![p,fstT (fstT x),sndT (fstT x),fstT t,sndT t,sndT x] (5 : Fin 6) = sndT x := rfl
  have lastOutput : ![p,z,B,a,b,N] (5 : Fin 6) = N := rfl
  apply program.eqTrans
  change Γ ⊢[PRAAx] row p (fstT (fstT x)) (sndT (fstT x)) (fstT t) (sndT t) (sndT x) ≐ row p z B a b N
  simpa only [subst_row,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,lastInput,lastOutput] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (row (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![p,fstT (fstT x),sndT (fstT x),fstT t,sndT t,sndT x])
      (σ' := ![p,z,B,a,b,N]) (fun i => by
        fin_cases i
        · exact .eqRefl p
        · exact zarg
        · exact barg
        · exact fst_pair a b
        · exact snd_pair a b
        · exact snd_pair (fixedData z B) N)

theorem grid_domain (i M C E T : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E)
    (hi : Γ ⊢[PRAAx] le i M) (hT : Γ ⊢[PRAAx] le (one+C) (E*T)) :
    Γ ⊢[PRAAx] domain (M+C*i) (E*M) E T := by
  have timePositive := le_trans hM (le_add_right M (C*i))
  have denominator := positive_product _ _ hE hM
  have left : Γ ⊢[PRAAx] le (E*M) (E*(M+C*i)) :=
    le_of_eq_add (d := E*C*i) (by ipra_ring)
  have rowRight : Γ ⊢[PRAAx] le (M+C*i) (M+C*M) :=
    add_le_add₂ (le_refl M) (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl C) hi)
  have right : Γ ⊢[PRAAx] le (M+C*M) (T*(E*M)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right M hT)
  exact .andI (.andI timePositive denominator) (.andI left (le_trans rowRight right))

def rowNumerator (p R E T N : PTm n) : PTm n :=
  majorant R E T*coefficient T*T*T*unit p+(majorant R E T+two)*N

ipra_subst rowNumerator [majorant, GaussianEulerCompactPowerMajorant.exponentRadius, coefficient, GaussianRadiusExponentialLipschitzRate.factor, GaussianBetaKernelLogarithm.radius]

theorem row_error (p z R B E T a b N : PTm n) (hz : Γ ⊢[PRAAx] source z R B E)
    (ht : Γ ⊢[PRAAx] domain a b E T) (hN : Γ ⊢[PRAAx] le one N) (hT : Γ ⊢[PRAAx] le (two*T) N) :
    Γ ⊢[PRAAx] distanceBounded (row p z B a b N) (GaussianEulerIntegrandName.sample p z B a b)
      (rowNumerator p R E T N) (N*unit p) := by
  let k := clock p z B a b
  let P := unit p
  let Q := unit k
  let H := coefficient T
  let A := H*T*T*P+N
  let D := N*P
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hq : Γ ⊢[PRAAx] le one Q := unit_positive k
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ hN hp
  have hb : Γ ⊢[PRAAx] le one b := ht.andE₁.andE₂
  have twiceTime : Γ ⊢[PRAAx] le (two*a) ((two*T)*b) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right two ht.andE₂.andE₂)
  have small : Γ ⊢[PRAAx] le (two*a) (b*N) :=
    le_trans twiceTime (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right b hT))
  have localSource : Γ ⊢[PRAAx] GaussianBetaKernelLogarithm.source a b N := .andI hb (.andI hN small)
  have timeSq := sq_le_sq ht.andE₂.andE₂
  have clockOrder := GaussianExponentialReference.unit_monotone (Γ := Γ)
    (GaussianEulerCompactProductComparison.clock_later p z B a b)
  have compare : Γ ⊢[PRAAx] le (errorNumerator k a b N T*D) (A*errorDenominator k a b N) := by
    unfold errorNumerator errorDenominator GaussianBetaKernelExponential.constantBound
    change Γ ⊢[PRAAx] le ((H*a*a*Q+b*b*N)*(N*P)) ((H*T*T*P+N)*(b*b*N*Q))
    ipra_le (𝔞(H)*𝔞(N)*𝔞(P)*𝔞(Q))*sl timeSq+(𝔞(b)*𝔞(b)*𝔞(N)*𝔞(N))*sl clockOrder
  have kernelError := distance_radius_mono _ _ _ _ A D
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hb hb) hN) hq) hd compare
    (GaussianBetaKernelExponential.original_decay_sample_bound k a b N T localSource ht.andE₂.andE₂)
  have both := replacement_error p p z R B E T a b (kernel a b N) A D hz ht hd kernelError
  exact distance_congr (.eqRefl _) (sample_at p z B a b).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ (rowNumerator p R E T N) D
      (positive_product _ _ hd (positive_product _ _ hp hp)) hd
      (le_of_eq_add (d := ConciseIPRA.PTm.zero) (by
        dsimp only [rowNumerator,A,D,H,P]
        ipra_ring)) both)

theorem cell_error (i p M C E T z R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B E)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i M)
    (hT : Γ ⊢[PRAAx] le (one+C) (E*T)) (hTN : Γ ⊢[PRAAx] le (two*T) N) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (sampleBody evaluatorF) i (sampleData p M one C E (sampleDataBeta z B N)))
      (inst2 (sampleBody GaussianEulerIntegrandName.evaluatorF) i (sampleData p M one C E (fixedData z B)))
      (rowNumerator p R E T N) (N*unit p) := by
  let a := M+C*i
  let b := E*M
  have front : Γ ⊢[PRAAx] one*M+C*i ≐ a := by dsimp only [a]; ipra_ring
  have grid : Γ ⊢[PRAAx] GaussianCompactRiemannName.grid i M one C E ≐ pairT a b :=
    congrPairT front (.eqRefl b)
  have left := (sample_body_at evaluatorF i p M one C E (sampleDataBeta z B N)).eqTrans
    ((congrAp3 evaluatorF (.eqRefl p) grid (.eqRefl _)).eqTrans (row_at p z B a b N))
  have right := (sample_body_at GaussianEulerIntegrandName.evaluatorF i p M one C E (fixedData z B)).eqTrans
    (congrAp3 GaussianEulerIntegrandName.evaluatorF (.eqRefl p) grid (.eqRefl _))
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (row_error p z R B E T a b N hz (grid_domain i M C E T hM hz.andE₂.andE₁ (le_of_lt hi) hT) hN hTN)

theorem same_grid (p M C E T z R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B E)
    (hM : Γ ⊢[PRAAx] le one M) (hN : Γ ⊢[PRAAx] le one N)
    (hT : Γ ⊢[PRAAx] le (one+C) (E*T)) (hTN : Γ ⊢[PRAAx] le (two*T) N) :
    Γ ⊢[PRAAx] distanceBounded (quadrature evaluatorF p M one C E (sampleDataBeta z B N))
      (quadrature GaussianEulerIntegrandName.evaluatorF p M one C E (fixedData z B))
      (C*rowNumerator p R E T N) (E*(N*unit p)) := by
  let f := sampleBody evaluatorF
  let g := sampleBody GaussianEulerIntegrandName.evaluatorF
  let x := sampleData p M one C E (sampleDataBeta z B N)
  let y := sampleData p M one C E (fixedData z B)
  have rows : Γ ⊢[PRAAx] termsDistance f g M x y (rowNumerator p R E T N) (N*unit p) := by
    have hsz : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) :=
      by simpa [Fm.shift,Syn.shift] using hz.shift
    have hsM : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
    have hsN : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
    have hsT : Γ.map Fm.shift ⊢[PRAAx] le (one+Syn.shift C) (Syn.shift E*Syn.shift T) :=
      by simpa [Fm.shift,Syn.shift] using hT.shift
    have hsTN : Γ.map Fm.shift ⊢[PRAAx] le (two*Syn.shift T) (Syn.shift N) :=
      by simpa [Fm.shift,Syn.shift] using hTN.shift
    refine .allI (.impI ?_)
    simpa [termsDistance,f,g,x,y,Syn.shift,fixedData] using
      cell_error (var 0) (Syn.shift p) (Syn.shift M) (Syn.shift C) (Syn.shift E) (Syn.shift T)
        (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hsz.wk hsM.wk hsN.wk Prf.hyp0 hsT.wk hsTN.wk
  exact GaussianCompactScalarMajorant.common_mesh_distance f g M x y C E _ _ hM hz.andE₂.andE₁
    (positive_product _ _ hN (unit_positive p)) rows

theorem original_Euler_same_grid_beta_kernel_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 5) (var 6) (var 7) (var 3) ⟶ (le one (var 1) ⋏ le one (var 8)) ⟶
      (le (one+var 2) (var 3*var 4) ⋏ le (two*var 4) (var 8)) ⟶
      distanceBounded (quadrature evaluatorF (var 0) (var 1) one (var 2) (var 3) (sampleDataBeta (var 5) (var 7) (var 8)))
        (quadrature GaussianEulerIntegrandName.evaluatorF (var 0) (var 1) one (var 2) (var 3) (fixedData (var 5) (var 7)))
        (var 2*rowNumerator (var 0) (var 6) (var 3) (var 4) (var 8)) (var 3*(var 8*unit (var 0)))) :=
  closeUniv 9 (.impI (.impI (.impI (same_grid _ _ _ _ _ _ _ _ _
    hyp2 Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂))))

def fixedGridBeta (q z R B k A N : PTm n) : PTm n :=
  quadrature evaluatorF (GaussianCompactRiemannName.precision q (top k A R)) (conservativeCells q k A R)
    one (width k A R) (etaDen k A R) (sampleDataBeta z B N)

theorem fixed_grid (q z R B k A N : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hN : Γ ⊢[PRAAx] le one N) (hTN : Γ ⊢[PRAAx] le (two*top k A R) N) :
    Γ ⊢[PRAAx] distanceBounded (fixedGridBeta q z R B k A N)
      (ap2 GaussianGammaEulerCompactQuadrature.nameF q (GaussianGammaEulerCompactQuadrature.data z R B k A))
      (width k A R*rowNumerator (GaussianCompactRiemannName.precision q (top k A R)) R (etaDen k A R) (top k A R) N)
      (etaDen k A R*(N*unit (GaussianCompactRiemannName.precision q (top k A R)))) := by
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have localSource : Γ ⊢[PRAAx] source z R B (etaDen k A R) := .andI hz.andE₁ (.andI he hz.andE₂)
  have hM : Γ ⊢[PRAAx] le one (conservativeCells q k A R) := GaussianCompactRiemannName.mesh_positive _ _ _
  have hT : Γ ⊢[PRAAx] le (one+width k A R) (etaDen k A R*top k A R) :=
    le_congr (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k A R).eqSymm (.eqRefl _) (le_refl _)
  exact distance_congr (.eqRefl _) (GaussianGammaEulerCompactQuadrature.original_sample q z R B k A).eqSymm
    (.eqRefl _) (.eqRefl _)
    (same_grid _ _ _ _ _ _ _ _ _ localSource hM hN hT hTN)

theorem original_fixed_Euler_sampler_beta_grid_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianGammaEulerCompactQuadrature.source (var 1) (var 2) (var 3) ⟶
      (le one (var 6) ⋏ le (two*top (var 4) (var 5) (var 2)) (var 6)) ⟶
      distanceBounded (fixedGridBeta (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (ap2 GaussianGammaEulerCompactQuadrature.nameF (var 0)
          (GaussianGammaEulerCompactQuadrature.data (var 1) (var 2) (var 3) (var 4) (var 5)))
        (width (var 4) (var 5) (var 2)*rowNumerator
          (GaussianCompactRiemannName.precision (var 0) (top (var 4) (var 5) (var 2)))
          (var 2) (etaDen (var 4) (var 5) (var 2)) (top (var 4) (var 5) (var 2)) (var 6))
        (etaDen (var 4) (var 5) (var 2)*(var 6*unit (GaussianCompactRiemannName.precision (var 0)
          (top (var 4) (var 5) (var 2)))))) :=
  closeUniv 7 (.impI (.impI (fixed_grid _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

def originalGridBeta (p z R B A N : PTm n) : PTm n :=
  quadrature evaluatorF (evaluationPrecision p A R) (cells p A R) one (width p A R) (etaDen p A R)
    (sampleDataBeta z B N)

theorem original_grid (p z R B A N : PTm n) (hz : Γ ⊢[PRAAx] GaussianGammaEulerCompactQuadrature.source z R B)
    (hN : Γ ⊢[PRAAx] le one N) (hTN : Γ ⊢[PRAAx] le (two*top p A R) N) :
    Γ ⊢[PRAAx] distanceBounded (originalGridBeta p z R B A N)
      (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data z R B A))
      (width p A R*rowNumerator (evaluationPrecision p A R) R (etaDen p A R) (top p A R) N)
      (etaDen p A R*(N*unit (evaluationPrecision p A R))) := by
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) p A R
  have localSource : Γ ⊢[PRAAx] source z R B (etaDen p A R) := .andI hz.andE₁ (.andI he hz.andE₂)
  have hM : Γ ⊢[PRAAx] le one (cells p A R) := GaussianCompactRiemannName.mesh_positive _ _ _
  have hT : Γ ⊢[PRAAx] le (one+width p A R) (etaDen p A R*top p A R) :=
    le_congr (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint p A R).eqSymm (.eqRefl _) (le_refl _)
  exact distance_congr (.eqRefl _) (GaussianEulerImproperName.actual_sampler p z R B A).eqSymm
    (.eqRefl _) (.eqRefl _)
    (same_grid _ _ _ _ _ _ _ _ _ localSource hM hN hT hTN)

theorem original_improper_Euler_sampler_beta_grid_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaEulerCompactQuadrature.source (var 1) (var 2) (var 3) ⟶
      (le one (var 5) ⋏ le (two*top (var 0) (var 4) (var 2)) (var 5)) ⟶
      distanceBounded (originalGridBeta (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (ap2 GaussianEulerImproperName.nameF (var 0) (GaussianEulerImproperName.data (var 1) (var 2) (var 3) (var 4)))
        (width (var 0) (var 4) (var 2)*rowNumerator (evaluationPrecision (var 0) (var 4) (var 2))
          (var 2) (etaDen (var 0) (var 4) (var 2)) (top (var 0) (var 4) (var 2)) (var 5))
        (etaDen (var 0) (var 4) (var 2)*(var 5*unit (evaluationPrecision (var 0) (var 4) (var 2))))) :=
  closeUniv 6 (.impI (.impI (original_grid _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelGridComparison
