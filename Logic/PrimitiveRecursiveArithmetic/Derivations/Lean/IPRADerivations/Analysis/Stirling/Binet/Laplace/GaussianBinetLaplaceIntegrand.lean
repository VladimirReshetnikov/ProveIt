import IPRADerivations.Analysis.Stirling.Binet.Kernel.Bounds.GaussianBinetKernelCoarseBound
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceExponential
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedMultiplyRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# The finite and cofinal Binet Laplace integrand

The integrands are normalized named products of the Gaussian damping
factor and the actual Binet kernel. Their time estimate is uniform in
the kernel cutoff. The cutoff comparison retains the sharp kernel
coefficient and the two ordinary observation errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceIntegrand

open_ipra
open GaussianBinetKernelRows (inputData rowF rowBody regular_rows)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianLogGammaEulerResidualDomain (source subst_source)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator leadingDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "ExpF" => GaussianBinetLaplaceExponential.nameF
local notation "expData" => GaussianBinetLaplaceExponential.data
local notation "FiniteK" => GaussianBinetKernelTail.finiteF
local notation "finiteKData" => GaussianBinetKernelTail.finiteData
local notation "CofinalK" => GaussianBinetKernelCofinal.nameF

abbrev finiteF : PR 2 := multiplyF ExpF FiniteK
abbrev cofinalF : PR 2 := multiplyF ExpF CofinalK

def finiteData (X Y D sign R T N A B : PTm n) : PTm n :=
  multiplyData ExpF FiniteK (expData X Y D sign R T A B) (finiteKData N A B)

def cofinalData (X Y D sign R T A B : PTm n) : PTm n :=
  multiplyData ExpF CofinalK (expData X Y D sign R T A B) (inputData A B)

def input (X Y D sign R T A B : PTm n) : Fm PTm n :=
  source X Y D sign R ⋏ (le one B ⋏ le A (T*B))

def meshGain (R T : PTm n) : PTm n := GaussianBinetLaplaceExponential.timeGain R T+two*T

def factorClock (K : PR 2) (p x y : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (multiplyModulus ExpF K x y) p

theorem product_at (K : PR 2) (p x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (multiplyF ExpF K) p (multiplyData ExpF K x y) ≐
      qmul (ap2 ExpF (factorClock K p x y) x) (ap2 K (factorClock K p x y) y) :=
  (GaussianNameArithmetic.multiply_at ExpF K x y p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _))

ipra_subst finiteData

ipra_subst cofinalData

ipra_subst input [one]

private theorem finite_kernel_regular (N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN FiniteK (finiteKData N A B) :=
  GaussianNamedFiniteSumFamily.regular rowF rowBody N (inputData A B) (regular_rows N A B hB)

theorem finite_regular (X Y D sign R T N A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] pointCN finiteF (finiteData X Y D sign R T N A B) :=
  multiply_fast _ _ _ _
    (GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
    (finite_kernel_regular N A B h.andE₂.andE₁)

theorem cofinal_regular (X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] pointCN cofinalF (cofinalData X Y D sign R T A B) :=
  multiply_fast _ _ _ _
    (GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
    (GaussianBinetKernelCofinal.regular A B h.andE₂.andE₁)

private theorem exp_bound_two (p X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] bounded (ap2 ExpF p (expData X Y D sign R T A B)) two one := by
  have hp := unit_positive (Γ := Γ) p
  exact bounded_radius_mono _ _ _ _ _ hp (le_refl one) (by ipra_le sl hp)
    (GaussianBinetLaplaceExponential.unit_bound p X Y D sign R T A B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)

theorem finite_bound (p X Y D sign R T N A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] bounded (ap2 finiteF p (finiteData X Y D sign R T N A B)) one two := by
  let x := expData X Y D sign R T A B
  let y := finiteKData N A B
  let j := factorClock FiniteK p x y
  have h4 : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
  have raw := bounded_product (ap2 ExpF j x) (ap2 FiniteK j y) two one one (num 4)
    (le_refl one) h4 (exp_bound_two j X Y D sign R T A B h)
    (GaussianBinetKernelCoarseBound.named_finite_at j N A B h.andE₂.andE₁)
  exact bound_congr (product_at FiniteK p x y).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) h4)
      (le_succ_self one) (by ipra_le 0) raw)

theorem cofinal_bound (p X Y D sign R T A B : PTm n) (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] bounded (ap2 cofinalF p (cofinalData X Y D sign R T A B)) one two := by
  let x := expData X Y D sign R T A B
  let y := inputData A B
  let j := factorClock CofinalK p x y
  have h4 : Γ ⊢[PRAAx] le one (num 4 : PTm n) := by ipra_le 3
  have raw := bounded_product (ap2 ExpF j x) (ap2 CofinalK j y) two one one (num 4)
    (le_refl one) h4 (exp_bound_two j X Y D sign R T A B h)
    (GaussianBinetKernelCoarseBound.cofinal_at j A B h.andE₂.andE₁)
  exact bound_congr (product_at CofinalK p x y).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) h4)
      (le_succ_self one) (by ipra_le 0) raw)

private theorem exp_sample_bound (X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    Γ ⊢[PRAAx] sampleBound ExpF (expData X Y D sign R T A B) two := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s B) := by
    simpa only [Fm.shift, Syn.shift, s, subst_input] using h.shift
  simpa only [sampleBound,Syn.shift,s,GaussianBinetLaplaceExponential.subst_data,
    two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    exp_bound_two (var 0) (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s B) hs

private theorem kernel_weaken {v : PTm n} (h : Γ ⊢[PRAAx] bounded v one (num 4)) :
    Γ ⊢[PRAAx] bounded v one one :=
  bounded_radius_mono _ _ _ _ _ (by ipra_le 3) (le_refl one) (by ipra_le 3) h

private theorem finite_kernel_sample_bound (N A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] sampleBound FiniteK (finiteKData N A B) one := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,one] using hB.shift
  simpa only [sampleBound,Syn.shift,GaussianNamedFiniteSumFamily.subst_data,GaussianBinetKernelRows.subst_inputData,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    kernel_weaken (GaussianBinetKernelCoarseBound.named_finite_at (var 0) (Syn.shift N) (Syn.shift A) (Syn.shift B) hs)

private theorem cofinal_kernel_sample_bound (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] sampleBound CofinalK (inputData A B) one := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift,one] using hB.shift
  simpa only [sampleBound,Syn.shift,GaussianBinetKernelRows.subst_inputData,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    kernel_weaken (GaussianBinetKernelCoarseBound.cofinal_at (var 0) (Syn.shift A) (Syn.shift B) hs)

private theorem product_time_rate (K : PR 2) (x y u v R T E Q : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Q)
    (hx : Γ ⊢[PRAAx] pointCN ExpF x) (hy : Γ ⊢[PRAAx] pointCN K y)
    (hu : Γ ⊢[PRAAx] pointCN ExpF u) (hv : Γ ⊢[PRAAx] pointCN K v)
    (hyb : Γ ⊢[PRAAx] sampleBound K y one) (hub : Γ ⊢[PRAAx] sampleBound ExpF u two)
    (hex : Γ ⊢[PRAAx] independentRate ExpF ExpF x u (GaussianBinetLaplaceExponential.timeGain R T*E) Q)
    (hker : Γ ⊢[PRAAx] independentRate K K y v (T*E) Q) :
    Γ ⊢[PRAAx] independentRate (multiplyF ExpF K) (multiplyF ExpF K) (multiplyData ExpF K x y)
      (multiplyData ExpF K u v) (meshGain R T*E) Q :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hQ hQ) hQ
    (le_of_eq_add (d := zero) (by dsimp only [leadingNumerator,leadingDenominator,meshGain]; ipra_ring))
    (GaussianNamedMultiplyRate.independent_rate ExpF K ExpF K x y u v _ Q _ Q one two
      hQ hQ hx hy hu hv hyb hub hex hker)

theorem finite_time_rate (X Y D sign R T N A B a b E Q : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (ht : Γ ⊢[PRAAx] GaussianBinetKernelTimeContinuity.source A B a b T E Q) :
    Γ ⊢[PRAAx] independentRate finiteF finiteF (finiteData X Y D sign R T N A B) (finiteData X Y D sign R T N a b)
      (meshGain R T*E) Q := by
  have hb := ht.andE₂.andE₁
  have hA := ht.andE₂.andE₂.andE₂.andE₁
  have ha := ht.andE₂.andE₂.andE₂.andE₂.andE₁
  exact product_time_rate FiniteK _ _ _ _ R T E Q ht.andE₂.andE₂.andE₁
    (GaussianBinetLaplaceExponential.regular X Y D sign R T A B hz ht.andE₁ hA) (finite_kernel_regular N A B ht.andE₁)
    (GaussianBinetLaplaceExponential.regular X Y D sign R T a b hz hb ha) (finite_kernel_regular N a b hb)
    (finite_kernel_sample_bound N A B ht.andE₁) (exp_sample_bound X Y D sign R T a b (.andI hz (.andI hb ha)))
    (GaussianBinetLaplaceExponential.time_rate X Y D sign R T A B a b E Q hz ht)
    (GaussianBinetKernelTimeContinuity.named_finite_rate N A B a b T E Q ht)

theorem cofinal_time_rate (X Y D sign R T A B a b E Q : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (ht : Γ ⊢[PRAAx] GaussianBinetKernelTimeContinuity.source A B a b T E Q) :
    Γ ⊢[PRAAx] independentRate cofinalF cofinalF (cofinalData X Y D sign R T A B) (cofinalData X Y D sign R T a b)
      (meshGain R T*E) Q := by
  have hb := ht.andE₂.andE₁
  have hA := ht.andE₂.andE₂.andE₂.andE₁
  have ha := ht.andE₂.andE₂.andE₂.andE₂.andE₁
  exact product_time_rate CofinalK _ _ _ _ R T E Q ht.andE₂.andE₂.andE₁
    (GaussianBinetLaplaceExponential.regular X Y D sign R T A B hz ht.andE₁ hA) (GaussianBinetKernelCofinal.regular A B ht.andE₁)
    (GaussianBinetLaplaceExponential.regular X Y D sign R T a b hz hb ha) (GaussianBinetKernelCofinal.regular a b hb)
    (cofinal_kernel_sample_bound A B ht.andE₁) (exp_sample_bound X Y D sign R T a b (.andI hz (.andI hb ha)))
    (GaussianBinetLaplaceExponential.time_rate X Y D sign R T A B a b E Q hz ht)
    (GaussianBinetKernelTimeContinuity.cofinal_rate A B a b T E Q ht)

theorem finite_mesh_rate (X Y D sign R T N A B j : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] le (A+j) (T*B)) :
    Γ ⊢[PRAAx] independentRate finiteF finiteF (finiteData X Y D sign R T N A B)
      (finiteData X Y D sign R T N (A+j) B) (meshGain R T*j) B :=
  finite_time_rate X Y D sign R T N A B (A+j) B j B hz (GaussianBinetKernelTimeContinuity.mesh_input A B j T hB ht)

private def cutoffCost (X Y D sign R T N A B : PTm n) : PTm n :=
  (multiplyModulus ExpF CofinalK (expData X Y D sign R T A B) (inputData A B)+one)+
    (multiplyModulus ExpF FiniteK (expData X Y D sign R T A B) (finiteKData N A B)+one)+num 5

@[simp] private theorem subst_cutoffCost {m : ℕ} (σ : Fin n → PTm m) (X Y D sign R T N A B : PTm n) :
    Syn.subst σ (cutoffCost X Y D sign R T N A B) =
      cutoffCost (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign)
        (Syn.subst σ R) (Syn.subst σ T) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [cutoffCost, one]

private theorem cutoff_diagonal (p X Y D sign R T N A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 cofinalF p (cofinalData X Y D sign R T A B))
      (ap2 finiteF p (finiteData X Y D sign R T N A B))
      (diagonalNumerator one (num 8*N) (cutoffCost X Y D sign R T N A B) p)
      (diagonalDenominator (num 8*N) p) := by
  let x := expData X Y D sign R T A B
  let y := inputData A B
  let v := finiteKData N A B
  let a := ap2 ExpF p x
  let b := ap2 CofinalK p y
  let c := ap2 FiniteK p v
  let U := unit p
  let K := num 8*N
  let W := K*U
  let L := multiplyModulus ExpF CofinalK x y+one
  let J := multiplyModulus ExpF FiniteK x v+one
  have hB := h.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) p
  have hK : Γ ⊢[PRAAx] le one K := positive_product _ _ GaussianBinetKernelTailMajorant.eight_positive hN
  have hW := positive_product _ _ hK hU
  have e := GaussianBinetLaplaceExponential.regular X Y D sign R T A B h.andE₁ hB h.andE₂.andE₂
  have r := GaussianBinetKernelCofinal.regular A B hB
  have s := finite_kernel_regular N A B hB
  have kd : Γ ⊢[PRAAx] distanceBounded b c (one*U+two*K) W :=
    GaussianNamedInverseRate.diagonal_rate CofinalK FiniteK y v one K p hK
      (GaussianBinetKernelCofinal.cutoff_rate N A B hN hB)
  have ed := GaussianBinetLaplaceExponential.unit_bound p X Y D sign R T A B h.andE₁ hB h.andE₂.andE₂
  have raw : Γ ⊢[PRAAx] distanceBounded (qmul a b) (qmul a c) ((U+one)*(one*U+two*K)) (U*W) :=
    bound_congr (GaussianRationalRoundedPower.multiplication_difference a b c).eqSymm
      (.eqRefl _) (.eqRefl _) (bounded_product a _ _ _ _ _ hU hW ed kd)
  have middle := distance_radius_mono _ _ _ _ (one*U+num 5*K) W (positive_product _ _ hU hW) hW
    (by dsimp only [W]; ipra_le 𝔞(K*U*U)*sl hK+2*𝔞(K*K*U)*sl hU) raw
  have before : Γ ⊢[PRAAx] distanceBounded (ap2 cofinalF p (cofinalData X Y D sign R T A B)) (qmul a b) L U :=
    GaussianNameRingLaws.multiply_sample_error ExpF CofinalK x y p e r
  have after : Γ ⊢[PRAAx] distanceBounded (ap2 finiteF p (finiteData X Y D sign R T N A B)) (qmul a c) J U :=
    GaussianNameRingLaws.multiply_sample_error ExpF FiniteK x v p e s
  have first := distance_radius_mono _ _ _ _ (L*K) W hU hW
    (le_of_eq_add (d := zero) (by dsimp only [W]; ipra_ring)) before
  have last := distance_radius_mono _ _ _ _ (J*K) W hU hW
    (le_of_eq_add (d := zero) (by dsimp only [W]; ipra_ring))
    (distance_symmetric _ _ _ _ hU after)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [L,J,K,U,x,y,v,diagonalNumerator,cutoffCost]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ W hW (distance_triangle_same _ _ _ _ _ W hW first middle) last)

theorem cutoff_rate (X Y D sign R T N A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate cofinalF finiteF (cofinalData X Y D sign R T A B)
      (finiteData X Y D sign R T N A B) one (num 8*N) := by
  have hK := positive_product _ _ (GaussianBinetKernelTailMajorant.eight_positive (Γ := Γ)) hN
  refine GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (cutoffCost X Y D sign R T N A B) hK
    (cofinal_regular X Y D sign R T A B h) (finite_regular X Y D sign R T N A B h) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (s X) (s Y) (s D) (s sign) (s R) (s T) (s A) (s B) := by
    simpa only [Fm.shift,Syn.shift,s,subst_input] using h.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le one (s N) := by simpa [Fm.shift,Syn.shift,s,one] using hN.shift
  simpa only [diagonalEnvelope,subst_cofinalData,subst_finiteData,subst_cutoffCost,Syn.shift,s,
    PTm.subst_mul,PTm.subst_num,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    cutoff_diagonal (var 0) (s X) (s Y) (s D) (s sign) (s R) (s T) (s N) (s A) (s B) hs ns

theorem actual_Binet_Laplace_integrand_cutoff_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 8) ⟶ le one (var 6) ⟶
        independentRate cofinalF finiteF (cofinalData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 7) (var 8))
          (finiteData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) one (num 8*var 6)) :=
  closeUniv 9 (.impI (.impI (cutoff_rate _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_finite_Binet_Laplace_integrand_mesh_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le one (var 8) ⟶ le (var 7+var 9) (var 5*var 8) ⟶
        independentRate finiteF finiteF (finiteData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
          (finiteData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7+var 9) (var 8))
          (meshGain (var 4) (var 5)*var 9) (var 8)) :=
  closeUniv 10 (.impI (.impI (.impI (finite_mesh_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceIntegrand
