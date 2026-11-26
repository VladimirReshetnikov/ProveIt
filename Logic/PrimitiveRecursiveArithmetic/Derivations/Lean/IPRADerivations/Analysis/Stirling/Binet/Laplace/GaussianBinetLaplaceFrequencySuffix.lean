import IPRADerivations.Analysis.Stirling.Binet.Kernel.GaussianBinetKernelFrequencyGrid
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceImproperName
import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineKernels.GaussianBinetSineStripCut
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence

/-!
# Original Binet integral on the common positive frequency suffix

An arbitrary sufficiently fine grid compares to the original compact
sampler by their common refinement. Removing a short initial interval
from the full grid retains the original tags and mesh weight.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceFrequencySuffix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetKernelFrequencyGrid (cofinalBody originalData physical_row_at)
open GaussianBinetLaplaceIntegrand (cofinal_bound meshGain)
open GaussianBinetLaplaceOrderedPrefixes (prefixData width)
open GaussianBinetLaplaceStrip (evaluatorF fixedData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (mesh mesh_positive precision quadrature)
open GaussianLogGammaEulerResidualDomain (source subst_source)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalFiniteSum (sum sum_index_congr)
open GaussianRationalHorner (positive_product qadd qmul qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound constantBody)
open GaussianRationalSyntheticDivision (qadd_sub_cancel qsub_congr qmul_congr)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => evaluatorF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "StripF" => GaussianBinetLaplaceStrip.nameF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "Improper" => GaussianBinetLaplaceImproperName.nameF
local notation "improperData" => GaussianBinetLaplaceImproperName.data

def wholeValue (q N X Y D sign R L : PTm n) : PTm n :=
  quadrature F q N (one+zero) (width D L) one (fixedData X Y D sign R (width D L) zero)

def prefixValue (q N X Y D sign R L J : PTm n) : PTm n :=
  qmul (weight (width D L) one N)
    (sum cofinalBody J (originalData q N X Y D sign R (width D L) (width D L)))

def suffixValue (q N X Y D sign R L J : PTm n) : PTm n :=
  qmul (weight (width D L) one N)
    (sum (offB cofinalBody) (monus N J) (pairT J (originalData q N X Y D sign R (width D L) (width D L))))

@[simp] theorem subst_wholeValue {m : ℕ} (σ : Fin n → PTm m) (q N X Y D sign R L : PTm n) :
    Syn.subst σ (wholeValue q N X Y D sign R L) =
      wholeValue (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D)
        (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ L) := by simp [wholeValue,width,one]

@[simp] theorem subst_prefixValue {m : ℕ} (σ : Fin n → PTm m) (q N X Y D sign R L J : PTm n) :
    Syn.subst σ (prefixValue q N X Y D sign R L J) =
      prefixValue (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D)
        (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ J) := by
  simp [prefixValue,originalData,width,one]

@[simp] theorem subst_suffixValue {m : ℕ} (σ : Fin n → PTm m) (q N X Y D sign R L J : PTm n) :
    Syn.subst σ (suffixValue q N X Y D sign R L J) =
      suffixValue (Syn.subst σ q) (Syn.subst σ N) (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D)
        (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ L) (Syn.subst σ J) := by
  simp [suffixValue,originalData,width,one]

theorem split_value (q N X Y D sign R L J : PTm n) (hJ : Γ ⊢[PRAAx] le J N) :
    Γ ⊢[PRAAx] wholeValue q N X Y D sign R L ≐
      qadd (prefixValue q N X Y D sign R L J) (suffixValue q N X Y D sign R L J) := by
  let C := width D L
  let x := originalData q N X Y D sign R C C
  let w := weight C one N
  let r := monus N J
  have s := (sum_index_congr cofinalBody (eq_add_of_le hJ) (.eqRefl x)).eqTrans
    (GaussianRationalMatrixFiniteSums.sum_split cofinalBody J r x)
  exact (qmul_congr (.eqRefl w) s).eqTrans
    (GaussianRationalCoefficientScaling.qmul_add w (sum cofinalBody J x) (sum (offB cofinalBody) r (pairT J x)))

private theorem row_bound (j q N X Y D sign R C : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hN : Γ ⊢[PRAAx] le one N) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] bounded (inst2 cofinalBody j (originalData q N X Y D sign R C C)) one two := by
  have guard := le_congr (mul_comm j C) (mul_comm N C) (mul_le_mul_right C hj)
  exact bound_congr (physical_row_at j q N X Y D sign R C C C (.eqRefl C)).eqSymm
    (.eqRefl _) (.eqRefl _) (cofinal_bound q X Y D sign R C (C*j) N (.andI h (.andI hN guard)))

theorem prefix_bound (q N X Y D sign R L J E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le J N)
    (hE : Γ ⊢[PRAAx] le one E) (hsmall : Γ ⊢[PRAAx] le (((D*L)*J)*E) N) :
    Γ ⊢[PRAAx] bounded (prefixValue q N X Y D sign R L J) one (two*E) := by
  let C := width D L
  let d := originalData q N X Y D sign R C C
  have h2 : Γ ⊢[PRAAx] le one two := le_succ_self one
  have rows : Γ ⊢[PRAAx] termsDistance cofinalBody constantBody J d qzero one two := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) :=
      by simpa only [Δ,Fm.shift,Syn.shift,s,subst_source] using h.shift
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,Fm.shift,Syn.shift,s] using hN.shift
    have js : Δ ⊢[PRAAx] le (s J) (s N) := by simpa [Δ,Fm.shift,Syn.shift,s] using hJ.shift
    have jb : _ ⊢[PRAAx] le (var 0) (s N) := le_trans (le_of_lt Prf.hyp0) js.wk
    have hb := row_bound (var 0) (s q) (s N) (s X) (s Y) (s D) (s sign) (s R) (s C) hs.wk ns.wk jb
    simpa only [d,originalData,s,Δ,Syn.shift,GaussianCompactRiemannName.subst_sampleData,subst_pairT,
      PTm.subst_add,one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,
      GaussianRationalHorner.subst_qzero,GaussianRationalRiemannRefinement.constant_entry] using
      (GaussianReconstructionRoots.distance_zero_iff _ _ _ (le_succ_self one)).iffMpr hb
  have z : Γ ⊢[PRAAx] sum constantBody J qzero ≐ qzero :=
    (GaussianRationalRiemannRefinement.constant_sum qzero J).eqTrans
      (GaussianRationalFactorialEulerSums.scale_zero_value J)
  have sums := (GaussianReconstructionRoots.distance_zero_iff _ _ _ h2).iffMp
    (distance_congr (.eqRefl _) z (by ipra_ring : Γ ⊢[PRAAx] J*one ≐ J) (.eqRefl _)
      (sum_distance _ _ J d qzero one two h2 rows))
  have nw := positive_product _ _ (le_refl (Γ := Γ) one) hN
  have scaled := bounded_product _ _ C (one*N) J two nw h2 (weight_bound C one N (le_refl one) hN) sums
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ nw h2) (positive_product _ _ h2 hE)
    (le_congr (by dsimp only [C,width]; ipra_ring) (by ipra_ring) (mul_le_mul_right two hsmall)) scaled

theorem discard_prefix_error (q N X Y D sign R L J E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hN : Γ ⊢[PRAAx] le one N) (hJ : Γ ⊢[PRAAx] le J N)
    (hE : Γ ⊢[PRAAx] le one E) (hsmall : Γ ⊢[PRAAx] le (((D*L)*J)*E) N) :
    Γ ⊢[PRAAx] distanceBounded (wholeValue q N X Y D sign R L)
      (suffixValue q N X Y D sign R L J) one (two*E) := by
  let a := prefixValue q N X Y D sign R L J
  let b := suffixValue q N X Y D sign R L J
  have e := (split_value q N X Y D sign R L J hJ).eqTrans (GaussianReciprocalHorner.qadd_commutative a b)
  exact bound_congr ((qsub_congr e (.eqRefl b)).eqTrans
    (qadd_sub_cancel b a (GaussianRationalHorner.qmul_canonical _ _))).eqSymm (.eqRefl _) (.eqRefl _)
    (prefix_bound q N X Y D sign R L J E h hN hJ hE hsmall)

def meshBudget (t R D L : PTm n) : PTm n :=
  unit (t+num 6)*meshGain R (width D L)*(width D L)*(width D L)

@[simp] theorem subst_meshBudget {m : ℕ} (σ : Fin n → PTm m) (t R D L : PTm n) :
    Syn.subst σ (meshBudget t R D L) =
      meshBudget (Syn.subst σ t) (Syn.subst σ R) (Syn.subst σ D) (Syn.subst σ L) := by
  simp [meshBudget,width,one]

/-- Use the common refinement of the original compact sampler and the
given physical grid. The actual count `N` can be any sufficiently large count. -/
theorem compact_prefix_quadrature (t q N X Y D sign R L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le (precision t (width D L)) q) (hmesh : Γ ⊢[PRAAx] le (meshBudget t R D L) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 StripF t (prefixData X Y D sign R L))
      (wholeValue q N X Y D sign R L) (num 6) (unit t) := by
  let C := width D L
  let G := meshGain R C
  let x := fixedData X Y D sign R C zero
  let M := mesh t G C
  let H := unit (t+num 6)
  let V := unit q
  have hM := mesh_positive (Γ := Γ) t G C
  have hH := unit_positive (Γ := Γ) (t+num 6)
  have hV := unit_positive (Γ := Γ) q
  have input := GaussianBinetLaplaceStrip.compact_input .cofinal X Y D sign R C zero zero C one
    (.andI h (.andI (le_refl one) (le_congr (zero_add C).eqSymm (one_mul C).eqSymm (le_refl C))))
  have a := GaussianCompactMeshIndependence.arbitrary_refinement F t q N (one+zero) C one G C x input hN hq
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) F t (one+zero) C one G C x
  have left := distance_symmetric _ _ _ _ hH (distance_congr (.eqRefl _) read.eqSymm (.eqRefl _) (.eqRefl _) a)
  have b := GaussianCompactRiemannName.quadrature_refinement F q q N M (one+zero) C one G x
    input.andE₁ (le_refl one) hN hM input.andE₂.andE₂.andE₂
  have cross := GaussianCompactRiemannName.quadrature_index_congr (Γ := Γ) F q (M*N) (N*M)
    (one+zero) C one x (mul_comm _ _)
  have lo := le_trans (GaussianCompactRiemannName.precision_lower (Γ := Γ) t C)
    (GaussianCompactRiemannName.dyadic_monotone _ _ hq)
  have den := positive_product _ _ (le_refl (Γ := Γ) one)
    (denominator_positive (one*N) q q (positive_product _ _ (le_refl one) hN))
  have right := distance_radius_mono _ _ _ _ (num 3) H den hH
    (GaussianCompactRiemannName.quadrature_budget C one G N V V H C input.andE₂.andE₂.andE₁ hmesh lo lo)
    (distance_congr cross (.eqRefl _) (.eqRefl _) (.eqRefl _) b)
  have both := distance_triangle_same _ _ _ _ _ _ hH left right
  have grow := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) t (t+num 6) (le_add_right _ _)
  exact distance_radius_mono _ _ _ _ _ _ hH (unit_positive t)
    (le_congr (by ipra_ring) (mul_comm _ _) (mul_le_mul_right (num 6) grow)) both

def tailDenominator (X L : PTm n) : PTm n := num 12*X*unit L

def errorDenominator (p t X L E : PTm n) : PTm n :=
  rateDenominator (tailDenominator X L) p t*(two*E)

def errorNumerator (p t X D L E : PTm n) : PTm n :=
  (rateNumerator D (tailDenominator X L) p t+num 6*tailDenominator X L*unit p)*(two*E)+
    rateDenominator (tailDenominator X L) p t

@[simp] theorem subst_tailDenominator {m : ℕ} (σ : Fin n → PTm m) (X L : PTm n) :
    Syn.subst σ (tailDenominator X L) = tailDenominator (Syn.subst σ X) (Syn.subst σ L) := by simp [tailDenominator]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (p t X L E : PTm n) :
    Syn.subst σ (errorDenominator p t X L E) =
      errorDenominator (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ X) (Syn.subst σ L) (Syn.subst σ E) := by
  simp [errorDenominator,two,one]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (p t X D L E : PTm n) :
    Syn.subst σ (errorNumerator p t X D L E) =
      errorNumerator (Syn.subst σ p) (Syn.subst σ t) (Syn.subst σ X) (Syn.subst σ D)
        (Syn.subst σ L) (Syn.subst σ E) := by simp [errorNumerator,two,one]

private theorem positive_tail (X L : PTm n) (hX : Γ ⊢[PRAAx] le one X) :
    Γ ⊢[PRAAx] le one (tailDenominator X L) :=
  positive_product _ _ (positive_product _ _ (by ipra_le 11) hX) (unit_positive L)

theorem error_denominator_positive (p t X L E : PTm n)
    (hX : Γ ⊢[PRAAx] le one X) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] le one (errorDenominator p t X L E) :=
  positive_product _ _ (denominator_positive _ p t (positive_tail X L hX))
    (positive_product _ _ (le_succ_self one) hE)

/-- Keep the original improper observation. Its distance to the retained
physical grid is bounded by `D/(12 X 2^L) + 1/2^p + 7/2^t + 1/(2E)`. -/
theorem improper_suffix_error (p t q N X Y D sign R L J E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hL : Γ ⊢[PRAAx] le one L)
    (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le (precision t (width D L)) q)
    (hmesh : Γ ⊢[PRAAx] le (meshBudget t R D L) N) (hJ : Γ ⊢[PRAAx] le J N)
    (hE : Γ ⊢[PRAAx] le one E) (hsmall : Γ ⊢[PRAAx] le (((D*L)*J)*E) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Improper p (improperData X Y D sign R))
      (suffixValue q N X Y D sign R L J) (errorNumerator p t X D L E) (errorDenominator p t X L E) := by
  let H := tailDenominator X L
  let V := rateDenominator H p t
  let Z := two*E
  let C := errorDenominator p t X L E
  let A := rateNumerator D H p t
  let B := num 6*H*unit p
  have hX := h.andE₁.andE₁.andE₁
  have hV := denominator_positive H p t (positive_tail X L hX)
  have hZ := positive_product _ _ (le_succ_self one) hE
  have hC := error_denominator_positive p t X L E hX hE
  have rawPrefix := rate_at Improper StripF (improperData X Y D sign R) (prefixData X Y D sign R L) D H p t
    (GaussianBinetLaplaceImproperName.prefix_rate X Y D sign R L h hL)
  have first := distance_radius_mono _ _ _ _ (A*Z) C hV hC
    (le_of_eq_add (d := zero) (by dsimp only [C,errorDenominator,A,V,H,Z]; ipra_ring)) rawPrefix
  have middle := distance_radius_mono _ _ _ _ (B*Z) C (unit_positive t) hC
    (le_of_eq_add (d := zero) (by dsimp only [B,C,errorDenominator,rateDenominator,H,Z]; ipra_ring))
    (compact_prefix_quadrature t q N X Y D sign R L h hN hq hmesh)
  have last := distance_radius_mono _ _ _ _ V C hZ hC
    (le_of_eq_add (d := zero) (by dsimp only [C,errorDenominator,V,H,Z]; ipra_ring))
    (discard_prefix_error q N X Y D sign R L J E h hN hJ hE hsmall)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [errorNumerator,A,B,V,H,Z]; ipra_ring) (.eqRefl C)
    (distance_triangle_same _ _ _ _ _ _ hC (distance_triangle_same _ _ _ _ _ _ hC first middle) last)

theorem sine_suffix_error (p t q N X Y D sign R L E : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hL : Γ ⊢[PRAAx] le one L)
    (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le (precision t (width D L)) q)
    (hmesh : Γ ⊢[PRAAx] le (meshBudget t R D L) N) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Improper p (improperData X Y D sign R))
      (suffixValue q N X Y D sign R L (GaussianBinetSineStripCut.cutoff N (D*L) E))
      (errorNumerator p t X D L E) (errorDenominator p t X L E) := by
  have cut := GaussianBinetSineStripCut.prefix_admission N (D*L) E (positive_product _ _ h.andE₁.andE₂ hL) hE
  exact improper_suffix_error p t q N X Y D sign R L _ E h hL hN hq hmesh cut.andE₁ hE cut.andE₂

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceFrequencySuffix
