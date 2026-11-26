import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelDomination
import IPRADerivations.Analysis.FiniteOperations.GaussianPositiveScalarProductBound
import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelGridComparison

/-!
# The literal weighted beta kernel has the original upper-tail majorant

Keep the original compact replacement row and its actual power query.
Positive scalar order transfers the full beta domination to this row.
The original multiplication clock absorbs the power bound, and a single
finite Euclidean gap removes only the auxiliary positive-reference error.
The factorial and original half-decay reference are unchanged.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelUpperTail

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUpperPowerOrder (source)
open GaussianEulerUpperPowerCompatibility (old_source)
open GaussianEulerIntegrandName (powerF powerData decayF decayData productF productData sample sample_at)
open GaussianEulerCompactProductComparison (clock replacement original_product)
open GaussianBetaKernelExponential (kernel)
open GaussianEulerUpperTailPointwise (referenceTop referenceBottom reference_bottom_positive)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData sample_canonical sample_nonnegative)
open GaussianEulerDecayOrder (signedTime original_decay_nonnegative_representative)
open GaussianRationalHorner (qadd qmul canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction)
open RationalGaussianEmbedding (embed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def positiveReference (s a b : PTm n) : PTm n := ap2 positiveF s (positiveData (signedTime a b))
def upperReference (s a b : PTm n) : PTm n :=
  embed (RationalArithmetic.add (fstT (positiveReference s a b)) (fraction (num 3) (unit s)))
def powerBudget (z B a b : PTm n) : PTm n := GaussianNameBounds.U powerF (powerData z B a b)
def row (p z B a b N : PTm n) : PTm n := replacement p z B a b (kernel a b N)
def top (p q R a b : PTm n) : PTm n := majorant R*referenceTop q a b*unit p+num 4*referenceBottom q a b
def bottom (p q a b : PTm n) : PTm n := referenceBottom q a b*unit p

@[simp] theorem subst_positiveReference {m : ℕ} (σ : Fin n → PTm m) (s a b : PTm n) :
    Syn.subst σ (positiveReference s a b) = positiveReference (Syn.subst σ s) (Syn.subst σ a) (Syn.subst σ b) :=
  by simp [positiveReference,signedTime]
@[simp] theorem subst_upperReference {m : ℕ} (σ : Fin n → PTm m) (s a b : PTm n) :
    Syn.subst σ (upperReference s a b) = upperReference (Syn.subst σ s) (Syn.subst σ a) (Syn.subst σ b) := by simp [upperReference]
@[simp] theorem subst_powerBudget {m : ℕ} (σ : Fin n → PTm m) (z B a b : PTm n) :
    Syn.subst σ (powerBudget z B a b) = powerBudget (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) := by simp [powerBudget]
@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (p z B a b N : PTm n) :
    Syn.subst σ (row p z B a b N) = row (Syn.subst σ p) (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) :=
  by simp [row,kernel,GaussianBetaKernelExponential.base]
@[simp] theorem subst_top {m : ℕ} (σ : Fin n → PTm m) (p q R a b : PTm n) :
    Syn.subst σ (top p q R a b) = top (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ R) (Syn.subst σ a) (Syn.subst σ b) := by simp [top]
@[simp] theorem subst_bottom {m : ℕ} (σ : Fin n → PTm m) (p q a b : PTm n) :
    Syn.subst σ (bottom p q a b) = bottom (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ a) (Syn.subst σ b) := by simp [bottom]

theorem upper_reference_real (s a b : PTm n) : Γ ⊢[PRAAx]
    fstT (upperReference s a b) ≐ RationalArithmetic.add (fstT (positiveReference s a b)) (fraction (num 3) (unit s)) :=
  (fst_pair _ _).eqTrans (RationalNormalForm.normalize_fixed_point _ (RationalArithmetic.add_guard _ _))

theorem reference_error (s k a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    distanceBounded (positiveReference s a b) (ap2 decayF k (decayData a b)) (unit s+unit k) (unit s*unit k) :=
  GaussianNameEquivalence.cross_at positiveF decayF _ _ s k (original_decay_nonnegative_representative a b hb)

theorem kernel_below_upper_reference (s a b N : PTm n) (h : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source a b N) : Γ ⊢[PRAAx]
    RationalArgmin.rationalLE (fstT (kernel a b N)) (fstT (upperReference s a b)) := by
  let U := unit s
  have hu : Γ ⊢[PRAAx] le one U := unit_positive s
  have hd := positive_product _ _ hu hu
  have near := distance_radius_mono _ _ (U+U) (U*U) two U hd hu
    (le_of_eq_add (d := zero) (by ipra_ring)) (reference_error s s a b h.andE₁)
  have scalar := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hu
      (distance_symmetric _ _ _ _ hu near))
  have both := RationalValueBounds.upper_triangle _ _ _ one U two U
    (GaussianBetaKernelDomination.original_kernel_upper s a b N h) scalar
  have up : Γ ⊢[PRAAx] RationalValueBounds.upper (fstT (kernel a b N)) (fstT (positiveReference s a b)) (num 3) U :=
    RationalValueBounds.upper_mono _ _ _ _ _ _ hd both (le_of_eq_add (d := zero) (by ipra_ring))
  exact RationalArgmin.rationalLE_congr (.eqRefl _) (upper_reference_real s a b).eqSymm
    (RationalConvexEndpointBudget.order_of_upper _ _ _ _ hu up)

theorem upper_reference_sum (s a b : PTm n) : Γ ⊢[PRAAx]
    upperReference s a b ≐ qadd (positiveReference s a b) (embed (fraction (num 3) (unit s))) :=
  (RationalGaussianEmbedding.embed_add _ _).eqTrans
    (qadd_congr (RationalGaussianEmbedding.canonical_axis_roundtrip _ (sample_canonical _ s)
      (sample_nonnegative (signedTime a b) s).andE₁) (.eqRefl _))

theorem upper_reference_error (s k a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    distanceBounded (upperReference s a b) (ap2 decayF k (decayData a b))
      (num 4*unit k+unit s) (unit s*unit k) := by
  have hu := unit_positive (Γ := Γ) s
  have hk := unit_positive (Γ := Γ) k
  have frac : Γ ⊢[PRAAx] embed (fraction (num 3) (unit s)) ≐ GaussianDominantPairAlgebra.radiusPoint (num 3) (unit s) :=
    (GaussianEulerDecayOrder.fraction_embedding _ _ hu).eqTrans
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ hu)
  have small : Γ ⊢[PRAAx] bounded (embed (fraction (num 3) (unit s))) (num 3) (unit s) :=
    bound_congr frac.eqSymm (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded _ _ hu)
  have first : Γ ⊢[PRAAx] distanceBounded (upperReference s a b) (positiveReference s a b) (num 3) (unit s) :=
    bound_congr ((qsub_congr (upper_reference_sum s a b) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel _ _ (RationalGaussianEmbedding.embed_canonical _))).eqSymm
      (.eqRefl _) (.eqRefl _) small
  have both := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hu (positive_product _ _ hu hk)
    first (reference_error s k a b hb)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu (positive_product _ _ hu hk))
    (positive_product _ _ hu hk) (le_of_eq_add (d := zero) (by ipra_ring)) both

theorem power_clock_budget (p z B a b : PTm n) : Γ ⊢[PRAAx]
    le (powerBudget z B a b*unit p) (unit (clock p z B a b)) := by
  have first := mul_le_mul_right (Γ := Γ) (unit p)
    (le_add_right (GaussianNameBounds.U powerF (powerData z B a b)) (GaussianNameBounds.U decayF (decayData a b)))
  exact le_trans first (GaussianFastValueCut.query_budget _ _)

theorem upper_product_error (p s z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (ap2 powerF (clock p z B a b) (powerData z B a b)) (upperReference s a b))
      (ap2 productF p (productData z B a b))
      (num 4*powerBudget z B a b*unit p+unit s) (unit s*unit p) := by
  let k := clock p z B a b
  let U := powerBudget z B a b
  let x := ap2 powerF k (powerData z B a b)
  have hs := unit_positive (Γ := Γ) s
  have hk := unit_positive (Γ := Γ) k
  have hp := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ hs hk
  have estimate := GaussianApproximateInverseDistance.multiply_distance x (upperReference s a b)
    (ap2 decayF k (decayData a b)) U (num 4*unit k+unit s) (unit s*unit k) hd
    (GaussianNameBounds.sample_bound powerF (powerData z B a b) k
      (GaussianEulerIntegrandName.power_regular z B a b (old_source z R B a b h)))
    (upper_reference_error s k a b h.andE₂.andE₁.andE₂)
  have lifted := mul_le_mul_right (unit s*unit s) (power_clock_budget (Γ := Γ) p z B a b)
  have compare : Γ ⊢[PRAAx] le
      ((U*(num 4*unit k+unit s))*(unit s*unit p))
      ((num 4*U*unit p+unit s)*(unit s*unit k)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (num 4*U*unit k*unit s*unit p) lifted)
  exact distance_congr (.eqRefl _) (original_product p z B a b).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hd (positive_product _ _ hs hp) compare estimate)

theorem original_product_bound (p q z R B a b : PTm n) (h : Γ ⊢[PRAAx] source z R B a b) : Γ ⊢[PRAAx]
    bounded (ap2 productF p (productData z B a b))
      (majorant R*referenceTop q a b*unit p+num 3*referenceBottom q a b) (bottom p q a b) := by
  let P := unit p
  let D := referenceBottom q a b
  let A := majorant R*referenceTop q a b
  have hp := unit_positive (Γ := Γ) p
  have hd := reference_bottom_positive (Γ := Γ) q a b
  have both := GaussianEulerIntegrandName.original_power_times_decay z B a b (old_source z R B a b h)
  have metric := GaussianNameEquivalence.cross_at _ _ _ _ p p both
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 productF p (productData z B a b)) (sample p z B a b) two P :=
    distance_congr (.eqRefl _) (sample_at p z B a b).eqSymm (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ (P+P) (P*P) two P (positive_product _ _ hp hp) hp
        (le_of_eq_add (d := zero) (by ipra_ring)) metric)
  have target := GaussianEulerUpperTailPointwise.original_upper_tail_pointwise p q z R B a b h
  have result := GaussianReconstructionRoots.norm_from_distance _ _ two P (A*P+D) (D*P)
    hp (positive_product _ _ hd hp) near target
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hp (positive_product _ _ hd hp))
    (positive_product _ _ hd hp) (le_of_eq_add (d := zero) (by dsimp only [bottom,A,D,P]; ipra_ring)) result

theorem beta_row_slack (p q s z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (b*N)) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (row p z B a b N) (top p q R a b) (bottom p q a b)
      (num 4*powerBudget z B a b) s := by
  let k := clock p z B a b
  let x := ap2 powerF k (powerData z B a b)
  let v := upperReference s a b
  let P := unit p
  let S := unit s
  let D := referenceBottom q a b
  let A := majorant R*referenceTop q a b
  let U := powerBudget z B a b
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have hd := reference_bottom_positive (Γ := Γ) q a b
  have hf : Γ ⊢[PRAAx] GaussianBetaKernelRefinement.source a b N := .andI h.andE₂.andE₁.andE₂ (.andI hN ht)
  have result := GaussianReconstructionRoots.norm_from_distance (qmul x v) (ap2 productF p (productData z B a b))
    (num 4*U*P+S) (S*P) (A*P+num 3*D) (D*P)
    (positive_product _ _ hs hp) (positive_product _ _ hd hp)
    (upper_product_error p s z R B a b h) (original_product_bound p q z R B a b h)
  have larger : Γ ⊢[PRAAx] bounded (qmul x v)
      ((top p q R a b)*S+(num 4*U)*(bottom p q a b)) ((bottom p q a b)*S) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hs hp) (positive_product _ _ hd hp))
      (positive_product _ _ (positive_product _ _ hd hp) hs)
      (le_of_eq_add (d := zero) (by dsimp only [top,bottom,A,D,P,S,U]; ipra_ring)) result
  exact GaussianPositiveScalarProductBound.product_bound_monotone x (kernel a b N) v _ _
    (positive_product _ _ (positive_product _ _ hd hp) hs)
    (GaussianRationalReciprocal.power_canonical _ _) (RationalGaussianEmbedding.embed_canonical _)
    (GaussianBetaKernelRefinement.kernel_positive a b N hf) (RationalGaussianEmbedding.embed_axis _)
    (kernel_below_upper_reference s a b N hf) larger

/-- The exact original beta row has the same factorial half-decay
majorant as the Euler row, with four ordinary observation errors. -/
theorem original_beta_upper_tail_pointwise (p q z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (b*N)) : Γ ⊢[PRAAx]
    bounded (row p z B a b N) (top p q R a b) (bottom p q a b) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (num 4*powerBudget z B a b)
    (positive_product _ _ (reference_bottom_positive q a b) (unit_positive p))
    (beta_row_slack p q (GaussianRationalSlackRemoval.precision (row p z B a b N) (top p q R a b)
      (bottom p q a b) (num 4*powerBudget z B a b)) z R B a b N h hN ht)

theorem original_grid_row (p z B a b N : PTm n) : Γ ⊢[PRAAx]
    GaussianBetaKernelGridComparison.row p z B a b N ≐ row p z B a b N := .eqRefl _

def output (p q z R B a b N : PTm n) : PTm n := pairT (row p z B a b N)
  (pairT (kernel a b N) (pairT (top p q R a b) (bottom p q a b)))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (p q z R B a b N : PTm n) : PTm n := PTm.app outputF ![p,q,z,R,B,a,b,N]
theorem program_at (p q z R B a b N : PTm n) : Γ ⊢[PRAAx] run p q z R B a b N ≐ output p q z R B a b N := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![p,q,z,R,B,a,b,N]
theorem returned_row (p q z R B a b N : PTm n) : Γ ⊢[PRAAx] fstT (run p q z R B a b N) ≐ row p z B a b N :=
  (congrFst (program_at p q z R B a b N)).eqTrans (fst_pair _ _)
theorem returned_tail (p q z R B a b N : PTm n) : Γ ⊢[PRAAx] sndT (run p q z R B a b N) ≐
    pairT (kernel a b N) (pairT (top p q R a b) (bottom p q a b)) :=
  (congrSnd (program_at p q z R B a b N)).eqTrans (snd_pair _ _)
theorem returned_kernel (p q z R B a b N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run p q z R B a b N)) ≐ kernel a b N :=
  (congrFst (returned_tail p q z R B a b N)).eqTrans (fst_pair _ _)
theorem returned_radius (p q z R B a b N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run p q z R B a b N)) ≐
    pairT (top p q R a b) (bottom p q a b) :=
  (congrSnd (returned_tail p q z R B a b N)).eqTrans (snd_pair _ _)
theorem returned_top (p q z R B a b N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run p q z R B a b N))) ≐ top p q R a b :=
  (congrFst (returned_radius p q z R B a b N)).eqTrans (fst_pair _ _)
theorem returned_bottom (p q z R B a b N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run p q z R B a b N))) ≐ bottom p q a b :=
  (congrSnd (returned_radius p q z R B a b N)).eqTrans (snd_pair _ _)
theorem returned_bound (p q z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (b*N)) : Γ ⊢[PRAAx]
    bounded (fstT (run p q z R B a b N)) (fstT (sndT (sndT (run p q z R B a b N))))
      (sndT (sndT (sndT (run p q z R B a b N)))) :=
  bound_congr (returned_row p q z R B a b N).eqSymm (returned_top p q z R B a b N).eqSymm
    (returned_bottom p q z R B a b N).eqSymm (original_beta_upper_tail_pointwise p q z R B a b N h hN ht)

theorem original_weighted_beta_upper_tail_pointwise_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      (le one (var 7) ⋏ le (var 5) (var 6*var 7)) ⟶
      bounded (row (var 0) (var 2) (var 4) (var 5) (var 6) (var 7))
        (top (var 0) (var 1) (var 3) (var 5) (var 6)) (bottom (var 0) (var 1) (var 5) (var 6))) :=
  closeUniv 8 (.impI (.impI (original_beta_upper_tail_pointwise _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))
theorem actual_original_beta_grid_upper_tail_pointwise_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      (le one (var 7) ⋏ le (var 5) (var 6*var 7)) ⟶
      bounded (GaussianBetaKernelGridComparison.row (var 0) (var 2) (var 4) (var 5) (var 6) (var 7))
        (top (var 0) (var 1) (var 3) (var 5) (var 6)) (bottom (var 0) (var 1) (var 5) (var 6))) :=
  closeUniv 8 (.impI (.impI (original_beta_upper_tail_pointwise _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))
theorem actual_weighted_beta_upper_tail_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _)
theorem actual_returned_weighted_beta_upper_tail_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      (le one (var 7) ⋏ le (var 5) (var 6*var 7)) ⟶
      bounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))) :=
  closeUniv 8 (.impI (.impI (returned_bound _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

def scalarMajorant (p R a b : PTm n) : PTm n := RationalArithmetic.add
  (GaussianEulerUpperTailScalar.scalarMajorant p R a b) (fraction (num 3) (unit p))
def referenceBudget (R : PTm n) : PTm n := num 3*majorant R+num 4
@[simp] theorem subst_scalarMajorant {m : ℕ} (σ : Fin n → PTm m) (p R a b : PTm n) :
    Syn.subst σ (scalarMajorant p R a b) = scalarMajorant (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ a) (Syn.subst σ b) := by simp [scalarMajorant]
@[simp] theorem subst_referenceBudget {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (referenceBudget R) = referenceBudget (Syn.subst σ R) := by simp [referenceBudget]

theorem original_beta_cell_majorized (p z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (b*N)) : Γ ⊢[PRAAx]
    GaussianRationalSumMajorant.majorized (row p z B a b N) (scalarMajorant p R a b) := by
  let U := unit p
  let A := top p p R a b
  let D := bottom p p a b
  have hu := unit_positive (Γ := Γ) p
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (reference_bottom_positive p a b) hu
  have old : Γ ⊢[PRAAx] RationalArithmetic.represents (GaussianEulerUpperTailScalar.scalarMajorant p R a b)
      (ZT.ofNat (GaussianEulerUpperTailPointwise.majorantTop p p R a b)) D :=
    RationalIntegerNormalization.normalize_preserves_value _ _ hd
  have extra := RationalIntegerNormalization.normalize_preserves_value (Γ := Γ) (ZT.ofNat (num 3)) U hu
  have both := RationalRepresentations.represents_add _ _ _ _ _ _ old extra
  have rep : Γ ⊢[PRAAx] RationalArithmetic.represents (scalarMajorant p R a b) (ZT.ofNat (A*U)) (D*U) :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
      dsimp only [A,D,top,bottom,GaussianEulerUpperTailPointwise.majorantTop,
        GaussianEulerUpperTailPointwise.majorantBottom]
      ipra_simps
      ring) (.eqRefl _) both
  have den := positive_product _ _ hd hu
  exact GaussianRationalSumMajorant.from_representation _ _ _ _ den
    (GaussianRationalL1.nonnegative_of_representation _ _ _ den rep) rep
    (bounded_radius_mono _ _ _ _ _ hd den (le_of_eq_add (d := zero) (by ipra_ring))
      (original_beta_upper_tail_pointwise p p z R B a b N h hN ht))

theorem scalar_majorant_reference_error (p R a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    distanceBounded (embed (scalarMajorant p R a b))
      (qmul (GaussianDominantPairAlgebra.radiusPoint (majorant R) one) (GaussianEulerWeightedHalfDecay.halfSample p a b))
      (referenceBudget R) (unit p) := by
  let old := embed (GaussianEulerUpperTailScalar.scalarMajorant p R a b)
  let extra := embed (fraction (num 3) (unit p))
  have hu := unit_positive (Γ := Γ) p
  have value : Γ ⊢[PRAAx] extra ≐ GaussianDominantPairAlgebra.radiusPoint (num 3) (unit p) :=
    (GaussianEulerDecayOrder.fraction_embedding _ _ hu).eqTrans
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ hu)
  have extraBound : Γ ⊢[PRAAx] bounded extra (num 3) (unit p) :=
    bound_congr value.eqSymm (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded _ _ hu)
  have near : Γ ⊢[PRAAx] distanceBounded (embed (scalarMajorant p R a b)) old (num 3) (unit p) :=
    bound_congr ((qsub_congr (RationalGaussianEmbedding.embed_add _ _) (.eqRefl old)).eqTrans
      (GaussianRationalSyntheticDivision.qadd_sub_cancel old extra (RationalGaussianEmbedding.embed_canonical _))).eqSymm
      (.eqRefl _) (.eqRefl _) extraBound
  have far := GaussianEulerUpperTailScalar.scalar_majorant_scaled_reference_error p R a b hb
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold referenceBudget GaussianEulerUpperTailScalar.budget; ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hu near far)

theorem original_beta_cell_scalar_majorant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      (le one (var 6) ⋏ le (var 4) (var 5*var 6)) ⟶
      GaussianRationalSumMajorant.majorized (row (var 0) (var 1) (var 3) (var 4) (var 5) (var 6))
        (scalarMajorant (var 0) (var 2) (var 4) (var 5))) :=
  closeUniv 7 (.impI (.impI (original_beta_cell_majorized _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0.andE₁ Prf.hyp0.andE₂)))
theorem actual_beta_scalar_majorant_half_decay_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (embed (scalarMajorant (var 0) (var 1) (var 2) (var 3)))
      (qmul (GaussianDominantPairAlgebra.radiusPoint (majorant (var 1)) one)
        (GaussianEulerWeightedHalfDecay.halfSample (var 0) (var 2) (var 3))) (referenceBudget (var 1)) (unit (var 0))) :=
  closeUniv 4 (.impI (scalar_majorant_reference_error _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelUpperTail
