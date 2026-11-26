import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalSigns
import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalRescale
import IPRADerivations.Analysis.Gamma.CriticalPoints.GaussianGammaNegativeCriticalSlope
import IPRADerivations.Core.Search

/-!
# Actual bounded search on the truncated negative digamma interval

Subdivide the paper's pole-separated interval by a dyadic refinement.
The rational sign test uses the original shifted name at the common
observation clock. Bounded search selects a negative left sample and
a nonnegative adjacent right sample. Their exact upper slope gives
an explicit residual at the selected negative rational location.
-/

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaDigammaCriticalSigns (quarter negativeQuarter)
open GaussianGammaDigammaDyadicMesh (clock grid grid_threshold)
open GaussianGammaDigammaGridSign (negative_from_upper nonnegative_from_upper near_zero_left)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalCorrectionSlope (domain)
open GaussianGammaNegativeCriticalEndpoints (mesh mesh_minimum rightNumerator right_add nameF nameData)
open GaussianGammaNegativeCriticalSigns (leftData rightData left_named_margin right_named_margin)
open GaussianGammaNegativeCriticalSlope (coefficient cap upper_at)
open GaussianEulerPowerChartTimeOrder (order_trans)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianNamedPositiveExponentialOrder (real_order_at)
open GaussianNamedRealOrderTransport (transport)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianPositiveRealArithmetic (sign)
open GaussianRationalHorner (scalar_congr positive_product)
open GaussianRationalMetric (qsub qnegative qnegative_canonical)
open GaussianRationalSyntheticDivision (qzero_add)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order)
open RationalArithmetic (represents)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalGaussianEmbedding (scalarZero)
open RationalSupMetric (numeratorOf)
open RationalValueBounds (upper upper_congr radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def denominator (p N : PTm n) : PTm n := unit p*mesh N
def numerator (p i : PTm n) : PTm n := unit p+i
def span (p N : PTm n) : PTm n := unit p*monus (mesh N) two
def sample (p N i : PTm n) : PTm n := fstT (ap2 nameF (clock p) (nameData (numerator p i) (denominator p N) N))

def test (p N i : PTm n) : PTm n := monus (numeratorOf (sample p N i)).neg (numeratorOf (sample p N i)).pos
def testBody : PTm 2 := test (fstT (var 1)) (sndT (var 1)) (var 0)
def first (p N : PTm n) : PTm n := Search.mu testBody (succ (span p N)) (pairT p N)
def leftIndex (p N : PTm n) : PTm n := pred (first p N)
def location (p N : PTm n) : PTm n :=
  qsub (fraction (numerator p (leftIndex p N)) (denominator p N)) (fraction (succ N) one)
def locationF : PR 2 := PTm.toPR (location (var 0) (var 1))

@[simp] theorem subst_denominator {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (denominator p N) = denominator (Syn.subst σ p) (Syn.subst σ N) := by simp [denominator]
@[simp] theorem subst_numerator {k : ℕ} (σ : Fin n → PTm k) (p i : PTm n) :
    Syn.subst σ (numerator p i) = numerator (Syn.subst σ p) (Syn.subst σ i) := by simp [numerator]
@[simp] theorem subst_span {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (span p N) = span (Syn.subst σ p) (Syn.subst σ N) := by simp [span]
@[simp] theorem subst_sample {k : ℕ} (σ : Fin n → PTm k) (p N i : PTm n) :
    Syn.subst σ (sample p N i) = sample (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ i) := by simp [sample]
@[simp] theorem subst_test {k : ℕ} (σ : Fin n → PTm k) (p N i : PTm n) :
    Syn.subst σ (test p N i) = test (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ i) := by simp [test,numeratorOf]
@[simp] theorem subst_first {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (first p N) = first (Syn.subst σ p) (Syn.subst σ N) := by simp [first]
@[simp] theorem subst_leftIndex {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (leftIndex p N) = leftIndex (Syn.subst σ p) (Syn.subst σ N) := by simp [leftIndex]
@[simp] theorem subst_location {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (location p N) = location (Syn.subst σ p) (Syn.subst σ N) := by simp [location]

theorem location_at (p N : PTm n) : Γ ⊢[PRAAx] ap2 locationF p N ≐ location p N := by
  simpa only [locationF,ap2,subst_location,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (toPR_eq (Γ := Γ) (location (var 0) (var 1) : PTm 2) ![p,N])

theorem room (p N i : PTm n) (hi : Γ ⊢[PRAAx] le i (span p N)) :
    Γ ⊢[PRAAx] le (numerator p i+unit p) (denominator p N) := by
  have h : Γ ⊢[PRAAx] le two (mesh N) := le_trans (by ipra_le 6) (mesh_minimum N)
  have e := natEq (eq_add_of_le h)
  dsimp only [numerator,denominator,span] at *
  ipra_le sl hi with 𝔞(unit p)*e

theorem grid_guard (p N i : PTm n) (hi : Γ ⊢[PRAAx] le i (span p N)) :
    Γ ⊢[PRAAx] guard (numerator p i) (denominator p N) := by
  have hp := unit_positive (Γ := Γ) p
  exact .andI (le_trans hp (le_add_right _ _))
    (le_trans (by ipra_le sl hp) (room p N i hi))

private theorem name_data_congr {a a' b b' N : PTm n}
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] nameData a b N ≐ nameData a' b' N := by
  simpa only [GaussianGammaNegativeCriticalEndpoints.subst_nameData,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (nameData (var 0) (var 1) (var 2) : PTm 3) (σ := ![a,b,N]) (σ' := ![a',b',N])
      (fun j => by fin_cases j; exacts [ha,hb,.eqRefl _])

private theorem left_cross (p N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (nameData (numerator p zero) (denominator p N) N) (leftData N) :=
  GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF _ _ _ _
    (name_data_congr (by unfold numerator; ipra_ring) (.eqRefl _)) (.eqRefl _)
    (GaussianGammaNegativeCriticalRescale.original_rescale one (mesh N) N (unit p)
      (GaussianGammaNegativeCriticalEndpoints.left_guard N) (unit_positive p))

private theorem right_cross (p N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (nameData (numerator p (span p N)) (denominator p N) N) (rightData N) := by
  have h : Γ ⊢[PRAAx] le two (mesh N) := le_trans (by ipra_le 6) (mesh_minimum N)
  have e := natEq (eq_add_of_le h)
  have e' := natEq (right_add (Γ := Γ) N)
  have ha : Γ ⊢[PRAAx] unit p*rightNumerator N ≐ numerator p (span p N) := by
    unfold numerator span
    apply deriveNat
    ipra_simps
    linear_combination 𝔞(unit p)*(e-e')
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF _ _ _ _
    (name_data_congr ha (.eqRefl _)) (.eqRefl _)
    (GaussianGammaNegativeCriticalRescale.original_rescale (rightNumerator N) (mesh N) N (unit p)
      (GaussianGammaNegativeCriticalEndpoints.right_guard N) (unit_positive p))

private theorem quarter_represents :
    Γ ⊢[PRAAx] represents (fstT (quarter : PTm n)) (ZT.ofNat one) (num 4) :=
  GaussianGammaDigammaHarmonicCells.point_fraction_represents one (num 4) (by ipra_le 3)

private theorem negative_quarter_represents :
    Γ ⊢[PRAAx] represents (fstT (negativeQuarter : PTm n)) (-ZT.ofNat one) (num 4) := by
  have e : Γ ⊢[PRAAx] negativeQuarter ≐ qnegative (quarter : PTm n) := qzero_add _ (qnegative_canonical quarter)
  exact scalar_congr ((congrFst e).eqTrans (fst_pair _ _)).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalRepresentations.represents_negative _ _ _ quarter_represents)

theorem endpoint_signs (p N : PTm n) : Γ ⊢[PRAAx]
    neg (sign (sample p N zero)) ⋏ sign (sample p N (span p N)) := by
  let P : PTm n := fraction (num 5) one
  let t := clock p
  let x := nameData (numerator p zero) (denominator p N) N
  let y := nameData (numerator p (span p N)) (denominator p N) N
  have h : Γ ⊢[PRAAx] rationalLE (fstT (quarter : PTm n)) (fstT P) :=
    fractions_order one (num 4) (num 5) one (by ipra_le 3) (le_refl _) (by ipra_le 19)
  have e : Γ ⊢[PRAAx] negativeQuarter ≐ qnegative (quarter : PTm n) := qzero_add _ (qnegative_canonical quarter)
  have l := constant_order (qnegative P) negativeQuarter
    (rationalLE_congr (fst_pair _ _).eqSymm ((congrFst e).eqTrans (fst_pair _ _)).eqSymm
      (RationalAlgebra.negative_antitone _ _ h))
  have r := constant_order quarter P h
  have nl := order_trans _ _ _ _ _ _ (left_named_margin N) l
  have nr := order_trans _ _ _ _ _ _ r (right_named_margin N)
  have lt := transport nameF nameF constantF constantF x (leftData N) negativeQuarter negativeQuarter
    (left_cross p N) (cross_refl _ _ (constant_regular _)) nl
  have rt := transport constantF constantF nameF nameF quarter quarter (rightData N) y
    (cross_refl _ _ (constant_regular _)) (cross_symm _ _ _ _ (right_cross p N)) nr
  exact .andI
    (negative_from_upper _ _ (grid p) (grid_threshold p) negative_quarter_represents
      (upper_congr (.eqRefl _) (congrFst (constant_at t negativeQuarter)) (.eqRefl _) (.eqRefl _)
        (real_order_at nameF constantF x negativeQuarter t t lt)))
    (nonnegative_from_upper _ _ (grid p) (grid_threshold p) quarter_represents
      (upper_congr (congrFst (constant_at t quarter)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (real_order_at constantF nameF quarter y t t rt)))

private theorem test_congr {p p' N N' i i' : PTm n} (hp : Γ ⊢[PRAAx] p ≐ p')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hi : Γ ⊢[PRAAx] i ≐ i') :
    Γ ⊢[PRAAx] test p N i ≐ test p' N' i' := by
  simpa only [subst_test,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (test (var 0) (var 1) (var 2) : PTm 3) (σ := ![p,N,i]) (σ' := ![p',N',i'])
      (fun j => by fin_cases j; exacts [hp,hN,hi])

theorem body_at (p N i : PTm n) : Γ ⊢[PRAAx] inst2 testBody i (pairT p N) ≐ test p N i := by
  simpa only [inst2,testBody,subst_test,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one] using
    test_congr (fst_pair (Γ := Γ) p N) (snd_pair p N) (.eqRefl i)

theorem selected (p N : PTm n) : Γ ⊢[PRAAx]
    lt (leftIndex p N) (span p N) ⋏
      (neg (sign (sample p N (leftIndex p N))) ⋏ sign (sample p N (succ (leftIndex p N)))) := by
  let J := first p N
  let i := leftIndex p N
  let S := span p N
  have ends := endpoint_signs (Γ := Γ) p N
  have stop : Γ ⊢[PRAAx] test p N S ≐ zero := ends.andE₂
  have found := Search.search_found (N := succ S) ((body_at p N S).eqTrans stop) (le_refl (succ S))
  have hit : Γ ⊢[PRAAx] test p N J ≐ zero := (body_at p N J).eqSymm.eqTrans found.andE₂.andE₁
  have e : Γ ⊢[PRAAx] J ≐ succ i := by
    refine .orE (zero_or_succ J) ?_ Prf.hyp0
    have bad : (J ≐ zero) :: Γ ⊢[PRAAx] test p N zero ≐ zero :=
      (test_congr (.eqRefl _) (.eqRefl _) Prf.hyp0).eqSymm.eqTrans hit.wk
    exact .botE _ (.impE ends.andE₁.wk bad)
  have bound : Γ ⊢[PRAAx] lt i S := le_congr e (.eqRefl _) found.andE₂.andE₂
  have before : Γ ⊢[PRAAx] lt i J := lt_congr (.eqRefl _) e.eqSymm (le_refl _)
  have minimal := Search.search_minimal (f := testBody) (N := succ S) (x := pairT p N) before
  have neg_i : Γ ⊢[PRAAx] neg (sign (sample p N i)) :=
    .impI (.impE minimal.wk ((body_at p N i).wk.eqTrans Prf.hyp0))
  exact .andI bound (.andI neg_i ((test_congr (.eqRefl _) (.eqRefl _) e).eqSymm.eqTrans hit))

theorem adjacent_domain (p N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (span p N)) :
    Γ ⊢[PRAAx] domain (numerator p i) (numerator p (succ i)) (denominator p N) (mesh N) := by
  let a := numerator p i
  let c := numerator p (succ i)
  let b := denominator p N
  let K := mesh N
  have hA := (grid_guard p N i (le_of_lt hi)).andE₁
  have hc := (grid_guard p N (succ i) hi).andE₂
  have hAC : Γ ⊢[PRAAx] le a c := by dsimp only [a,c,numerator]; ipra_le 1
  have e := natEq (eq_add_of_le (le_of_lt hc))
  have margin : Γ ⊢[PRAAx] le (unit p) (monus b c) := by
    have hr : Γ ⊢[PRAAx] le (c+unit p) b := room p N (succ i) hi
    ipra_le sl hr with -e
  exact .andI (.andI hA (.andI hAC hc)) (.andI
    (by dsimp only [b,K,a,denominator,numerator]; ipra_le 𝔞(mesh N)*𝔞(i))
    (by dsimp only [b,K,denominator] at *; ipra_le 𝔞(mesh N)*sl margin))

theorem adjacent_upper (p N i : PTm n) (hi : Γ ⊢[PRAAx] lt i (span p N)) :
    Γ ⊢[PRAAx] upper (sample p N (succ i)) (sample p N i)
      (rateNumerator (coefficient N (mesh N)) (denominator p N) (clock p) (clock p))
      (rateDenominator (denominator p N) (clock p) (clock p)) := by
  let a := numerator p i
  let c := numerator p (succ i)
  let b := denominator p N
  let K := mesh N
  let t := clock p
  have ac : Γ ⊢[PRAAx] c ≐ one+a := by dsimp only [a,c,numerator]; ipra_ring
  have gap := (congrMonus ac (.eqRefl _)).eqTrans (add_monus _ _)
  refine upper_congr (.eqRefl _) (.eqRefl _) ?_ (.eqRefl _) (upper_at t t a c b N K (adjacent_domain p N i hi))
  unfold rateNumerator cap
  have e := natEq gap
  apply deriveNat
  ipra_simps
  linear_combination 𝔞(coefficient N K)*𝔞(unit t)^2*e

theorem residual_at (p N : PTm n) : Γ ⊢[PRAAx]
    radius (sample p N (leftIndex p N)) scalarZero
      (rateNumerator (coefficient N (mesh N)) (denominator p N) (clock p) (clock p))
      (rateDenominator (denominator p N) (clock p) (clock p)) := by
  have h := selected (Γ := Γ) p N
  exact near_zero_left _ _ _ _ h.andE₂.andE₁ h.andE₂.andE₂ (adjacent_upper p N _ h.andE₁)

theorem residual_bound (p N : PTm n) : Γ ⊢[PRAAx]
    radius (sample p N (leftIndex p N)) scalarZero
      (coefficient N (mesh N)+mesh N) (denominator p N) := by
  let B := denominator p N
  let M := mesh N
  let U := unit (clock p)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive (clock p)
  have hM : Γ ⊢[PRAAx] le one M := le_trans (by ipra_le 7) (mesh_minimum N)
  have hB : Γ ⊢[PRAAx] le one B := positive_product _ _ (unit_positive p) hM
  have e := natEq (show Γ ⊢[PRAAx] U ≐ num 64*unit p from GaussianGammaDigammaDyadicMesh.grid_scale p)
  have spare : Γ ⊢[PRAAx] le (two*B) (M*U) := by
    dsimp only [M,B,denominator]
    ipra_le 62*𝔞(mesh N)*𝔞(unit p) with 𝔞(mesh N)*e
  exact RationalValueBounds.radius_mono _ _ _ _ _ _
    (GaussianNamedInverseRate.denominator_positive B (clock p) (clock p) hB) (residual_at p N)
    (by dsimp only [rateNumerator,rateDenominator]; ipra_le 𝔞(B)*𝔞(U)*sl spare)

theorem original_shifted_negative_digamma_grid_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (leftIndex (var 0) (var 1)) (span (var 0) (var 1)) ⋏
      (neg (sign (sample (var 0) (var 1) (leftIndex (var 0) (var 1)))) ⋏
        sign (sample (var 0) (var 1) (succ (leftIndex (var 0) (var 1)))))) :=
  closeUniv 2 (selected _ _)

theorem original_shifted_negative_digamma_grid_residual_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (radius (sample (var 0) (var 1) (leftIndex (var 0) (var 1))) scalarZero
      (coefficient (var 1) (mesh (var 1))+mesh (var 1)) (denominator (var 0) (var 1))) :=
  closeUniv 2 (residual_bound _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalGrid
