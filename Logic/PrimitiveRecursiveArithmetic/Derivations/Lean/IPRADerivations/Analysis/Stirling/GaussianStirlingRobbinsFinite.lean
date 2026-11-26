import IPRADerivations.Analysis.Stirling.GaussianStirlingGlobalBoundsFinite

/-!
# The finite Robbins lower bound for the original Stirling endpoints

The first difference retains the explicit positive Robbins margin.
After it, the lower rational telescoper bounds every difference.
The approximation errors from the finite sum disappear in named order.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingRobbinsFinite

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianStirlingDifferenceBounds (robbins_sample_lower)
open GaussianStirlingGlobalBoundsFinite (swap_suffix raw_first raw_step)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers
  (lowerDifference lowerMargin lower_den_positive small_numeral_positive)
open GaussianStirlingTailComparison (point_add_upper_same point_add_order point_order_refl)
open GaussianStirlingTelescope (rawSum shifted shifted_source)
open RationalArgmin (rationalLE_congr)
open RationalValueBounds (upper upper_congr upper_mono upper_order_left)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianStirlingDifference.nameF
local notation "DD" => GaussianStirlingDifference.data
local notation "A" => GaussianStirlingNames.nameF
local notation "G" => GaussianNamedDifference.nameF A A

def lowerCap (N a b : PTm n) : PTm n := qadd (lowerDifference a b (succ N)) (lowerMargin a b)
@[simp] theorem subst_lowerCap {l : ℕ} (σ : Fin n → PTm l) (N a b : PTm n) :
    Syn.subst σ (lowerCap N a b) = lowerCap (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by simp [lowerCap]

private theorem lower_step (a b N : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (lowerDifference a b N) (lowerDifference (shifted a b N) b one) ≐ lowerDifference a b (succ N) := by
  let c := shifted a b N
  let X := num 12*a+b
  let Y := num 12*c+b
  let Z := num 12*(c+b*one)+b
  let W := num 12*(a+b*succ N)+b
  have ha' := le_trans ha (le_add_right a (b*N))
  have hz' := le_trans ha' (le_add_right c (b*one))
  have hw' := le_trans ha (le_add_right a (b*succ N))
  have hx : Γ ⊢[PRAAx] le one X := lower_den_positive a b ha
  have hy : Γ ⊢[PRAAx] le one Y := lower_den_positive c b ha'
  have hz : Γ ⊢[PRAAx] le one Z := lower_den_positive (c+b*one) b hz'
  have hw : Γ ⊢[PRAAx] le one W := lower_den_positive (a+b*succ N) b hw'
  have g := GaussianEulerPositivePowerChartCorrectedImage.fraction_sum (num 12*b*b*N) (X*Y) (num 12*b*b*one) (Y*Z)
    (positive_product _ _ hx hy) (positive_product _ _ hy hz)
  exact g.eqTrans (GaussianStirlingRationalTelescopers.fraction_same _ _ _ _
    (positive_product _ _ (positive_product _ _ hx hy) (positive_product _ _ hy hz))
    (positive_product _ _ hx hw) (by dsimp [X,Y,Z,W,c,shifted]; ipra_ring))

private theorem lower_succ (N a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (lowerCap N a b) (lowerDifference (shifted a b (succ N)) b one) ≐ lowerCap (succ N) a b :=
  (swap_suffix _ _ _).eqTrans (qadd_congr (lower_step a b (succ N) ha) (.eqRefl _))

private theorem weak_lower (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] upper (fstT (lowerDifference a b one)) (fstT (ap2 D p (DD a b))) one (unit p) := by
  let M := lowerMargin a b
  let L := lowerDifference a b one
  let Z : PTm n := GaussianRationalHorner.qzero
  let E := num 3*GaussianStirlingRationalTelescopers.denominatorSquare a b*(num 12*a+b)*(num 12*a+num 13*b)
  have hW := GaussianStirlingRationalTelescopers.square_positive a b hs.andE₂
  have hX := lower_den_positive a b hs.andE₁
  have hY : Γ ⊢[PRAAx] le one (num 12*a+num 13*b) :=
    le_trans (GaussianStirlingRationalTelescopers.upper_den_positive a hs.andE₁) (le_add_right _ _)
  have hE := positive_product _ _ (positive_product _ _ (positive_product _ _ (small_numeral_positive 2) hW) hX) hY
  have nonneg := (GaussianRationalNonnegativeFractions.fraction_nonnegative
    (b*b*b*LeanProofs.IPRA.PTm.monus (num 24*a) (num 23*b)) E hE).andE₁
  have mz := rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _) nonneg
  have mono := point_add_order L L Z M (point_order_refl L) mz
  have den := positive_product _ _ hX (lower_den_positive (a+b*one) b (le_trans hs.andE₁ (le_add_right _ _)))
  have cl : Γ ⊢[PRAAx] GaussianRationalHorner.canonical L := GaussianRationalHorner.ofGaussian_canonical _ _ den
  exact upper_order_left _ _ _ _ _
    (rationalLE_congr (congrFst (GaussianReciprocalHorner.qadd_zero_right L cl)) (.eqRefl _) mono)
    (robbins_sample_lower p a b hs hba)

def rawLower (p N a b : PTm n) : Fm PTm n :=
  upper (fstT (lowerCap N a b)) (fstT (rawSum p (succ N) a b)) (succ N) (unit p)
@[simp] theorem subst_rawLower {l : ℕ} (σ : Fin n → PTm l) (p N a b : PTm n) :
    (rawLower p N a b).subst σ = rawLower (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [rawLower]

private theorem raw_succ (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (h : Γ ⊢[PRAAx] rawLower p N a b) : Γ ⊢[PRAAx] rawLower p (succ N) a b := by
  let c := shifted a b (succ N)
  have hbc : Γ ⊢[PRAAx] le b c := le_trans hba (le_add_right _ _)
  have cell := weak_lower p c b (shifted_source a b (succ N) hs) hbc
  have add := point_add_upper_same (lowerCap N a b) (rawSum p (succ N) a b)
    (lowerDifference c b one) (ap2 D p (DD c b)) (succ N) one (unit p) (unit_positive p) h cell
  exact upper_congr (congrFst (lower_succ N a b hs.andE₁)) (congrFst (raw_step p (succ N) a b).eqSymm)
    (succ_eq_add_one (succ N)).eqSymm (.eqRefl _) add

theorem raw_lower (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] rawLower p N a b := by
  let sh (x : PTm n) := Syn.shift x
  have hall : Γ ⊢[PRAAx] .all (rawLower (sh p) (var 0) (sh a) (sh b)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [subst_rawLower,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact upper_congr (.eqRefl _) (congrFst (raw_first p a b).eqSymm) (.eqRefl _) (.eqRefl _) (robbins_sample_lower p a b hs hba)
    · simp only [subst_rawLower,sh,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ := rawLower (sh p) (var 0) (sh a) (sh b) :: Γ.map Fm.shift
      have hs' : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.wk
      have hb' : Δ ⊢[PRAAx] le (sh b) (sh a) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hba.shift.wk
      exact raw_succ _ _ _ _ hs' hb' Prf.hyp0
  simpa only [subst_rawLower,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE N

private theorem observation (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (lowerCap N a b)))
      (fstT (ap2 GaussianStirlingTelescopeName.nameF p (GaussianStirlingTelescopeName.data (succ N) a b))) (succ N) (unit p) := by
  let K := succ N
  let q := GaussianFastValueCut.exponent K p
  have h := raw_lower q N a b hs hba
  have e := congrFst (GaussianStirlingTelescopeName.name_at (Γ := Γ) p K a b).eqSymm
  have m := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right p (GaussianFastValueCut.normalizer K))
  have cmp := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right K m)
  exact upper_congr (congrFst (constant_at p (lowerCap N a b)).eqSymm) e (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (unit_positive q) h cmp)

theorem lower_endpoint (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    realOrder constantF G (lowerCap N a b) (GaussianStirlingTelescopeName.endpointData (succ N) a b) := by
  let F := GaussianStirlingTelescopeName.nameF
  let X := GaussianStirlingTelescopeName.data (succ N) a b
  let sh (x : PTm n) := Syn.shift x
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have hb : Δ ⊢[PRAAx] le (sh b) (sh a) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hba.shift
  have l : Γ ⊢[PRAAx] envelope constantF F (lowerCap N a b) X (succ N) := by
    refine .allI ?_
    simpa [envelope,sh,Syn.shift,Δ,F,X] using observation (var 0) (sh N) (sh a) (sh b) h hb
  have hl := constant_regular (Γ := Γ) (lowerCap N a b)
  have hx := GaussianStirlingTelescopeName.name_regular (succ N) a b hs
  have e := GaussianStirlingTelescopeName.telescope_cross (succ N) a b hs
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_refl _ _ hl) e
    (order_from_envelope _ _ _ _ _ hl hx l)

end LeanProofs.IPRA.Analysis.GaussianStirlingRobbinsFinite
