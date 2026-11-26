import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingDifferenceBounds

/-!
# Finite Stirling endpoint bounds with the first margin

The first difference retains its two sharp odd-series bounds. Later
differences are nonnegative and are bounded by the elementary upper
telescoper. The resulting bounds apply to the actual named endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsFinite

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianRationalHorner (canonical qadd qzero positive_product)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qzero_add)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalLinearProduct (qadd_commutative)
open GaussianStirlingDifferenceBounds (first_sample_lower sharp_sample_upper weak_local_bounds)
open GaussianStirlingFiniteTelescopeBounds (upper_step)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers
  (firstTerm upperDifference upperMargin geometricMain small_numeral_positive square_positive gap)
open GaussianStirlingTailComparison (point_add_upper_same sharpUpperValue)
open GaussianStirlingTelescope (rawSum shifted shifted_source dBody d_at sampleData)
open RationalValueBounds (upper upper_congr upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "D" => GaussianStirlingDifference.nameF
local notation "DD" => GaussianStirlingDifference.data
local notation "A" => GaussianStirlingNames.nameF
local notation "G" => GaussianNamedDifference.nameF A A

def upperCap (N a b : PTm n) : PTm n := qsub (upperDifference a b (succ N)) (upperMargin a b)

ipra_subst upperCap

theorem swap_suffix (a b c : PTm n) :
    Γ ⊢[PRAAx] qadd (qadd a b) c ≐ qadd (qadd a c) b :=
  (qadd_associative a b c).eqTrans
    ((qadd_congr (.eqRefl _) (qadd_commutative b c)).eqTrans (qadd_associative a c b).eqSymm)

theorem raw_step (p N a b : PTm n) : Γ ⊢[PRAAx]
    rawSum p (succ N) a b ≐ qadd (rawSum p N a b) (ap2 D p (DD (shifted a b N) b)) :=
  (GaussianRationalFiniteSum.sum_succ dBody N (sampleData p a b)).eqTrans
    (qadd_congr (.eqRefl _) (d_at p a b N))

theorem raw_first (p a b : PTm n) : Γ ⊢[PRAAx] rawSum p one a b ≐ ap2 D p (DD a b) := by
  have data : Γ ⊢[PRAAx] DD (shifted a b zero) b ≐ DD a b := by
    have h := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (DD (var 0) (var 1) : PTm 2)
      (σ := ![shifted a b zero,b]) (σ' := ![a,b]) (fun i => by
        fin_cases i
        · dsimp [shifted]; ipra_ring
        · exact .eqRefl _)
    simpa using h
  have canon : Γ ⊢[PRAAx] canonical (ap2 D p (DD a b)) :=
    GaussianNameArithmetic.add_canonical _ _ _ _ _
  exact (raw_step p zero a b).eqTrans ((qadd_congr (GaussianRationalFiniteSum.sum_zero dBody (sampleData p a b))
    (congrAp2 D (.eqRefl _) data)).eqTrans (qzero_add _ canon))

private theorem upper_first (a b : PTm n) : Γ ⊢[PRAAx] upperCap zero a b ≐ sharpUpperValue a b := by
  apply qsub_congr ?_ (.eqRefl _)
  apply GaussianCompactRiemannName.fraction_congr
  · ipra_ring
  · unfold gap
    ipra_ring

private theorem upper_succ (N a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) :
    Γ ⊢[PRAAx] qadd (upperCap N a b) (geometricMain (shifted a b (succ N)) b) ≐ upperCap (succ N) a b :=
  (swap_suffix _ _ _).eqTrans (qadd_congr (upper_step a b (succ N) ha) (.eqRefl _))

def rawBounds (p N a b : PTm n) : Fm PTm n :=
  upper (fstT (firstTerm a b)) (fstT (rawSum p (succ N) a b)) (succ N) (unit p) ⋏
    upper (fstT (rawSum p (succ N) a b)) (fstT (upperCap N a b)) (succ N) (unit p)

ipra_subst rawBounds

private theorem raw_zero (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] rawBounds p zero a b :=
  .andI (upper_congr (.eqRefl _) (congrFst (raw_first p a b).eqSymm) (.eqRefl _) (.eqRefl _) (first_sample_lower p a b hs))
    (upper_congr (congrFst (raw_first p a b).eqSymm) (congrFst (upper_first a b).eqSymm)
      (.eqRefl _) (.eqRefl _) (sharp_sample_upper p a b hs))

private theorem raw_succ (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (prev : Γ ⊢[PRAAx] rawBounds p N a b) : Γ ⊢[PRAAx] rawBounds p (succ N) a b := by
  let X := firstTerm a b
  let E := shifted a b (succ N)
  let Y := rawSum p (succ N) a b
  let Z := ap2 D p (DD E b)
  have h := weak_local_bounds p E b (shifted_source a b (succ N) hs)
  have low := point_add_upper_same X Y qzero Z (succ N) one (unit p) (unit_positive p) prev.andE₁ h.andE₁
  have high := point_add_upper_same Y (upperCap N a b) Z (geometricMain E b) (succ N) one (unit p) (unit_positive p)
    prev.andE₂ h.andE₂
  have cX : Γ ⊢[PRAAx] canonical X :=
    GaussianRationalHorner.ofGaussian_canonical _ _
      (positive_product _ _ (small_numeral_positive 2) (square_positive a b hs.andE₂))
  have e := congrFst (raw_step (Γ := Γ) p (succ N) a b).eqSymm
  have r := (succ_eq_add_one (Γ := Γ) (succ N)).eqSymm
  exact .andI (upper_congr (congrFst (GaussianReciprocalHorner.qadd_zero_right X cX)) e r (.eqRefl _) low)
    (upper_congr e (congrFst (upper_succ N a b hs.andE₁)) r (.eqRefl _) high)

theorem raw_bounds (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] rawBounds p N a b := by
  let sh (x : PTm n) := Syn.shift x
  have hall : Γ ⊢[PRAAx] .all (rawBounds (sh p) (var 0) (sh a) (sh b)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simpa only [subst_rawBounds,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using raw_zero p a b hs
    · simp only [subst_rawBounds,sh,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let Δ := rawBounds (sh p) (var 0) (sh a) (sh b) :: Γ.map Fm.shift
      have h : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.wk
      exact raw_succ _ _ _ _ h Prf.hyp0
  simpa only [subst_rawBounds,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE N

def endpointBounds (N a b : PTm n) : Fm PTm n :=
  realOrder constantF G (firstTerm a b) (GaussianStirlingTelescopeName.endpointData (succ N) a b) ⋏
  realOrder G constantF (GaussianStirlingTelescopeName.endpointData (succ N) a b) (upperCap N a b)

private theorem observations (p N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p (firstTerm a b)))
      (fstT (ap2 GaussianStirlingTelescopeName.nameF p (GaussianStirlingTelescopeName.data (succ N) a b))) (succ N) (unit p) ⋏
    upper (fstT (ap2 GaussianStirlingTelescopeName.nameF p (GaussianStirlingTelescopeName.data (succ N) a b)))
      (fstT (ap2 constantF p (upperCap N a b))) (succ N) (unit p) := by
  let K := succ N
  let q := GaussianFastValueCut.exponent K p
  have h := raw_bounds q N a b hs
  have e := congrFst (GaussianStirlingTelescopeName.name_at (Γ := Γ) p K a b).eqSymm
  have m := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right p (GaussianFastValueCut.normalizer K))
  have cmp := le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right K m)
  exact .andI
    (upper_congr (congrFst (constant_at p (firstTerm a b)).eqSymm) e (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (unit_positive q) h.andE₁ cmp))
    (upper_congr e (congrFst (constant_at p (upperCap N a b)).eqSymm) (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (unit_positive q) h.andE₂ cmp))

theorem endpoint_bounds (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] endpointBounds N a b := by
  let F := GaussianStirlingTelescopeName.nameF
  let X := GaussianStirlingTelescopeName.data (succ N) a b
  let L := firstTerm a b
  let U := upperCap N a b
  let sh (x : PTm n) := Syn.shift x
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have l : Γ ⊢[PRAAx] envelope constantF F L X (succ N) := by
    refine .allI ?_
    simpa [envelope,sh,Syn.shift,Δ,F,L,X] using (observations (var 0) (sh N) (sh a) (sh b) h).andE₁
  have u : Γ ⊢[PRAAx] envelope F constantF X U (succ N) := by
    refine .allI ?_
    simpa [envelope,sh,Syn.shift,Δ,F,U,X] using (observations (var 0) (sh N) (sh a) (sh b) h).andE₂
  have hl := constant_regular (Γ := Γ) L
  have hu := constant_regular (Γ := Γ) U
  have hx := GaussianStirlingTelescopeName.name_regular (succ N) a b hs
  have e := GaussianStirlingTelescopeName.telescope_cross (succ N) a b hs
  exact .andI
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_refl _ _ hl) e (order_from_envelope _ _ _ _ _ hl hx l))
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ e) (cross_refl _ _ hu)
      (order_from_envelope _ _ _ _ _ hx hu u))

end LeanProofs.IPRA.Analysis.GaussianStirlingGlobalBoundsFinite
