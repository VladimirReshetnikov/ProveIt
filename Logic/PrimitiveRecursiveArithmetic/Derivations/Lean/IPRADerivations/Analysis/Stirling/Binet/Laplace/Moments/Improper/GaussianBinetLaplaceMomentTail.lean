import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.Improper.GaussianBinetLaplaceMomentDecay
import IPRADerivations.Analysis.Names.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.Decay.GaussianBinetSecondDecayEnvelope
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerReciprocalTail
import IPRADerivations.DiophantineNumberTheory.AperyMultibound

/-!
# Far-tail bound for the actual weighted Binet quadrature

The actual observation allowance is absorbed into the reciprocal-square
coefficient at the original compact precision. Refining the original
mesh to step 1/(E*N) then gives a telescoping tail bound independent of
the right endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTail

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentCompact (data compact_input)
open GaussianBinetLaplaceMomentDecay (tailScale observation_inverse_square_bound)
open GaussianBinetLaplaceMomentFloor (evaluatorF evaluator_at fixedData gain nameF)
open GaussianBinetLaplaceStrip (source tagNumerator tag_inside)
open GaussianBinetLaplaceStripCutoff (grid_tag)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (grid inside grid_inside quadrature sampleBody sampleData sample_body_at precision mesh)
open GaussianNamedDampingPowerReciprocalTail (body gridData affine_grid_term original_scalar_left_embedded_bound)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSumMajorant (majorized majorized_congr termsMajorized)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def coefficient (j D : PTm n) : PTm n := tailScale j D+num 4

ipra_subst coefficient

private def squareLaw (T : PTm n) : Fm PTm n := le ((T+num 3)*(T+num 3)) (num 16*unit T)

@[simp] private theorem subst_squareLaw {m : ℕ} (σ : Fin n → PTm m) (T : PTm n) :
    (squareLaw T).subst σ = squareLaw (Syn.subst σ T) := by simp [squareLaw]

private theorem square_clock (p T : PTm n) : Γ ⊢[PRAAx] le (T*T) (unit (precision p T)) := by
  have all : Γ ⊢[PRAAx] .all (squareLaw (var 0)) := by
    refine PRA.qfInd (squareLaw (var 0)) (le_QF _ _) ?_ ?_
    · have base : Γ ⊢[PRAAx] le ((zero+num 3)*(zero+num 3)) (num 16*one) := by ipra_le 7
      have raw : Γ ⊢[PRAAx] squareLaw zero :=
        le_congr (.eqRefl _) (congrMul (.eqRefl _) (pw_zero two)).eqSymm base
      simpa only [subst_squareLaw,Syn.subst_var,Syn.inst_zero] using raw
    · simp only [subst_squareLaw,Syn.subst_var,Syn.repl_zero]
      let i : PTm (n+1) := var 0
      have prev : (squareLaw i :: Γ.map Fm.shift) ⊢[PRAAx] squareLaw i := Prf.hyp0
      have step : (squareLaw i :: Γ.map Fm.shift) ⊢[PRAAx]
          le ((succ i+num 3)*(succ i+num 3)) (two*((i+num 3)*(i+num 3))) := by
        ipra_le 𝔞(i)*𝔞(i)+4*𝔞(i)+2
      exact le_trans step (le_congr (.eqRefl _)
        ((by ipra_ring : (squareLaw i::Γ.map Fm.shift) ⊢[PRAAx] two*(num 16*unit i) ≐ num 16*(unit i*two)).eqTrans
          (congrMul (.eqRefl _) (pw_succ two i).eqSymm))
        (le_mul_mono (le_refl two) prev))
  have h : Γ ⊢[PRAAx] squareLaw T := by simpa only [subst_squareLaw,Syn.subst_var,Syn.inst_zero] using all.allE T
  have grow : Γ ⊢[PRAAx] le T (T+num 3) := le_add_right _ _
  have pow4 : Γ ⊢[PRAAx] pw two (num 4) ≐ num 16 :=
    LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 4
  have sixteen : Γ ⊢[PRAAx] num 16*unit T ≐ unit (T+num 4) :=
    (mul_comm _ _).eqTrans ((congrMul (.eqRefl _) pow4.eqSymm).eqTrans (pw_add _ _ _).eqSymm)
  have et : Γ ⊢[PRAAx] le (T+num 4) (precision p T) := by
    unfold precision
    ipra_le 𝔞(p)+2
  exact le_trans (le_mul_mono grow grow)
    (le_trans (le_congr (.eqRefl _) sixteen h) (GaussianExponentialReference.unit_monotone et))

@[simp] private theorem subst_gridData {m : ℕ} (σ : Fin n → PTm m) (K A E N : PTm n) :
    Syn.subst σ (gridData K A E N) = gridData (Syn.subst σ K) (Syn.subst σ A) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [gridData]

private theorem cell_majorant (i p N j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le (T*T) (unit p)) (hi : Γ ⊢[PRAAx] lt i (C*N)) : Γ ⊢[PRAAx]
    majorized (inst2 (sampleBody evaluatorF) i (sampleData p (C*N) (E+A) C E (fixedData j X D R T)))
      (inst2 body i (gridData (coefficient j D) A E N)) := by
  let M := C*N
  let t := grid i M (E+A) C E
  let a := tagNumerator t
  let b := sndT t
  let K := coefficient j D
  let u := grid i M A C E
  have hM := positive_product C N hC hN
  have hE := h.andE₂.andE₁
  have ht : Γ ⊢[PRAAx] inside (E+A) C E t :=
    grid_inside i M (E+A) C E (le_trans hE (le_add_right _ _)) hE hM (le_of_lt hi)
  have exactTag := grid_tag (Γ := Γ) i M A C E
  have ha : Γ ⊢[PRAAx] le one a :=
    le_congr (.eqRefl _) exactTag.andE₁.eqSymm
      (le_trans (positive_product _ _ hA hM) (le_add_right _ _))
  have hb := ht.andE₂.andE₁
  have time := (tag_inside t A C E T hE h.andE₂.andE₂ ht).andE₂
  have hAA := positive_product _ _ ha ha
  have raw := observation_inverse_square_bound p j X D R T a b
    (.andI h.andE₁ (.andI hb time)) ha
  have compare : Γ ⊢[PRAAx] le (a*a) ((b*b)*unit p) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono time time))
      (le_mul_mono (le_refl (b*b)) hq)
  have bb := bounded_radius_mono _ _ _ (K*b*b) (a*a) (positive_product _ _ (unit_positive p) hAA) hAA
    (by dsimp only [K,coefficient]; ipra_le 4*𝔞(a)*𝔞(a)*sl compare) raw
  have maj := GaussianBinetSecondDecayEnvelope.fraction_majorized _ _ _ hAA bb
  have read := (sample_body_at (Γ := Γ) evaluatorF i p M (E+A) C E (fixedData j X D R T)).eqTrans
    (evaluator_at p t j X D R T)
  have en : Γ ⊢[PRAAx] fstT u ≐ a := (fst_pair _ _).eqTrans exactTag.andE₁.eqSymm
  have ed : Γ ⊢[PRAAx] sndT u ≐ b := (snd_pair _ _).eqTrans exactTag.andE₂.eqSymm
  have scalar : Γ ⊢[PRAAx] inst2 body i (gridData K A E N) ≐ GaussianEuclideanDistanceName.fraction (K*b*b) (a*a) :=
    (affine_grid_term i K A C E N hA hC hN).eqTrans
      (RationalNonnegativePowers.fraction_congr (congrMul (congrMul (.eqRefl K) ed) ed) (congrMul en en))
  exact majorized_congr read.eqSymm scalar.eqSymm maj

theorem upper_tail_bound (p N j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le (T*T) (unit p)) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p (C*N) (E+A) C E (fixedData j X D R T))
      (two*coefficient j D*E) A := by
  let M := C*N
  let f := sampleBody evaluatorF
  let x := sampleData p M (E+A) C E (fixedData j X D R T)
  let y := gridData (coefficient j D) A E N
  have rows : Γ ⊢[PRAAx] termsMajorized f body M x y := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s C*s N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift.wk
    have a : Δ ⊢[PRAAx] le one (s A) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hA.shift.wk
    have c : Δ ⊢[PRAAx] le one (s C) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hC.shift.wk
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have q : Δ ⊢[PRAAx] le (s T*s T) (unit (s p)) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit] using hq.shift.wk
    simpa only [f,x,y,M,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianBinetLaplaceMomentFloor.subst_fixedData,subst_gridData,subst_coefficient,PTm.subst_add,PTm.subst_mul] using
      cell_majorant (var 0) (s p) (s N) (s j) (s X) (s D) (s R) (s T) (s A) (s C) (s E) hs a c ns q Prf.hyp0
  exact GaussianRationalSumMajorant.majorant_bound _ _ _ _ hA
    (GaussianCompactScalarMajorant.weighted_majorant f body M x y C E (positive_product C N hC hN) h.andE₂.andE₁ rows)
    (original_scalar_left_embedded_bound (coefficient j D) A C E N hA hC h.andE₂.andE₁ hN)

theorem name_bound (p j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data j X D R T A C E))
      (A+(two*coefficient j D*E)*unit p) (unit p*A) := by
  let x := fixedData j X D R T
  let L := gain j R T
  let M := mesh p L T
  let q := precision p T
  let S := unit (p+num 6)
  let u := GaussianCompactRiemannName.sample evaluatorF p (E+A) C E L T x
  let v := quadrature evaluatorF q (C*M) (E+A) C E x
  have b := upper_tail_bound q M j X D R T A C E h hA hC
    (GaussianCompactRiemannName.mesh_positive p L T) (square_clock p T)
  have near := GaussianCompactNamedAdditivity.refinement_distance evaluatorF p (E+A) C E L T x hC
    (compact_input j X D R T A C E h)
  have ds : Γ ⊢[PRAAx] distanceBounded u v one (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive _) (unit_positive p)
      (le_congr (.eqRefl _) (by ipra_ring) (GaussianCompactRiemannName.dyadic_six_lower p))
      (distance_symmetric v u (num 3) S (unit_positive _) near)
  have norm := GaussianReconstructionRoots.norm_from_distance u v one (unit p) _ _ (unit_positive p) hA ds b
  exact bound_congr (GaussianCompactRiemannName.name_at evaluatorF p (E+A) C E L T x).eqSymm
    (by ipra_ring) (.eqRefl _) norm

theorem actual_weighted_Binet_compact_far_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) zero (var 3) zero (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      le one (var 6) ⟶ le one (var 7) ⟶
        bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
          (var 6+(two*coefficient (var 1) (var 3)*var 8)*unit (var 0)) (unit (var 0)*var 6)) :=
  closeUniv 9 (.impI (.impI (.impI (name_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTail
