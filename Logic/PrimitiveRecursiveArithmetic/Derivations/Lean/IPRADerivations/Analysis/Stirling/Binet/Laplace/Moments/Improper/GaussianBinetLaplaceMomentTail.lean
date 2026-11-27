import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.Improper.GaussianBinetLaplaceMomentDecay
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactNamedAdditivity
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerReciprocalTail
import IPRADerivations.DiophantineNumberTheory.AperyMultibound
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Strips.GaussianBinetLaplaceStripCutoff

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
open GaussianBinetLaplaceStripCutoff (grid_tag_numerator_positive reciprocal_square_majorant)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentCompact (data compact_input)
open GaussianBinetLaplaceMomentDecay (tailScale observation_inverse_square_bound)
open GaussianBinetLaplaceMomentFloor (evaluatorF evaluator_at fixedData gain nameF observation)
open GaussianBinetLaplaceStrip (source tagNumerator tag_inside)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianCompactRiemannName (grid inside grid_inside quadrature sampleBody sampleData sample_body_at precision mesh)
open GaussianNamedDampingPowerReciprocalTail (body gridData subst_gridData quadrature_bound_of_majorized)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSumMajorant (majorized termsMajorized)

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

/-- Absorb an observation allowance into the inverse-square majorant on the actual grid. -/
theorem cell_majorant_of_observation (i p N j X D R T A C E S P K : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E)
    (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N)
    (hi : Γ ⊢[PRAAx] lt i (C*N)) (pay : Γ ⊢[PRAAx] le (P*(T*T)) (K*unit p))
    (observation_bound : ∀ a b : PTm n,
      (Γ ⊢[PRAAx] le one a) → (Γ ⊢[PRAAx] le one b) → (Γ ⊢[PRAAx] le a (T*b)) →
      (Γ ⊢[PRAAx] bounded (observation p j X D R T a b)
        (P*(a*a)+(S*(b*b))*unit p) (unit p*(a*a)))) :
    Γ ⊢[PRAAx] majorized
      (inst2 (sampleBody evaluatorF) i (sampleData p (C*N) (E+A) C E (fixedData j X D R T)))
      (inst2 body i (gridData (S+K) A E N)) := by
  let M := C*N
  let t := grid i M (E+A) C E
  let a := tagNumerator t
  let b := sndT t
  have hM := positive_product C N hC hN
  have hE := h.andE₂.andE₁
  have ht : Γ ⊢[PRAAx] inside (E+A) C E t :=
    grid_inside i M (E+A) C E (le_trans hE (le_add_right _ _)) hE hM (le_of_lt hi)
  have ha : Γ ⊢[PRAAx] le one a := grid_tag_numerator_positive i M A C E hA hM
  have time : Γ ⊢[PRAAx] le a (T*b) := (tag_inside t A C E T hE h.andE₂.andE₂ ht).andE₂
  have hAA := positive_product a a ha ha
  have tagSquare : Γ ⊢[PRAAx] le (a*a) ((b*b)*(T*T)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono time time)
  have paid : Γ ⊢[PRAAx] le (P*(a*a)) (K*((b*b)*unit p)) :=
    le_trans (le_mul_mono (le_refl P) tagSquare)
      (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono (le_refl (b*b)) pay))
  have bound := bounded_radius_mono _ _ (unit p*(a*a)) ((S+K)*b*b) (a*a)
    (positive_product _ _ (unit_positive p) hAA) hAA
    (by ipra_le 𝔞(a)*𝔞(a)*sl paid) (observation_bound a b ha ht.andE₂.andE₁ time)
  have read := (sample_body_at (Γ := Γ) evaluatorF i p M (E+A) C E (fixedData j X D R T)).eqTrans
    (evaluator_at p t j X D R T)
  exact reciprocal_square_majorant i (S+K) A C E N hA hC hN read bound

private theorem cell_majorant (i p N j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le (T*T) (unit p)) (hi : Γ ⊢[PRAAx] lt i (C*N)) : Γ ⊢[PRAAx]
    majorized (inst2 (sampleBody evaluatorF) i (sampleData p (C*N) (E+A) C E (fixedData j X D R T)))
      (inst2 body i (gridData (coefficient j D) A E N)) :=
  cell_majorant_of_observation i p N j X D R T A C E (tailScale j D) (num 4) (num 4)
    h hA hC hN hi (le_mul_mono (le_refl _) hq)
    (fun a b ha hb time =>
      observation_inverse_square_bound p j X D R T a b (.andI h.andE₁ (.andI hb time)) ha)

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
    have a : Δ ⊢[PRAAx] le one (s A) := (Order.shift_one_le hA).wk
    have c : Δ ⊢[PRAAx] le one (s C) := (Order.shift_one_le hC).wk
    have ns : Δ ⊢[PRAAx] le one (s N) := (Order.shift_one_le hN).wk
    have q : Δ ⊢[PRAAx] le (s T*s T) (unit (s p)) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit] using hq.shift.wk
    simpa only [f,x,y,M,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianBinetLaplaceMomentFloor.subst_fixedData,subst_gridData,subst_coefficient,PTm.subst_add,PTm.subst_mul] using
      cell_majorant (var 0) (s p) (s N) (s j) (s X) (s D) (s R) (s T) (s A) (s C) (s E) hs a c ns q Prf.hyp0
  exact quadrature_bound_of_majorized evaluatorF p (coefficient j D) A (E+A) C E N _
    hA hC h.andE₂.andE₁ hN rows

/-- Transfer a bound at any later refined grid clock to the original compact name. -/
theorem name_bound_of_late_grid (p q j X D R T A C E V : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E)
    (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) (hq : Γ ⊢[PRAAx] le (precision p T) q)
    (bound : Γ ⊢[PRAAx] bounded
      (quadrature evaluatorF q (C*mesh p (gain j R T) T) (E+A) C E (fixedData j X D R T)) V A) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data j X D R T A C E)) (A+V*unit p) (unit p*A) := by
  let x := fixedData j X D R T
  let L := gain j R T
  let u := GaussianCompactRiemannName.sample evaluatorF p (E+A) C E L T x
  let v := quadrature evaluatorF q (C*mesh p L T) (E+A) C E x
  have hp := unit_positive (Γ := Γ) p
  have hS := unit_positive (Γ := Γ) (p+num 6)
  have near := GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF p q C (E+A) C E L T x
    (compact_input j X D R T A C E h) hC hq
  have gap : Γ ⊢[PRAAx] distanceBounded u v one (unit p) :=
    distance_radius_mono _ _ _ _ _ _ hS hp
      (le_congr (.eqRefl _) (by ipra_ring) (GaussianCompactRiemannName.dyadic_six_lower p))
      (distance_symmetric v u (num 3) (unit (p+num 6)) hS near)
  exact bound_congr (GaussianCompactRiemannName.name_at evaluatorF p (E+A) C E L T x).eqSymm
    (by ipra_ring) (.eqRefl _) (GaussianReconstructionRoots.norm_from_distance u v _ _ _ _ hp hA gap bound)

theorem name_bound (p j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E) (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data j X D R T A C E))
      (A+(two*coefficient j D*E)*unit p) (unit p*A) := by
  let L := gain j R T
  let M := mesh p L T
  let q := precision p T
  exact name_bound_of_late_grid p q j X D R T A C E _ h hA hC (le_refl _)
    (upper_tail_bound q M j X D R T A C E h hA hC
      (GaussianCompactRiemannName.mesh_positive p L T) (square_clock p T))

theorem actual_weighted_Binet_compact_far_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) zero (var 3) zero (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
      le one (var 6) ⟶ le one (var 7) ⟶
        bounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
          (var 6+(two*coefficient (var 1) (var 3)*var 8)*unit (var 0)) (unit (var 0)*var 6)) :=
  closeUniv 9 (.impI (.impI (.impI (name_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentTail
