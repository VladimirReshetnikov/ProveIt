import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentMarginRows
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondDecayEnvelope
import IPRADerivations.Analysis.SpecialFunctions.DampingPower.GaussianNamedDampingPowerReciprocalTail

/-!
# Uniform positive-margin tails of the actual Binet quadrature

Late compact observations absorb the row error into an inverse-square
majorant at a fixed lower chart. Its original affine left grid gives
a bound independent of the right endpoint and of the input denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentMarginTail

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentCompact (data compact_input)
open GaussianBinetLaplaceMomentDecay (tailScale)
open GaussianBinetLaplaceMomentMarginRows (allowance observation_inverse_square_bound)
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

def coefficient (j K : PTm n) : PTm n := tailScale j K+num 30

ipra_subst coefficient

@[simp] private theorem subst_gridData {m : ℕ} (σ : Fin n → PTm m) (K A E N : PTm n) :
    Syn.subst σ (gridData K A E N) = gridData (Syn.subst σ K) (Syn.subst σ A) (Syn.subst σ E) (Syn.subst σ N) := by
  simp [gridData]

private theorem cell_majorant (i p N j X D R K T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E)
    (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*X)) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N)
    (hq : Γ ⊢[PRAAx] le ((T*T)*(one+pw T j)) (unit p)) (hi : Γ ⊢[PRAAx] lt i (C*N)) : Γ ⊢[PRAAx]
    majorized (inst2 (sampleBody evaluatorF) i (sampleData p (C*N) (E+A) C E (fixedData j X D R T)))
      (inst2 body i (gridData (coefficient j K) A E N)) := by
  let M := C*N
  let t := grid i M (E+A) C E
  let a := tagNumerator t
  let b := sndT t
  let V := coefficient j K
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
  have raw := observation_inverse_square_bound p j X D R K T a b
    (.andI h.andE₁ (.andI hb time)) hK hmargin ha
  have tagSquare : Γ ⊢[PRAAx] le (a*a) ((b*b)*(T*T)) :=
    le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono time time)
  have pad : Γ ⊢[PRAAx] le (allowance j T) (num 30*(one+pw T j)) := by
    unfold allowance
    ipra_le 26+4*𝔞(pw T j)
  have cmp : Γ ⊢[PRAAx] le (allowance j T*(a*a)) (num 30*((b*b)*unit p)) := by
    have scaled : Γ ⊢[PRAAx] le ((num 30*(b*b))*((T*T)*(one+pw T j))) ((num 30*(b*b))*unit p) :=
      le_mul_mono (le_refl _) hq
    exact le_trans (le_mul_mono pad tagSquare)
      (le_congr (by ipra_ring) (by ipra_ring) scaled)
  have bb := bounded_radius_mono _ _ _ (V*b*b) (a*a) (positive_product _ _ (unit_positive p) hAA) hAA
    (by dsimp only [V,coefficient]; ipra_le 𝔞(a)*𝔞(a)*sl cmp) raw
  have maj := GaussianBinetSecondDecayEnvelope.fraction_majorized _ _ _ hAA bb
  have read := (sample_body_at (Γ := Γ) evaluatorF i p M (E+A) C E (fixedData j X D R T)).eqTrans
    (evaluator_at p t j X D R T)
  have en : Γ ⊢[PRAAx] fstT u ≐ a := (fst_pair _ _).eqTrans exactTag.andE₁.eqSymm
  have ed : Γ ⊢[PRAAx] sndT u ≐ b := (snd_pair _ _).eqTrans exactTag.andE₂.eqSymm
  have scalar : Γ ⊢[PRAAx] inst2 body i (gridData V A E N) ≐ GaussianEuclideanDistanceName.fraction (V*b*b) (a*a) :=
    (affine_grid_term i V A C E N hA hC hN).eqTrans
      (RationalNonnegativePowers.fraction_congr (congrMul (congrMul (.eqRefl V) ed) ed) (congrMul en en))
  exact majorized_congr read.eqSymm scalar.eqSymm maj

theorem upper_tail_bound (p N j X D R K T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E)
    (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*X)) (hA : Γ ⊢[PRAAx] le one A)
    (hC : Γ ⊢[PRAAx] le one C) (hN : Γ ⊢[PRAAx] le one N) (hq : Γ ⊢[PRAAx] le ((T*T)*(one+pw T j)) (unit p)) :
    Γ ⊢[PRAAx] bounded (quadrature evaluatorF p (C*N) (E+A) C E (fixedData j X D R T))
      (two*coefficient j K*E) A := by
  let M := C*N
  let f := sampleBody evaluatorF
  let x := sampleData p M (E+A) C E (fixedData j X D R T)
  let y := gridData (coefficient j K) A E N
  have rows : Γ ⊢[PRAAx] termsMajorized f body M x y := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s C*s N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift.wk
    have a : Δ ⊢[PRAAx] le one (s A) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hA.shift.wk
    have c : Δ ⊢[PRAAx] le one (s C) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hC.shift.wk
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    have ks : Δ ⊢[PRAAx] le one (s K) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hK.shift.wk
    have ms : Δ ⊢[PRAAx] le (s D) (s K*s X) := by
      simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,PTm.subst_mul] using hmargin.shift.wk
    have q : Δ ⊢[PRAAx] le ((s T*s T)*(one+pw (s T) (s j))) (unit (s p)) := by
      simpa [Δ,s,Fm.shift,Syn.shift,one] using hq.shift.wk
    simpa only [f,x,y,M,Δ,s,Syn.shift,GaussianCompactRiemannName.subst_sampleData,
      GaussianBinetLaplaceMomentFloor.subst_fixedData,subst_gridData,subst_coefficient,PTm.subst_add,PTm.subst_mul] using
      cell_majorant (var 0) (s p) (s N) (s j) (s X) (s D) (s R) (s K) (s T) (s A) (s C) (s E) hs ks ms a c ns q Prf.hyp0
  exact GaussianRationalSumMajorant.majorant_bound _ _ _ _ hA
    (GaussianCompactScalarMajorant.weighted_majorant f body M x y C E (positive_product C N hC hN) h.andE₂.andE₁ rows)
    (original_scalar_left_embedded_bound (coefficient j K) A C E N hA hC h.andE₂.andE₁ hN)

theorem name_bound (p j X D R K T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X zero D zero R T A C E)
    (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*X))
    (hA : Γ ⊢[PRAAx] le one A) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data j X D R T A C E))
      (A+(two*coefficient j K*E)*unit p) (unit p*A) := by
  let x := fixedData j X D R T
  let L := gain j R T
  let M := mesh p L T
  let q := GaussianFastValueCut.exponent ((T*T)*(one+pw T j)) (precision p T)
  let S := unit (p+num 6)
  let u := GaussianCompactRiemannName.sample evaluatorF p (E+A) C E L T x
  let v := quadrature evaluatorF q (C*M) (E+A) C E x
  have hq : Γ ⊢[PRAAx] le (precision p T) q := le_add_right _ _
  have hp := unit_positive (Γ := Γ) p
  have budget : Γ ⊢[PRAAx] le ((T*T)*(one+pw T j)) (unit q) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _)
      (le_mul_mono (le_refl ((T*T)*(one+pw T j))) (unit_positive (precision p T)))) (GaussianFastValueCut.query_budget _ _)
  have b := upper_tail_bound q M j X D R K T A C E h hK hmargin hA hC
    (GaussianCompactRiemannName.mesh_positive p L T) budget
  have near := GaussianCompactMeshIndependence.arbitrary_refinement evaluatorF p q C (E+A) C E L T x
    (compact_input j X D R T A C E h) hC hq
  have ds : Γ ⊢[PRAAx] distanceBounded u v one (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive _) hp
      (le_congr (.eqRefl _) (by ipra_ring) (GaussianCompactRiemannName.dyadic_six_lower p))
      (distance_symmetric v u (num 3) S (unit_positive _) near)
  exact bound_congr (GaussianCompactRiemannName.name_at evaluatorF p (E+A) C E L T x).eqSymm
    (by ipra_ring) (.eqRefl _) (GaussianReconstructionRoots.norm_from_distance u v _ _ _ _ hp hA ds b)

theorem actual_weighted_Binet_margin_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let p := var 0
     let j := var 1
     let X := var 2
     let D := var 3
     let R := var 4
     let K := var 5
     let T := var 6
     let A := var 7
     let C := var 8
     let E := var 9
     source X zero D zero R T A C E ⟶ (le one K ⋏ le D (K*X)) ⟶ (le one A ⋏ le one C) ⟶
       bounded (ap2 nameF p (data j X D R T A C E)) (A+(two*coefficient j K*E)*unit p) (unit p*A)) :=
  closeUniv 10 (.impI (.impI (.impI (name_bound _ _ _ _ _ _ _ _ _ _ hyp2 Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentMarginTail
