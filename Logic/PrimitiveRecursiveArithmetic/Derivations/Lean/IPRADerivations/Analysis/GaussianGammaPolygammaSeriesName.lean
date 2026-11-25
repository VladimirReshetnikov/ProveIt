import IPRADerivations.Analysis.GaussianGammaPolygammaPrefix
import IPRADerivations.Analysis.GaussianGammaReciprocalInverse

/-!
# A regular name for the signed polygamma series

The observation program returns the actual finite sum in C29 through a
computed cutoff. The C30 bound proves regularity and compares each
observation to every prescribed cutoff in the same certified disk.
All numerical orders and cutoff lengths stay internal.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaPolygammaSeriesName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerHeadLower (pole_at translated)
open GaussianGammaPolygammaPrefix (partialSum partial_sum_gap)
open GaussianGammaPolygammaTailRows (argument argument_lower)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_radius_mono)
open GaussianRationalHorner (positive_product ofGaussian_represents)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)
open Products (fact)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B E : PTm n) : Fm PTm n := GaussianGammaReciprocalInverse.source z R B one E
def weight (m : PTm n) : PTm n := fact (pred m)*pw two (succ m)
def clock (p R m : PTm n) : PTm n := two*R+(one+weight m)*unit p
def observation (p z R B m : PTm n) : PTm n := partialSum z B m (clock p R m)
def data (z R B m : PTm n) : PTm n := pairT z (pairT R (pairT B m))
def body : PTm 2 := observation (var 0) (fstT (var 1)) (fstT (sndT (var 1)))
  (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
def nameF : PR 2 := PTm.toPR body

@[simp] theorem subst_source {l : ℕ} (σ : Fin n → PTm l) (z R B E : PTm n) :
    (source z R B E).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) := by
  simp [source,one]
@[simp] theorem subst_weight {l : ℕ} (σ : Fin n → PTm l) (m : PTm n) :
    Syn.subst σ (weight m) = weight (Syn.subst σ m) := by
  simp [weight,Products.fact,two]
@[simp] theorem subst_observation {l : ℕ} (σ : Fin n → PTm l) (p z R B m : PTm n) :
    Syn.subst σ (observation p z R B m) = observation (Syn.subst σ p) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) := by simp [observation,clock,one,two]
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (z R B m : PTm n) :
    Syn.subst σ (data z R B m) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ m) := by
  simp [data]

theorem name_at (p z R B m : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data z R B m) ≐ observation p z R B m := by
  let x := data z R B m
  let Y := fstT x
  let S := fstT (sndT x)
  let D := fstT (sndT (sndT x))
  let M := sndT (sndT (sndT x))
  have read : Γ ⊢[PRAAx] ap2 nameF p x ≐ observation p Y S D M := by
    simpa only [nameF,body,ap2,subst_observation,subst_fstT,subst_sndT,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one,Y,S,D,M] using toPR_eq (Γ := Γ) body ![p,x]
  have y : Γ ⊢[PRAAx] sndT x ≐ pairT R (pairT B m) := snd_pair _ _
  have w := (congrSnd y).eqTrans (snd_pair R (pairT B m))
  have eq := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![p,Y,S,D,M]) (σ' := ![p,z,R,B,m]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact (congrFst y).eqTrans (fst_pair _ _)
      · exact (congrFst w).eqTrans (fst_pair _ _)
      · exact (congrSnd w).eqTrans (snd_pair _ _))
  exact read.eqTrans (by
    simpa only [subst_observation,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] using eq)

theorem row_norm_positive (z R B E k : PTm n) (h : Γ ⊢[PRAAx] source z R B E) : Γ ⊢[PRAAx]
    le one (GaussianRationalReciprocal.normNumerator (argument z B k)) := by
  let q := argument z B k
  let w := translated z B k
  have hb := h.andE₁.andE₂.andE₁
  have he := h.andE₂.andE₂.andE₁
  refine .orE (le_total k (two*R)) ?_ ?_
  · have point := pole_at z B one E (two*R) k h.andE₂.andE₂.andE₂.wk Prf.hyp0
    have bound : (le k (two*R)::Γ) ⊢[PRAAx] GaussianNameReciprocal.lower q E :=
      GaussianRationalLowerBounds.lower_from_representation q w B one E hb.wk he.wk
        (ofGaussian_represents w B hb.wk) (le_congr (by ipra_ring) (.eqRefl _) point)
    exact GaussianNameReciprocal.lower_norm_positive q E he.wk bound
  · have later : (le (two*R) k::Γ) ⊢[PRAAx] le (two*R) k := Prf.hyp0
    have hn : (le (two*R) k::Γ) ⊢[PRAAx] le one k :=
      le_trans (positive_product _ _ (le_succ_self one) h.andE₁.andE₁.wk) later
    have lower := argument_lower z R B k hb.wk h.andE₁.andE₂.andE₂.wk later
    have ht : (le (two*R) k::Γ) ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
    exact GaussianNameReciprocal.lower_norm_positive q two ht
      (GaussianRationalLowerBounds.name_lower q k two hn ht lower)

theorem clock_radius (p R m : PTm n) : Γ ⊢[PRAAx] le (two*R) (clock p R m) :=
  le_add_right _ _

theorem clock_positive (p R m : PTm n) : Γ ⊢[PRAAx] le one (clock p R m) := by
  refine le_trans (unit_positive p) (le_trans ?_ (le_add_left _ _))
  exact le_congr (one_mul _ ) (.eqRefl _) (mul_le_mul_right (unit p) (le_add_right one (weight m)))

theorem clock_monotone (p q R m : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (clock p R m) (clock q R m) := by
  have grow := GaussianExponentialReference.unit_monotone h
  unfold clock
  exact add_le_add₂ (le_refl _) (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right _ grow))

theorem clock_paid (p R m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (weight m*unit p) (pw (clock p R m) m) := by
  let N := clock p R m
  have grow := GaussianFactorBudget.power_monotone_length N one m (clock_positive p R m) hm
  have first : Γ ⊢[PRAAx] le (weight m*unit p) N := by
    unfold N clock
    exact le_trans (mul_le_mul_right (unit p) (le_add_left (weight m) one)) (le_add_left _ _)
  exact le_trans first (le_congr (RationalNonnegativePowers.natural_power_one N) (.eqRefl _) grow)

private theorem partial_congr (z B m N K : PTm n) (h : Γ ⊢[PRAAx] N ≐ K) :
    Γ ⊢[PRAAx] partialSum z B m N ≐ partialSum z B m K := by
  simpa only [GaussianGammaPolygammaPrefix.subst_partialSum,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
    Prf.eqCongr1 (partialSum (Syn.shift z) (Syn.shift B) (Syn.shift m) (var 0)) h

theorem ordered_gap (z R B E m N K : PTm n) (h : Γ ⊢[PRAAx] source z R B E)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) (hR : Γ ⊢[PRAAx] le (two*R) N)
    (hK : Γ ⊢[PRAAx] le N K) :
    Γ ⊢[PRAAx] distanceBounded (partialSum z B m K) (partialSum z B m N) (weight m) (pw N m) :=
  distance_congr (partial_congr _ _ _ _ _ (eq_add_of_le hK).eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (partial_sum_gap z R B m N (monus K N) h.andE₁.andE₂.andE₁ h.andE₁.andE₂.andE₂ hm hN hR)

private theorem observations_of_le (p q z R B E m : PTm n) (h : Γ ⊢[PRAAx] source z R B E)
    (hm : Γ ⊢[PRAAx] le one m) (hpq : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    distanceBounded (observation q z R B m) (observation p z R B m) (unit p+unit q) (unit p*unit q) := by
  let N := clock p R m
  let K := clock q R m
  let D := pw N m
  have hN := clock_positive (Γ := Γ) p R m
  have hD := GaussianFactorBudget.power_positive N m hN
  have a := ordered_gap z R B E m N K h hm hN (clock_radius p R m) (clock_monotone p q R m hpq)
  have paid := clock_paid p R m hm
  exact distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ (unit_positive p) (unit_positive q))
    (by ipra_le 𝔞(unit q)*sl paid+𝔞(unit p)*𝔞(D)) a

theorem observations (p q z R B E m : PTm n) (h : Γ ⊢[PRAAx] source z R B E)
    (hm : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx]
    distanceBounded (observation p z R B m) (observation q z R B m) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) ?_ ?_
  · exact distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive q))
      (observations_of_le p q z R B E m h.wk hm.wk Prf.hyp0)
  · exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
      (observations_of_le q p z R B E m h.wk hm.wk Prf.hyp0)

theorem name_regular (z R B E m : PTm n) (h : Γ ⊢[PRAAx] source z R B E) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B m) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh E) := by
    simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift.shift
  have ms : Δ ⊢[PRAAx] le one (sh m) := by
    simpa [Δ,Fm.shift,Syn.shift,sh] using hm.shift.shift
  have obs := observations p q (sh z) (sh R) (sh B) (sh E) (sh m) hs ms
  refine .allI (.allI ?_)
  simpa only [pointCN,Syn.shift,subst_data,sh,p,q,GaussianCoefficientNameBounds.unit,GaussianEuclideanPointDistance.unit] using
    distance_congr (name_at p (sh z) (sh R) (sh B) (sh m)).eqSymm
      (name_at q (sh z) (sh R) (sh B) (sh m)).eqSymm (.eqRefl _) (.eqRefl _) obs

theorem cutoff_error (p z R B E m N : PTm n) (h : Γ ⊢[PRAAx] source z R B E)
    (hm : Γ ⊢[PRAAx] le one m) (hn : Γ ⊢[PRAAx] le one N) (hr : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data z R B m)) (partialSum z B m N)
      (weight m*unit p+pw N m) (pw N m*unit p) := by
  let K := clock p R m
  let D := pw N m
  let F := pw K m
  let U := unit p
  let W := weight m
  have hD := GaussianFactorBudget.power_positive N m hn
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have hK := clock_positive (Γ := Γ) p R m
  have hF := GaussianFactorBudget.power_positive K m hK
  have hDU := positive_product D U hD hU
  have hpaid := clock_paid p R m hm
  have narrow : Γ ⊢[PRAAx] le (W*(D*U)) ((W*U+D)*D) := by
    ipra_le 𝔞(D)^2
  have wide : Γ ⊢[PRAAx] le (W*(D*U)) ((W*U+D)*F) := by
    ipra_le 𝔞(D)*sl hpaid+𝔞(W)*𝔞(U)*𝔞(F)
  apply distance_congr (name_at p z R B m).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
  refine .orE (le_total N K) ?_ ?_
  · exact distance_radius_mono _ _ _ _ _ _ hD.wk hDU.wk
      narrow.wk (ordered_gap z R B E m N K h.wk hm.wk hn.wk hr.wk Prf.hyp0)
  · have other := ordered_gap z R B E m K N h.wk hm.wk hK.wk (clock_radius p R m) Prf.hyp0
    exact distance_radius_mono _ _ _ _ _ _ hF.wk hDU.wk
      wide.wk
      (distance_symmetric _ _ _ _ hF.wk other)

theorem actual_original_polygamma_C29_series_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶ le one (var 4) ⟶
      pointCN nameF (data (var 0) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (name_regular _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_polygamma_C29_series_cutoff_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 1) (var 2) (var 3) (var 4) ⟶
      (le one (var 5) ⋏ (le one (var 6) ⋏ le (two*var 2) (var 6))) ⟶
      distanceBounded (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 5)))
        (partialSum (var 1) (var 3) (var 5) (var 6))
        (weight (var 5)*unit (var 0)+pw (var 6) (var 5)) (pw (var 6) (var 5)*unit (var 0))) :=
  closeUniv 7 (.impI (.impI (cutoff_error _ _ _ _ _ _ _ Prf.hyp1
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

theorem actual_original_polygamma_C29_all_denominators_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) ⟶
      le one (GaussianRationalReciprocal.normNumerator (argument (var 0) (var 2) (var 4)))) :=
  closeUniv 5 (.impI (row_norm_positive _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaPolygammaSeriesName
