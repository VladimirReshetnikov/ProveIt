import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseLiteralPrefix

/-!
# Normalized cofinal sum of the original Bose exponential rows

The truncation grows as `B² * 2^p` for time `A/B > 0`. The
observation precision also pays for the total literal row error.
The resulting normalized name agrees with the reciprocal of the
original Bose denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralCofinal

open_ipra
open GaussianBinetBoseDenominator (reciprocalF reciprocalData reciprocal_regular subst_reciprocalData)
open GaussianBinetBoseSeries (prefixValue partial_error)
open GaussianBinetBoseSeriesRows (rowClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def source (A B : PTm n) : Fm PTm n := le one A ⋏ le one B
def cutoff (p B : PTm n) : PTm n := (B*B)*unit p
def late (p A B : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (cutoff p B*GaussianBinetBoseLiteralPrefix.budget (cutoff p B) A B) p
def rawSample (p A B : PTm n) : PTm n :=
  GaussianBinetBoseLiteralPrefix.value (late p A B) (cutoff p B) A B
def rawF : PR 2 := PTm.toPR (rawSample (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2)

ipra_subst rawSample [late, cutoff]

theorem raw_at (p A B : PTm n) : Γ ⊢[PRAAx] ap2 rawF p (pairT A B) ≐ rawSample p A B := by
  let x := pairT A B
  have read : Γ ⊢[PRAAx] ap2 rawF p x ≐ rawSample p (fstT x) (sndT x) := by
    simpa only [rawF,ap2,subst_rawSample,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      toPR_eq (Γ := Γ) (rawSample (var 0) (fstT (var 1)) (sndT (var 1)) : PTm 2) ![p,x]
  exact read.eqTrans (by
    simpa only [subst_rawSample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.head_cons,Matrix.tail_cons] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (rawSample (var 0) (var 1) (var 2) : PTm 3)
        (σ := ![p,fstT x,sndT x]) (σ' := ![p,A,B])
        (fun i => by fin_cases i; exact .eqRefl _; exact fst_pair _ _; exact snd_pair _ _))

private theorem row_clock_later (p B : PTm n) : Γ ⊢[PRAAx] le p (rowClock p B) := by
  let d := GaussianBinetBoseSeries.denominatorClock p B
  have he : Γ ⊢[PRAAx] le p (GaussianFastValueCut.exponent (GaussianNameReciprocal.modulus B) p) :=
    le_add_right _ _
  have hd : Γ ⊢[PRAAx] le p d := le_trans he (le_add_right _ _)
  exact le_trans hd (le_add_right d (GaussianFastValueCut.normalizer two))

private theorem truncation_error (p s A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] distanceBounded (prefixValue s A B (cutoff p B)) (ap2 reciprocalF s (reciprocalData A B)) one (unit p) := by
  let C := num 4*A
  let N := cutoff p B
  let E := B+N*C
  have hC : Γ ⊢[PRAAx] le one C := positive_product _ _ (by ipra_le 3) hA
  have hE : Γ ⊢[PRAAx] le one E := le_trans hB (le_add_right _ _)
  have hNC : Γ ⊢[PRAAx] le N (N*C) :=
    le_congr (one_mul N) (by ipra_ring) (mul_le_mul_right N hC)
  have hCE : Γ ⊢[PRAAx] le E (C*E) := le_congr (one_mul E) (.eqRefl _) (mul_le_mul_right E hC)
  have enough : Γ ⊢[PRAAx] le ((B*B)*unit p) (one*(C*E)) :=
    le_congr (.eqRefl _) (one_mul (C*E)).eqSymm (le_trans hNC (le_trans (le_add_left _ _) hCE))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hC hE) (unit_positive p) enough
    (partial_error s A B N hA hB)

private theorem rawSample_error (p A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (rawSample p A B) (ap2 reciprocalF p (reciprocalData A B)) (num 4) (unit p) := by
  let N := cutoff p B
  let K := N*GaussianBinetBoseLiteralPrefix.budget N A B
  let s := late p A B
  let r := rowClock s B
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have hr := unit_positive (Γ := Γ) r
  have hN : Γ ⊢[PRAAx] le one N := positive_product _ _ (positive_product _ _ h.andE₂ h.andE₂) hp
  have later : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have budgeted : Γ ⊢[PRAAx] le (K*unit p) (one*unit r) :=
    le_congr (.eqRefl _) (one_mul (unit r)).eqSymm
      (le_trans (GaussianFastValueCut.query_budget K p) (GaussianExponentialReference.unit_monotone (row_clock_later s B)))
  have literal := distance_radius_mono _ _ _ _ one (unit p) hr hp budgeted
    (GaussianBinetBoseLiteralPrefix.finite_error s N A B hN h.andE₂)
  have trunc := truncation_error p s A B h.andE₁ h.andE₂
  have look := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hs hp) hp
    (by ipra_le 𝔞(unit p)*sl (GaussianExponentialReference.unit_monotone later))
    (point_at reciprocalF (reciprocalData A B) s p (reciprocal_regular A B h.andE₁ h.andE₂))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp literal trunc) look)

theorem raw_error (p A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rawF p (pairT A B)) (ap2 reciprocalF p (reciprocalData A B)) (num 4) (unit p) :=
  distance_congr (raw_at p A B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (rawSample_error p A B h)

private theorem raw_observations (p q A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 rawF p (pairT A B)) (ap2 rawF q (pairT A B))
      (num 5*(unit p+unit q)) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  let E := P*Q
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hE := positive_product _ _ hp hq
  have l := distance_radius_mono _ _ _ _ (num 4*Q) E hp hE
    (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) (raw_error p A B h)
  have r := distance_radius_mono _ _ _ _ (num 4*P) E hq hE
    (le_of_eq_add (d := zero) (by dsimp only [E]; ipra_ring)) (raw_error q A B h)
  have m := point_at reciprocalF (reciprocalData A B) p q (reciprocal_regular A B h.andE₁ h.andE₂)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [P,Q]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hE (distance_triangle_same _ _ _ _ _ _ hE l m)
      (distance_symmetric _ _ _ _ hE r))

theorem raw_regular (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] GaussianFastValueCut.regular rawF (num 5) (pairT A B) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (s A) (s B) := by
    simpa [Fm.shift,Syn.shift,s,source,one] using h.shift.shift
  simpa only [GaussianFastValueCut.regular,Syn.shift,s,PTm.subst_num,subst_pairT] using
    raw_observations (var 1) (var 0) (s A) (s B) hs

abbrev nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (A B : PTm n) : PTm n := GaussianFastValueCut.nameData (num 5) (pairT A B)
def clock (p : PTm n) : PTm n := GaussianFastValueCut.exponent (num 5) p

ipra_subst data

theorem sample_at (p A B : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data A B) ≐ rawSample (clock p) A B :=
  (GaussianFastValueCut.name_at rawF (num 5) (pairT A B) p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p) A B)).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianBinetBoseLiteralPrefix.value_canonical _ _ _ _)))

theorem regular (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) : Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  GaussianFastValueCut.name_fast rawF _ _ (raw_regular A B h)

theorem error_at (p A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B)) (ap2 reciprocalF p (reciprocalData A B)) (num 6) (unit p) := by
  let s := clock p
  have hp := unit_positive (Γ := Γ) p
  have hs := unit_positive (Γ := Γ) s
  have later : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have raw := distance_congr (sample_at p A B).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (rawSample_error s A B h)
  have compare := GaussianExponentialReference.dyadic_weaken _ _ _ p s later raw
  have look := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hs hp) hp
    (by ipra_le 𝔞(unit p)*sl (GaussianExponentialReference.unit_monotone later))
    (point_at reciprocalF (reciprocalData A B) s p (reciprocal_regular A B h.andE₁ h.andE₂))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp compare look)

theorem equivalent (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent nameF reciprocalF (data A B) (reciprocalData A B) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 6)
    (regular A B h) (reciprocal_regular A B h.andE₁ h.andE₂) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s B) := by
    simpa [Fm.shift,Syn.shift,s,source,one] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,s,subst_data,subst_reciprocalData,PTm.subst_num] using
    error_at (var 0) (s A) (s B) hs

theorem actual_Bose_literal_exponential_sum_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source (var 0) (var 1) ⟶ pointCN nameF (data (var 0) (var 1)) ⋏
        crossEquivalent nameF reciprocalF (data (var 0) (var 1)) (reciprocalData (var 0) (var 1))) :=
  closeUniv 2 (.impI (.andI (regular _ _ Prf.hyp0) (equivalent _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralCofinal
