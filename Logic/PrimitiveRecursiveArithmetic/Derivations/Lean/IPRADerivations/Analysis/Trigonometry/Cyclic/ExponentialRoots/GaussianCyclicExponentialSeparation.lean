import IPRADerivations.Analysis.Trigonometry.Cyclic.Chords.GaussianCyclicRootChord

/-!
# Pairwise apartness of the actual cyclic root samples

For r<s<m, either s-r or its complement m-(s-r) is a positive
half-turn index. The checked cyclic multiplication laws, including the
endpoint identity, bind that half-angle chord to the actual sample
difference. A single later clock suffices for every pair.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicExponentialSeparation

open_ipra
open GaussianCyclicExponentialRoots
  (rootF rootData sample source root_regular sample_bound sampleRadius angleF angleData angle_input)
open GaussianCyclicExponentialGroup (productF productData product_index_cross product_equal_cross endpoint_root_cross)
open GaussianCyclicExponentialSamples (product_error exponential_lower inverseBudget lower_under_half_error)
open GaussianArctangentExponentialPeriod (fullTurnRadius)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameEquivalence (diagonal_at cross_to_diagonal)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qmul positive_product represents_congr)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative_represents)
open GaussianRationalReciprocal (qone)
open GaussianRationalLowerBounds (lower lower_from_representation lower_to_cleared product_lower)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono reversed_difference)
open GaussianReciprocalHorner (qmul_one_right)
open GaussianApproximateInverseDistance (multiply_distance)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalSyntheticDivision (qsub_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def budget : PTm n := two+num 10*sampleRadius
def chordDenominator (m : PTm n) : PTm n := (two*sampleRadius)*GaussianCyclicRootChord.denominator m
def denominator (m : PTm n) : PTm n := two*chordDenominator m
def reserve (m : PTm n) : PTm n :=
  two*inverseBudget fullTurnRadius+GaussianCyclicRootChord.reserve m+denominator m*budget
def clock (m p : PTm n) : PTm n := p+reserve m
def fine (m p : PTm n) : Fm PTm n := le (reserve m) (unit p)

ipra_subst denominator [chordDenominator, GaussianCyclicRootChord.denominator, GaussianCyclicRootChord.phaseDenominator]
ipra_subst reserve [budget, fullTurnRadius, GaussianArctangentExponentialPeriod.twiceRadius, GaussianArctangentQuarterExponential.radius]
ipra_subst clock

theorem clock_later (m p : PTm n) : Γ ⊢[PRAAx] le p (clock m p) := le_add_right _ _
theorem clock_fine (m p : PTm n) : Γ ⊢[PRAAx] fine m (clock m p) :=
  le_trans (le_add_left _ _) (le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow _))

private theorem chord_denominator_positive (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le one (chordDenominator m) :=
  positive_product _ _ (positive_product _ _ (le_succ_self _)
    (RationalNonnegativePowers.denominator_positive _ _ (by ipra_le 2)))
    (GaussianCyclicRootChord.denominator_positive m hm)

theorem denominator_positive (m : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le one (denominator m) :=
  positive_product _ _ (le_succ_self _) (chord_denominator_positive m hm)

theorem sample_index_congr (p m x : PTm n) {r s : PTm n} (h : Γ ⊢[PRAAx] r ≐ s) :
    Γ ⊢[PRAAx] sample p r m x ≐ sample p s m x := by
  simpa only [GaussianCyclicExponentialRoots.subst_sample,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using
    (Prf.eqCongr (sample (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![p,r,m,x]) (σ' := ![p,s,m,x]) (fun j => by fin_cases j; exact .eqRefl p; exact h; exact .eqRefl m; exact .eqRefl x))

private theorem root_product_error (p r s m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m) :
    Γ ⊢[PRAAx] distanceBounded (ap2 productF p (productData r s m x))
      (qmul (sample p r m x) (sample p s m x)) (num 4*sampleRadius) (unit p) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (product_error rootF rootF _ _ p sampleRadius sampleRadius (root_regular r m x hr) (root_regular s m x hs)
      (fun t => sample_bound t r m x hr) (fun t => sample_bound t s m x hs))

private theorem direct_error (p r s d m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m)
    (hd : Γ ⊢[PRAAx] source d m) (e : Γ ⊢[PRAAx] r+d ≐ s) :
    Γ ⊢[PRAAx] distanceBounded (sample p s m x) (qmul (sample p r m x) (sample p d m x)) budget (unit p) := by
  have hp := unit_positive (Γ := Γ) p
  have hs' : Γ ⊢[PRAAx] source (r+d) m := .andI hr.andE₁ (le_congr e.eqSymm (.eqRefl _) hs.andE₂)
  have eq := product_index_cross r d m x hr hd hs'
  have first := distance_symmetric _ _ _ _ hp
    (distance_congr (.eqRefl _) (sample_index_congr p m x e) (.eqRefl _) (.eqRefl _)
      (diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ eq)))
  have last := distance_triangle_same _ _ _ _ _ _ hp first (root_product_error p r d m x hr hd)
  exact distance_radius_mono _ _ _ _ _ _ hp hp
    (by unfold budget; ipra_le 6*Groth.ι (Q.mk Γ (sampleRadius : PTm n))*Groth.ι (Q.mk Γ (unit p))) last

private theorem wrapped_error (p r s d m x : PTm n) (hr : Γ ⊢[PRAAx] source r m) (hs : Γ ⊢[PRAAx] source s m)
    (hd : Γ ⊢[PRAAx] source d m) (e : Γ ⊢[PRAAx] r+m ≐ s+d) :
    Γ ⊢[PRAAx] distanceBounded (sample p r m x) (qmul (sample p s m x) (sample p d m x)) budget (unit p) := by
  let H : PTm n := sampleRadius
  let a := sample p r m x
  let b := sample p m m x
  have hm : Γ ⊢[PRAAx] source m m := .andI hr.andE₁ (le_refl m)
  have hp := unit_positive (Γ := Γ) p
  have last := root_product_error p s d m x hs hd
  have mid := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ (product_equal_cross r m s d m x hr hm hs hd e))
  have prev := distance_symmetric _ _ _ _ hp (root_product_error p r m m x hr hm)
  have bdist : Γ ⊢[PRAAx] distanceBounded b qone two (unit p) :=
    distance_congr (.eqRefl _) (constant_at p qone) (.eqRefl _) (.eqRefl _)
      (diagonal_at rootF constantF (rootData m m x) qone p (cross_to_diagonal _ _ _ _ (endpoint_root_cross m x hr.andE₁)))
  have hC := GaussianRadiusExponentialName.sample_canonical (Γ := Γ) angleF fullTurnRadius p (angleData r m x)
  have start := distance_symmetric _ _ _ _ hp (distance_congr (.eqRefl _) (qmul_one_right a hC)
    (.eqRefl _) (.eqRefl _) (multiply_distance a b qone H two (unit p) hp (sample_bound p r m x hr) bdist))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold budget; dsimp only [H]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp
      (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp start prev) mid) last)

private theorem perturbed_chord (p r s d m x : PTm n) (hs : Γ ⊢[PRAAx] source s m)
    (half : Γ ⊢[PRAAx] GaussianArctangentDivisionAngles.source d m) (hd : Γ ⊢[PRAAx] le one d)
    (hp : Γ ⊢[PRAAx] fine m p)
    (he : Γ ⊢[PRAAx] distanceBounded (sample p r m x) (qmul (sample p s m x) (sample p d m x)) budget (unit p)) :
    Γ ⊢[PRAAx] lower (qsub (sample p r m x) (sample p s m x)) one (denominator m) := by
  let a := sample p s m x
  let b := sample p d m x
  let q := qsub (sample p r m x) a
  let d₀ := GaussianCyclicRootChord.denominator m
  let U := unit p
  let H : PTm n := sampleRadius
  have hU := unit_positive (Γ := Γ) p
  have guard : Γ ⊢[PRAAx] le (two*inverseBudget fullTurnRadius) U :=
    le_trans (le_of_eq_add (d := GaussianCyclicRootChord.reserve m+denominator m*budget) (by unfold reserve; ipra_ring)) hp
  have hHalf : Γ ⊢[PRAAx] le (GaussianCyclicRootChord.reserve m) U :=
    le_trans (le_of_eq_add (d := two*inverseBudget fullTurnRadius+denominator m*budget) (by unfold reserve; ipra_ring)) hp
  have hError : Γ ⊢[PRAAx] le (denominator m*budget) (one*U) :=
    le_congr (.eqRefl _) (one_mul U).eqSymm (le_trans (le_add_left _ _) hp)
  have aLow : Γ ⊢[PRAAx] lower a one (two*H) := exponential_lower angleF fullTurnRadius _ p (angle_input s m x hs) guard
  have hA : Γ ⊢[PRAAx] le one (two*H) :=
    positive_product _ _ (le_succ_self _) (RationalNonnegativePowers.denominator_positive _ _ (by ipra_le 2))
  have hD := GaussianCyclicRootChord.denominator_positive m hs.andE₁
  have low : Γ ⊢[PRAAx] lower (qmul a (qsub b qone)) one (chordDenominator m) :=
    GaussianRationalLowerBounds.lower_congr (.eqRefl _) (one_mul one) (.eqRefl _)
      (product_lower _ _ _ _ _ _ hA hD aLow (GaussianCyclicRootChord.root_minus_one_margin p d m x half hd hHalf))
  have can := GaussianRadiusExponentialName.sample_canonical (Γ := Γ) angleF fullTurnRadius p (angleData s m x)
  have coe : Γ ⊢[PRAAx] qsub (qmul a b) a ≐ qmul a (qsub b qone) :=
    (qsub_congr (.eqRefl _) (qmul_one_right a can).eqSymm).eqTrans
      (GaussianRationalRoundedPower.multiplication_difference a b qone)
  have near := distance_congr (.eqRefl _) coe (add_zero _) (.eqRefl _)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ hU he (distance_refl_zero a U hU))
  exact lower_under_half_error q _ one _ _ U (chord_denominator_positive m hs.andE₁) hU low near hError

private theorem reverse_lower (q r D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] lower (qsub q r) one D) :
    Γ ⊢[PRAAx] lower (qsub r q) one D := by
  let a := qsub q r
  let z := rawGaussian a
  let E := rawDen a
  have hE := raw_den_positive (Γ := Γ) a
  have hh := lower_to_cleared _ _ _ _ _ hE hD (raw_represents a) h
  exact lower_from_representation _ _ E _ _ hE hD
    (represents_congr (reversed_difference q r) (GaussianRootAlgebra.equal_refl _)
      (.eqRefl _) (qnegative_represents _ _ _ (raw_represents a)))
    (le_congr (.eqRefl _) (congrMul (.eqRefl _) (ComplexLogarithmRemainder.normSq_neg z).eqSymm) hh)

private alias positive_gap := Common.one_le_monus_of_lt

theorem pair_margin_at (p r s m x : PTm n) (hrs : Γ ⊢[PRAAx] lt r s)
    (hs : Γ ⊢[PRAAx] lt s m) (hp : Γ ⊢[PRAAx] fine m p) :
    Γ ⊢[PRAAx] lower (qsub (sample p r m x) (sample p s m x)) one (denominator m) := by
  let d := monus s r
  let e := monus m d
  have hm : Γ ⊢[PRAAx] le one m := le_trans (zero_lt_succ s) hs
  have hr : Γ ⊢[PRAAx] source r m := .andI hm (le_trans (le_of_lt hrs) (le_of_lt hs))
  have hs' : Γ ⊢[PRAAx] source s m := .andI hm (le_of_lt hs)
  have d_lt : Γ ⊢[PRAAx] lt d m :=
    lt_of_le_of_lt (GaussianMonicResidualRadius.monus_le_left s r) hs
  have de : Γ ⊢[PRAAx] s ≐ r+d := eq_add_of_le (le_of_lt hrs)
  have ee : Γ ⊢[PRAAx] m ≐ d+e := eq_add_of_le (le_of_lt d_lt)
  refine .orE (le_total (two*d) m) ?_ ?_
  · have c : le (two*d) m :: Γ ⊢[PRAAx] GaussianArctangentDivisionAngles.source d m := .andI hm.wk Prf.hyp0
    have gap := perturbed_chord p s r d m x hr.wk c (positive_gap r s hrs.wk) hp.wk
      (direct_error p r s d m x hr.wk hs'.wk (.andI hm.wk (le_of_lt d_lt.wk)) de.eqSymm.wk)
    exact reverse_lower _ _ _ (denominator_positive m hm.wk) gap
  · let Δ := le m (two*d) :: Γ
    have off : Δ ⊢[PRAAx] le (two*e) m := by
      have b : Δ ⊢[PRAAx] le (e+d) (d+d) :=
        le_congr (ee.wk.eqTrans (add_comm _ _)) (by ipra_ring) Prf.hyp0
      have le' := le_of_add_le_add_right b
      exact le_congr (by ipra_ring) ee.wk.eqSymm
        (le_congr (.eqRefl _) (add_comm _ _) (add_le_add₂ (le_refl e) le'))
    have c : Δ ⊢[PRAAx] GaussianArctangentDivisionAngles.source e m := .andI hm.wk off
    have sum : Δ ⊢[PRAAx] r+m ≐ s+e := by
      have d₁ := natEq (de.wk : Δ ⊢[PRAAx] s ≐ r+d)
      have d₂ := natEq (ee.wk : Δ ⊢[PRAAx] m ≐ d+e)
      apply deriveNat
      ipra_simps
      linear_combination d₂-d₁
    exact perturbed_chord p r s e m x hs'.wk c (positive_gap d m d_lt.wk) hp.wk
      (wrapped_error p r s e m x hr.wk hs'.wk (GaussianCyclicRootHalfAngle.cyclic_source e m c) sum)

theorem pair_margin (p r s m x : PTm n) (hrs : Γ ⊢[PRAAx] lt r s) (hs : Γ ⊢[PRAAx] lt s m) :
    Γ ⊢[PRAAx] lower (qsub (sample (clock m p) r m x) (sample (clock m p) s m x)) one (denominator m) :=
  pair_margin_at _ r s m x hrs hs (clock_fine m p)

theorem actual_cyclic_root_separation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((lt (var 3) (var 2) ⋏ lt (var 2) (var 1)) ⟶
      lower (qsub (sample (clock (var 1) (var 4)) (var 3) (var 1) (var 0))
        (sample (clock (var 1) (var 4)) (var 2) (var 1) (var 0))) one (denominator (var 1))) :=
  closeUniv 5 (.impI (pair_margin _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianCyclicExponentialSeparation
