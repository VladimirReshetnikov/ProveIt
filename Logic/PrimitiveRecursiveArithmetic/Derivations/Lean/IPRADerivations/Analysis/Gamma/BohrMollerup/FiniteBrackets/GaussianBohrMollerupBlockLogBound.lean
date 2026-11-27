import IPRADerivations.Analysis.Gamma.BohrMollerup.FiniteBrackets.GaussianBohrMollerupBracketEndpoints
import IPRADerivations.Analysis.Logarithm.PositiveAxis.Bounds.GaussianPositiveRationalLogarithmOrder
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderEnvelope

/-!
# The maximum logarithm on the finite Bohr–Mollerup block

The actual sum of B shifted logarithm names is bounded above by B
times its final logarithm. The finite comparison uses the same
original harmonic clock on every term and on its constant cap.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupBlockLogBound

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianBohrMollerupBracketEndpoints (rowBody row_at sumData sum_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyModulus multiplyData)
open GaussianNameEquivalence (cross_refl)
open GaussianNameRingLaws (multiply_sample_error)
open GaussianNamedFiniteSumFamily (finite body term_at sample_at)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (constantBody constant_sum)
open GaussianRationalNaturalScale (naturalPoint natScale)
open GaussianStirlingGammaLogarithm (source)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalValueBounds (upper upper_of_order upper_of_radius upper_triangle upper_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "Sum" => GaussianBohrMollerupBracketEndpoints.sumF
local notation "logData" => GaussianHarmonicLogarithmName.data

def cap (a b N : PTm n) : PTm n := a+b*pred N

ipra_subst cap

theorem cap_source (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] source (cap a b N) b :=
  .andI (le_trans hs.andE₁ (le_add_right a (b*pred N))) hs.andE₂

private theorem cap_ge_row (a b N i : PTm n) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (a+b*i) (cap a b N) := by
  have eq := pos_of_one_le hN
  have h' : Γ ⊢[PRAAx] le (succ i) (succ (pred N)) := le_congr (.eqRefl _) eq hi
  have idx : Γ ⊢[PRAAx] le i (pred N) := (succ_monus_succ _ _).eqSymm.eqTrans h'
  exact add_le_add₂ (le_refl a) (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right b idx))

private abbrev row : PTm 2 := body H rowBody
private def observed (p a b N : PTm n) : PTm n := ap2 H p (logData (cap a b N) b)
private def sumLaw (p a b N j : PTm n) : Fm PTm n :=
  le j N ⟶ rationalLE (fstT (finite H rowBody p j (pairT a b)))
    (fstT (GaussianRationalFiniteSum.sum constantBody j (observed p a b N)))

@[simp] private theorem subst_sumLaw {m : ℕ} (σ : Fin n → PTm m) (p a b N j : PTm n) :
    (sumLaw p a b N j).subst σ =
      sumLaw (Syn.subst σ p) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) (Syn.subst σ j) := by simp [sumLaw,finite,observed]

private theorem raw_step (p a b N j : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hj : Γ ⊢[PRAAx] lt j N)
    (ih : Γ ⊢[PRAAx] rationalLE (fstT (finite H rowBody p j (pairT a b)))
      (fstT (GaussianRationalFiniteSum.sum constantBody j (observed p a b N)))) :
    Γ ⊢[PRAAx] rationalLE (fstT (finite H rowBody p (succ j) (pairT a b)))
      (fstT (GaussianRationalFiniteSum.sum constantBody (succ j) (observed p a b N))) := by
  let x := pairT p (pairT a b)
  let y := observed p a b N
  let f := finite H rowBody p j (pairT a b)
  let g := GaussianRationalFiniteSum.sum constantBody j y
  let u := ap2 H p (logData (a+b*j) b)
  have cell := (term_at (Γ := Γ) H rowBody j p (pairT a b)).eqTrans (congrAp2 H (.eqRefl p) (row_at j a b))
  have h := GaussianPositiveRationalLogarithmOrder.observation_order p (a+b*j) (cap a b N) b (cap_ge_row a b N j hN hj)
  have add := GaussianRationalSyntheticBounds.add_monotone _ _ _ _ ih h
  have one : Γ ⊢[PRAAx] fstT (finite H rowBody p (succ j) (pairT a b)) ≐ RationalArithmetic.add (fstT f) (fstT u) :=
    (congrFst ((GaussianRationalFiniteSum.sum_succ row j x).eqTrans
      (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl f) cell))).eqTrans (RationalGaussianRealPart.real_add f u)
  have two : Γ ⊢[PRAAx] fstT (GaussianRationalFiniteSum.sum constantBody (succ j) y) ≐ RationalArithmetic.add (fstT g) (fstT y) :=
    (congrFst (GaussianRationalFiniteSum.sum_succ constantBody j y)).eqTrans (RationalGaussianRealPart.real_add g y)
  exact rationalLE_congr one.eqSymm two.eqSymm add

theorem raw_order (p a b N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] rationalLE (fstT (finite H rowBody p N (pairT a b))) (fstT (natScale N (observed p a b N))) := by
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have ns : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift
  have out : Γ ⊢[PRAAx] .all (sumLaw (sh p) (sh a) (sh b) (sh N) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,le_QF _ _⟩) [subst_sumLaw, sh]
    · exact .impI (rationalLE_congr
        (congrFst (GaussianRationalFiniteSum.sum_zero row (pairT p (pairT a b)))).eqSymm
        (congrFst (GaussianRationalFiniteSum.sum_zero constantBody (observed p a b N))).eqSymm
        (RationalArgmin.reflexive _))
    · exact .impI (raw_step _ _ _ _ _ ns.wk.wk Prf.hyp0
        (Prf.hyp1.impE (le_trans (le_succ_self _) Prf.hyp0)))
  have e : Γ ⊢[PRAAx] sumLaw p a b N N := by
    simpa only [subst_sumLaw,sh,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using out.allE N
  exact rationalLE_congr (.eqRefl _) (congrFst (constant_sum (observed p a b N) N)) (e.impE (le_refl N))

private def budget (a b N : PTm n) : PTm n :=
  two*N+(multiplyModulus constantF H (naturalPoint N) (logData (cap a b N) b)+one)

@[simp] private theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (budget a b N) = budget (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [budget,two,one]

private theorem diagonal_order (p a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] upper (fstT (ap2 Sum p (sumData a b N)))
      (fstT (ap2 (productF H) p (productData H N (logData (cap a b N) b)))) (budget a b N) (unit p) := by
  let k := exponent N p
  let D := unit p
  let x := logData (cap a b N) b
  let w := naturalPoint N
  let r := productData H N x
  let K := multiplyModulus constantF H w x+one
  let u := ap2 H k x
  let v := ap2 H p x
  let f := ap2 Sum p (sumData a b N)
  let g := ap2 (productF H) p r
  have hD := unit_positive (Γ := Γ) p
  have ht := GaussianHarmonicLogarithmName.name_regular (cap a b N) b (cap_source a b N hs)
  have read := sample_at (Γ := Γ) H rowBody p N (pairT a b)
  have raw := rationalLE_congr (congrFst read).eqSymm
    (congrFst (GaussianRationalNaturalScale.natScale_as_product N u)) (raw_order k a b N hN)
  have obs := GaussianEulerUpperPowerCompatibility.later_cross H H x x p k p (le_add_right _ _) (le_refl p) (cross_refl _ _ ht)
  have current : Γ ⊢[PRAAx] distanceBounded (qmul w u) (qmul w v) (N*two) D :=
    GaussianApproximateInverseDistance.multiply_distance w u v N two D hD
      (GaussianNamedNaturalScale.natural_point_bound N) obs
  have h0 := upper_of_radius _ _ _ _ (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hD current)
  have last := multiply_sample_error constantF H w x p (constant_regular w) ht
  have fix := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_congr (constant_at p w) (.eqRefl _))
    (.eqRefl _) (.eqRefl _) last
  have h1 := upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ hD (distance_symmetric g (qmul w v) K D hD fix))
  have exactOrder : Γ ⊢[PRAAx] upper (fstT f) (fstT (qmul w u)) zero D := upper_of_order _ _ _ _ raw
  have joined := RationalValueBounds.upper_triangle _ _ _ _ _ _ _
    (RationalValueBounds.upper_triangle _ _ _ _ _ _ _ exactOrder h0) h1
  exact RationalValueBounds.upper_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hD hD) hD) joined (le_of_eq_add (d := zero) (by
      change Γ ⊢[PRAAx]
        ((two*N+K)*((D*D)*D)) ≐ (((zero*D+(N*two)*D)*D+K*(D*D))*D)+zero
      ipra_ring))

theorem sum_order (a b N : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] realOrder Sum (productF H) (sumData a b N) (productData H N (logData (cap a b N) b)) := by
  have r := GaussianHarmonicLogarithmName.name_regular (cap a b N) b (cap_source a b N hs)
  apply GaussianNamedRealOrderEnvelope.order_from_envelope _ _ _ _ (budget a b N) (sum_regular a b N hs)
    (GaussianBohrMollerupChords.scaled_regular H N _ r)
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have ss : Δ ⊢[PRAAx] source (sh a) (sh b) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  have nn : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift
  simpa only [GaussianNamedRealOrderEnvelope.envelope,Syn.shift,sh,Δ,
    GaussianBohrMollerupBracketEndpoints.subst_sumData,GaussianNaturalScaleProductName.subst_productData,
    subst_cap,subst_budget,GaussianHarmonicLogarithmName.subst_data] using diagonal_order (var 0) (sh a) (sh b) (sh N) ss nn

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupBlockLogBound
