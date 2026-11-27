import IPRADerivations.Analysis.Integration.Quadrature.BaselRiemann
import IPRADerivations.Analysis.Stirling.Wallis.GaussianGammaHalfWallisRate
import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddCoefficients
import IPRADerivations.Analysis.Names.Arithmetic.RationalReciprocalPowerName

/-!
# Literal reciprocal squares in the original Basel estimate

The rational sum evaluator and the factorial-cleared Basel sum agree at
every admissible cutoff. After normalization, the Basel Riemann estimate
compares that literal reciprocal-square sum with the original π grid.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBaselBinding

open_ipra
open BaselSquares (S qq sB S_succ fact_eq)
open BaselUniform (cut)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaHalfRisingFactorial (factorial_positive)
open GaussianGammaHalfWallisRate (piGrid)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianStirlingOddCoefficients (fraction_equal fraction_embed fraction_add_same fraction_product)
open Products (fact)
open RationalGaussianEmbedding (embed embed_at embedF embed_add)
open RationalReciprocalPowerTail (reciprocalPower tail tail_succ tail_zero)
open RationalValueBounds (upper radius radius_of_upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "scalarFraction" => GaussianEuclideanDistanceName.fraction

def literalSum (m : PTm n) : PTm n := embed (tail two zero m)

ipra_subst literalSum [two, one]

private theorem embed_congr {x y : PTm n} (e : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] embed x ≐ embed y :=
  (embed_at x).eqSymm.eqTrans ((congrAp1 embedF e).eqTrans (embed_at y))

private theorem fraction_congr {A B C D : PTm n} (e : Γ ⊢[PRAAx] A ≐ C) (d : Γ ⊢[PRAAx] B ≐ D) :
    Γ ⊢[PRAAx] fraction A B ≐ fraction C D :=
  GaussianCompactRiemannName.fraction_congr A C B D e d

theorem reciprocal_square_cleared (m L : PTm n) (h : Γ ⊢[PRAAx] le (succ m) L) : Γ ⊢[PRAAx]
    embed (reciprocalPower two (succ m)) ≐ fraction (qq (succ m) L) (fact L*fact L) := by
  let j := succ m
  let F := fact L
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have hF := factorial_positive (Γ := Γ) L
  have hD := positive_product _ _ hF hF
  have square : Γ ⊢[PRAAx] pw j two ≐ j*j := (pw_succ j one).eqTrans (congrMul (pw_one j) (.eqRefl _))
  have e := natEq (fact_eq h)
  have native : Γ ⊢[PRAAx] one*(F*F) ≐ qq j L*(j*j) := by
    apply deriveNat
    dsimp only [F, j, qq]
    ipra_simps
    rw [e]
    ring
  exact (embed_congr (RationalNonnegativePowers.fraction_congr (.eqRefl _) square)).eqTrans
    ((fraction_embed one (j*j) (positive_product _ _ hj hj)).eqTrans
      (fraction_equal one (j*j) (qq j L) (F*F) (positive_product _ _ hj hj) hD native))

private def clearingLaw (m L : PTm n) : Fm PTm n :=
  le m L ⟶ literalSum m ≐ fraction (S m L) (fact L*fact L)

@[simp] private theorem subst_clearingLaw {l : ℕ} (σ : Fin n → PTm l) (m L : PTm n) :
    (clearingLaw m L).subst σ = clearingLaw (Syn.subst σ m) (Syn.subst σ L) := by
  simp [clearingLaw, fact]

private theorem cleared_zero (L : PTm n) : Γ ⊢[PRAAx] literalSum zero ≐ fraction (S zero L) (fact L*fact L) := by
  have hF := factorial_positive (Γ := Γ) L
  have hD := positive_product _ _ hF hF
  have e : Γ ⊢[PRAAx] S zero L ≐ zero := sum_zero sB L
  exact (embed_congr (tail_zero two zero)).eqTrans ((fraction_embed zero one (le_refl one)).eqTrans
    ((fraction_equal zero one zero (fact L*fact L) (le_refl one) hD (by ipra_ring)).eqTrans
      (fraction_congr e.eqSymm (.eqRefl _))))

private theorem cleared_succ (m L : PTm n) (ih : Γ ⊢[PRAAx] clearingLaw m L)
    (h : Γ ⊢[PRAAx] le (succ m) L) : Γ ⊢[PRAAx]
    literalSum (succ m) ≐ fraction (S (succ m) L) (fact L*fact L) := by
  let D := fact L*fact L
  have hF := factorial_positive (Γ := Γ) L
  have hD := positive_product _ _ hF hF
  have previous := ih.impE (le_trans (le_succ_self m) h)
  have step := (RationalReciprocalPowerTail.reciprocal_congr (Γ := Γ) (m := two) (.eqRefl two)
    (congrSucc (zero_add m)))
  have read := (embed_congr ((tail_succ two zero m).eqTrans (RationalAlgebra.add_congr (.eqRefl _) step))).eqTrans
    (embed_add (tail two zero m) (reciprocalPower two (succ m)))
  exact read.eqTrans ((qadd_congr previous (reciprocal_square_cleared m L h)).eqTrans
    ((fraction_add_same (S m L) (qq (succ m) L) D hD).eqTrans (fraction_congr (S_succ m L).eqSymm (.eqRefl _))))

theorem literal_sum_cleared (m L : PTm n) (h : Γ ⊢[PRAAx] le m L) : Γ ⊢[PRAAx]
    literalSum m ≐ fraction (S m L) (fact L*fact L) := by
  have hall : Γ ⊢[PRAAx] .all (clearingLaw (var 0) (Syn.shift L)) := by
    ipra_qfind (⟨le_QF _ _, trivial⟩) [subst_clearingLaw]
    · exact .impI (cleared_zero L)
    · exact .impI (cleared_succ (var 0) (Syn.shift L) Prf.hyp1 Prf.hyp0)
  have hm : Γ ⊢[PRAAx] clearingLaw m L := by
    simpa only [subst_clearingLaw,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using hall.allE m
  exact hm.impE h

private theorem fraction_upper_same (A B E U : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] le (U*A) (U*B+E)) : Γ ⊢[PRAAx] upper (scalarFraction A E) (scalarFraction B E) one U := by
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ _ _ E E one U hE hE
    (GaussianEuclideanDistanceName.fraction_represents A E hE) (GaussianEuclideanDistanceName.fraction_represents B E hE)
  apply zle_of_toZ (E*monus (U*B+E) (U*A))
  have e := natEq (eq_add_of_le h)
  simp only [ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat]
  ipra_simps
  linear_combination -𝔞(E)*e

private theorem fraction_distance_same (A B E U : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] le (U*A) (U*B+E)) (h' : Γ ⊢[PRAAx] le (U*B) (U*A+E)) : Γ ⊢[PRAAx]
    distanceBounded (fraction A E) (fraction B E) one U := by
  have r : Γ ⊢[PRAAx] radius (scalarFraction A E) (scalarFraction B E) one U :=
    radius_of_upper _ _ _ _ (fraction_upper_same A B E U hE h) (fraction_upper_same B A E U hE h')
  exact distance_congr (fraction_embed A E hE) (fraction_embed B E hE) (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hU r)

theorem finite_Basel_distance (p m L : PTm n) (hm : Γ ⊢[PRAAx] le (cut p) m)
    (hL : Γ ⊢[PRAAx] le (succ (two*cut p)) L)
    (hQ : Γ ⊢[PRAAx] le (two*(cut p*cut p*(cut p*cut p))) L) (hmL : Γ ⊢[PRAAx] le m L) :
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction (num 6) one) (literalSum m))
      (qmul (piGrid (cut p*cut p) L) (piGrid (cut p*cut p) L)) one (unit p) := by
  let F := fact L
  let M := cut p*cut p
  let Q := BaselQuadrature.Q M L
  have hF := factorial_positive (Γ := Γ) L
  have hD := positive_product _ _ hF hF
  have raw := BaselRiemann.riemann hm hL hQ hmL
  have base := fraction_distance_same (num 6*S m L) (num 16*(Q*Q)) (F*F) (unit p) hD (unit_positive p)
    raw.andE₁ raw.andE₂
  have lhs : Γ ⊢[PRAAx] qmul (fraction (num 6) one) (literalSum m) ≐ fraction (num 6*S m L) (F*F) :=
    (qmul_congr (.eqRefl _) (literal_sum_cleared m L hmL)).eqTrans
      ((fraction_product (num 6) one (S m L) (F*F) (le_refl one) hD).eqTrans (fraction_congr (.eqRefl _) (one_mul _)))
  have rhs : Γ ⊢[PRAAx] qmul (piGrid M L) (piGrid M L) ≐ fraction (num 16*(Q*Q)) (F*F) :=
    (fraction_product (num 4*Q) F (num 4*Q) F hF hF).eqTrans (fraction_congr (by ipra_ring) (.eqRefl _))
  exact distance_congr lhs.eqSymm rhs.eqSymm (.eqRefl _) (.eqRefl _) base

end LeanProofs.IPRA.Analysis.GaussianBinetBaselBinding
