import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.FirstTerm.GaussianDigammaFirstBernoulliPanel
import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.FinitePanels.GaussianStirlingAllOrderPanelPartsRecurrence

/-!
# Exact finite readback of the first digamma panel

The actual cubic Bernoulli panel is a signed linear combination of
the three original reciprocal-power mass folds on the same mesh.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliPanelSum

open_ipra
open GaussianDigammaFirstBernoulliPanel (reciprocalPart squarePart cubePart decomposed literal_row)
open GaussianStirlingAllOrderFirstPanel (base)
open GaussianStirlingAllOrderKernel (offset offset_positive)
open GaussianStirlingAllOrderPanelPartsFinite (weightBody weightAt weight_at parameters)
open GaussianStirlingAllOrderPanelPartsRecurrence (fullMass panelMass)
open GaussianStirlingAllOrderPanelTail (panel panelData panelBody panel_row_at)
open GaussianStirlingAllOrderReciprocalGridError (gridDen)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product)
open RationalAlgebra (add_congr add_commutative multiply_congr multiply_add multiply_associative
  multiply_commutative multiply_negative negative_congr)
open RationalArithmetic (add multiply negative)
open RationalFiniteSum (sum term termwiseEq sum_ext canonical_equal)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalNormalForm (normalize_well_formed)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" x:max => Groth.ι (Q.mk Γ x)
local notation "subBody" => GaussianStirlingAllOrderSubtractiveSum.body
local notation "subData" => GaussianStirlingAllOrderSubtractiveSum.data

def squareCoeff (U B : PTm n) : PTm n := fraction (two*U+B) B
def cubeCoeff (U B : PTm n) : PTm n := fraction (U*(U+B)) (B*B)

private def lowerBody : PTm 2 := subBody (scaledBody (weightBody 2)) (weightBody 1)
private def splitBody : PTm 2 := subBody lowerBody (scaledBody (weightBody 3))

private def lowerData (U B M : PTm n) : PTm n :=
  subData (pairT (squareCoeff U B) (parameters U B M)) (parameters U B M)

private def splitData (U B M : PTm n) : PTm n :=
  subData (lowerData U B M) (pairT (cubeCoeff U B) (parameters U B M))

private theorem same_fraction (A B C D : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (e : Γ ⊢[PRAAx] A*D ≐ C*B) :
    Γ ⊢[PRAAx] fraction A B ≐ fraction C D := by
  apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ hB) (normalize_well_formed _ _ hD)
    (fraction_represents _ _ hB) (fraction_represents _ _ hD) hB hD
  apply ZT.derive
  simpa only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul] using natEq e

private theorem masses_at (U B M r : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) :
    (Γ ⊢[PRAAx] reciprocalPart U B M zero r ≐ weightAt 1 U B M r) ∧
      (Γ ⊢[PRAAx] squarePart U B M zero r ≐ multiply (squareCoeff U B) (weightAt 2 U B M r)) ∧
      (Γ ⊢[PRAAx] cubePart U B M zero r ≐ multiply (cubeCoeff U B) (weightAt 3 U B M r)) := by
  let P := B*M
  let D := base U B M zero r
  have hD : Γ ⊢[PRAAx] le one D := le_trans (offset_positive U B M zero hU hM) (le_add_right _ _)
  have hd : Γ ⊢[PRAAx] D ≐ gridDen U B M r := by dsimp [D,base,offset,gridDen]; ipra_ring
  have w1 : Γ ⊢[PRAAx] weightAt 1 U B M r ≐ fraction P D :=
    fraction_congr (pw_one P) ((pw_one _).eqTrans hd.eqSymm)
  have p2 (x : PTm n) : Γ ⊢[PRAAx] pw x two ≐ x*x :=
    (pw_succ x one).eqTrans (congrMul (pw_one x) (.eqRefl x))
  have p3 (x : PTm n) : Γ ⊢[PRAAx] pw x (ConciseIPRA.PTm.succ two) ≐ x*x*x :=
    (pw_succ x two).eqTrans (congrMul (p2 x) (.eqRefl x))
  have w2 : Γ ⊢[PRAAx] weightAt 2 U B M r ≐ fraction (P*P) (D*D) :=
    fraction_congr (p2 P) ((p2 _).eqTrans (congrMul hd.eqSymm hd.eqSymm))
  have w3 : Γ ⊢[PRAAx] weightAt 3 U B M r ≐ fraction (P*P*P) (D*D*D) :=
    fraction_congr (p3 P) ((p3 _).eqTrans (congrMul (congrMul hd.eqSymm hd.eqSymm) hd.eqSymm))
  have h2 := positive_product _ _ hD hD
  have h3 := positive_product _ _ h2 hD
  have hBB := positive_product _ _ hB hB
  refine ⟨w1.eqSymm, ?_, ?_⟩
  · refine ((multiply_congr (.eqRefl _) w2).eqTrans
      ((fraction_multiply _ _ _ _ hB h2).eqTrans
        (same_fraction _ _ _ _ (positive_product _ _ hB h2) h2 ?_))).eqSymm
    dsimp [P,D,squarePart]
    ipra_ring
  · refine ((multiply_congr (.eqRefl _) w3).eqTrans
      ((fraction_multiply _ _ _ _ hBB h3).eqTrans
        (same_fraction _ _ _ _ (positive_product _ _ hBB h3) h3 ?_))).eqSymm
    dsimp [P,D,cubePart]
    ipra_ring

private theorem split_at (U B M r : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) (hr : Γ ⊢[PRAAx] le r M) :
    Γ ⊢[PRAAx] term (panelBody 0) r (panelData two U B M zero) ≐ term splitBody r (splitData U B M) := by
  let X := parameters U B M
  let c := squareCoeff U B
  let d := cubeCoeff U B
  let f := scaledBody (weightBody 2)
  let g := scaledBody (weightBody 3)
  have first := (scaled_term (Γ := Γ) (weightBody 2) r c X).eqTrans
    (multiply_congr (.eqRefl c) (weight_at 2 U B M r))
  have last := (scaled_term (Γ := Γ) (weightBody 3) r d X).eqTrans
    (multiply_congr (.eqRefl d) (weight_at 3 U B M r))
  have lower := (GaussianStirlingAllOrderSubtractiveSum.term_at f (weightBody 1) r (pairT c X) X).eqTrans
    (add_congr first (negative_congr (weight_at 1 U B M r)))
  have terms := (GaussianStirlingAllOrderSubtractiveSum.term_at lowerBody g r (lowerData U B M) (pairT d X)).eqTrans
    (add_congr lower (negative_congr last))
  have p := masses_at U B M r hU hB hM
  have e := add_congr ((add_commutative _ _).eqTrans
    (add_congr p.2.1 (negative_congr p.1))) (negative_congr p.2.2)
  exact (panel_row_at 0 two U B M zero r).eqTrans
    ((literal_row U B M zero r hU hM hr).eqTrans (e.eqTrans terms.eqSymm))

private theorem sum_readback (U B M : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] sum (panelBody 0) M (panelData two U B M zero) ≐ sum splitBody M (splitData U B M) := by
  apply sum_ext
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
  have lift (v : PTm n) (hv : Γ ⊢[PRAAx] le one v) : Δ ⊢[PRAAx] le one (Syn.shift v) := by
    simpa [Δ,Fm.shift,Syn.shift,one] using hv.shift.wk
  have hr : Δ ⊢[PRAAx] le (var 0) (Syn.shift M) := le_trans (le_succ_self _) Prf.hyp0
  have h := split_at (Syn.shift U) (Syn.shift B) (Syn.shift M) (var 0) (lift _ hU) (lift _ hB) (lift _ hM) hr
  simpa [Δ,termwiseEq,Syn.shift,splitData,lowerData,squareCoeff,cubeCoeff,two,one] using
    RationalArgmin.rationalEq_congr h.eqSymm (.eqRefl _) (.eqRefl _)

theorem actual_first_panel (U B M : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] panel 0 two U B M zero ≐
      sub (sub (multiply (squareCoeff U B) (panelMass 2 U B M)) (panelMass 1 U B M))
        (multiply (cubeCoeff U B) (panelMass 3 U B M)) := by
  let c := fraction one M
  let X := parameters U B M
  let s := squareCoeff U B
  let t := cubeCoeff U B
  let f := scaledBody (weightBody 2)
  let g := scaledBody (weightBody 3)
  have a := GaussianStirlingAllOrderSubtractiveSum.sum_at (Γ := Γ) f (weightBody 1) M (pairT s X) X
  have b := GaussianStirlingAllOrderSubtractiveSum.sum_at (Γ := Γ) lowerBody g M (lowerData U B M) (pairT t X)
  have v := b.eqTrans (add_congr (a.eqTrans (add_congr (sum_homogeneous _ _ _ _) (.eqRefl _)))
    (negative_congr (sum_homogeneous _ _ _ _)))
  have pull (x y : PTm n) : Γ ⊢[PRAAx] multiply c (sub x y) ≐ sub (multiply c x) (multiply c y) :=
    (multiply_add c x _).eqTrans (add_congr (.eqRefl _) (multiply_negative c y))
  have swap (u v : PTm n) : Γ ⊢[PRAAx] multiply c (multiply u v) ≐ multiply u (multiply c v) :=
    (multiply_associative c u v).eqSymm.eqTrans
      ((multiply_congr (multiply_commutative c u) (.eqRefl v)).eqTrans (multiply_associative _ _ _))
  exact (multiply_congr (.eqRefl _) ((sum_readback U B M hU hB hM).eqTrans v)).eqTrans
    ((pull _ _).eqTrans (add_congr ((pull _ _).eqTrans (add_congr (swap _ _) (.eqRefl _))) (negative_congr (swap _ _))))

theorem actual_first_digamma_Bernoulli_panel_split_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 0) ⋏ (le one (var 1) ⋏ le one (var 2))) ⟶
        panel 0 two (var 0) (var 1) (var 2) zero ≐
          sub (sub (multiply (squareCoeff (var 0) (var 1)) (panelMass 2 (var 0) (var 1) (var 2)))
            (panelMass 1 (var 0) (var 1) (var 2)))
            (multiply (cubeCoeff (var 0) (var 1)) (panelMass 3 (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (.impI (actual_first_panel _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliPanelSum
