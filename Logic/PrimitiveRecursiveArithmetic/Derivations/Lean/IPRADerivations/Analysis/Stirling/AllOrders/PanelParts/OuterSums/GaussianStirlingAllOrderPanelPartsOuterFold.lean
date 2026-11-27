import IPRADerivations.Analysis.Stirling.AllOrders.PanelParts.OuterSums.GaussianStirlingAllOrderPanelPartsOuter

/-!
# Exact readback of the outer integration-by-parts sum

The residual sum splits into the three original cofinal prefixes,
with each panel read at the same mesh and runtime index.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsOuterFold

open_ipra
open GaussianStirlingAllOrderPanelPartsOuter (data body errorSum row_at)
open GaussianStirlingAllOrderPanelPartsRecurrence (panelMass residual)
open GaussianStirlingAllOrderPanelPartsDensities (lowScalar highScalar)
open GaussianStirlingAllOrderPanelDerivative (signedMean)
open GaussianStirlingAllOrderPanelTail (panel panelData)
open GaussianStirlingAllOrderDiscreteParts (sub)
open RationalArithmetic (add multiply negative)
open RationalAlgebra (add_congr multiply_congr negative_congr)
open RationalFiniteSum (term termwiseEq sum_ext)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rsum" => RationalFiniteSum.sum
local notation "diffBody" => GaussianStirlingAllOrderSubtractiveSum.body
local notation "diffData" => GaussianStirlingAllOrderSubtractiveSum.data
local notation "diff_at" => GaussianStirlingAllOrderSubtractiveSum.term_at
local notation "diff_sum_at" => GaussianStirlingAllOrderSubtractiveSum.sum_at

def massBody (e : ℕ) : PTm 2 :=
  let x := var 1
  panelMass e (fstT x+fstT (sndT x)*var 0) (fstT (sndT x)) (sndT (sndT x))

def panelBody (m : ℕ) (q : ℕ) : PTm 2 :=
  let x := var 1
  panel m (num q) (fstT x) (fstT (sndT x)) (sndT (sndT x)) (var 0)

def massPrefix (e : ℕ) (A B M L : PTm n) : PTm n := rsum (massBody e) L (data A B M)
def panelPrefix (m q : ℕ) (A B M L : PTm n) : PTm n := rsum (panelBody m q) L (data A B M)

ipra_subst panelMass [GaussianStirlingAllOrderPanelPartsRecurrence.fullMass, GaussianStirlingAllOrderPanelPartsFold.weightInput, GaussianStirlingAllOrderPanelPartsFinite.parameters]

ipra_subst massPrefix
ipra_subst panelPrefix

theorem mass_at (e : ℕ) (A B M k : PTm n) : Γ ⊢[PRAAx]
    term (massBody e) k (data A B M) ≐ panelMass e (A+B*k) B M := by
  let x := data A B M
  have r : Γ ⊢[PRAAx] sndT x ≐ pairT B M := snd_pair _ _
  have p := (congrFst r).eqTrans (fst_pair _ _)
  have q := (congrSnd r).eqTrans (snd_pair _ _)
  have w : Γ ⊢[PRAAx] fstT x+fstT (sndT x)*k ≐ A+B*k :=
    congrAdd (fst_pair _ _) (congrMul p (.eqRefl _))
  simpa only [term,massBody,inst2,subst_panelMass,subst_fstT,subst_sndT,
    PTm.subst_add,PTm.subst_mul,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (panelMass e (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![fstT x+fstT (sndT x)*k,fstT (sndT x),sndT (sndT x)]) (σ' := ![A+B*k,B,M])
      (fun i => by fin_cases i; exact w; exact p; exact q)

theorem panel_at (m q : ℕ) (A B M k : PTm n) : Γ ⊢[PRAAx]
    term (panelBody m q) k (data A B M) ≐ panel m (num q) A B M k := by
  let x := data A B M
  have r : Γ ⊢[PRAAx] sndT x ≐ pairT B M := snd_pair _ _
  simpa only [term,panelBody,inst2,GaussianStirlingAllOrderPanelTail.subst_panel,
    LeanProofs.IPRA.PTm.subst_num,subst_fstT,subst_sndT,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (panel m (num q) (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![fstT x,fstT (sndT x),sndT (sndT x),k]) (σ' := ![A,B,M,k])
      (fun i => by fin_cases i; exact fst_pair _ _; exact (congrFst r).eqTrans (fst_pair _ _)
                   exact (congrSnd r).eqTrans (snd_pair _ _); exact .eqRefl _)

theorem mass_succ (e : ℕ) (A B M L : PTm n) : Γ ⊢[PRAAx]
    massPrefix e A B M (ConciseIPRA.PTm.succ L) ≐ add (massPrefix e A B M L) (panelMass e (A+B*L) B M) :=
  (RationalFiniteSum.sum_succ _ _ _).eqTrans (add_congr (.eqRefl _) (mass_at e A B M L))

theorem panel_succ (m q : ℕ) (A B M L : PTm n) : Γ ⊢[PRAAx]
    panelPrefix m q A B M (ConciseIPRA.PTm.succ L) ≐ add (panelPrefix m q A B M L) (panel m (num q) A B M L) :=
  (RationalFiniteSum.sum_succ _ _ _).eqTrans (add_congr (.eqRefl _) (panel_at m q A B M L))

private theorem panel_shift (m : ℕ) (q A B M k : PTm n) : Γ ⊢[PRAAx]
    panel m q A B M k ≐ panel m q (A+B*k) B M zero := by
  let x := panelData q A B M k
  let y := panelData q (A+B*k) B M zero
  let f := GaussianStirlingAllOrderPanelTail.panelBody m
  have rows : Γ ⊢[PRAAx] termwiseEq f f M x y := by
    refine .allI (.impI ?_)
    let a := Syn.shift A
    let b := Syn.shift B
    let z := Syn.shift M
    let s := Syn.shift k
    let p := Syn.shift q
    let i : PTm (n+1) := var 0
    let Δ := lt i z :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] GaussianStirlingAllOrderKernel.offset a b z s+b*i ≐
        GaussianStirlingAllOrderKernel.offset (a+b*s) b z zero+b*i := by
      unfold GaussianStirlingAllOrderKernel.offset
      ipra_ring
    have h := (GaussianStirlingAllOrderPanelTail.panel_row_at (Γ := Δ) m p a b z s i).eqTrans
      ((multiply_congr (.eqRefl _)
        (RationalNonnegativePowers.fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) e))).eqTrans
        (GaussianStirlingAllOrderPanelTail.panel_row_at m p (a+b*s) b z zero i).eqSymm)
    simpa [termwiseEq,Δ,f,x,y,a,b,z,s,p,i,Syn.shift] using
      RationalArgmin.rationalEq_congr (.eqRefl _) h (.eqRefl _)
  exact multiply_congr (.eqRefl _) (sum_ext f f M x y rows)

private def meanBody (e : ℕ) : PTm 2 := scaledBody (massBody e)
private def lowerBody (m e : ℕ) : PTm 2 := diffBody (meanBody e) (panelBody (m-1) (e-1))
private def combinedBody (m e : ℕ) : PTm 2 :=
  diffBody (scaledBody (lowerBody m e)) (scaledBody (panelBody m (e+1)))

private def meanInput (m : ℕ) (A B M : PTm n) : PTm n := pairT (signedMean m) (data A B M)
private def lowerInput (m : ℕ) (A B M : PTm n) : PTm n := diffData (meanInput m A B M) (data A B M)
private def combinedInput (m e : ℕ) (A B M : PTm n) : PTm n :=
  diffData (pairT (lowScalar m) (lowerInput m A B M)) (pairT (highScalar e) (data A B M))

private theorem combined_at (m e : ℕ) (A B M i : PTm n) : Γ ⊢[PRAAx]
    term (combinedBody m e) i (combinedInput m e A B M) ≐
      GaussianStirlingAllOrderPanelPartsRecurrence.residual m e (A+B*i) B M := by
  have a := (scaled_term (Γ := Γ) (massBody e) i (signedMean m) (data A B M)).eqTrans
    (multiply_congr (.eqRefl _) (mass_at e A B M i))
  have b := (panel_at (Γ := Γ) (m-1) (e-1) A B M i).eqTrans (panel_shift (m-1) (num (e-1)) A B M i)
  have c := (panel_at (Γ := Γ) m (e+1) A B M i).eqTrans (panel_shift m (num (e+1)) A B M i)
  have d : Γ ⊢[PRAAx] term (lowerBody m e) i (lowerInput m A B M) ≐
      sub (multiply (signedMean m) (panelMass e (A+B*i) B M)) (panel (m-1) (num (e-1)) (A+B*i) B M zero) :=
    (diff_at (meanBody e) (panelBody (m-1) (e-1)) i (meanInput m A B M) (data A B M)).eqTrans
    (add_congr a (negative_congr b))
  exact (diff_at _ _ _ _ _).eqTrans
    (add_congr ((scaled_term _ _ _ _).eqTrans (multiply_congr (.eqRefl _) d))
      (negative_congr ((scaled_term _ _ _ _).eqTrans (multiply_congr (.eqRefl _) c))))

theorem fold_identity (m e : ℕ) (A B M L : PTm n) : Γ ⊢[PRAAx]
    errorSum m e A B M L ≐ sub (multiply (lowScalar m)
      (sub (multiply (signedMean m) (massPrefix e A B M L)) (panelPrefix (m-1) (e-1) A B M L)))
      (multiply (highScalar e) (panelPrefix m (e+1) A B M L)) := by
  let x := data A B M
  let y := combinedInput m e A B M
  let f := body m e
  let g := combinedBody m e
  have rows : Γ ⊢[PRAAx] termwiseEq f g L x y := by
    refine .allI (.impI ?_)
    let a := Syn.shift A
    let b := Syn.shift B
    let z := Syn.shift M
    let j : PTm (n+1) := var 0
    let Δ := lt j (Syn.shift L) :: Γ.map Fm.shift
    have eq := (row_at (Γ := Δ) m e a b z j).eqTrans (combined_at m e a b z j).eqSymm
    simpa [termwiseEq,x,y,combinedInput,lowerInput,meanInput,lowScalar,highScalar,
      GaussianStirlingAllOrderReciprocalWeightError.coefficient,signedMean,GaussianStirlingAllOrderPanelDerivative.meanNumerator,
      BernoulliBounds.zint,Δ,a,b,z,j,Syn.shift] using RationalArgmin.rationalEq_congr (.eqRefl _) eq (.eqRefl _)
  have left : Γ ⊢[PRAAx] rsum (lowerBody m e) L (lowerInput m A B M) ≐
      sub (multiply (signedMean m) (massPrefix e A B M L)) (panelPrefix (m-1) (e-1) A B M L) :=
    (diff_sum_at _ _ _ _ _).eqTrans (add_congr (sum_homogeneous _ _ _ _) (.eqRefl _))
  exact (sum_ext f g L x y rows).eqTrans ((diff_sum_at _ _ _ _ _).eqTrans
    (add_congr ((sum_homogeneous _ _ _ _).eqTrans (multiply_congr (.eqRefl _) left))
      (negative_congr (sum_homogeneous _ _ _ _))))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPartsOuterFold
