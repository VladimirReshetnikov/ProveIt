import IPRADerivations.Analysis.Gamma.BohrMollerup.GaussianBohrMollerupPresentation
import IPRADerivations.Analysis.Gamma.GaussianGammaRationalFractionalChord
import IPRADerivations.Analysis.Stirling.GaussianStirlingGammaFractionalIncrementConvexity

/-!
# Two rational chords across an integer-translated argument

For a positive rational a/b and a positive integer j, interpolate j+1
between j and j+1+a/b. Also interpolate j+1+a/b between j+1 and
j+2+a/b. The center fractions are rescaled explicitly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupChords

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianBohrMollerupPresentation (Presentation argument scaledF scaledData
  observe_value observe_rescale observe_convex values rescaling convexity)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianGammaWeierstrassApproximant (constant_data_cross)
open GaussianNameArithmetic (addF addData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianStirlingGammaLogarithm (source)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def base (b j : PTm n) : PTm n := b*succ j
def translated (a b j : PTm n) : PTm n := a+base b j

theorem base_source (b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] source (base b j) b :=
  .andI (positive_product _ _ hb (zero_lt_succ _)) hb

theorem translated_source (a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] source (translated a b j) b :=
  .andI (le_trans (base_source b j hb).andE₁ (le_add_left _ _)) hb

theorem argument_congr (P : Presentation) (a b c d : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ c) (hb : Γ ⊢[PRAAx] b ≐ d) :
    Γ ⊢[PRAAx] argument P a b ≐ argument P c d := by
  simpa only [GaussianBohrMollerupPresentation.subst_argument,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (argument P (var 0) (var 1) : PTm 2)
      (σ := ![a,b]) (σ' := ![c,d]) (fun i => by fin_cases i; exact ha; exact hb)

theorem scaled_regular (f : PR 2) (k x : PTm n) (hx : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] pointCN (productF f) (productData f k x) :=
  multiply_fast _ _ _ _ (constant_regular _) hx

theorem scale_cross (f : PR 2) (i j x y : PTm n) (e : Γ ⊢[PRAAx] i ≐ j)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN f y)
    (hxy : Γ ⊢[PRAAx] crossEquivalent f f x y) :
    Γ ⊢[PRAAx] crossEquivalent (productF f) (productF f) (productData f i x) (productData f j y) := by
  have ec : Γ ⊢[PRAAx] naturalPoint i ≐ naturalPoint j := by
    simpa only [GaussianRationalNaturalScale.subst_naturalPoint,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (naturalPoint (var 0) : PTm 1)
        (σ := ![i]) (σ' := ![j]) (fun k => by fin_cases k; exact e)
  exact GaussianGammaAdjacentCutoff.multiply_cross _ _ _ _ _ _ _ _
    (constant_regular _) (constant_regular _) hx hy (constant_data_cross _ _ ec) hxy

theorem rescale_from (P : Presentation) (c d a b k : PTm n)
    (hr : Γ ⊢[PRAAx] rescaling P) (hs : Γ ⊢[PRAAx] source a b) (hk : Γ ⊢[PRAAx] le one k)
    (ec : Γ ⊢[PRAAx] c ≐ k*a) (ed : Γ ⊢[PRAAx] d ≐ k*b) :
    Γ ⊢[PRAAx] crossEquivalent P.nameF P.nameF (argument P c d) (argument P a b) :=
  cross_data_congr _ _ _ _ _ _ (argument_congr P _ _ _ _ ec ed).eqSymm (.eqRefl _)
    (observe_rescale P a b k hr hs hk)

theorem centered_chord (P : Presentation) (x y c b r s : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] rescaling P) (hj : Γ ⊢[PRAAx] convexity P)
    (hx : Γ ⊢[PRAAx] source x b) (hy : Γ ⊢[PRAAx] le one y) (hc : Γ ⊢[PRAAx] le one c)
    (ec : Γ ⊢[PRAAx] barycenter x y r s ≐ weight r s*c) :
    Γ ⊢[PRAAx] realOrder (scaledF P) (addF (scaledF P) (scaledF P))
      (scaledData P (weight r s) c b) (addData (scaledData P (succ r) x b) (scaledData P s y b)) := by
  let w := weight r s
  let t := barycenter x y r s
  have hw : Γ ⊢[PRAAx] le one w := zero_lt_succ _
  have et : Γ ⊢[PRAAx] source t (w*b) := .andI
    (le_congr (.eqRefl _) ec.eqSymm (positive_product _ _ hw hc)) (positive_product _ _ hw hx.andE₂)
  have ht := (observe_value P t (w*b) hv et).andE₁
  have hz := (observe_value P c b hv (.andI hc hx.andE₂)).andE₁
  have ecross := scale_cross P.nameF w w _ _ (.eqRefl _) ht hz
    (rescale_from P t (w*b) c b w hr (.andI hc hx.andE₂) hw ec (.eqRefl _))
  have right := GaussianNameArithmetic.add_fast _ _ _ _
    (scaled_regular _ (succ r) _ (observe_value P x b hv hx).andE₁)
    (scaled_regular _ s _ (observe_value P y b hv (.andI hy hx.andE₂)).andE₁)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ ecross)
    (cross_refl _ _ right) (observe_convex P x y b r s hj hx hy)

private theorem chord_weights (P : Presentation) (x y c b u v : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] rescaling P) (hj : Γ ⊢[PRAAx] convexity P)
    (hx : Γ ⊢[PRAAx] source x b) (hy : Γ ⊢[PRAAx] le one y) (hc : Γ ⊢[PRAAx] le one c)
    (hu : Γ ⊢[PRAAx] le one u) (eq : Γ ⊢[PRAAx] u*x+v*y ≐ (u+v)*c) :
    Γ ⊢[PRAAx] realOrder (scaledF P) (addF (scaledF P) (scaledF P))
      (scaledData P (u+v) c b) (addData (scaledData P u x b) (scaledData P v y b)) := by
  let k := pred u
  let w := weight k v
  have eu : Γ ⊢[PRAAx] succ k ≐ u := (pos_of_one_le hu).eqSymm
  have ew : Γ ⊢[PRAAx] w ≐ u+v := by
    have a := natEq eu
    dsimp [w,weight]
    apply deriveNat
    ipra_simps
    linear_combination a
  have center : Γ ⊢[PRAAx] barycenter x y k v ≐ w*c :=
    (congrAdd (congrMul eu (.eqRefl _)) (.eqRefl _)).eqTrans (eq.eqTrans (congrMul ew.eqSymm (.eqRefl _)))
  have hx' := (observe_value P x b hv hx).andE₁
  have hy' := (observe_value P y b hv (.andI hy hx.andE₂)).andE₁
  have hc' := (observe_value P c b hv (.andI hc hx.andE₂)).andE₁
  have left := scale_cross P.nameF (u+v) w _ _ ew.eqSymm hc' hc' (cross_refl _ _ hc')
  have right := add_cross (scaledF P) (scaledF P) (scaledF P) (scaledF P)
    (scaledData P (succ k) x b) (scaledData P u x b) (scaledData P v y b) (scaledData P v y b)
    (scaled_regular _ _ _ hx') (scaled_regular _ _ _ hx') (scaled_regular _ _ _ hy') (scaled_regular _ _ _ hy')
    (scale_cross P.nameF (succ k) u _ _ eu hx' hx' (cross_refl _ _ hx'))
    (cross_refl _ _ (scaled_regular _ _ _ hy'))
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ left right
    (centered_chord P x y c b k v hv hr hj hx hy hc center)

theorem lower_chord (P : Presentation) (a b j : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] rescaling P) (hj : Γ ⊢[PRAAx] convexity P)
    (s : Γ ⊢[PRAAx] source a b) (h : Γ ⊢[PRAAx] le one j) : Γ ⊢[PRAAx]
    realOrder (scaledF P) (addF (scaledF P) (scaledF P)) (scaledData P (a+b) (base b j) b)
      (addData (scaledData P a (b*j) b) (scaledData P b (translated a b j) b)) := by
  apply chord_weights P (b*j) (translated a b j) (base b j) b a b hv hr hj
    (.andI (positive_product _ _ s.andE₂ h) s.andE₂) (translated_source a b j s.andE₂).andE₁
    (base_source b j s.andE₂).andE₁ s.andE₁
  unfold translated base
  ipra_ring

theorem upper_chord (P : Presentation) (a b j : PTm n)
    (hv : Γ ⊢[PRAAx] values P) (hr : Γ ⊢[PRAAx] rescaling P) (hj : Γ ⊢[PRAAx] convexity P)
    (s : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    realOrder (scaledF P) (addF (scaledF P) (scaledF P)) (scaledData P (b+a) (translated a b j) b)
      (addData (scaledData P b (base b j) b) (scaledData P a (translated a b j+b) b)) := by
  have ht := (translated_source a b j s.andE₂).andE₁
  apply chord_weights P (base b j) (translated a b j+b) (translated a b j) b b a hv hr hj
    (base_source b j s.andE₂) (le_trans ht (le_add_right _ _)) ht s.andE₂
  unfold translated base
  ipra_ring

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupChords
