import IPRADerivations.Analysis.Gamma.BohrMollerup.FiniteBrackets.GaussianBohrMollerupChords
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderLinear

/-!
# The upper Bohr–Mollerup chord on an integer block

The argument n+x with 0<x<=B lies on the chord from n to n+B.
The first endpoint in the weighted convexity instance is n+B, with
strictly positive weight a when x=a/b. This includes x=B.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupBlockChord

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianBohrMollerupChords (base translated base_source translated_source centered_chord scale_cross scaled_regular)
open GaussianBohrMollerupPresentation (Presentation argument scaledF scaledData observe_value laws)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderLinear (fractionData fractional_regular scaled_fraction)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianRationalNaturalScale (naturalPoint)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def top (b B j : PTm n) : PTm n := base b j+B*b
def complement (a b B : PTm n) : PTm n := monus (B*b) a
def source (a b B : PTm n) : Fm PTm n :=
  GaussianStirlingGammaLogarithm.source a b ⋏ (le one B ⋏ le a (B*b))

@[simp] theorem subst_top {m : ℕ} (σ : Fin n → PTm m) (b B j : PTm n) :
    Syn.subst σ (top b B j) = top (Syn.subst σ b) (Syn.subst σ B) (Syn.subst σ j) := by
  simp [top,base]
@[simp] theorem subst_complement {m : ℕ} (σ : Fin n → PTm m) (a b B : PTm n) :
    Syn.subst σ (complement a b B) = complement (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ B) := by simp [complement]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (a b B : PTm n) :
    (source a b B).subst σ = source (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ B) := by simp [source]

theorem top_source (b B j : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (top b B j) b :=
  .andI (le_trans (base_source b j hb).andE₁ (le_add_right (base b j) (B*b))) hb

theorem scaled_chord (P : Presentation) (a b B j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] realOrder (scaledF P) (addF (scaledF P) (scaledF P))
      (scaledData P (B*b) (translated a b j) b)
      (addData (scaledData P a (top b B j) b) (scaledData P (complement a b B) (base b j) b)) := by
  let V := B*b
  let s := complement a b B
  let k := pred a
  let W := weight k s
  let x := top b B j
  let y := base b j
  let c := translated a b j
  have hv := hp.andE₂.andE₁
  have hr := hp.andE₂.andE₂.andE₂.andE₁
  have hc := hp.andE₂.andE₂.andE₂.andE₂
  have hb := hs.andE₁.andE₂
  have ex : Γ ⊢[PRAAx] succ k ≐ a := (pos_of_one_le hs.andE₁.andE₁).eqSymm
  have es : Γ ⊢[PRAAx] V ≐ a+s := eq_add_of_le hs.andE₂.andE₂
  have ew : Γ ⊢[PRAAx] W ≐ V :=
    (succ_add k s).eqSymm.eqTrans ((congrAdd ex (.eqRefl s)).eqTrans es.eqSymm)
  have center : Γ ⊢[PRAAx] barycenter x y k s ≐ W*c := by
    have e : Γ ⊢[PRAAx] a*x+s*y ≐ V*c := by
      have h := natEq es
      apply deriveNat
      change Groth.ι (IPRA.Q.mk Γ (a*(base b j+V)+s*base b j)) = Groth.ι (IPRA.Q.mk Γ (V*(a+base b j)))
      ipra_simps
      linear_combination -(Groth.ι (IPRA.Q.mk Γ (base b j)))*h
    exact (congrAdd (congrMul ex (.eqRefl x)) (.eqRefl _)).eqTrans
      (e.eqTrans (congrMul ew.eqSymm (.eqRefl c)))
  have hx := top_source b B j hb
  have hy := base_source b j hb
  have hz := translated_source a b j hb
  have original := centered_chord P x y c b k s hv hr hc hx hy.andE₁ hz.andE₁ center
  have px := (observe_value P x b hv hx).andE₁
  have py := (observe_value P y b hv hy).andE₁
  have pz := (observe_value P c b hv hz).andE₁
  have left := scale_cross P.nameF V W _ _ ew.eqSymm pz pz (cross_refl _ _ pz)
  have yreg := scaled_regular P.nameF s _ py
  have right := add_cross (scaledF P) (scaledF P) (scaledF P) (scaledF P)
    (scaledData P (succ k) x b) (scaledData P a x b) (scaledData P s y b) (scaledData P s y b)
    (scaled_regular _ _ _ px) (scaled_regular _ _ _ px) yreg yreg
    (scale_cross P.nameF (succ k) a _ _ ex px px (cross_refl _ _ px)) (cross_refl _ _ yreg)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ left right original

def weightedF (P : Presentation) : PR 2 := addF (scaledF P) (scaledF P)
def weightedData (P : Presentation) (a b B j : PTm n) : PTm n :=
  addData (fractionData P.nameF a (B*b) (argument P (top b B j) b))
    (fractionData P.nameF (complement a b B) (B*b) (argument P (base b j) b))

theorem chord (P : Presentation) (a b B j : PTm n)
    (hp : Γ ⊢[PRAAx] laws P) (hs : Γ ⊢[PRAAx] source a b B) :
    Γ ⊢[PRAAx] realOrder P.nameF (weightedF P) (argument P (translated a b j) b) (weightedData P a b B j) := by
  let V := B*b
  let s := complement a b B
  let F := P.nameF
  let G := scaledF P
  let u := argument P (top b B j) b
  let v := argument P (base b j) b
  let w := argument P (translated a b j) b
  let x := fractionData F a V u
  let y := fractionData F s V v
  let q := naturalPoint V
  have hp' := hp.andE₂.andE₁
  have hb := hs.andE₁.andE₂
  have hV := positive_product _ _ hs.andE₂.andE₁ hb
  have hu := (observe_value P _ _ hp' (top_source b B j hb)).andE₁
  have hv := (observe_value P _ _ hp' (base_source b j hb)).andE₁
  have hw := (observe_value P _ _ hp' (translated_source a b j hb)).andE₁
  have hx := fractional_regular F a V u hu
  have hy := fractional_regular F s V v hv
  have hq := constant_regular (Γ := Γ) q
  have distributed := GaussianNameRingLaws.distributive constantF G G q x y hq hx hy
  have combined := add_cross (productF G) G (productF G) G
    (productData G V x) (productData F a u) (productData G V y) (productData F s v)
    (scaled_regular _ _ _ hx) (scaled_regular _ _ _ hu) (scaled_regular _ _ _ hy) (scaled_regular _ _ _ hv)
    (scaled_fraction F a V u hV hu) (scaled_fraction F s V v hV hv)
  have right := cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ distributed combined)
  have original := scaled_chord P a b B j hp hs
  refine GaussianNamedNaturalScaleOrder.reflect_order F (weightedF P) V w (weightedData P a b B j) hV hw
    (add_fast G G x y hx hy) ?_
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (scaled_regular F V w hw)) right original

theorem actual_general_B_Bohr_Mollerup_chord_closed (P : Presentation) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (laws P ⟶ source (var 0) (var 1) (var 2) ⟶
        realOrder P.nameF (weightedF P) (argument P (translated (var 0) (var 1) (var 3)) (var 1))
          (weightedData P (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (chord P _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupBlockChord
