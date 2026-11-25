import IPRADerivations.Analysis.GaussianDigammaFirstBernoulliTelescope

/-!
# Finite prefix comparison for the original weighted digamma panels

The exact reference telescope and the local arbitrary-mesh error
give a finite prefix rate on the actual weighted Bernoulli sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianDigammaFirstBernoulliLocal (finite_error coefficient)
open GaussianDigammaFirstBernoulliTelescope (refBody ref_at exact_prefix meshTarget)
open GaussianGammaDigammaFiniteSum (index row_source)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianStirlingAllOrderKernel (offset)
open GaussianStirlingAllOrderPanelPartsOuter (data)
open GaussianStirlingAllOrderPanelPartsOuterFold (panelPrefix panel_at panelBody)
open GaussianStirlingAllOrderPanelTail (panel panel_row_at panelData)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingGammaLogarithm (source)
open RationalAlgebra (multiply_congr)
open RationalFiniteSum (sum_ext termwiseEq)
open RationalGaussianEmbedding (embed subst_embed)
open RationalGaussianRealPart (embedBody embed_sum embed_congr)
open RationalNonnegativePowers (fraction_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def budget (A B L : PTm n) : PTm n := L*coefficient (index A B L) B

@[simp] theorem subst_budget {l : ℕ} (σ : Fin n → PTm l) (A B L : PTm n) :
    Syn.subst σ (budget A B L) = budget (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ L) := by
  simp [budget,coefficient,power,two]

theorem panel_at_base (A B M k : PTm n) : Γ ⊢[PRAAx]
    panel 0 two A B M k ≐ panel 0 two (index A B k) B M zero := by
  let f := GaussianStirlingAllOrderPanelTail.panelBody 0
  let x := panelData two A B M k
  let y := panelData two (index A B k) B M zero
  have rows : Γ ⊢[PRAAx] termwiseEq f f M x y := by
    refine .allI (.impI ?_)
    let a := Syn.shift A
    let b := Syn.shift B
    let m := Syn.shift M
    let j := Syn.shift k
    let i : PTm (n+1) := var 0
    let Δ := lt i m :: Γ.map Fm.shift
    have eq : Δ ⊢[PRAAx] offset a b m j+b*i ≐ offset (index a b j) b m zero+b*i := by
      unfold offset index
      ipra_ring
    have e := (panel_row_at (Γ := Δ) 0 two a b m j i).eqTrans
      ((multiply_congr (.eqRefl _) (fraction_congr (.eqRefl _) (congrAp2 powF (.eqRefl _) eq))).eqTrans
        (panel_row_at 0 two (index a b j) b m zero i).eqSymm)
    simpa [termwiseEq,x,y,f,a,b,m,j,i,Δ,Syn.shift,two] using
      RationalArgmin.rationalEq_congr (.eqRefl _) e (.eqRefl _)
  exact multiply_congr (.eqRefl _) (sum_ext f f M x y rows)

theorem coefficient_mono (U V B : PTm n) (h : Γ ⊢[PRAAx] le U V) :
    Γ ⊢[PRAAx] le (coefficient U B) (coefficient V B) := by
  unfold coefficient
  ipra_le sl h*(2*𝔞 (power 2 B)+(𝔞 U+𝔞 V+𝔞 B)*𝔞 (power 3 B))

theorem prefix_error (A B Q L : PTm n) (hs : Γ ⊢[PRAAx] source A B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] distanceBounded (embed (panelPrefix 0 2 A B (B*Q) L)) (meshTarget A B Q L) (budget A B L) Q := by
  let f := embedBody (panelBody 0 2)
  let x := data A B (B*Q)
  let y := data A B Q
  have rows : Γ ⊢[PRAAx] termsDistance f refBody L x y (coefficient (index A B L) B) Q := by
    refine .allI (.impI ?_)
    let sh (v : PTm n) := Syn.shift v
    let a := sh A
    let b := sh B
    let q := sh Q
    let j := sh L
    let i : PTm (n+1) := var 0
    let Δ := lt i j :: Γ.map Fm.shift
    have s : Δ ⊢[PRAAx] source a b := by simpa [Δ,sh,a,b,Fm.shift,Syn.shift] using hs.shift.wk
    have hq : Δ ⊢[PRAAx] le one q := by simpa [Δ,sh,q,Fm.shift,Syn.shift] using hQ.shift.wk
    have hi : Δ ⊢[PRAAx] lt i j := Prf.hyp0
    have e : Δ ⊢[PRAAx] inst2 f i (data a b (b*q)) ≐ embed (panel 0 two (index a b i) b (b*q) zero) := by
      have read := embed_congr ((panel_at (Γ := Δ) 0 2 a b (b*q) i).eqTrans (panel_at_base a b (b*q) i))
      simpa only [f,embedBody,inst2,RationalFiniteSum.term,subst_embed] using read
    have loc := finite_error (index a b i) b q (row_source a b i s).andE₁ s.andE₂ hq
    have mono : Δ ⊢[PRAAx] le (index a b i) (index a b j) := by
      unfold index
      ipra_le Groth.ι (IPRA.Q.mk Δ b)*sl (le_of_lt hi)
    have bound := le_mul_mono (coefficient_mono (index a b i) (index a b j) b mono) (le_refl q)
    have wide := distance_radius_mono _ _ _ _ _ _ hq hq bound loc
    simpa [termsDistance,x,y,a,b,q,j,i,Δ,sh,Syn.shift,data,coefficient,power,two] using
      distance_congr e.eqSymm (ref_at a b q i).eqSymm (.eqRefl _) (.eqRefl _) wide
  exact distance_congr (embed_sum (panelBody 0 2) L x).eqSymm (exact_prefix A B Q L hs)
    (.eqRefl _) (.eqRefl _) (sum_distance f refBody L x y _ _ hQ rows)

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliPrefix
