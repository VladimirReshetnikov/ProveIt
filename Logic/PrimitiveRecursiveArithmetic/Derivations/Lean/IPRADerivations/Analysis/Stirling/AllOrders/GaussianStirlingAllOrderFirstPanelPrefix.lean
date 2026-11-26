import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderFirstPanelCommonMesh
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderFirstPanelImproper
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderPanelPartsOuterFold

/-!
# A common-mesh original prefix for the first Bernoulli kernel

All panels in the prefix use one actual grid. At the original cutoff
the half of that finite sum approaches the original Stirling remainder.
The comparison keeps the original harmonic-logarithm and Stirling
telescope programs at their independent clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianRationalHorner (positive_product)
open GaussianNameEquivalence (cross_at)
open GaussianFastValueCut (exponent query_budget)
open GaussianStirlingAllOrderFirstPanelCommonMesh (original_difference_at)
open GaussianStirlingAllOrderFirstPanelReadback (halfPanel)
open GaussianStirlingAllOrderPanelPartsOuter (data)
open GaussianStirlingAllOrderPanelPartsOuterFold (panelPrefix panel_at)
open GaussianStirlingTelescope (rawSum sampleData dBody d_at)
open GaussianStirlingNames (source)
open GaussianStirlingGlobalBounds (steps remainderF remainderData)
open RationalArithmetic (multiply)
open RationalAlgebra (multiply_congr)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)
open RationalGaussianEmbedding (embed)
open RationalGaussianRealPart (embedBody embed_congr embed_sum)
open GaussianEuclideanDistanceName (fraction)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)
local notation "body" => GaussianStirlingAllOrderPanelPartsOuterFold.panelBody 0 1

def halfPrefix (A B Q L : PTm n) : PTm n := embed (multiply (fraction one two) (panelPrefix 0 1 A B (B*Q) L))

def rowCap (A B L : PTm n) : PTm n := num 4*(A+B*L+B)+two
def rowClock (A B L p : PTm n) : PTm n := exponent (L*rowCap A B L) p

@[simp] theorem subst_rowCap {l : ℕ} (σ : Fin n → PTm l) (A B L : PTm n) :
    Syn.subst σ (rowCap A B L) = rowCap (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ L) := by simp [rowCap]
@[simp] theorem subst_rowClock {l : ℕ} (σ : Fin n → PTm l) (A B L p : PTm n) :
    Syn.subst σ (rowClock A B L p) = rowClock (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ L) (Syn.subst σ p) :=
  by simp [rowClock]

theorem row_clock_ge (A B L p : PTm n) : Γ ⊢[PRAAx] le (L*unit p) (unit (rowClock A B L p)) := by
  have h : Γ ⊢[PRAAx] le (L*unit p) (L*rowCap A B L*unit p) := by
    unfold rowCap
    ipra_le 4*𝔞 L*𝔞 (unit p)*(𝔞 A+𝔞 B*𝔞 L+𝔞 B)+𝔞 L*𝔞 (unit p)
  exact le_trans h (query_budget (L*rowCap A B L) p)

private def gaussianBody : PTm 2 := embedBody (scaledBody body)
private def gaussianData (A B Q : PTm n) : PTm n := pairT (fraction one two) (data A B (B*Q))

@[simp] theorem subst_gaussianData {l : ℕ} (σ : Fin n → PTm l) (A B Q : PTm n) :
    Syn.subst σ (gaussianData A B Q) = gaussianData (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ Q) :=
  by simp [gaussianData]

private theorem gaussian_at (A B Q k : PTm n) : Γ ⊢[PRAAx]
    inst2 gaussianBody k (gaussianData A B Q) ≐ halfPanel A B Q k := by
  have h : Γ ⊢[PRAAx] RationalFiniteSum.term (scaledBody body) k (gaussianData A B Q) ≐
      multiply (fraction one two) (GaussianStirlingAllOrderPanelTail.panel 0 one A B (B*Q) k) :=
    (scaled_term body k (fraction one two) (data A B (B*Q))).eqTrans
      (multiply_congr (.eqRefl _) (panel_at 0 1 A B (B*Q) k))
  simpa only [gaussianBody,embedBody,inst2,RationalFiniteSum.term,RationalGaussianEmbedding.subst_embed,halfPanel] using
    embed_congr h

private theorem gaussian_sum (A B Q L : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum gaussianBody L (gaussianData A B Q) ≐ halfPrefix A B Q L :=
  (embed_sum (scaledBody body) L (gaussianData A B Q)).eqSymm.eqTrans
    (embed_congr (sum_homogeneous body L (fraction one two) (data A B (B*Q))))

theorem finite_prefix_distance (A B Q L t : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hQ : Γ ⊢[PRAAx] le (unit t) Q) : Γ ⊢[PRAAx]
    distanceBounded (halfPrefix A B Q L) (rawSum t L A B) (L*rowCap A B L) (unit t) := by
  have rows : Γ ⊢[PRAAx] termsDistance gaussianBody dBody L (gaussianData A B Q) (sampleData t A B)
      (rowCap A B L) (unit t) := by
    refine .allI (.impI ?_)
    let a := Syn.shift A
    let b := Syn.shift B
    let q := Syn.shift Q
    let j := Syn.shift L
    let s := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i j :: Γ.map Fm.shift
    have ss : Δ ⊢[PRAAx] source a b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hs.shift.wk
    have qq : Δ ⊢[PRAAx] le (unit s) q := by simpa [Δ,s,q,Fm.shift,Syn.shift] using hQ.shift.wk
    have ii : Δ ⊢[PRAAx] lt i j := Prf.hyp0
    have jj := le_trans (le_succ_self i) ii
    have h := original_difference_at a b q i s ss.andE₁ ss.andE₂ qq
    have e : Δ ⊢[PRAAx] le ((num 4*((a+b*i)+b)+two)*unit s) (rowCap a b j*unit s) := by
      unfold rowCap
      ipra_le 4*𝔞 b*𝔞 (unit s)*sl jj
    have e' := distance_radius_mono _ _ _ _ (rowCap a b j) (unit s) (unit_positive s) (unit_positive s) e h
    have out := distance_congr (gaussian_at a b q i).eqSymm (d_at s a b i).eqSymm (.eqRefl _) (.eqRefl _) e'
    simpa [termsDistance,a,b,q,j,s,i,Δ,Syn.shift,GaussianStirlingTelescope.shifted] using out
  exact distance_congr (gaussian_sum A B Q L) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (sum_distance gaussianBody dBody L (gaussianData A B Q) (sampleData t A B) (rowCap A B L) (unit t)
      (unit_positive t) rows)

theorem cutoff_distance (A B Q p x : PTm n) (hs : Γ ⊢[PRAAx] source A B)
    (hQ : Γ ⊢[PRAAx] le (unit (rowClock A B (steps p) p)) Q) : Γ ⊢[PRAAx]
    distanceBounded (halfPrefix A B Q (steps p)) (ap2 remainderF p (remainderData A B x)) (num 51) (unit p) := by
  let L := steps p
  let t := rowClock A B L p
  let s := exponent L p
  let SA := GaussianStirlingTelescopeName.nameF
  let SB := GaussianStirlingAllOrderFirstPanelFiniteSum.nameF
  let d := GaussianStirlingTelescopeName.data L A B
  let e := GaussianStirlingAllOrderFirstPanelFiniteSum.data L A B
  have hu := unit_positive (Γ := Γ) p
  have hs' := unit_positive (Γ := Γ) s
  have ht' := unit_positive (Γ := Γ) t
  have first := distance_radius_mono _ _ _ _ one (unit p) ht' hu
    (le_congr (.eqRefl _) (one_mul _).eqSymm (query_budget (L*rowCap A B L) p))
    (finite_prefix_distance A B Q L t hs hQ)
  have cs := query_budget (Γ := Γ) L p
  have ct := row_clock_ge (Γ := Γ) A B L p
  have hp : Γ ⊢[PRAAx] le (L*(unit t+unit s)*unit p) (two*(unit t*unit s)) := by
    ipra_le 𝔞 (unit s)*sl ct+𝔞 (unit t)*sl cs
  have second := distance_congr (.eqRefl _) (GaussianStirlingTelescopeName.name_at p L A B).eqSymm
    (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ ht' hs') hu hp
      (GaussianStirlingTelescopeName.raw_distance t s L A B hs))
  have third := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hu hu) hu (by ipra_le 0)
    (distance_symmetric _ _ _ _ (positive_product _ _ hu hu)
      (cross_at SB SA e d p p (GaussianStirlingAllOrderFirstPanelFiniteSum.telescope_cross L A B hs)))
  have fourth := GaussianStirlingAllOrderFirstPanelImproper.cutoff_error p A B x hs
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hu
      (distance_triangle_same _ _ _ _ _ _ hu (distance_triangle_same _ _ _ _ _ _ hu first second) third) fourth)

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderFirstPanelPrefix
