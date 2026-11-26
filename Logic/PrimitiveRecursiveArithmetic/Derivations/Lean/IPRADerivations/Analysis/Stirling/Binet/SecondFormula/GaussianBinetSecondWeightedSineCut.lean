import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondWeightedSineSuffix

/-!
# A positive dyadic-budget cutoff for the weighted frequency grid

The actual sine schedule already has enough cells to choose the
integer quotient of the mesh size by the requested reciprocal-width
scale. Its physical position is between the two certified margins.
-/

set_option autoImplicit false
set_option maxHeartbeats 560000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineCut

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentSineUniform
  (cutoff count clock angularScale cellFactor roundingCost cutoff_positive count_dominates clock_budget)
open GaussianBinetSecondWeightedSineSuffix (window)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def cut (q D R T K E : PTm n) : PTm n := quo (count q D R T K) ((D*cutoff q T K)*E)
def marginClock (k E : PTm n) : PTm n := exponent (two*E) k

@[simp] theorem subst_cut {m : ℕ} (σ : Fin n → PTm m) (q D R T K E : PTm n) :
    Syn.subst σ (cut q D R T K E) =
      cut (Syn.subst σ q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ T) (Syn.subst σ K) (Syn.subst σ E) := by
  simp [cut,quo]

@[simp] theorem subst_marginClock {m : ℕ} (σ : Fin n → PTm m) (k E : PTm n) :
    Syn.subst σ (marginClock k E) = marginClock (Syn.subst σ k) (Syn.subst σ E) := by simp [marginClock,two]

theorem margin_clock_later (k E : PTm n) : Γ ⊢[PRAAx] le k (marginClock k E) := le_add_right _ _

theorem margin_clock_budget (k E : PTm n) : Γ ⊢[PRAAx] le (two*E) (unit (marginClock k E)) :=
  le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl (two*E)) (unit_positive k)))
    (query_budget (two*E) k)

theorem count_width_budget (q D R T K : PTm n) :
    Γ ⊢[PRAAx] le ((D*cutoff q T K)*unit q) (count q D R T K) := by
  let S := D*cutoff q T K
  let C := T*S
  let G := angularScale q D T S
  let W := roundingCost q D R T K S
  have factor : Γ ⊢[PRAAx] le one (cellFactor q S T) :=
    positive_product _ _ (unit_positive q) (le_trans (le_add_right _ _) (le_add_right _ _))
  have g : Γ ⊢[PRAAx] le one G := positive_product _ _ factor (mesh_positive _ _ _)
  have a : Γ ⊢[PRAAx] le S ((LeanProofs.IPRA.PTm.num 20*LeanProofs.IPRA.PTm.num 16)*S*G) := by
    ipra_le 320*𝔞(S)*sl g+319*𝔞(S)
  have b : Γ ⊢[PRAAx] le ((LeanProofs.IPRA.PTm.num 20*LeanProofs.IPRA.PTm.num 16)*S*G) W :=
    le_add_left _ _
  exact le_trans (le_trans (le_mul_mono (le_trans a b) (le_refl (unit q))) (clock_budget q D R T K))
    (count_dominates q D R T K).andE₂

theorem certificates (q D R T K E : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le two E) (hQ : Γ ⊢[PRAAx] le (two*E) (unit q)) :
    let S := D*cutoff q T K
    let N := count q D R T K
    let c := cut q D R T K E
    Γ ⊢[PRAAx] le one c ⋏
      (lt c N ⋏ (window q D R T K c E ⋏ le N ((two*E)*(S*c)))) := by
  let S := D*cutoff q T K
  let N := count q D R T K
  let B := S*E
  let c := cut q D R T K E
  let r := rem N B
  have hs : Γ ⊢[PRAAx] le one S := positive_product _ _ hD (cutoff_positive q T K)
  have he := le_trans (le_succ_self (Γ := Γ) one) hE
  have hb : Γ ⊢[PRAAx] le one B := positive_product _ _ hs he
  have hb₂ : Γ ⊢[PRAAx] le two B := le_congr (one_mul two) (.eqRefl _) (le_mul_mono hs hE)
  have cover : Γ ⊢[PRAAx] le (two*B) N := by
    have first : Γ ⊢[PRAAx] le (two*B) (S*unit q) :=
      le_congr (by dsimp only [B]; ipra_ring) (.eqRefl _) (le_mul_mono (le_refl S) hQ)
    exact le_trans first (count_width_budget q D R T K)
  have division : Γ ⊢[PRAAx] (N ≐ B*c+r) ⋏ lt r B :=
    div_mod_at ((eq_add_of_le hb).eqTrans (by ipra_ring))
  have hc : Γ ⊢[PRAAx] le one c := by
    refine .orE (zero_or_succ c) ?_ ?_
    · let Δ := (c ≐ zero)::Γ
      have eqr : Δ ⊢[PRAAx] N ≐ r := division.andE₁.wk.eqTrans
        ((congrAdd (congrMul (.eqRefl B) Prf.hyp0) (.eqRefl r)).eqTrans (by ipra_ring))
      have bN : Δ ⊢[PRAAx] le B N := le_trans (le_of_eq_add (d := B) (by ipra_ring)) cover.wk
      exact le_lt_absurd _ (le_congr (.eqRefl B) eqr bN) division.andE₂.wk
    · exact le_congr (.eqRefl one) Prf.hyp0.eqSymm (zero_lt_succ (pred c))
  have first : Γ ⊢[PRAAx] le (B*c) N := le_congr (.eqRefl _) division.andE₁.eqSymm (le_add_right _ _)
  have left : Γ ⊢[PRAAx] le (succ c) (two*c) := by
    have q : Γ ⊢[PRAAx] le (c+one) (two*c) := by ipra_le sl hc
    exact le_congr (succ_eq_add_one c).eqSymm (.eqRefl _) q
  have strict : Γ ⊢[PRAAx] lt c N :=
    le_trans left (le_trans (le_mul_mono hb₂ (le_refl c)) first)
  have second : Γ ⊢[PRAAx] le B (B*c) :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl B) hc)
  have right : Γ ⊢[PRAAx] le N ((two*E)*(S*c)) := by
    have h := add_le_add₂ (le_refl (B*c)) (le_trans (le_of_lt division.andE₂) second)
    exact le_congr division.andE₁.eqSymm (by dsimp only [B]; ipra_ring) h
  have small : Γ ⊢[PRAAx] le ((S*c)*E) N := le_congr (by dsimp only [B]; ipra_ring) (.eqRefl _) first
  exact .andI hc (.andI strict (.andI (.andI (le_of_lt strict) (.andI he small)) right))

theorem remaining_margin (q D R T K E j : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hE : Γ ⊢[PRAAx] le two E) (hQ : Γ ⊢[PRAAx] le (two*E) (unit q)) :
    let S := D*cutoff q T K
    let c := cut q D R T K E
    Γ ⊢[PRAAx] le (count q D R T K) ((two*E)*(S*(c+j))) :=
  le_trans (certificates q D R T K E hD hE hQ).andE₂.andE₂.andE₂
    (le_mul_mono (le_refl (two*E)) (le_mul_mono (le_refl _) (le_add_right _ _)))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineCut
