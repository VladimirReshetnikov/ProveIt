import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasMeshConstancy
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasBaseInterval
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasProportionality

/-!
# Barnes proportionality from certified quotient meshes

Reduce the queried positive rational input to the first unit interval,
use all verified dyadic grids there, and recover the original candidate
value. The multiplier is the actual candidate value at one.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasCertifiedMesh

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesVignerasBaseInterval (baseNumerator)
open GaussianBarnesVignerasCyclicDerivative (LowerJet)
open GaussianBarnesVignerasIntegerPeriod (advance chart_at)
open GaussianBarnesVignerasMeshConstancy (positive_chart subst_positive_chart schedule)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNameRingLaws (oneF)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianBarnesVignerasLogQuotient.nameF
local notation "cd" => GaussianBarnesVignerasIntegerPeriod.data
local notation "I" => GaussianBarnesVignerasIntegerPeriod.input
local notation "M" => GaussianBarnesVignerasIntegerPeriod.margin
local notation "Bnd" => GaussianBarnesVignerasIntegerPeriod.bound
local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "gd" => GaussianBarnesCanonicalHyperfactorial.barnesData
local notation "Orbit" => GaussianBarnesVignerasIntegerPeriod.source

theorem positive_at_start (f : PR 2) (t : PTm 2) (a b : PTm n)
    (h : Γ ⊢[PRAAx] Orbit f t a b) : Γ ⊢[PRAAx] positive_chart f t a b := by
  have h₀ : Γ ⊢[PRAAx] positive_chart f t (advance a b zero) b := (chart_at f t a b zero h).andE₂.andE₁.andE₁
  have e : Γ ⊢[PRAAx] advance a b zero ≐ a := by unfold advance; ipra_ring
  have lift := Prf.eqSubst (positive_chart f t (var 0) (var 1) : Fm PTm 2) ![advance a b zero,b] ![a,b]
    (fun j => by fin_cases j; exact e; exact .eqRefl b)
  have transported : (Γ ⊢[PRAAx] positive_chart f t (advance a b zero) b) → (Γ ⊢[PRAAx] positive_chart f t a b) := by
    simpa only [subst_positive_chart,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using lift
  exact transported h₀

def source (f g : PR 2) (t v s : PTm 2) (J : LowerJet) (a b x : PTm n) : Fm PTm n :=
  (le one a ⋏ le one b) ⋏ (Orbit f t a b ⋏ (Orbit f t (baseNumerator a b) b ⋏
    (positive_chart f t one one ⋏ schedule f g t v s J (baseNumerator a b) b x)))

theorem constant (f g : PR 2) (t v s : PTm 2) (J : LowerJet) (a b x : PTm n)
    (h : Γ ⊢[PRAAx] source f g t v s J a b x) : Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) (cd t a b) (cd t one one) := by
  let c := baseNumerator a b
  have hb := h.andE₁.andE₂
  have hC := le_trans hb (GaussianBarnesVignerasBaseInterval.interval a b hb).andE₁
  have base := GaussianBarnesVignerasBaseInterval.reduction f t a b hb h.andE₂.andE₁ h.andE₂.andE₂.andE₁
  have fixed := GaussianBarnesVignerasMeshConstancy.constant f g t v s J c b x hC hb
    (positive_at_start f t c b h.andE₂.andE₂.andE₁) h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂
  exact cross_trans _ _ _ _ _ _ base fixed

theorem proportional (f g : PR 2) (t v s : PTm 2) (J : LowerJet) (a b x : PTm n)
    (h : Γ ⊢[PRAAx] source f g t v s J a b x) : Γ ⊢[PRAAx]
    crossEquivalent f (multiplyF f G) (I t a b) (multiplyData f G (I t one one) (gd a b)) :=
  GaussianBarnesVignerasProportionality.proportional f a b (I t a b) (I t one one) (M t a b) (Bnd t a b)
    (M t one one) (Bnd t one one) h.andE₁.andE₁ h.andE₁.andE₂ (positive_at_start f t a b h.andE₂.andE₁)
    h.andE₂.andE₂.andE₂.andE₁ (constant f g t v s J a b x h)

theorem actual_Barnes_candidate_proportional_from_certified_meshes_closed (f g : PR 2) (t v s : PTm 2) (J : LowerJet) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let a := var 0
       let b := var 1
       let x := var 2
       source f g t v s J a b x ⟶
         crossEquivalent f (multiplyF f G) (I t a b) (multiplyData f G (I t one one) (gd a b))) :=
  closeUniv 3 (.impI (proportional f g t v s J _ _ _ Prf.hyp0))

theorem normalized (f g : PR 2) (t v s : PTm 2) (J : LowerJet) (a b x : PTm n)
    (h : Γ ⊢[PRAAx] source f g t v s J a b x)
    (h₁ : Γ ⊢[PRAAx] crossEquivalent f oneF (I t one one) (I t one one)) : Γ ⊢[PRAAx]
    crossEquivalent f G (I t a b) (gd a b) :=
  GaussianBarnesVignerasProportionality.normalized f a b (I t a b) (I t one one) (M t a b) (Bnd t a b)
    (M t one one) (Bnd t one one) h.andE₁.andE₁ h.andE₁.andE₂ (positive_at_start f t a b h.andE₂.andE₁)
    h.andE₂.andE₂.andE₂.andE₁ (constant f g t v s J a b x h) h₁

theorem actual_normalized_Barnes_candidate_from_certified_meshes_closed (f g : PR 2) (t v s : PTm 2) (J : LowerJet) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let a := var 0
       let b := var 1
       let x := var 2
       source f g t v s J a b x ⟶ crossEquivalent f oneF (I t one one) (I t one one) ⟶
         crossEquivalent f G (I t a b) (gd a b)) :=
  closeUniv 3 (.impI (.impI (normalized f g t v s J _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasCertifiedMesh
