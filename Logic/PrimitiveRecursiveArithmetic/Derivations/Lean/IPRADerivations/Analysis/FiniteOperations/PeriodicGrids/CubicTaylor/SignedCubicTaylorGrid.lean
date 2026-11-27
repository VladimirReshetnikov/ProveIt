import IPRADerivations.Analysis.FiniteOperations.PeriodicGrids.CubicTaylor.PeriodicThirdDifferenceModulo
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut

/-!
# Signed cubic Taylor comparisons on four consecutive samples

The third difference at offsets 0, H, 2H, and 3H of the
same cubic polynomial is six times its cubic coefficient times H³.
Errors of at most E at the four samples cost at most 8E on
the third difference. A dyadic clock absorbs the resulting
periodic grid budget at a prescribed precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.SignedCubicTaylorGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit)
open PolynomialBisection (zle_add zle_congr zle_scale)
open SignedGridStepBounds (neg_order)
open PeriodicThirdDifferenceConstancy (band cubicBudget)
open PeriodicThirdDifferenceModulo (third third_value)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (c₀ c₁ c₂ c₃ : ZT n) (H j : PTm n) : ZT n :=
  let t := ZT.ofNat (j*H)
  c₀+t*(c₁+t*(c₂+t*c₃))

def force (c₃ : ZT n) (H : PTm n) : ZT n := ZT.ofNat (num 6*(H*(H*H)))*c₃

def combination (y₀ y₁ y₂ y₃ : ZT n) : ZT n :=
  y₃-ZT.ofNat (num 3)*y₂+ZT.ofNat (num 3)*y₁-y₀

def error (A E : PTm n) : PTm n := A+num 8*E

def clock (N A E p : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (cubicBudget N (error A E)) p

theorem clock_budget (N A E p : PTm n) :
    Γ ⊢[PRAAx] le (cubicBudget N (error A E)*unit p) (unit (clock N A E p)) :=
  GaussianFastValueCut.query_budget _ _

theorem cubic_combination (c₀ c₁ c₂ c₃ : ZT n) (H : PTm n) :
    ZT.toZ Γ (combination (value c₀ c₁ c₂ c₃ H zero) (value c₀ c₁ c₂ c₃ H one)
      (value c₀ c₁ c₂ c₃ H two) (value c₀ c₁ c₂ c₃ H (num 3))) =
      ZT.toZ Γ (force c₃ H) := by
  simp only [combination,value,force,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  ipra_simps
  ring

def approximation (y : ZT n) (c₀ c₁ c₂ c₃ : ZT n) (H j E : PTm n) : Fm PTm n :=
  band (y-value c₀ c₁ c₂ c₃ H j) E

theorem third_lower (y₀ y₁ y₂ y₃ c₀ c₁ c₂ c₃ : ZT n) (H A E : PTm n)
    (hForce : Γ ⊢[PRAAx] zle (-ZT.ofNat A) (force c₃ H))
    (h₀ : Γ ⊢[PRAAx] approximation y₀ c₀ c₁ c₂ c₃ H zero E)
    (h₁ : Γ ⊢[PRAAx] approximation y₁ c₀ c₁ c₂ c₃ H one E)
    (h₂ : Γ ⊢[PRAAx] approximation y₂ c₀ c₁ c₂ c₃ H two E)
    (h₃ : Γ ⊢[PRAAx] approximation y₃ c₀ c₁ c₂ c₃ H (num 3) E) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (error A E)) (combination y₀ y₁ y₂ y₃) := by
  have r₀ := neg_order (Prf.andE₂ h₀)
  have r₁ := zle_scale (num 3) (Prf.andE₁ h₁)
  have r₂ := zle_scale (num 3) (neg_order (Prf.andE₂ h₂))
  have r₃ := Prf.andE₁ h₃
  have accumulated := zle_add hForce (zle_add (zle_add (zle_add r₃ r₂) r₁) r₀)
  have cubic := cubic_combination (Γ := Γ) c₀ c₁ c₂ c₃ H
  refine zle_congr ?_ ?_ accumulated
  · simp only [error,ZT.toZ_add,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_add,map_add,Q.mk_mul,map_mul]
    ipra_simps
    ring
  · simp only [combination,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_mul,ZT.toZ_ofNat] at cubic ⊢
    linear_combination cubic.symm

theorem third_lower_at (b : ZB) (i x : PTm n) (c₀ c₁ c₂ c₃ : ZT n) (H A E : PTm n)
    (hForce : Γ ⊢[PRAAx] zle (-ZT.ofNat A) (force c₃ H))
    (h₀ : Γ ⊢[PRAAx] approximation (b.val i x) c₀ c₁ c₂ c₃ H zero E)
    (h₁ : Γ ⊢[PRAAx] approximation (b.val (succ i) x) c₀ c₁ c₂ c₃ H one E)
    (h₂ : Γ ⊢[PRAAx] approximation (b.val (succ (succ i)) x) c₀ c₁ c₂ c₃ H two E)
    (h₃ : Γ ⊢[PRAAx] approximation (b.val (succ (succ (succ i))) x) c₀ c₁ c₂ c₃ H (num 3) E) :
    Γ ⊢[PRAAx] zle (-ZT.ofNat (error A E)) ((third b).val i x) := by
  apply zle_congr rfl ?_ (third_lower _ _ _ _ _ _ _ _ H A E hForce h₀ h₁ h₂ h₃)
  rw [third_value]
  simp only [combination,ZT.toZ_sub,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  ring

end LeanProofs.IPRA.Analysis.SignedCubicTaylorGrid
