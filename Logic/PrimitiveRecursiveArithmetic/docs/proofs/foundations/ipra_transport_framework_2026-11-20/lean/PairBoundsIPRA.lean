import IPRADerivations.Core.SumOrder

/-! An ordinary `Prf PRAAx` derivation for the binary split used in the
polyhedral proof. A/B is the proposed lower slope. The two source-target
pairs use a common rational denominator. For a convex combination the
cleared weights are r and s. No division or positivity premise is needed
for this polynomial implication. -/
namespace PairBoundsIPRA

open LeanProofs.ConciseIPRA LeanProofs.IPRA Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem weightedLower (A B r s u v U V : PTm n)
    (hu : Γ ⊢[PRAAx] le (A*u) (B*U)) (hv : Γ ⊢[PRAAx] le (A*v) (B*V)) :
    Γ ⊢[PRAAx] le (A*(r*u + s*v)) (B*(r*U + s*V)) := by
  exact le_congr (by ipra_ring) (by ipra_ring)
    (add_le_add₂ (mul_le_mul_right r hu) (mul_le_mul_right s hv))

def mixLower (A B r s u v U V : PTm n) : Fm PTm n :=
  le (A*u) (B*U) ⟶ le (A*v) (B*V) ⟶ le (A*(r*u+s*v)) (B*(r*U+s*V))

def closedMixLower : Fm PTm 0 :=
  allN 8 (mixLower (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))

theorem closed_mix_lower : ([] : List (Fm PTm 0)) ⊢[PRAAx] closedMixLower := by
  apply closeAll 8
  apply Prf.impI
  apply Prf.impI
  exact weightedLower _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0

#print axioms PairBoundsIPRA.closed_mix_lower
end PairBoundsIPRA
