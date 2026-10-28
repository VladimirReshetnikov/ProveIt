import BusyBeaver.ZFC.ArithmeticCantor
import Foundation.FirstOrder.Arithmetic.Exponential.Exp

/-!
Arithmetic of a least-significant prefix of internal length n consisting of
ones, with an arbitrary untouched numeric suffix. Exp.exp is the existing
IΣ1-total internal base-two exponential, not an external-Nat power operator.
The bounded graph is fixed before choosing the model. No machine row or run
semantics is assumed or proved in this standalone algebra substrate.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def onesPrefix (n suffix : V) : V := Exp.exp n * (suffix+1) - 1

lemma prefix_product_positive (n suffix : V) : 1 ≤ Exp.exp n * (suffix+1) := by
  have hm : Exp.exp n ≤ Exp.exp n * (suffix+1) := by
    calc
      Exp.exp n = Exp.exp n * 1 := by simp
      _ ≤ Exp.exp n * (suffix+1) := mul_le_mul_left (by simp : (1 : V) ≤ suffix+1)
  exact le_trans (one_le_exp n) hm

/-- This cancellation law retains the boundary value n=0,suffix=0. -/
lemma onesPrefix_add_one (n suffix : V) :
    onesPrefix n suffix + 1 = Exp.exp n * (suffix+1) :=
  tsub_add_cancel_of_le (prefix_product_positive n suffix)

@[simp] lemma onesPrefix_zero (suffix : V) : onesPrefix 0 suffix = suffix := by
  simp [onesPrefix]

lemma onesPrefix_succ (n suffix : V) :
    onesPrefix (n+1) suffix = 2 * onesPrefix n suffix + 1 := by
  have hp : Exp.exp (n+1) * (suffix+1) = (2 * onesPrefix n suffix+1)+1 := by
    rw [exp_succ, mul_assoc, ←onesPrefix_add_one]
    ring
  change Exp.exp (n+1) * (suffix+1) - 1 = _
  rw [hp]
  simp

/-- Moving the first one to the left half yields the same entire prefix. -/
lemma onesPrefix_push (n suffix : V) :
    onesPrefix n (2*suffix+1) = onesPrefix (n+1) suffix := by
  have he : onesPrefix n (2*suffix+1)+1 = onesPrefix (n+1) suffix+1 := by
    rw [onesPrefix_add_one, onesPrefix_add_one, exp_succ]
    ring
  exact add_right_cancel he

lemma onesPrefix_bit (n suffix : V) : onesPrefix (n+1) suffix % 2 = 1 := by
  rw [onesPrefix_succ]
  simpa only [mul_comm] using
    (mod_mul_add_of_lt (onesPrefix n suffix) 2 (by simp : (1 : V) < 2))

lemma onesPrefix_half (n suffix : V) :
    onesPrefix (n+1) suffix / 2 = onesPrefix n suffix := by
  rw [onesPrefix_succ]
  exact div_mul_add' (onesPrefix n suffix) 2 (by simp : (1 : V) < 2)

lemma exp_le_prefix_add_one (n suffix : V) : Exp.exp n ≤ onesPrefix n suffix+1 := by
  rw [onesPrefix_add_one]
  calc
    Exp.exp n = Exp.exp n * 1 := by simp
    _ ≤ Exp.exp n * (suffix+1) := mul_le_mul_left (by simp : (1 : V) ≤ suffix+1)

/-- The power witness is bounded by out+1, so the zero output is covered. -/
def onesPrefixDef : 𝚺₀.Semisentence 3 := .mkSigma
  “out n suffix. ∃ power <⁺ out+1, !expDef power n ∧ out+1 = power*(suffix+1)”

instance onesPrefix_defined : 𝚺₀-Function₂[V] onesPrefix via onesPrefixDef := .mk fun e => by
  have hn :
      (Exp.exp (e 1) ≤ e 0+1 ∧ e 0+1 = Exp.exp (e 1)*(e 2+1)) ↔
        e 0 = onesPrefix (e 1) (e 2) := by
    constructor
    · intro h
      exact add_right_cancel (h.2.trans (onesPrefix_add_one (e 1) (e 2)).symm)
    · intro h
      rw [h]
      exact ⟨exp_le_prefix_add_one _ _, onesPrefix_add_one _ _⟩
  simpa [onesPrefixDef] using hn

instance onesPrefix_definable : 𝚺₀-Function₂[V] onesPrefix := onesPrefix_defined.to_definable

end SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254
