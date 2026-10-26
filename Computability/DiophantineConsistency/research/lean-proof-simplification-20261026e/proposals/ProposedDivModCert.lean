import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
UNCOMPILED REFACTOR PROTOTYPE. Static-source evidence only.
Pinned upstream: 60e9c5d620c6c387d932876cfa2d9376f64ea56c.
This neutral arithmetic API reuses the exact original certificate proof.
It does not identify or change the two representation programs: their
witness counts remain distinct, 1 for QuadraticDivMod and 23 for RegisterDivMod.
In a production patch, minimize imports against the pinned mathlib version.
-/
namespace DiophantineConsistency.ProposedDivModCert

def Holds (q r n b : ℕ) : Prop :=
  ∃ s, n = q * b + r ∧ b = r + s + 1

theorem correct_iff (q r n b : ℕ) :
    Holds q r n b ↔
      0 < b ∧ q = n / b ∧ r = n % b := by
  unfold Holds
  constructor
  · rintro ⟨s,hn,hb⟩
    have hb0 : 0 < b := by omega
    have hr : r < b := by omega
    have hmod : n % b = r := by
      simp [hn,Nat.add_mod,Nat.mod_eq_of_lt hr]
    have hdiv : n / b = q := by
      rw [hn,Nat.add_comm (q*b) r,Nat.add_mul_div_right r q hb0,Nat.div_eq_of_lt hr,Nat.zero_add]
    exact ⟨hb0,hdiv.symm,hmod.symm⟩
  · rintro ⟨hb,hq,hr⟩
    have hrb : r < b := by rw [hr]; exact Nat.mod_lt n hb
    refine ⟨b-r-1,?_,by omega⟩
    rw [hq,hr]
    exact (Nat.div_add_mod' n b).symm


end DiophantineConsistency.ProposedDivModCert
