import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {J : Type*} (q : ℕ) [NeZero q]

def integerResidueLatticePoint (r : J → ZMod q) (k : J → ℤ) : J → ℤ :=
  fun j => (r j).val + q * k j

@[simp] theorem integerResidueLatticePoint_cast
    (r : J → ZMod q) (k : J → ℤ) (j : J) :
    (integerResidueLatticePoint q r k j : ZMod q) = r j := by
  exact (ZMod.intCast_eq_iff q _ _).2 ⟨k j, rfl⟩

theorem integerResidueLatticePoint_bijective :
    Function.Bijective (fun p : (J → ZMod q) × (J → ℤ) =>
      integerResidueLatticePoint q p.1 p.2) := by
  constructor
  · rintro ⟨r, k⟩ ⟨r', k'⟩ h
    have hr : r = r' := by
      funext j
      have hj := congrArg (fun x : J → ℤ => (x j : ZMod q)) h
      simpa only [integerResidueLatticePoint_cast] using hj
    subst r'
    have hk : k = k' := by
      funext j
      have hj := congrFun h j
      change (r j).val + (q : ℤ) * k j = (r j).val + (q : ℤ) * k' j at hj
      exact mul_left_cancel₀ (show (q : ℤ) ≠ 0 by exact_mod_cast NeZero.ne q)
        (add_left_cancel hj)
    exact Prod.ext rfl hk
  · intro x
    refine ⟨(fun j => (x j : ZMod q), fun j => x j / q), ?_⟩
    funext j
    change ((x j : ZMod q).val : ℤ) + q * (x j / q) = x j
    rw [ZMod.val_intCast, Int.emod_add_mul_ediv]

noncomputable def integerResidueLatticeEquiv :
    ((J → ZMod q) × (J → ℤ)) ≃ (J → ℤ) :=
  Equiv.ofBijective _ (integerResidueLatticePoint_bijective q)

@[simp] theorem integerResidueLatticeEquiv_apply
    (r : J → ZMod q) (k : J → ℤ) :
    integerResidueLatticeEquiv q (r, k) = integerResidueLatticePoint q r k := rfl

theorem summable_integerResidueLatticePoint
    (f : (J → ℤ) → ℂ) (hf : Summable f) (r : J → ZMod q) :
    Summable (fun k => f (integerResidueLatticePoint q r k)) := by
  have he : Summable (fun p => f (integerResidueLatticeEquiv (J := J) q p)) :=
    (integerResidueLatticeEquiv q).summable_iff.2 hf
  exact he.prod_factor r

theorem tsum_integerResidueLatticePoint [Fintype J]
    (f : (J → ℤ) → ℂ) (hf : Summable f) :
    ∑' x, f x = ∑ r : J → ZMod q, ∑' k, f (integerResidueLatticePoint q r k) := by
  classical
  let e := integerResidueLatticeEquiv (J := J) q
  have he : Summable (fun p => f (e p)) := e.summable_iff.2 hf
  calc
    _ = ∑' p, f (e p) := (e.tsum_eq f).symm
    _ = ∑' r, ∑' k, f (integerResidueLatticePoint q r k) := he.tsum_prod
    _ = _ := tsum_fintype _

end Erdos3

end

end OAI
