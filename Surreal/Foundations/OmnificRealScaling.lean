import Surreal.Foundations.OmnificUnits

/-!
# Real scaling of purely infinite omnific integers

The real support ring lets us multiply a purely infinite omnific integer
by any real number and stay purely infinite. These operations support
`odg:ex:euclid` and `odg:thm:nogcd`.
-/

universe u
namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Scale a purely infinite omnific integer by a real coefficient. -/
def omnificRealScale (r : ℝ) (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) : OmnificInteger.{u} :=
  ⟨realConstants r * x.val, purelyInfinite_mem_omnificSubring _
    (purelyInfiniteIdeal.mul_mem_left _ (by
      exact (mem_purelyInfiniteIdeal_iff x.val).mpr
        ((mem_omnificPurelyInfiniteIdeal_iff x).mp hx)))⟩

/-- Real scaling has its literal multiplication value in the surreal field. -/
@[simp] theorem omnificToSurreal_realScale (r : ℝ) (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) :
    omnificToSurreal (omnificRealScale r x hx) = ofReal r * omnificToSurreal x := rfl

/-- Real scaling preserves the purely infinite ideal. -/
theorem omnificRealScale_mem_purelyInfinite (r : ℝ) (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) :
    omnificRealScale r x hx ∈ omnificPurelyInfiniteIdeal := by
  apply (mem_omnificPurelyInfiniteIdeal_iff _).mpr
  apply (mem_purelyInfiniteIdeal_iff _).mp
  exact purelyInfiniteIdeal.mul_mem_left _
    ((mem_purelyInfiniteIdeal_iff x.val).mpr ((mem_omnificPurelyInfiniteIdeal_iff x).mp hx))

/-- A nonzero purely infinite omnific integer cannot be finite. -/
theorem omnific_purelyInfinite_not_finite (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (hn : x ≠ 0) :
    ¬ IsFinite (omnificToSurreal x) := by
  intro hf
  have he := omnific_eq_intConstant_of_finite x hf
  have hc : omnificConstantCoeff x = 0 := hx
  rw [hc, map_zero] at he
  exact hn he

end
end Surreal.Foundations.SignSequence
