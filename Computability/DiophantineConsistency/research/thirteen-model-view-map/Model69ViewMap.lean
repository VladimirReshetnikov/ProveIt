import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ArithmeticCarrierRadix2011
import Model69GraphCut

/-! Experimental exact subtraction mapping for a natural-like arithmetic model.
This file does not yet connect a carrier zero to the graph cut. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69ViewMap
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ModelDifferenceRing
open Model69GraphCutDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem map_sub_of_le (a b : V) (h : b≤a) :
    (ι (a-b) : DiffRing V) = ι a - ι b := by
  apply eq_sub_iff_add_eq.mpr
  have hh := congrArg (ι : V → DiffRing V) (tsub_add_cancel_of_le h)
  simpa only [map_add] using hh

/-- The two subtractions in the rank formula are transported only under
explicit bounds. -/
theorem map_rank (b q F alpha L H J : V) (hF : F≤q) (hq : 1≤q^2) :
    (ι b * (ι q - ι F) + ι alpha) * ((ι q)^2 - 1) +
        (ι L + ι q * ι H) * ι J =
      ι ((b*(q-F)+alpha)*(q^2-1)+(L+q*H)*J) := by
  simp only [map_add, map_mul, map_pow, map_sub_of_le _ _ hF,
    map_sub_of_le _ _ hq, map_one]

/-- The printed gap is transported under the actual positivity bounds. -/
theorem map_gap (q F alpha : V) (hF : F≤q) (ha : alpha≤q-F) :
    (ι q : DiffRing V) - ι F - ι alpha = ι (q-F-alpha) := by
  rw [map_sub_of_le _ _ ha, map_sub_of_le _ _ hF]

end Model69ViewMap
#print axioms Model69ViewMap.map_sub_of_le
#print axioms Model69ViewMap.map_rank
#print axioms Model69ViewMap.map_gap
