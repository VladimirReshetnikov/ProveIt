import Surreal.Algebra.QuarticConstants
import Surreal.HahnSeries.QuarticVariant

/-!
# The original quartic in intermediate ordered Hahn rings

The Hahn version of `odg:thm:standarddef`, used by the seven-witness
variant of `odg:def:cor:ctquartic`. Only the prescribed intersection
with the coefficient field is needed.
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The original six-witness quartic defines Z in every integer-constant intermediate ring. -/
theorem integer_intermediate_quartic_iff (A : Subring (nonpositiveSupportSubring Γ K))
    (hA : ∀ a, nonpositiveConstants a ∈ A ↔ a ∈ (Int.castRingHom K).range) (x : A) :
    QuarticConstants.Defines x ↔ ∃ b : ℤ, x.val = nonpositiveConstants (b : K) := by
  let φ := intermediateLexInclusion A
  let ι := intermediateConstants (Int.castRingHom K) A hA
  constructor
  · rintro ⟨u, v, s, he⟩
    obtain ⟨hp, hs⟩ := (QuarticConstants.value_eq_zero_iff φ
      (intermediateLexInclusion_injective A) x u v s).mp he
    obtain ⟨a, _, _, hu, _⟩ := intermediate_pell_two_rigidity A (Int.castRingHom K).range hA u v hp
    obtain ⟨b, hb⟩ := a.property
    have hu' : u = ι b := by
      apply Subtype.ext
      change u.val = nonpositiveConstants (b : K)
      rw [show (b : K) = a.val from hb]
      exact hu
    have hs' := congrArg φ hs
    simp only [map_sub, map_pow, map_sum] at hs'
    have hz : 0 ≤ ∑ j, φ (s j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hx : φ x ^ 2 ≤ φ (ι b) := by rw [← hu']; linarith
    have hb0 : 0 ≤ φ (ι b) := (sq_nonneg _).trans hx
    have hbound : φ x ^ 2 ≤ φ (ι (b + 1)) ^ 2 := by
      rw [map_add, map_one, map_add, map_one]
      nlinarith [sq_nonneg (φ (ι b))]
    obtain ⟨c, hc⟩ := integer_intermediate_square_bound A hA x (b + 1) hbound
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · rintro ⟨b, hb⟩
    have hx : x = ι b := Subtype.ext hb
    rw [hx]
    exact (QuarticConstants.integer_defines b).map ι

end
end Surreal.HahnSeries
