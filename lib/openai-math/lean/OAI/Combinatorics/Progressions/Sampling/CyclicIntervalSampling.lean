import OAI.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice

namespace OAI

section

namespace Erdos3

theorem finiteCorrelation_image_of_injOn {A B : Type*} [DecidableEq B]
    (Q : Finset A) (φ : A → B) (hφ : Set.InjOn φ (Q : Set A)) (f u : B → ℂ) :
    finiteCorrelation (Q.image φ) f u =
      finiteCorrelation Q (fun x => f (φ x)) (fun x => u (φ x)) := by
  unfold finiteCorrelation
  exact Finset.expect_image hφ

theorem cyclicInterval_representative_correlation {N : ℕ} [NeZero N]
    (a len : ℕ) (hbound : a + len ≤ N) (hshort : 2 * ((len : ℤ) - 1) < N)
    (f : ZMod N → ℂ) (u : ℤ → ℂ) :
    finiteCorrelation (cyclicInterval (a : ZMod N) len) f (fun x => u (x.val : ℤ)) =
      finiteCorrelation (Finset.Ico (a : ℤ) (a + len)) (fun x => f (x : ZMod N)) u := by
  have he := integerInterval_reflectsPairSums N (a : ℤ) (a + len) (by omega)
  rw [← Int.cast_natCast a, ← integerInterval_image_cyclicInterval,
    finiteCorrelation_image_of_injOn _ _ he.injOn]
  unfold finiteCorrelation
  apply Finset.expect_congr rfl
  intro x hx
  have hx' := Finset.mem_Ico.mp hx
  have hrep : (((x : ZMod N).val : ℕ) : ℤ) = x := by
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (by omega) (by omega)]
  change f (x : ZMod N) * star (u (((x : ZMod N).val : ℕ) : ℤ)) = _
  rw [hrep]

end Erdos3

end

end OAI
