import GowersSzemeredi.Proofs03LinearPatternBound

/-! A uniformity bound at any position in a progression, with unchanged
degree and exponent. This supports relative counting for arbitrary lengths. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem linearPatternAverage_reindex {N k : Nat} [NeZero N]
    (c : Fin k → ZMod N) (f : Fin k → ZMod N → Complex) (e : Equiv.Perm (Fin k)) :
    linearPatternAverage (fun i => c (e i)) (fun i => f (e i)) = linearPatternAverage c f := by
  unfold linearPatternAverage
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  exact Equiv.prod_comp e (fun i => f i (s - c i * r))

/-- The generalized von Neumann estimate for arbitrary distinct coefficients
and a uniform factor at an arbitrary index. -/
theorem linearPattern_uniform_bound {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (c : Fin k → ZMod N) (hc : Function.Injective c)
    (f : Fin k → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (alpha : Real) (hα : 0 ≤ alpha) (j : Fin k)
    (hu : UniformOfDegree (f j) alpha (k - 2)) :
    ‖linearPatternAverage c f‖ ≤ alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
  let last : Fin k := ⟨k - 1, by omega⟩
  let e := Equiv.swap last j
  have hp := linearPattern_uniform_last_bound hk (fun i => c (e i)) (hc.comp e.injective)
    (fun i => f (e i)) (fun i => hf (e i)) alpha hα (by
      intro i hi
      have hilast : i = last := Fin.ext (by dsimp [last]; omega)
      simpa only [hilast, e, Equiv.swap_apply_left] using hu)
  rwa [linearPatternAverage_reindex] at hp

/-- The uniform factor in a k-term progression can be in any position. -/
theorem progressionAverage_uniform_bound {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (hN : k ≤ N)
    (f : Fin k → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (alpha : Real) (hα : 0 ≤ alpha) (j : Fin k)
    (hu : UniformOfDegree (f j) alpha (k - 2)) :
    ‖progressionAverage f‖ ≤ alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
  have hc : Function.Injective (fun i : Fin k => ((i : Nat) : ZMod N)) := by
    intro i j hij
    apply Fin.ext
    have hv := congrArg ZMod.val hij
    simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hN),
      ZMod.val_natCast_of_lt (j.isLt.trans_le hN)] using hv
  change ‖linearPatternAverage (fun i : Fin k => ((i : Nat) : ZMod N)) f‖ ≤ _
  exact linearPattern_uniform_bound hk (fun i : Fin k => ((i : Nat) : ZMod N)) hc f hf alpha hα j hu

end LeanProofs.GowersSzemeredi
