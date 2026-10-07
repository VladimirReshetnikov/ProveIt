import OAI.Combinatorics.Progressions.Lattices.ResidueBoxSliceCoordinateDisintegration

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ V : Type*} [Finite σ] [AddCommGroup V] [Module ℚ V]
  [Module ℝ V] [IsScalarTower ℚ ℝ V]

theorem eq_of_eval₂_eq_on_residueBoxSlice
    {N : σ → ℕ} {step : ℕ} (A : ResidueBoxSlice N step) (hstep : 0 < step)
    {d : ℕ} {p q : VectorPolynomial σ ℚ V}
    (hp : DegreeLE (fun _ => 1) d p) (hq : DegreeLE (fun _ => 1) d q)
    (hlen : ∀ i, d < A.length i)
    (heval : ∀ j : ∀ i, Fin (A.length i),
      eval₂ (fun i => (A.integerPoint j i : ℝ)) p =
        eval₂ (fun i => (A.integerPoint j i : ℝ)) q) :
    p = q := by
  refine eq_of_eval₂_eq_on_grid A.length
    (fun i j => ((A.start i + step * j.val : ℕ) : ℝ)) ?_ hp hq hlen ?_
  · intro i j k h
    apply Fin.ext
    dsimp only at h
    have hnat : A.start i + step * j.val = A.start i + step * k.val := by
      exact_mod_cast h
    exact Nat.eq_of_mul_eq_mul_left hstep (Nat.add_left_cancel hnat)
  · intro j
    simpa only [ResidueBoxSlice.integerPoint, ResidueBoxSlice.point, Int.cast_natCast]
      using heval j

end Erdos3.VectorPolynomial

end

end OAI
