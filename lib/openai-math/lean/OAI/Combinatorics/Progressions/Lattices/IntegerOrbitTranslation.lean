import OAI.Combinatorics.Progressions.Estimates.ProjectedNativeCoefficient

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

@[simp] theorem integerOrbitPoint_translate
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (c n : ℤ) :
    D.integerOrbitPoint (g.translate (fun _ => Nat.zero_lt_one) (fun _ => c)) n =
      D.integerOrbitPoint g (n + c) := by
  unfold integerOrbitPoint
  rw [NilpotentLieFiltration.polynomialOrbitEval_translate]
  rfl

end Erdos3.RationalFilteredNilmanifold

end

end OAI
