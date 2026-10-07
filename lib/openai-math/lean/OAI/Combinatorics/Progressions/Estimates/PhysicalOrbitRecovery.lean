import OAI.Combinatorics.Progressions.Dynamics.EpochPhysicalRebase

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

theorem scalarAffineOrbitHom_one_zero {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (g : F.PolynomialOrbit (fun _ : σ => 1)) :
    F.scalarAffineOrbitHom 1 (fun _ => 0) g = g := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (scalarAffinePolynomial 1 (fun _ => 0)) g.log = g.log
  have h : scalarAffinePolynomial (σ := σ) 1 (fun _ => 0) = fun i => MvPolynomial.X i := by
    funext i
    simp [scalarAffinePolynomial]
  rw [h, VectorPolynomial.substitute_X]

theorem scalarAffineOrbitHom_inverse_recover {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (g : F.PolynomialOrbit (fun _ : σ => 1))
    (M : ℕ) (hM : 0 < M) (u : σ → ℤ) :
    F.scalarAffineOrbitHom (M : ℚ) (fun i => (u i : ℚ))
      (F.scalarAffineOrbitHom (1 / (M : ℚ)) (fun i => -(u i : ℚ) / M) g) = g := by
  rw [scalarAffineOrbitHom_comp]
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hscale : (1 / (M : ℚ)) * M = 1 := by field_simp
  have hshift : (fun i => (1 / (M : ℚ)) * (u i : ℚ) + -(u i : ℚ) / M) = fun _ => 0 := by
    funext i
    ring
  rw [hscale, hshift, scalarAffineOrbitHom_one_zero]

end Erdos3.NilpotentLieFiltration

end

end OAI
