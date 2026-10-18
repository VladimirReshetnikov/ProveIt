import GowersSzemeredi.Proofs13CommonStepCover

/-! Declarations of `Proofs13CommonStepCover` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

/-- Corollary 13.10 follows from a bounded integer step ratio. The actual
square is constructed by padded covers, without assuming a square-grid
partition or discarding endpoints of the dense set. -/
theorem corollary_13_10_of_integer_step_fit {N : Nat} [Fact N.Prime]
    (S : Section13Context N) (E : Stage135Data N) (G : Stage137Data N)
    (H : Stage138Data N) (J : Stage139Data N)
    (h139 : IsStage139Data S E G H J) (hS : G.S.IsProper)
    (hsupport : J.D ⊆ G.S.carrier.product (translateFinset J.U.carrier G.y))
    (hUpos : 0 < J.U.length) (t : Nat) (ht : 0 < t)
    (hstep : J.U.step = (t : ZMod N) * G.S.step)
    (hfit : t * Nat.sqrt J.U.length ≤ G.S.length) :
    ∃ V W : ModAP N, ∃ E' : Finset (Pair N),
      V.step != 0 ∧ V.step = W.step ∧ V.IsProper ∧ W.IsProper ∧
      V.length = W.length ∧
      (J.U.length : Real) ^ ((1 : Real) / 2) - 1 ≤ V.length ∧
      E' ⊆ J.D ∧ E' ⊆ V.carrier.product W.carrier ∧
      (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 * V.length * W.length ≤ E'.card ∧
      BilinearOn E' S.phi := by
  let delta := (2 : Real) ^ (-(135 : Int)) * S.alpha ^ 704
  let T := J.U.translateBy G.y
  have hδ : 0 ≤ delta := mul_nonneg (zpow_nonneg (by norm_num) _) (pow_nonneg S.alpha_pos.le _)
  obtain ⟨V, W, E', hVstep, hWstep, hV, hW, hVl, hWl, hsub, hbox, hmass, hbilinear⟩ :=
    bilinear_square_of_integer_step_fit G.S T J.D S.phi delta t (Nat.sqrt J.U.length)
      hS (J.U.translateBy_isProper G.y h139.2.1) h139.1 hstep ht
      (Nat.sqrt_pos.mpr hUpos) hfit (Nat.sqrt_le_self _)
      hδ (by simpa only [T, J.U.translateBy_carrier] using hsupport)
      h139.2.2.2.2.2.2.1 h139.2.2.2.2.2.2.2
  refine ⟨V, W, E', ?_, hVstep.trans hWstep.symm, hV, hW, hVl.trans hWl.symm,
    ?_, hsub, hbox, ?_, hbilinear⟩
  · rw [hVstep]
    exact h139.1
  · rw [hVl, ← Real.sqrt_eq_rpow]
    have h := Real.real_sqrt_le_nat_sqrt_succ (a := J.U.length)
    linarith only [h]
  · rw [hVl, hWl]
    have hδeq : delta / 4 = (2 : Real) ^ (-(137 : Int)) * S.alpha ^ 704 := by
      dsimp [delta]
      norm_num [zpow_neg]
      ring
    rwa [hδeq] at hmass

end LeanProofs.GowersSzemeredi
