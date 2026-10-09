import GowersSzemeredi.Proofs16AdaptiveRelationBudget

/-! Dense relation refinement with state-dependent cutoff and tolerance.
The state follows one exact recurrence, so no monotonicity of the chosen
error schedule is required. Strict relation growth still forces stopping. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Adaptive refinement stops at a tolerance chosen for its current retained
density. The final state is an actual iterate, not just an upper bound. -/
theorem adaptive_dense_relation_iteration {N Q : Nat} [NeZero N] [NeZero Q] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (L : κ → ZMod N → ZMod N) (theta : Nat → Real) (R : Nat → Nat)
    (htheta : ∀ d, 0 < theta d) {sigma alpha : Real}
    (hsigma : 0 < sigma) (hsigmaMax : sigma ≤ 1 / (8 * Real.pi))
    (ha : 0 < alpha) (hQ : 4 ≤ sigma * Q) :
    ∀ n d : Nat, ∀ W F Gamma : Finset (ZMod N), ∀ a : ZMod N, ∀ eta : Real,
      0 ≤ eta → Gamma.card ≤ d → F.card ≤ d →
      Fintype.card κ ≤ Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L) + n →
      W ⊆ bohr Gamma (sigma / 4) →
      (∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j)) →
      (alpha / (Q : Real)^d) * N ≤ W.card → tupleRowGeometry A W F L a eta →
      ∃ s : Nat, s ≤ n ∧
      let D := (adaptiveRelationBudget theta R Q (Fintype.card κ))^[s] d
      ∃ (S V F' : Finset (ZMod N)) (a' : ZMod N),
        Gamma ⊆ S ∧ S.card ≤ D ∧ F'.card ≤ D ∧
        bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
        V.Nonempty ∧ V ⊆ bohr S (sigma / 4) ∧
        (alpha / (Q : Real)^D) * N ≤ V.card ∧
        F ⊆ F' ∧ F'.card ≤ F.card + s * Fintype.card κ ∧
        tupleRowGeometry A V F' L a' (eta / (2 : Real)^s) ∧
        ((boundedBadRelationPairs (fun i : ↥F' => (i : ZMod N)) (bohr S sigma)
          L (bohr S (sigma / 4)) (R D)).card : Real) <
            theta D * ((bohr S (sigma / 4)).card : Real)^2 := by
  let Phi := adaptiveRelationBudget theta R Q (Fintype.card κ)
  have hQpos : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hrank (S : Finset (ZMod N)) :
      Module.finrank (ZMod N) (relationSubmodule (bohr S sigma) L) ≤ Fintype.card κ := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      Submodule.finrank_le (relationSubmodule (bohr S sigma) L)
  intro n
  induction n with
  | zero =>
    intro d W F G a eta heta hG hF hcap hW hL hcard hgeom
    by_cases hgood : ((boundedBadRelationPairs (fun i : ↥F => (i : ZMod N))
        (bohr G sigma) L (bohr G (sigma / 4)) (R d)).card : Real) <
          theta d * ((bohr G (sigma / 4)).card : Real)^2
    · have hWne : W.Nonempty := Finset.card_pos.mp (by
        exact_mod_cast (mul_pos (show 0 < alpha / (Q : Real)^d by positivity)
          (show (0 : Real) < N by exact_mod_cast NeZero.pos N)).trans_le hcard)
      refine ⟨0, le_rfl, G, W, F, a, Finset.Subset.refl _, hG, hF, Finset.Subset.refl _,
        Finset.Subset.refl _, hWne, hW, hcard, Finset.Subset.refl _, ?_, ?_, hgood⟩
      · simp
      · simpa using hgeom
    · obtain ⟨T, _, _, _, _, hstrict⟩ :=
        bounded_bad_pair_refinement_rank (fun i : ↥F => (i : ZMod N)) G
          hsigma hsigmaMax hQ L hL (R d) (htheta d) (le_of_not_gt hgood)
      have hinc := Submodule.finrank_lt_finrank_of_lt hstrict
      have hmax := hrank T
      omega
  | succ n ih =>
    intro d W F G a eta heta hG hF hcap hW hL hcard hgeom
    by_cases hgood : ((boundedBadRelationPairs (fun i : ↥F => (i : ZMod N))
        (bohr G sigma) L (bohr G (sigma / 4)) (R d)).card : Real) <
          theta d * ((bohr G (sigma / 4)).card : Real)^2
    · have hWne : W.Nonempty := Finset.card_pos.mp (by
        exact_mod_cast (mul_pos (show 0 < alpha / (Q : Real)^d by positivity)
          (show (0 : Real) < N by exact_mod_cast NeZero.pos N)).trans_le hcard)
      refine ⟨0, Nat.zero_le _, G, W, F, a, Finset.Subset.refl _, hG, hF, Finset.Subset.refl _,
        Finset.Subset.refl _, hWne, hW, hcard, Finset.Subset.refl _, ?_, ?_, hgood⟩
      · simp
      · simpa using hgeom
    · obtain ⟨T, t, U, H, hGT, hT, hfull, hquarter, hstrict, hUne, hU,
          hrel, hUcard, hFH, hHcard, hUW, hgeomU⟩ :=
        dense_relation_refinement A W F G L a hsigma hsigmaMax heta
          (by positivity : 0 < alpha / (Q : Real)^d) (htheta d) hQ
          hW hL hcard hgeom (R d) (le_of_not_gt hgood)
      have hTbudget : T.card ≤ denseRelationBudget (theta d) (R d) Q (Fintype.card κ) d := hT.trans
        (relationRankStep_le_denseRelationBudget (htheta d) (R d) Q _ d G.card F.card hG hF)
      have hPsi : denseRelationBudget (theta d) (R d) Q (Fintype.card κ) d ≤ Phi d := Nat.le_add_left _ _
      have hHbudget : H.card ≤ Phi d := hHcard.trans
        ((Nat.add_le_add_right hF _).trans ((denseRelationBudget_ge (theta d) (R d) Q _ d).trans hPsi))
      have hUbudget : (alpha / (Q : Real)^(Phi d)) * N ≤ U.card :=
        (mul_le_mul_of_nonneg_right (adaptive_relation_density_step ha.le theta R Q _ d _ hTbudget)
          (by positivity)).trans hUcard
      have hinc := Submodule.finrank_lt_finrank_of_lt hstrict
      have hLT : ∀ j, IsFreimanLinearOn (bohr T sigma) (L j) := by
        intro j x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ heq
        exact hL j x₁ x₂ x₃ x₄ (hfull h₁) (hfull h₂) (hfull h₃) (hfull h₄) heq
      obtain ⟨s, hs, S, V, F', a', hTS, hS, hF', hSfull, hSquarter, hVne, hV,
          hVcard, hHF', hF'card, hgeomV, hgoodV⟩ :=
        ih (Phi d) U H T (a + t) (eta / 2) (by positivity)
          (hTbudget.trans hPsi) hHbudget (by omega) hU hLT hUbudget hgeomU
      have hiter : Phi^[s] (Phi d) = Phi^[s + 1] d :=
        (Function.iterate_succ_apply Phi s d).symm
      refine ⟨s + 1, by omega, S, V, F', a', hGT.trans hTS, hiter ▸ hS, hiter ▸ hF',
        hSfull.trans hfull, hSquarter.trans hquarter, hVne, hV, hiter ▸ hVcard,
        hFH.trans hHF', ?_, ?_, hiter ▸ hgoodV⟩
      · have := hF'card.trans (Nat.add_le_add_right hHcard _)
        nlinarith
      · convert hgeomV using 1
        simp [pow_succ, div_div, mul_comm]

end LeanProofs.GowersSzemeredi
