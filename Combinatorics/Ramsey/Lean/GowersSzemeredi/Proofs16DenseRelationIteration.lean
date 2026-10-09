import GowersSzemeredi.Proofs16DenseRelationBudget

/-! Quantitative relation refinement retaining a dense row set. The
fixed frequencies evolve with the affine offsets at every iteration. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Termination with a common rank budget and explicit density/radius loss.
The bad-pair conclusion uses the final, enlarged fixed-frequency set. -/
theorem dense_relation_iteration_budget {N Q : Nat} [NeZero N] [NeZero Q] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (L : κ → ZMod N → ZMod N) {sigma theta : Real}
    (hsigma : 0 < sigma) (hsigmaMax : sigma ≤ 1 / (8 * Real.pi))
    (htheta : 0 < theta) (hQ : 4 ≤ sigma * Q) (R : Nat) :
    ∀ n d : Nat, ∀ W F Gamma : Finset (ZMod N), ∀ a : ZMod N, ∀ alpha eta : Real,
      0 < alpha → 0 ≤ eta → Gamma.card ≤ d → F.card ≤ d →
      Fintype.card κ ≤ Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L) + n →
      W ⊆ bohr Gamma (sigma / 4) →
      (∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j)) →
      alpha * N ≤ W.card → tupleRowGeometry A W F L a eta →
      let D := (denseRelationBudget theta R Q (Fintype.card κ))^[n] d
      ∃ (S V F' : Finset (ZMod N)) (a' : ZMod N),
        Gamma ⊆ S ∧ S.card ≤ D ∧
        bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
        V.Nonempty ∧ V ⊆ bohr S (sigma / 4) ∧
        (alpha / (Q : Real)^(n * D)) * N ≤ V.card ∧
        F ⊆ F' ∧ F'.card ≤ F.card + n * Fintype.card κ ∧
        tupleRowGeometry A V F' L a' (eta / (2 : Real)^n) ∧
        ((boundedBadRelationPairs (fun i : ↥F' => (i : ZMod N)) (bohr S sigma)
          L (bohr S (sigma / 4)) R).card : Real) <
            theta * ((bohr S (sigma / 4)).card : Real)^2 := by
  let Phi := denseRelationBudget theta R Q (Fintype.card κ)
  have hge : ∀ d, d ≤ Phi d := fun d =>
    (Nat.le_add_right d _).trans (denseRelationBudget_ge theta R Q _ d)
  have hQpos : (0 : Real) < Q := by exact_mod_cast NeZero.pos Q
  have hQone : (1 : Real) ≤ Q := by exact_mod_cast NeZero.pos Q
  have hrank (S : Finset (ZMod N)) :
      Module.finrank (ZMod N) (relationSubmodule (bohr S sigma) L) ≤ Fintype.card κ := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      Submodule.finrank_le (relationSubmodule (bohr S sigma) L)
  intro n
  induction n with
  | zero =>
    intro d W F G a alpha eta ha heta hG hF hcap hW hL hcard hgeom
    dsimp only
    by_cases hgood : ((boundedBadRelationPairs (fun i : ↥F => (i : ZMod N))
        (bohr G sigma) L (bohr G (sigma / 4)) R).card : Real) <
          theta * ((bohr G (sigma / 4)).card : Real)^2
    · have hWne : W.Nonempty := Finset.card_pos.mp (by
        exact_mod_cast (mul_pos ha (show (0 : Real) < N by exact_mod_cast NeZero.pos N)).trans_le hcard)
      refine ⟨G, W, F, a, Finset.Subset.refl _, hG, Finset.Subset.refl _,
        Finset.Subset.refl _, hWne, hW, ?_, Finset.Subset.refl _, ?_, ?_, hgood⟩
      · simpa using hcard
      · simp
      · simpa using hgeom
    · obtain ⟨T, _, _, _, _, hstrict⟩ :=
        bounded_bad_pair_refinement_rank (fun i : ↥F => (i : ZMod N)) G
          hsigma hsigmaMax hQ L hL R htheta (le_of_not_gt hgood)
      have hinc := Submodule.finrank_lt_finrank_of_lt hstrict
      have hmax := hrank T
      omega
  | succ n ih =>
    intro d W F G a alpha eta ha heta hG hF hcap hW hL hcard hgeom
    dsimp only
    by_cases hgood : ((boundedBadRelationPairs (fun i : ↥F => (i : ZMod N))
        (bohr G sigma) L (bohr G (sigma / 4)) R).card : Real) <
          theta * ((bohr G (sigma / 4)).card : Real)^2
    · have hWne : W.Nonempty := Finset.card_pos.mp (by
        exact_mod_cast (mul_pos ha (show (0 : Real) < N by exact_mod_cast NeZero.pos N)).trans_le hcard)
      refine ⟨G, W, F, a, Finset.Subset.refl _, hG.trans (Function.id_le_iterate_of_id_le hge _ d),
        Finset.Subset.refl _, Finset.Subset.refl _, hWne, hW, ?_, Finset.Subset.refl _,
        Nat.le_add_right _ _, ?_, hgood⟩
      · apply le_trans _ hcard
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_self ha.le (one_le_pow₀ hQone)
      · apply hgeom.mono_radius
        exact div_le_self heta (one_le_pow₀ (by norm_num))
    · obtain ⟨T, t, U, H, hGT, hT, hfull, hquarter, hstrict, hUne, hU,
          hrel, hUcard, hFH, hHcard, hUW, hgeomU⟩ :=
        dense_relation_refinement A W F G L a hsigma hsigmaMax heta ha htheta hQ
          hW hL hcard hgeom R (le_of_not_gt hgood)
      have hTbudget : T.card ≤ Phi d := hT.trans
        (relationRankStep_le_denseRelationBudget htheta R Q _ d G.card F.card hG hF)
      have hHbudget : H.card ≤ Phi d := hHcard.trans
        ((Nat.add_le_add_right hF _).trans (denseRelationBudget_ge theta R Q _ d))
      have hinc := Submodule.finrank_lt_finrank_of_lt hstrict
      have hLT : ∀ j, IsFreimanLinearOn (bohr T sigma) (L j) := by
        intro j x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ heq
        exact hL j x₁ x₂ x₃ x₄ (hfull h₁) (hfull h₂) (hfull h₃) (hfull h₄) heq
      obtain ⟨S, V, F', a', hTS, hS, hSfull, hSquarter, hVne, hV,
          hVcard, hHF', hF'card, hgeomV, hgoodV⟩ :=
        ih (Phi d) U H T (a + t) (alpha / (Q : Real)^T.card) (eta / 2)
          (by positivity) (by positivity) hTbudget hHbudget (by omega) hU hLT hUcard hgeomU
      have hiter : Phi^[n] (Phi d) = Phi^[n + 1] d :=
        (Function.iterate_succ_apply Phi n d).symm
      have hTfinal : T.card ≤ Phi^[n + 1] d := hTbudget.trans
        (hiter ▸ Function.id_le_iterate_of_id_le hge n (Phi d))
      refine ⟨S, V, F', a', hGT.trans hTS, ?_, hSfull.trans hfull,
        hSquarter.trans hquarter, hVne, hV, ?_, hFH.trans hHF', ?_, ?_, hgoodV⟩
      · exact hiter ▸ hS
      · rw [hiter] at hVcard
        exact (mul_le_mul_of_nonneg_right
          (dense_relation_density_compose ha.le Q n _ _ hTfinal) (by positivity)).trans hVcard
      · have := hF'card.trans (Nat.add_le_add_right hHcard _)
        nlinarith
      · convert hgeomV using 1
        simp [pow_succ, div_div, mul_comm]

/-- A dense row configuration has a dense refinement with few bad bounded
relations, using at most the initial relation codimension many steps. -/
theorem exists_dense_sparse_relation_domain {N Q : Nat} [NeZero N] [NeZero Q] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (W F Gamma : Finset (ZMod N)) (L : κ → ZMod N → ZMod N) (a : ZMod N)
    {sigma theta alpha eta : Real} (hsigma : 0 < sigma)
    (hsigmaMax : sigma ≤ 1 / (8 * Real.pi)) (htheta : 0 < theta)
    (ha : 0 < alpha) (heta : 0 ≤ eta) (hQ : 4 ≤ sigma * Q) (R : Nat)
    (hW : W ⊆ bohr Gamma (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (hcard : alpha * N ≤ W.card) (hgeom : tupleRowGeometry A W F L a eta) :
    let n := Fintype.card κ - Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L)
    let D := (denseRelationBudget theta R Q (Fintype.card κ))^[n] (max Gamma.card F.card)
    ∃ (S V F' : Finset (ZMod N)) (a' : ZMod N),
      Gamma ⊆ S ∧ S.card ≤ D ∧
      bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
      V.Nonempty ∧ V ⊆ bohr S (sigma / 4) ∧
      (alpha / (Q : Real)^(n * D)) * N ≤ V.card ∧
      F ⊆ F' ∧ F'.card ≤ F.card + n * Fintype.card κ ∧
      tupleRowGeometry A V F' L a' (eta / (2 : Real)^n) ∧
      ((boundedBadRelationPairs (fun i : ↥F' => (i : ZMod N)) (bohr S sigma)
        L (bohr S (sigma / 4)) R).card : Real) <
          theta * ((bohr S (sigma / 4)).card : Real)^2 := by
  apply dense_relation_iteration_budget A L hsigma hsigmaMax htheta hQ R
    _ _ W F Gamma a alpha eta ha heta (le_max_left _ _) (le_max_right _ _) _ hW hL hcard hgeom
  have h : Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L) ≤ Fintype.card κ := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      Submodule.finrank_le (relationSubmodule (bohr Gamma sigma) L)
  omega

end LeanProofs.GowersSzemeredi
