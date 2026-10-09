import GowersSzemeredi.Proofs16RelationRankBudget
import Mathlib.Order.Iterate

/-! Quantitative termination of the Bohr relation refinement. Every failed
bad-pair estimate strictly raises the relation-subspace dimension, so the
explicit rank recurrence is iterated only as many times as the initial
relation codimension. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem exists_sparse_bad_relation_domain {N Q : Nat} [NeZero N] [NeZero Q] [Fact N.Prime]
    {ι κ : Type*} [Fintype ι] [Fintype κ] (gamma : ι → ZMod N)
    (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 < sigma)
    (hsigmaMax : sigma ≤ 1 / (8 * Real.pi)) (hQ : 4 ≤ sigma * Q)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (R : Nat) {theta : Real} (htheta : 0 < theta) :
    let M : Real := ((2 * R + 1)^(Fintype.card ι + 2 * Fintype.card κ) : Nat)
    let n := Fintype.card κ - Module.finrank (ZMod N) (relationSubmodule (bohr Gamma sigma) L)
    ∃ S : Finset (ZMod N), Gamma ⊆ S ∧
      S.card ≤ (relationRankStep theta M Q)^[n] Gamma.card ∧
      bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
      ((boundedBadRelationPairs gamma (bohr S sigma) L (bohr S (sigma / 4)) R).card : Real) <
        theta * ((bohr S (sigma / 4)).card : Real)^2 := by
  let M : Real := ((2 * R + 1)^(Fintype.card ι + 2 * Fintype.card κ) : Nat)
  let Phi := relationRankStep theta M Q
  have hM : 0 < M := by dsimp [M]; positivity
  have hmono : Monotone Phi := relationRankStep_mono htheta hM Q
  have hge : ∀ d, d ≤ Phi d := relationRankStep_ge theta M Q
  have hrank (S : Finset (ZMod N)) :
      Module.finrank (ZMod N) (relationSubmodule (bohr S sigma) L) ≤ Fintype.card κ := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      Submodule.finrank_le (relationSubmodule (bohr S sigma) L)
  have haux : ∀ n : Nat, ∀ G : Finset (ZMod N),
      (∀ j, IsFreimanLinearOn (bohr G sigma) (L j)) →
      Fintype.card κ ≤ Module.finrank (ZMod N) (relationSubmodule (bohr G sigma) L) + n →
      ∃ S : Finset (ZMod N), G ⊆ S ∧ S.card ≤ Phi^[n] G.card ∧
        bohr S sigma ⊆ bohr G sigma ∧ bohr S (sigma / 4) ⊆ bohr G (sigma / 4) ∧
        ((boundedBadRelationPairs gamma (bohr S sigma) L (bohr S (sigma / 4)) R).card : Real) <
          theta * ((bohr S (sigma / 4)).card : Real)^2 := by
    intro n
    induction n with
    | zero =>
      intro G hLG hcap
      by_cases hgood : ((boundedBadRelationPairs gamma (bohr G sigma) L (bohr G (sigma / 4)) R).card : Real) <
          theta * ((bohr G (sigma / 4)).card : Real)^2
      · exact ⟨G, Finset.Subset.refl _, le_rfl, Finset.Subset.refl _, Finset.Subset.refl _, hgood⟩
      · obtain ⟨T, hGT, hT, hfull, hquarter, hstrict⟩ :=
          bounded_bad_pair_refinement_rank gamma G hsigma hsigmaMax hQ L hLG R htheta (le_of_not_gt hgood)
        have hinc := Submodule.finrank_lt_finrank_of_lt hstrict
        have hmax := hrank T
        omega
    | succ n ih =>
      intro G hLG hcap
      by_cases hgood : ((boundedBadRelationPairs gamma (bohr G sigma) L (bohr G (sigma / 4)) R).card : Real) <
          theta * ((bohr G (sigma / 4)).card : Real)^2
      · refine ⟨G, Finset.Subset.refl _, ?_, Finset.Subset.refl _, Finset.Subset.refl _, hgood⟩
        exact Function.id_le_iterate_of_id_le hge (n + 1) G.card
      · obtain ⟨T, hGT, hT, hfull, hquarter, hstrict⟩ :=
          bounded_bad_pair_refinement_rank gamma G hsigma hsigmaMax hQ L hLG R htheta (le_of_not_gt hgood)
        have hinc := Submodule.finrank_lt_finrank_of_lt hstrict
        have hLT : ∀ j, IsFreimanLinearOn (bohr T sigma) (L j) := by
          intro j x₁ x₂ x₃ x₄ h₁ h₂ h₃ h₄ heq
          exact hLG j x₁ x₂ x₃ x₄ (hfull h₁) (hfull h₂) (hfull h₃) (hfull h₄) heq
        obtain ⟨S, hTS, hS, hSfull, hSquarter, hgoodS⟩ := ih T hLT (by omega)
        refine ⟨S, hGT.trans hTS, ?_, hSfull.trans hfull, hSquarter.trans hquarter, hgoodS⟩
        calc
          S.card ≤ Phi^[n] T.card := hS
          _ ≤ Phi^[n] (Phi G.card) := (hmono.iterate n) hT
          _ = Phi^[n + 1] G.card := (Function.iterate_succ_apply Phi n G.card).symm
  apply haux _ Gamma hL
  have h := hrank Gamma
  omega

end LeanProofs.GowersSzemeredi
