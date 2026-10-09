import GowersSzemeredi.Proofs16CoherentAdaptiveState

/-! Adaptive coherent regularity stops at an exact rank/density state.
The original points and quadruples are retained through a source map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem coherent_adaptive_relation_iteration {N ell cells : Nat}
    [NeZero N] [NeZero cells] [Fact N.Prime]
    (theta : Fin ell → ZMod N → ZMod N)
    (epsilon : Nat × Real → Real) (cutoff : Nat × Real → Nat)
    (heps : ∀ a, 0 < a.2 → 0 < epsilon a) {rho : Real}
    (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi)) (hcells : 4 ≤ rho*cells) :
    ∀ n : Nat, ∀ a : Nat × Real, ∀ Gamma B X : Finset (ZMod N),
      ∀ F : ZMod N → ZMod N → ZMod N, ∀ Q : Finset (Fin 4 → ZMod N), ∀ sigma : Real,
      0 < a.2 → 0 ≤ sigma → Gamma.card ≤ a.1 → B.card ≤ a.1 →
      ell ≤ Module.finrank (ZMod N) (relationSubmodule (bohr Gamma rho) theta)+n →
      (∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0) →
      X ⊆ bohr Gamma (rho/4) → CoherentFrequencyFamily X B theta F sigma Q →
      a.2*(N : Real)^3 ≤ Q.card →
      (∀ j ≤ n, 8 ≤ ((coherentAdaptiveState epsilon cutoff cells ell rho)^[j] a).2*(N : Real)) →
      ∃ s : Nat, s ≤ n ∧
      let final := (coherentAdaptiveState epsilon cutoff cells ell rho)^[s] a
      ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)) (source : ZMod N → ZMod N),
        IsCoherentFrequencyRefinement Q X Gamma B theta F rho (sigma/(2 : Real)^s)
          final.2 final.1 (B.card+4*s*ell) (4^s) S B' V R source ∧
        B'.card ≤ final.1 ∧
        ((boundedBadRelationPairs (fun i : ↥B' => (i : ZMod N)) (bohr S rho)
          theta (bohr S (rho/4)) (cutoff final)).card : Real) <
            epsilon final*((bohr S (rho/4)).card : Real)^2 := by
  let Phi := coherentAdaptiveState epsilon cutoff cells ell rho
  have hrank (S : Finset (ZMod N)) :
      Module.finrank (ZMod N) (relationSubmodule (bohr S rho) theta) ≤ ell := by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      Submodule.finrank_le (relationSubmodule (bohr S rho) theta)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a Gamma B X F Q sigma ha hs hGamma hB hcap htheta hX hfamily hmass hN
    by_cases hgood : ((boundedBadRelationPairs (fun i : ↥B => (i : ZMod N)) (bohr Gamma rho)
        theta (bohr Gamma (rho/4)) (cutoff a)).card : Real) <
          epsilon a*((bohr Gamma (rho/4)).card : Real)^2
    · refine ⟨0,Nat.zero_le _,Gamma,B,X,Q,id,?_,hB,hgood⟩
      refine ⟨Finset.Subset.refl _,hGamma,Finset.Subset.refl _,by simp,htheta,hX,
        hfamily.point_density hmass,hmass,?_,fun u hu => hu,fun b hb => hb,?_⟩
      · simp only [sourceTranslationOffsets_id_card,pow_zero,le_refl]
      · simpa using hfamily
    · obtain ⟨Gamma',hGG,hG',hfull,hquarter,hstrict⟩ := bounded_bad_pair_refinement_rank
        (fun i : ↥B => (i : ZMod N)) Gamma hrho hrhoMax hcells theta
        (fun i => (htheta i).1.isFreimanLinearOn (by decide)) (cutoff a) (heps a ha) (le_of_not_gt hgood)
      have hinc := Submodule.finrank_lt_finrank_of_lt hstrict
      have hnpos : 0 < n := by have hmax := hrank Gamma'; omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hnpos)
      simp only [Fintype.card_coe,Fintype.card_fin] at hG'
      have hGbudget : Gamma'.card ≤ (Phi a).1 := hG'.trans
        (relationRankStep_le_coherentRelationBudget (heps a ha) (cutoff a) cells ell a.1
          Gamma.card B.card hGamma hB)
      have hNnext : 8 ≤ (Phi a).2*(N : Real) := by simpa only [Function.iterate_one] using hN 1 (by omega)
      have hNstep : 8 ≤ (a.2*(quarterBohrDensity (Phi a).1 rho)^4)*(N : Real) :=
        hNnext.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (coherentIterationLoss_le_fourth (Phi a).1 rho) ha.le) (Nat.cast_nonneg N))
      have href := coherent_translation_localization Q X (bohr Gamma' (rho/4)) Gamma B theta F
        hrho.le ha (quarterBohrDensity_pos (Phi a).1 hrho) htheta hX hquarter hfamily.1 hfamily.2 hmass
        (quarterBohrDensity_card_le Gamma' hrho hGbudget) hNstep
      have hdensity : a.2*(quarterBohrDensity (Phi a).1 rho)^4/512 = (Phi a).2 := by
        change a.2*(quarterBohrDensity (Phi a).1 rho)^4/512 = a.2*coherentIterationLoss (Phi a).1 rho
        unfold coherentIterationLoss
        ring
      rw [hdensity] at href
      obtain ⟨B₀,V₀,R₀,source₀,hBB₀,hB₀,hV₀,hV₀mass,hR₀mass,hoffset₀,hsource₀,hquad₀,hfamily₀⟩ := href.frequency_family
      have hBbudget : B₀.card ≤ (Phi a).1 := hB₀.trans ((Nat.add_le_add_right hB _).trans
        (coherentRelationBudget_ge (epsilon a) (cutoff a) cells ell a.1))
      have htheta' : ∀ i, FreimanHom 2 (bohr Gamma' rho) (theta i) ∧ theta i 0 = 0 := fun i =>
        ⟨IsAddFreimanHom.subset hfull (htheta i).1 (Set.mapsTo_univ _ _),(htheta i).2⟩
      have hNrec : ∀ j ≤ k, 8 ≤ (Phi^[j] (Phi a)).2*(N : Real) := by
        intro j hj
        rw [← Function.iterate_succ_apply]
        exact hN (j+1) (by omega)
      obtain ⟨s,hsn,S,B',V,R,source₁,hprops,hBstate,hgoodS⟩ :=
        ih k (Nat.lt_succ_self k) (Phi a) Gamma' B₀ V₀ (fun u => F (source₀ u)) R₀
          (sigma/2) (mul_pos ha (coherentIterationLoss_pos _ hrho)) (by positivity)
          hGbudget hBbudget (by omega) htheta' hV₀ hfamily₀ hR₀mass hNrec
      have hiter : Phi^[s] (Phi a) = Phi^[s+1] a := (Function.iterate_succ_apply Phi s a).symm
      change IsCoherentFrequencyRefinement _ _ _ _ _ _ _ _ (Phi^[s] (Phi a)).2 (Phi^[s] (Phi a)).1 _ _ _ _ _ _ _ at hprops
      rw [hiter] at hprops hBstate hgoodS
      obtain ⟨hG'S,hS,hB₀B',hB',hthetaS,hV,hVmass,hRmass,hoffset₁,hsource₁,hquad₁,hfamily₁⟩ := hprops
      refine ⟨s+1,by omega,S,B',V,R,fun u => source₀ (source₁ u),?_,hBstate,hgoodS⟩
      refine ⟨hGG.trans hG'S,hS,hBB₀.trans hB₀B',?_,hthetaS,hV,hVmass,hRmass,?_,
        fun u hu => hsource₀ _ (hsource₁ u hu),?_,?_⟩
      · calc B'.card ≤ B₀.card+4*s*ell := hB'
          _ ≤ (B.card+4*ell)+4*s*ell := Nat.add_le_add_right hB₀ _
          _ = B.card+4*(s+1)*ell := by ring
      · exact (sourceTranslationOffsets_comp_card_le source₀ source₁).trans
          ((Nat.mul_le_mul hoffset₀ hoffset₁).trans (by rw [pow_succ]; omega))
      · intro b hb
        exact hquad₀ _ (hquad₁ b hb)
      · convert hfamily₁ using 1
        simp only [pow_succ,div_div]
        ring

end LeanProofs.GowersSzemeredi
