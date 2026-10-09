import GowersSzemeredi.Proofs16CoherentFrequencyFamily

/-! Terminating relation refinement with whole coherent configurations.
The varying maps never change, so strict relation-rank growth bounds the
number of steps. A source map retains the original points and tuples. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem coherent_relation_iteration_budget {N ell cells : Nat}
    [NeZero N] [NeZero cells] [Fact N.Prime]
    (theta : Fin ell → ZMod N → ZMod N) {rho epsilon : Real}
    (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi)) (heps : 0 < epsilon)
    (hcells : 4 ≤ rho*cells) (cutoff D : Nat) :
    ∀ n d : Nat, ∀ Gamma B X : Finset (ZMod N), ∀ F : ZMod N → ZMod N → ZMod N,
      ∀ Q : Finset (Fin 4 → ZMod N), ∀ kappa sigma : Real,
      0 < kappa → 0 ≤ sigma → Gamma.card ≤ d → B.card ≤ d →
      (coherentRelationBudget epsilon cutoff cells ell)^[n] d ≤ D →
      ell ≤ Module.finrank (ZMod N) (relationSubmodule (bohr Gamma rho) theta)+n →
      (∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0) →
      X ⊆ bohr Gamma (rho/4) → CoherentFrequencyFamily X B theta F sigma Q →
      kappa*(N : Real)^3 ≤ Q.card →
      8 ≤ (kappa*(coherentIterationLoss D rho)^n)*(N : Real) →
      ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)) (source : ZMod N → ZMod N),
        Gamma ⊆ S ∧ S.card ≤ D ∧ B ⊆ B' ∧ B'.card ≤ B.card+4*n*ell ∧
        (∀ i, FreimanHom 2 (bohr S rho) (theta i) ∧ theta i 0 = 0) ∧
        V ⊆ bohr S (rho/4) ∧
        (kappa*(coherentIterationLoss D rho)^n)*N ≤ (V.card : Real) ∧
        (kappa*(coherentIterationLoss D rho)^n)*(N : Real)^3 ≤ R.card ∧
        (sourceTranslationOffsets source).card ≤ 4^n ∧
        (∀ u ∈ V, source u ∈ X) ∧ (∀ b ∈ R, (fun j => source (b j)) ∈ Q) ∧
        CoherentFrequencyFamily V B' theta (fun u => F (source u)) (sigma/(2 : Real)^n) R ∧
        ((boundedBadRelationPairs (fun i : ↥B' => (i : ZMod N)) (bohr S rho)
          theta (bohr S (rho/4)) cutoff).card : Real) < epsilon*((bohr S (rho/4)).card : Real)^2 := by
  let Phi := coherentRelationBudget epsilon cutoff cells ell
  let q := coherentIterationLoss D rho
  have hq : 0 < q := coherentIterationLoss_pos D hrho
  have hq1 : q ≤ 1 := coherentIterationLoss_le_one D hrho
  have hge (d : Nat) : d ≤ Phi d := (Nat.le_add_right d (4*ell)).trans
    (coherentRelationBudget_ge epsilon cutoff cells ell d)
  have hrank (S : Finset (ZMod N)) :
      Module.finrank (ZMod N) (relationSubmodule (bohr S rho) theta) ≤ ell := by
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin] using
      Submodule.finrank_le (relationSubmodule (bohr S rho) theta)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d Gamma B X F Q kappa sigma hk hs hGamma hB hD hcap htheta hX hfamily hmass hN
    change Phi^[n] d ≤ D at hD
    by_cases hgood : ((boundedBadRelationPairs (fun i : ↥B => (i : ZMod N)) (bohr Gamma rho)
        theta (bohr Gamma (rho/4)) cutoff).card : Real) < epsilon*((bohr Gamma (rho/4)).card : Real)^2
    · have hsmall : kappa*q^n ≤ kappa := by
        calc kappa*q^n ≤ kappa*1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hq.le hq1) hk.le
          _ = _ := mul_one _
      refine ⟨Gamma,B,X,Q,id,Finset.Subset.refl _,hGamma.trans
        ((Function.id_le_iterate_of_id_le hge n d).trans hD),Finset.Subset.refl _,
        by omega,htheta,hX,?_,?_,?_,fun u hu => hu,fun b hb => hb,?_,hgood⟩
      · exact (mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg N)).trans (hfamily.point_density hmass)
      · exact (mul_le_mul_of_nonneg_right hsmall (by positivity)).trans hmass
      · rw [sourceTranslationOffsets_id_card]
        exact Nat.one_le_pow _ _ (by norm_num)
      · exact hfamily.mono_radius (div_le_self hs (one_le_pow₀ (by norm_num)))
    · obtain ⟨Gamma',hGG,hG',hfull,hquarter,hstrict⟩ := bounded_bad_pair_refinement_rank
        (fun i : ↥B => (i : ZMod N)) Gamma hrho hrhoMax hcells theta
        (fun i => (htheta i).1.isFreimanLinearOn (by decide)) cutoff heps (le_of_not_gt hgood)
      have hinc := Submodule.finrank_lt_finrank_of_lt hstrict
      have hnpos : 0 < n := by have hmax := hrank Gamma'; omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hnpos)
      rw [Function.iterate_succ_apply] at hD
      have hPhiD : Phi d ≤ D := (Function.id_le_iterate_of_id_le hge k (Phi d)).trans hD
      simp only [Fintype.card_coe,Fintype.card_fin] at hG'
      have hGbudget : Gamma'.card ≤ Phi d := hG'.trans
        (relationRankStep_le_coherentRelationBudget heps cutoff cells ell d Gamma.card B.card hGamma hB)
      have hpow : q^(k+1) ≤ (quarterBohrDensity D rho)^4 := by
        calc q^(k+1) = q^k*q := pow_succ _ _
          _ ≤ 1*q := mul_le_mul_of_nonneg_right (pow_le_one₀ hq.le hq1) hq.le
          _ = q := one_mul _
          _ ≤ _ := coherentIterationLoss_le_fourth D rho
      have hNstep : 8 ≤ (kappa*(quarterBohrDensity D rho)^4)*(N : Real) :=
        hN.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hk.le) (Nat.cast_nonneg N))
      have href := coherent_translation_localization Q X (bohr Gamma' (rho/4)) Gamma B theta F
        hrho.le hk (quarterBohrDensity_pos D hrho) htheta hX hquarter hfamily.1 hfamily.2 hmass
        (quarterBohrDensity_card_le Gamma' hrho (hGbudget.trans hPhiD)) hNstep
      have hdensity : kappa*(quarterBohrDensity D rho)^4/512 = kappa*q := by
        dsimp only [q,coherentIterationLoss]
        ring
      rw [hdensity] at href
      obtain ⟨B₀,V₀,R₀,source₀,hBB₀,hB₀,hV₀,hV₀mass,hR₀mass,hoffset₀,hsource₀,hquad₀,hfamily₀⟩ := href.frequency_family
      have hBbudget : B₀.card ≤ Phi d := hB₀.trans ((Nat.add_le_add_right hB _).trans
        (coherentRelationBudget_ge epsilon cutoff cells ell d))
      have htheta' : ∀ i, FreimanHom 2 (bohr Gamma' rho) (theta i) ∧ theta i 0 = 0 := fun i =>
        ⟨IsAddFreimanHom.subset hfull (htheta i).1 (Set.mapsTo_univ _ _),(htheta i).2⟩
      have hNrec : 8 ≤ ((kappa*q)*q^k)*(N : Real) := by
        convert hN using 1
        simp only [pow_succ]
        ring
      obtain ⟨S,B',V,R,source₁,hG'S,hS,hB₀B',hB',hthetaS,hV,hVmass,hRmass,hoffset₁,hsource₁,hquad₁,hfamily₁,hgoodS⟩ :=
        ih k (Nat.lt_succ_self k) (Phi d) Gamma' B₀ V₀ (fun u => F (source₀ u)) R₀
          (kappa*q) (sigma/2) (mul_pos hk hq) (by positivity) hGbudget hBbudget hD
          (by omega) htheta' hV₀ hfamily₀ hR₀mass hNrec
      refine ⟨S,B',V,R,fun u => source₀ (source₁ u),hGG.trans hG'S,hS,hBB₀.trans hB₀B',?_,
        hthetaS,hV,?_,?_,?_,fun u hu => hsource₀ _ (hsource₁ u hu),?_,?_,hgoodS⟩
      · calc B'.card ≤ B₀.card+4*k*ell := hB'
          _ ≤ (B.card+4*ell)+4*k*ell := Nat.add_le_add_right hB₀ _
          _ = B.card+4*(k+1)*ell := by ring
      · convert hVmass using 1
        simp only [pow_succ]
        ring
      · convert hRmass using 1
        simp only [pow_succ]
        ring
      · exact (sourceTranslationOffsets_comp_card_le source₀ source₁).trans
          ((Nat.mul_le_mul hoffset₀ hoffset₁).trans (by rw [pow_succ]; omega))
      · intro b hb
        exact hquad₀ _ (hquad₁ b hb)
      · convert hfamily₁ using 1
        simp only [pow_succ,div_div]
        ring

end LeanProofs.GowersSzemeredi
