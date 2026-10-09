import GowersSzemeredi.Proofs16CoherentRelationIteration

/-! A uniform terminating refinement with sparse bounded relations.
All bounds depend on input parameters, not on the ambient modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentRegularityRank (epsilon : Real) (cutoff cells ell d : Nat) : Nat :=
  (coherentRelationBudget epsilon cutoff cells ell)^[ell] d

def coherentRegularityDensity (epsilon : Real) (cutoff cells ell d : Nat) (rho kappa : Real) : Real :=
  kappa*(coherentIterationLoss (coherentRegularityRank epsilon cutoff cells ell d) rho)^ell

def coherentRegularityModulusBound (epsilon : Real) (cutoff cells ell d : Nat) (rho kappa : Real) : Nat :=
  ⌈8/coherentRegularityDensity epsilon cutoff cells ell d rho kappa⌉₊

theorem coherentRegularityDensity_pos (epsilon : Real) (cutoff cells ell d : Nat)
    {rho kappa : Real} (hr : 0 < rho) (hk : 0 < kappa) :
    0 < coherentRegularityDensity epsilon cutoff cells ell d rho kappa :=
  mul_pos hk (pow_pos (coherentIterationLoss_pos _ hr) ell)

theorem coherentRegularityModulusBound_mass {N cutoff cells ell d : Nat} {epsilon rho kappa : Real}
    (hr : 0 < rho) (hk : 0 < kappa)
    (hN : coherentRegularityModulusBound epsilon cutoff cells ell d rho kappa ≤ N) :
    8 ≤ coherentRegularityDensity epsilon cutoff cells ell d rho kappa*(N : Real) := by
  have h : 8/coherentRegularityDensity epsilon cutoff cells ell d rho kappa ≤ (N : Real) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  simpa only [mul_comm] using (div_le_iff₀ (coherentRegularityDensity_pos _ _ _ _ _ hr hk)).mp h

def IsCoherentFrequencyRefinement {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (rho sigma density : Real) (rankBound fixedBound offsetBound : Nat)
    (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)) (source : ZMod N → ZMod N) : Prop :=
  Gamma ⊆ S ∧ S.card ≤ rankBound ∧ B ⊆ B' ∧ B'.card ≤ fixedBound ∧
  (∀ i, FreimanHom 2 (bohr S rho) (theta i) ∧ theta i 0 = 0) ∧
  V ⊆ bohr S (rho/4) ∧ density*N ≤ (V.card : Real) ∧ density*(N : Real)^3 ≤ R.card ∧
  (sourceTranslationOffsets source).card ≤ offsetBound ∧
  (∀ u ∈ V, source u ∈ X) ∧ (∀ b ∈ R, (fun j => source (b j)) ∈ Q) ∧
  CoherentFrequencyFamily V B' theta (fun u => F (source u)) sigma R

theorem exists_coherent_sparse_relation_domain {N ell cells : Nat}
    [NeZero N] [NeZero cells] [Fact N.Prime]
    (Q : Finset (Fin 4 → ZMod N)) (X Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    {rho sigma kappa epsilon : Real} (hrho : 0 < rho) (hrhoMax : rho ≤ 1/(8*Real.pi))
    (hs : 0 ≤ sigma) (hk : 0 < kappa) (heps : 0 < epsilon) (hcells : 4 ≤ rho*cells)
    (cutoff d : Nat) (hG : Gamma.card ≤ d) (hB : B.card ≤ d)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4)) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : coherentRegularityModulusBound epsilon cutoff cells ell d rho kappa ≤ N) :
    ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)) (source : ZMod N → ZMod N),
      IsCoherentFrequencyRefinement Q X Gamma B theta F rho (sigma/(2 : Real)^ell)
        (coherentRegularityDensity epsilon cutoff cells ell d rho kappa)
        (coherentRegularityRank epsilon cutoff cells ell d) (B.card+4*ell*ell) (4^ell) S B' V R source ∧
      ((boundedBadRelationPairs (fun i : ↥B' => (i : ZMod N)) (bohr S rho)
        theta (bohr S (rho/4)) cutoff).card : Real) < epsilon*((bohr S (rho/4)).card : Real)^2 := by
  obtain ⟨S,B',V,R,source,hGS,hS,hBB',hB',hthetaS,hV,hVmass,hRmass,hoffset,hsource,hquad,hfamily',hgood⟩ :=
    coherent_relation_iteration_budget theta hrho hrhoMax heps hcells cutoff
      (coherentRegularityRank epsilon cutoff cells ell d) ell d Gamma B X F Q kappa sigma
      hk hs hG hB le_rfl (by omega) htheta hX hfamily hmass
      (coherentRegularityModulusBound_mass hrho hk hN)
  exact ⟨S,B',V,R,source,⟨hGS,hS,hBB',hB',hthetaS,hV,hVmass,hRmass,hoffset,hsource,hquad,hfamily'⟩,hgood⟩

end LeanProofs.GowersSzemeredi
