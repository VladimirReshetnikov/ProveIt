import GowersSzemeredi.Proofs16EvenModelEliminationIteration

/-! Eliminate every active model for an arbitrary fixed even list length. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Eliminate all active models, preserving an explicit positive fraction
of the original core. The remaining additive relations are zero. -/
theorem even_model_elimination_zero_core {J : Type*} {N g d k : Nat} [NeZero N] [Fact N.Prime] [NeZero k]
    (A : Finset (ZMod N)) (I : Finset J) (Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : J → ZMod N → ZMod N) {rho r s : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hA : A.Nonempty) (hGamma : Gamma.card ≤ g)
    (hT : ∀ x ∈ A, (T x).card ≤ d)
    (hf : ∀ j ∈ I, IsFreimanLinearOn (bohr Gamma rho) (f j))
    (hf0 : ∀ j ∈ I, f j 0 = 0)
    (hne : ∀ j ∈ I, ∃ y ∈ bohr Gamma (refinementKernelRadius g d rho (r/2)), f j y ≠ 0)
    (hN : refinementKernelCap g d rho (r/2) < N) (h7 : 7 ≤ N)
    (hcover : ColumnEvenModelAlternatives A Gamma T L k s r I f) :
    let beta := modelTestDensity g d r
    let t := modelEliminationRounds beta I.card
    ∃ P ⊆ A, P.Nonempty ∧ (beta/(5*k))^t*A.card ≤ (P.card : Real) ∧
      ∀ as : List (ZMod N), as.length = 2*k → (∀ x ∈ as, x ∈ P) → columnAnchorEval id as = 0 →
        ∀ y ∈ bohr Gamma s, (∀ x ∈ as, y ∈ bohr (T x) s) → columnAnchorEval (fun x => L x y) as = 0 := by
  let beta := modelTestDensity g d r
  let t := modelEliminationRounds beta I.card
  have hk0 : (0 : Real) < k := by exact_mod_cast NeZero.pos k
  have hb : 0 < beta := modelTestDensity_pos g d hr
  have hb1 : beta ≤ 1 := (modelTestDensity_le_quarter g d hr).trans (by norm_num)
  obtain ⟨P,hPA,I',_,hP,hI',hcov⟩ := even_model_elimination_iterate A I Gamma T L f
    hrho hr hrle hA hGamma hT hf hf0 hne hN h7 hcover t
  have hcard : I'.card < 1 := by
    exact_mod_cast hI'.trans_lt (modelEliminationRounds_kills hb hb1 I.card)
  have hIe : I' = ∅ := Finset.card_eq_zero.mp (by omega)
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : Real) < P.card :=
      (mul_pos (pow_pos (by positivity : 0 < beta/(5*k)) t)
        (by exact_mod_cast Finset.card_pos.mpr hA)).trans_le hP
    exact_mod_cast hp
  refine ⟨P,hPA,hPne,hP,?_⟩
  intro as hlen has hadd
  rcases hcov as hlen has hadd with hz | ⟨j,hj,_⟩
  · exact hz
  · simp only [hIe,Finset.notMem_empty] at hj

end LeanProofs.GowersSzemeredi
