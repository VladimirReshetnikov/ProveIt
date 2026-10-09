import GowersSzemeredi.Proofs16ModelEliminationIteration

/-! A logarithmic number of rounds in the initial model count suffices. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def modelEliminationRounds (beta : Real) (M : Nat) : Nat :=
  ⌈Real.log ((M : Real)+1)/beta⌉₊

/-- The geometric survivor bound is strictly below one after these rounds. -/
theorem modelEliminationRounds_kills {beta : Real} (hb : 0 < beta) (hb1 : beta ≤ 1) (M : Nat) :
    (1-beta)^(modelEliminationRounds beta M)*(M : Real) < 1 := by
  have hlog : Real.log ((M : Real)+1) ≤ (modelEliminationRounds beta M : Real)*beta := by
    have ht : Real.log ((M : Real)+1)/beta ≤ (modelEliminationRounds beta M : Real) := Nat.le_ceil _
    exact (div_le_iff₀ hb).mp ht
  have hbase : 1-beta ≤ Real.exp (-beta) := by
    have h := Real.add_one_le_exp (-beta)
    linarith
  have hp : (1-beta)^(modelEliminationRounds beta M) ≤ 1/((M : Real)+1) := by
    calc _ ≤ (Real.exp (-beta))^(modelEliminationRounds beta M) :=
        pow_le_pow_left₀ (by linarith) hbase _
      _ = Real.exp ((modelEliminationRounds beta M : Real)*(-beta)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-Real.log ((M : Real)+1)) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg,Real.exp_log (by positivity),one_div]
  calc _ ≤ (1/((M : Real)+1))*M := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)
    _ < 1 := by rw [one_div_mul_eq_div]; exact (div_lt_one (by positivity)).mpr (by linarith)

/-- Eliminate all active models, preserving an explicit positive fraction
of the original core. The remaining additive relations are zero. -/
theorem column_model_elimination_zero_core {J : Type*} {N g d : Nat} [NeZero N] [Fact N.Prime]
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
    (hcover : ColumnQuadModelAlternatives A Gamma T L s r I f) :
    let beta := modelTestDensity g d r
    let t := modelEliminationRounds beta I.card
    ∃ P ⊆ A, P.Nonempty ∧ (beta/10)^t*A.card ≤ (P.card : Real) ∧
      ∀ q : Fin 4 → ZMod N, (∀ i, q i ∈ P) → q 0-q 1+q 2-q 3 = 0 →
        ∀ y ∈ bohr Gamma s, (∀ i, y ∈ bohr (T (q i)) s) → columnQuadValue L q y = 0 := by
  let beta := modelTestDensity g d r
  let t := modelEliminationRounds beta I.card
  have hb : 0 < beta := modelTestDensity_pos g d hr
  have hb1 : beta ≤ 1 := (modelTestDensity_le_quarter g d hr).trans (by norm_num)
  obtain ⟨P,hPA,I',_,hP,hI',hcov⟩ := column_model_elimination_iterate A I Gamma T L f
    hrho hr hrle hA hGamma hT hf hf0 hne hN h7 hcover t
  have hcard : I'.card < 1 := by
    exact_mod_cast hI'.trans_lt (modelEliminationRounds_kills hb hb1 I.card)
  have hIe : I' = ∅ := Finset.card_eq_zero.mp (by omega)
  have hPne : P.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : Real) < P.card :=
      (mul_pos (pow_pos (by positivity : 0 < beta/10) t)
        (by exact_mod_cast Finset.card_pos.mpr hA)).trans_le hP
    exact_mod_cast hp
  refine ⟨P,hPA,hPne,hP,?_⟩
  intro q hq hadd
  rcases hcov q hq hadd with hz | ⟨j,hj,_⟩
  · exact hz
  · simp only [hIe,Finset.notMem_empty] at hj

end LeanProofs.GowersSzemeredi
