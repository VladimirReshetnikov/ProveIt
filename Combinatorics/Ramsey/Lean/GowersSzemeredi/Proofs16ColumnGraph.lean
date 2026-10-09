import GowersSzemeredi.Proofs16SymmetricColumnPairs

/-! A dense symmetric loopless graph of coherent column pairs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Removing loops from a pair family deletes at most one pair per vertex. -/
theorem pair_card_le_off_diagonal_add {V : Type*} [Fintype V]
    (Q : Finset (V × V)) :
    Q.card ≤ (Q.filter (fun p => p.1 ≠ p.2)).card + Fintype.card V := by
  have hdiag : (Q.filter (fun p => p.1 = p.2)).card ≤ Fintype.card V := by
    apply Finset.card_le_card_of_injOn Prod.fst (by simp)
    intro p hp q hq heq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    exact Prod.ext heq (hp'.symm.trans (heq.trans hq'))
  have hsum := Finset.card_filter_add_card_filter_not (s := Q) (fun p => p.1 = p.2)
  change Q.card ≤ (Q.filter (fun p => ¬p.1 = p.2)).card + Fintype.card V
  omega

def globalColumnGraphModulusBound (alpha : Real) : Nat :=
  max (globalColumnCompositionModulusBound alpha 2)
    (⌈4 / globalColumnQuadrupleDensity alpha⌉₊ + 3)

/-- The graph has ordered-edge density at least `theta/4`, is symmetric
and loopless, and has coherent identities in every difference fibre. -/
theorem global_coherent_column_graph {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnGraphModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (E : Finset (ZMod N × ZMod N)),
      (alpha / (2 - alpha)) * N ≤ X.card ∧
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧
      0 < globalColumnQuadrupleDensity alpha ∧
      0 < columnIdentityRadius d rho 1 ∧
      (globalColumnQuadrupleDensity alpha / 4) * (N : Real)^2 ≤ E.card ∧
      E ⊆ X ×ˢ X ∧ (∀ p ∈ E, p.1 ≠ p.2) ∧ (∀ p ∈ E, p.swap ∈ E) ∧
      (∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 →
        ColumnPairIdentity T L (columnIdentityRadius d rho 1) p q) := by
  have hNbase : globalColumnCompositionModulusBound alpha 2 ≤ N := (le_max_left _ _).trans hN
  have hNsize : ⌈4 / globalColumnQuadrupleDensity alpha⌉₊ + 3 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨X, T, L, W, P, hX, hsys, hT, hL, hzero, htheta, hr, hP, hPX, hcoh⟩ :=
    global_coherent_column_pairs A phi ha ha1 hA hphi hNbase
  obtain ⟨Q, hPQ, hQX, hsym, hQcoh⟩ :=
    exists_symmetric_coherent_pairs (by omega) X T L _ P hPX hcoh
  let E := Q.filter (fun p => p.1 ≠ p.2)
  have hQE : (Q.card : Real) ≤ E.card + N := by
    have h : Q.card ≤ E.card + N := by simpa only [ZMod.card, E, ne_eq] using pair_card_le_off_diagonal_add Q
    exact_mod_cast h
  have hPQ' : (P.card : Real) ≤ 2 * Q.card := by exact_mod_cast hPQ
  have hceil : 4 / globalColumnQuadrupleDensity alpha ≤ (N : Real) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4 / globalColumnQuadrupleDensity alpha⌉₊ ≤ N by omega))
  have hfour : 4 ≤ globalColumnQuadrupleDensity alpha * N := by
    have h := (div_le_iff₀ htheta).mp hceil
    nlinarith
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hloop : (N : Real) ≤ (globalColumnQuadrupleDensity alpha / 4) * (N : Real)^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hfour hNpos.le]
  refine ⟨X, T, L, W, E, hX, hsys, hT, hL, hzero, htheta, hr, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · exact (Finset.filter_subset _ _).trans hQX
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    obtain ⟨hpQ, hpne⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hsym p hpQ, Ne.symm hpne⟩
  · intro p hp q hq hd
    exact hQcoh p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1 hd

end LeanProofs.GowersSzemeredi
