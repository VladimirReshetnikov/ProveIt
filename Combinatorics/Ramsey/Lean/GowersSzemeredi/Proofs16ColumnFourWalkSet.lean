import GowersSzemeredi.Proofs16GraphEdgeExtraction

/-! Dense columns joined by many four-walks in the graph of coherent
local identities, constructed from the original bihomomorphism. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The graph extraction stage retains the column maps and their
original witnesses, and supplies a dense vertex set with uniform walk counts. -/
theorem global_column_four_walk_set {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnGraphModulusBound alpha ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    let delta := globalColumnQuadrupleDensity alpha/4
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (E : Finset (ZMod N × ZMod N)) (B : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧
      0 < delta ∧ 0 < columnIdentityRadius d rho 1 ∧
      E ⊆ X ×ˢ X ∧ (∀ p ∈ E, p.1 ≠ p.2) ∧ (∀ p ∈ E, p.swap ∈ E) ∧
      (∀ p ∈ E, ∀ q ∈ E, p.1-p.2 = q.1-q.2 →
        ColumnPairIdentity T L (columnIdentityRadius d rho 1) p q) ∧
      B ⊆ X ∧ 3*delta*N/8 ≤ (B.card : Real) ∧
      (∀ u ∈ B, ∀ v ∈ B, delta^5*(N : Real)^3/16384 ≤
        ((graphFourWalks (fun a b => (a,b) ∈ E) u v).card : Real)) := by
  obtain ⟨X, T, L, W, E, hX, hsys, hLfull, hW, hT, hL, hzero, htheta, hr, hE, hEX, hloop, hsym, hcoh⟩ :=
    global_coherent_column_graph A phi ha ha1 hA hphi hN
  have hd : 0 < globalColumnQuadrupleDensity alpha/4 := by positivity
  obtain ⟨B, hBX, hB, hwalk⟩ := exists_dense_four_walk_set_on X E hEX hsym hd (by simpa using hE)
  refine ⟨X, T, L, W, E, B, hsys, hLfull, hW, hT, hL, hzero, hd, hr, hEX, hloop, hsym, hcoh, hBX, ?_, ?_⟩
  · simpa using hB
  · simpa using hwalk

end LeanProofs.GowersSzemeredi
