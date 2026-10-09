import GowersSzemeredi.Proofs16GlobalColumnRelations
import GowersSzemeredi.Proofs16DifferenceStars

/-! A dense bihomomorphism gives a dense family of column pairs whose
identities agree whenever their index differences agree. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The first coherent pair extraction retains the relation density:
`theta*N^3` relations yield `theta*N^2` selected pairs. -/
theorem global_coherent_column_pairs {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnCompositionModulusBound alpha 2 ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let rho := globalColumnIdentityRadius alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (P : Finset (ZMod N × ZMod N)),
      (alpha / (2 - alpha)) * N ≤ X.card ∧
      IsColumnWitnessSystem A phi X T L W (1 / (4 * Real.pi)) ∧
      (∀ x ∈ X, (T x).card ≤ d) ∧
      (∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x)) ∧
      (∀ x ∈ X, L x 0 = 0) ∧
      0 < globalColumnQuadrupleDensity alpha ∧
      0 < columnIdentityRadius d rho 1 ∧
      globalColumnQuadrupleDensity alpha * (N : Real)^2 ≤ P.card ∧
      P ⊆ X ×ˢ X ∧
      (∀ p ∈ P, ∀ q ∈ P, p.1-p.2 = q.1-q.2 →
        ColumnPairIdentity T L (columnIdentityRadius d rho 1) p q) := by
  obtain ⟨X, T, L, W, hX, hsys, hT, hL, hzero, hW, hrho, htheta, hmany, hcomp⟩ :=
    global_dense_column_relations A phi ha ha1 hA hphi hN
  let R := ColumnPairRelated X T L (globalColumnIdentityRadius alpha)
  obtain ⟨P, hPcard, hP, hbridge⟩ := exists_difference_stars R (fun _ _ h => h.2.2.1)
  have hcount : globalColumnQuadrupleDensity alpha * (N : Real)^3 ≤ N * (P.card : Real) := by
    exact hmany.trans (by exact_mod_cast hPcard)
  have hNpos : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hdensity : globalColumnQuadrupleDensity alpha * (N : Real)^2 ≤ P.card := by
    apply (mul_le_mul_iff_right₀ hNpos).mp
    nlinarith [hcount]
  refine ⟨X, T, L, W, P, hX, hsys, hT, hL, hzero, htheta,
    columnIdentityRadius_pos _ hrho 1, hdensity, ?_, ?_⟩
  · intro p hp
    obtain ⟨z, hz⟩ := hP p hp
    exact Finset.mem_product.mpr hz.2.1
  · intro p hp q hq hd
    obtain ⟨z, hzp, hzq⟩ := hbridge p hp q hq hd
    have h := hcomp 1 1 p z q (by omega) (by omega) (by omega) hzp.symm hzq
    exact h.2.2.2

end LeanProofs.GowersSzemeredi
