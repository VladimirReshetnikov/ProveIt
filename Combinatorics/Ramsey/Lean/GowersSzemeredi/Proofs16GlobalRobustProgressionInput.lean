import GowersSzemeredi.Proofs16GlobalAlmostAllTupleImages
import GowersSzemeredi.Proofs16RobustDifferenceProgression

/-! The original dense bihomomorphism supplies both almost-all tuple image
control and a proper progression with uniformly many original-index
representations. This is the geometric input to progression-indexed maps;
those maps and their compatibility are not assumed or asserted here. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnProgressionLogDensity (alpha : Real) : Real :=
  max 1 (-Real.log (globalColumnAlmostAllTupleDensity alpha))

theorem globalColumnProgressionLogDensity_pos (alpha : Real) :
    0 < globalColumnProgressionLogDensity alpha :=
  lt_of_lt_of_le (by norm_num : (0 : Real) < 1) (le_max_left _ _)

theorem exp_neg_globalColumnProgressionLogDensity_le {alpha : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    Real.exp (-globalColumnProgressionLogDensity alpha) ≤ globalColumnAlmostAllTupleDensity alpha := by
  have hdelta := globalColumnAlmostAllTupleDensity_pos ha ha1
  have hp : -Real.log (globalColumnAlmostAllTupleDensity alpha) ≤ globalColumnProgressionLogDensity alpha :=
    le_max_right _ _
  have h := Real.exp_le_exp.mpr (neg_le_neg hp)
  simpa only [neg_neg, Real.exp_log hdelta] using h

/-- From the original dense bihomomorphism obtain the controlled column
set and a structured progression with robust four-term representations.
All rank and mass guarantees are independent of the exceptional fraction. -/
theorem global_almost_all_images_with_robust_progression {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha epsilon : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnTupleSampleModulusBound alpha 15 1 ≤ N) :
    let p := globalColumnProgressionLogDensity alpha
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U Gamma : Finset (ZMod N)) (y : ZMod N)
      (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ columnSpectrumCap (columnEightDensity alpha) ∧
        IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x) ∧ L x 0 = 0) ∧
      U ⊆ X ∧ globalColumnAlmostAllTupleDensity alpha*N ≤ (U.card : Real) ∧
      Gamma.card ≤ globalColumnTupleValueCharacterBudget alpha ∧ y ≠ 0 ∧
      (∀ x ∈ U, y ∈ bohr (T x) (globalColumnTupleClassRadius alpha 15)) ∧
      (∀ a ∈ columnAnchorFibre U 15 0,
        columnAnchorEval (fun x => L x y) (columnAnchorList a) = 0) ∧
      ((columnTupleImageExceptions U T L (1/(4*Real.pi))
        (globalColumnAlmostAllTupleImageCap alpha epsilon)).card : Real) ≤ epsilon*(N : Real)^15/2 ∧
      (Q.rank : Real) ≤ 2+robustDifferenceBohrConstant*(p+1)^4 ∧ Q.Proper ∧
      Real.exp (-(robustDifferenceProgressionConstant*(p+1)^8))*N ≤ (Q.carrier.card : Real) ∧
      ∀ t ∈ Q.carrier, (Real.exp (-p))^4/8*(N : Real)^3 ≤
        ((fourDifferenceRepresentations U t).card : Real) := by
  obtain ⟨X, T, L, W, U, Gamma, y, hsys, hW, hcol, hUX, hU, hGamma, hy0, hy, hzero, hexceptions⟩ :=
    global_column_almost_all_tuple_images A phi ha ha1 he hA hphi hN
  have hp := globalColumnProgressionLogDensity_pos alpha
  have hdensity : Real.exp (-globalColumnProgressionLogDensity alpha)*N ≤ (U.card : Real) :=
    (mul_le_mul_of_nonneg_right (exp_neg_globalColumnProgressionLogDensity_le ha ha1)
      (Nat.cast_nonneg N)).trans hU
  obtain ⟨Q, hQrank, hproper, hmass, hrepresentations⟩ := exists_robust_difference_progression U hp.le hdensity
  exact ⟨X, T, L, W, U, Gamma, y, Q, hsys, hW, hcol, hUX, hU, hGamma, hy0, hy, hzero, hexceptions,
    hQrank, hproper, hmass, hrepresentations⟩

end LeanProofs.GowersSzemeredi
