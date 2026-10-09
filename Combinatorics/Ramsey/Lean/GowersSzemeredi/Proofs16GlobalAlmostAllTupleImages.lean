import GowersSzemeredi.Proofs16GlobalColumnTupleSampling
import GowersSzemeredi.Proofs16TupleAlmostAllImages

/-! The prime-cyclic almost-all 16-tuple image theorem from the original
dense bihomomorphism. Exact tuple classes allow a single sampled point.
The retained density and modulus threshold are independent of epsilon. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnTupleValueModelCap (alpha : Real) : Nat :=
  ⌈1/globalColumnTupleRepresentationDensity alpha 15⌉₊

def globalColumnTupleValueCharacterBudget (alpha : Real) : Nat :=
  Nat.clog 2 (globalColumnTupleValueModelCap alpha+1)

def globalColumnAlmostAllTupleDensity (alpha : Real) : Real :=
  globalColumnTupleSampleDensity alpha 15 1/
    (40 : Real)^(globalColumnTupleValueCharacterBudget alpha)

def globalColumnAlmostAllTupleImageCap (alpha epsilon : Real) : Nat :=
  denseLevelImageCap (16*columnSpectrumCap (columnEightDensity alpha))
    (denseLevelCells (1/(4*Real.pi))) (globalColumnSparseKernelDensity alpha 15 1 epsilon)

theorem globalColumnAlmostAllTupleDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnAlmostAllTupleDensity alpha := by
  have hs := globalColumnTupleSampleDensity_pos ha ha1 15 (by norm_num : 0 < (1 : Nat))
  unfold globalColumnAlmostAllTupleDensity
  positivity

theorem globalColumnAlmostAllTupleImageCap_pos {alpha epsilon : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon) :
    0 < globalColumnAlmostAllTupleImageCap alpha epsilon := by
  have heta := globalColumnSparseKernelDensity_pos ha ha1 he 15 (by norm_num : 0 < (1 : Nat))
  have hcells : (0 : Real) < denseLevelCells (1/(4*Real.pi)) := by
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity) : 0 < denseLevelCells (1/(4*Real.pi)))
  unfold globalColumnAlmostAllTupleImageCap denseLevelImageCap
  exact Nat.ceil_pos.mpr (by positivity)

/-- Original witness-linked maps on a dense index set have bounded image
on the half-radius common domain for all but `epsilon*N^15/2` additive
16-tuples. A single nonzero common point and its zero identities are retained. -/
theorem global_column_almost_all_tuple_images {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha epsilon : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnTupleSampleModulusBound alpha 15 1 ≤ N) :
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (U Gamma : Finset (ZMod N)) (y : ZMod N),
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
        (globalColumnAlmostAllTupleImageCap alpha epsilon)).card : Real) ≤ epsilon*(N : Real)^15/2 := by
  have h7 : 7 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨X, T, L, W, B, P, V, e, hsys, hW, hcol, hPB, hBX, hP, hVP, hV, hsample, hinj, hcube, hbad, hclasses⟩ :=
    global_column_tuple_sample_system A phi ha ha1 he hA hphi 15 1 (by norm_num) hN
  obtain ⟨J, hJA, hJ, classOf, hmodels, hclass, hpair⟩ := hclasses 0
  have hdelta := globalColumnTupleRepresentationDensity_pos ha ha1 15
  have hJReal : (J.card : Real) ≤ 1/globalColumnTupleRepresentationDensity alpha 15 :=
    (le_div_iff₀ hdelta).mpr hJ
  have hJM : J.card ≤ globalColumnTupleValueModelCap alpha := by
    exact_mod_cast hJReal.trans (Nat.le_ceil _)
  have ht := globalColumnTupleClassRadius_pos ha ha1 15
  have htaut : globalColumnTupleSampleRadius alpha 15 1 ≤ globalColumnTupleClassRadius alpha 15 := by
    unfold globalColumnTupleSampleRadius
    norm_num
    exact div_le_self ht.le (by norm_num)
  have hyV : ∀ x ∈ V, e 0 ∈ bohr (T x) (globalColumnTupleClassRadius alpha 15) :=
    fun x hx => bohr_mono_radius _ htaut (hsample x hx 0)
  have hvalues := (column_tuple_value_image_card_le P V hVP T L
    (globalColumnTupleClassRadius alpha 15) (e 0) 0 J classOf
    (fun a ha => (hclass a ha).1) hpair hyV).trans hJM
  have hrho : (0 : Real) < 1/(4*Real.pi) := by positivity
  have htrho : globalColumnTupleClassRadius alpha 15 ≤ 1/(4*Real.pi) :=
    refinementKernelRadius_le_base _ _ hrho (globalColumnTupleRepresentativeRadius_pos ha ha1 15)
  have heta := globalColumnSparseKernelDensity_pos ha ha1 he 15 (by norm_num : 0 < (1 : Nat))
  obtain ⟨Gamma, U, hGamma, hUV, hUmass, hzero, hexceptions⟩ := exists_tuple_almost_all_image_set
    (M := globalColumnTupleValueModelCap alpha) (K := globalColumnAlmostAllTupleImageCap alpha epsilon)
    h7 X P V (hPB.trans hBX) hVP T L hrho htrho heta
    (fun x hx => (hcol x hx).1) (fun x hx => (hcol x hx).2.1) e hyV hvalues
    (Nat.le_ceil _) hbad
  have hmass : globalColumnAlmostAllTupleDensity alpha*N ≤ (U.card : Real) := by
    have hd := div_le_div_of_nonneg_right hV
      (by positivity : (0 : Real) ≤ (40 : Real)^(globalColumnTupleValueCharacterBudget alpha))
    have hm : globalColumnAlmostAllTupleDensity alpha*N ≤
        (V.card : Real)/(40 : Real)^(globalColumnTupleValueCharacterBudget alpha) := by
      simpa only [globalColumnAlmostAllTupleDensity, div_mul_eq_mul_div] using hd
    exact hm.trans hUmass
  exact ⟨X, T, L, W, U, Gamma, e 0, hsys, hW, hcol, hUV.trans (hVP.trans (hPB.trans hBX)),
    hmass, hGamma, single_boolean_sample_ne_zero e hinj,
    (fun x hx => hyV x (hUV hx)), hzero, hexceptions⟩

end LeanProofs.GowersSzemeredi
