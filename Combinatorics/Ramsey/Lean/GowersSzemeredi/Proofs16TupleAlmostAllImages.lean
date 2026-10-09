import GowersSzemeredi.Proofs16TupleValueCells
import GowersSzemeredi.Proofs16SingleSampleTupleKernels

/-! Exact tuple classes, one sample, and a popular value cell give bounded
images for almost every additive 16-tuple. Sparse kernels lie in the already
counted bad family; all other kernels use the dense-level image theorem. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnTupleImageExceptions {N : Nat} [NeZero N] (U : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (rho : Real) (K : Nat) : Finset (ColumnAnchorTuple N 15) :=
  (columnAnchorFibre U 15 0).filter fun a => K <
    ((bohr (columnListSpectrum T (columnAnchorList a)) (rho/2)).image
      (fun y => columnAnchorEval (fun x => L x y) (columnAnchorList a))).card

theorem exists_tuple_almost_all_image_set {N d M K : Nat} [NeZero N] [Fact N.Prime]
    (h7 : 7 ≤ N) (X P V : Finset (ZMod N)) (hPX : P ⊆ X) (hVP : V ⊆ P)
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    {rho t eta epsilon : Real} (hrho : 0 < rho) (ht : t ≤ rho) (heta : 0 < eta)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (e : Fin 1 → ZMod N) (hy : ∀ x ∈ V, e 0 ∈ bohr (T x) t)
    (hvalues : ((columnAnchorFibre V 15 0).image
      (fun a => columnAnchorEval (fun x => L x (e 0)) (columnAnchorList a))).card ≤ M)
    (hcap : (denseLevelCells rho : Real)^(16*d)/eta ≤ K)
    (hbad : ((sampleBadIndices (sparseColumnTuples (k := 15) P T L t eta)
      (columnTupleZeroLevel T L t) e).card : Real) ≤ epsilon*(N : Real)^15/2) :
    ∃ (Gamma U : Finset (ZMod N)), Gamma.card ≤ Nat.clog 2 (M+1) ∧ U ⊆ V ∧
      (V.card : Real)/(40 : Real)^(Nat.clog 2 (M+1)) ≤ (U.card : Real) ∧
      (∀ a ∈ columnAnchorFibre U 15 0,
        columnAnchorEval (fun x => L x (e 0)) (columnAnchorList a) = 0) ∧
      ((columnTupleImageExceptions U T L rho K).card : Real) ≤ epsilon*(N : Real)^15/2 := by
  obtain ⟨Gamma, U, hGamma, hUV, hmass, hzero⟩ := exists_tuple_zero_value_cell h7 V
    (fun x => L x (e 0)) hvalues
  have hsub : columnTupleImageExceptions U T L rho K ⊆
      sampleBadIndices (sparseColumnTuples (k := 15) P T L t eta) (columnTupleZeroLevel T L t) e := by
    intro a ha
    obtain ⟨haU, hbig⟩ := Finset.mem_filter.mp ha
    by_cases hsparse : ((columnTupleZeroLevel T L t a).card : Real) ≤ eta*N
    · have haSparse : a ∈ sparseColumnTuples (k := 15) P T L t eta :=
        Finset.mem_filter.mpr ⟨columnAnchorFibre_mono (hUV.trans hVP) 0 haU, hsparse⟩
      exact column_tuple_zero_at_single_sample_is_bad P T L t eta e haSparse
        (fun x hx => hy x (hUV ((Finset.mem_filter.mp haU).2.1 x hx))) (hzero a haU)
    · have hbound := column_tuple_image_card_le_of_dense_zero X T L hrho ht heta hT hL a
        (fun x hx => hPX (hVP (hUV ((Finset.mem_filter.mp haU).2.1 x hx))))
        (not_le.mp hsparse).le
      have hK : ((bohr (columnListSpectrum T (columnAnchorList a)) (rho/2)).image
          (fun y => columnAnchorEval (fun x => L x y) (columnAnchorList a))).card ≤ K := by
        exact_mod_cast hbound.trans hcap
      exact ((not_lt_of_ge hK) hbig).elim
  have hcard : ((columnTupleImageExceptions U T L rho K).card : Real) ≤
      (sampleBadIndices (sparseColumnTuples (k := 15) P T L t eta) (columnTupleZeroLevel T L t) e).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact ⟨Gamma, U, hGamma, hUV, hmass, hzero, hcard.trans hbad⟩

end LeanProofs.GowersSzemeredi
