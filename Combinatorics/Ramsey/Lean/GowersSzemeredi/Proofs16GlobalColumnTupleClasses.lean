import GowersSzemeredi.Proofs16GlobalColumnWordEndpoints
import GowersSzemeredi.Proofs16FixedRelationWordFamilies
import GowersSzemeredi.Proofs16ColumnTupleClassCover
import GowersSzemeredi.Proofs16GlobalColumnModels

/-! Bounded classes of tuples from the original dense bihomomorphism.
Representatives have individual Bohr spectra of rank at most `(k+1)*d`.
Pairwise identities inside each class use only the two tuples' spectra;
there is no shared-spectrum cost proportional to the number of classes. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnTupleRepresentationDensity (alpha : Real) (k : Nat) : Real :=
  thresholdColumnWordDensity (absBsgWordLambda (globalColumnQuadrupleDensity alpha) 1)
    (absBsgWordEta (globalColumnQuadrupleDensity alpha) 1) k

def globalColumnTupleRepresentativeRadius (alpha : Real) (k : Nat) : Real :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d) (1/(4*Real.pi))
    (globalColumnWordEndpointRadius alpha k)

def globalColumnTupleClassRadius (alpha : Real) (k : Nat) : Real :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  refinementKernelRadius (2*(k+1)*d) ((k+1)*d) (1/(4*Real.pi))
    (globalColumnTupleRepresentativeRadius alpha k)

def globalColumnTupleClassModulusBound (alpha : Real) (k : Nat) : Nat :=
  let d := columnSpectrumCap (columnEightDensity alpha)
  max (globalColumnWordEndpointModulusBound alpha k)
    (max (refinementKernelCap (2*(k+1)*d) (3*(k+1)*d) (1/(4*Real.pi))
      (globalColumnWordEndpointRadius alpha k)+1)
      (refinementKernelCap (2*(k+1)*d) ((k+1)*d) (1/(4*Real.pi))
        (globalColumnTupleRepresentativeRadius alpha k)+1))

theorem globalColumnTupleRepresentationDensity_pos {alpha : Real} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) (k : Nat) : 0 < globalColumnTupleRepresentationDensity alpha k := by
  have hp := absBsgWord_parameters_pos (globalColumnQuadrupleDensity_pos ha ha1)
    (by norm_num : (0 : Real) < 1) k
  exact thresholdColumnWordDensity_pos hp.1 hp.2.1 k

theorem globalColumnTupleRepresentativeRadius_pos {alpha : Real} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) (k : Nat) : 0 < globalColumnTupleRepresentativeRadius alpha k :=
  refinementKernelRadius_pos _ _ (by positivity) (globalColumnWordEndpointRadius_pos ha ha1 k)

theorem globalColumnTupleClassRadius_pos {alpha : Real} (ha : 0 < alpha)
    (ha1 : alpha ≤ 1) (k : Nat) : 0 < globalColumnTupleClassRadius alpha k :=
  refinementKernelRadius_pos _ _ (by positivity) (globalColumnTupleRepresentativeRadius_pos ha ha1 k)

/-- Every alternating-value fibre of original column tuples has bounded
classes with exact pairwise identities and individually controlled models. -/
theorem global_column_tuple_classes {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (k : Nat) (hN : globalColumnTupleClassModulusBound alpha k ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let delta := globalColumnTupleRepresentationDensity alpha k
    let s := globalColumnTupleRepresentativeRadius alpha k
    let t := globalColumnTupleClassRadius alpha k
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (B P : Finset (ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d ∧
        IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x) ∧ L x 0 = 0) ∧
      P ⊆ B ∧ B ⊆ X ∧ absBsgEps (globalColumnQuadrupleDensity alpha) 1*N ≤ (P.card : Real) ∧
      0 < delta ∧ 0 < s ∧ 0 < t ∧
      (∀ a : ColumnAnchorTuple N k, (∀ x ∈ columnAnchorList a, x ∈ P) →
        delta*(N : Real)^(3*k+2) ≤ (fixedRelationWordRepresentations B
          (columnZeroQ X T L d (1/(4*Real.pi)) (globalColumnIdentityRadius alpha) 16) a).card) ∧
      ∀ c : ZMod N, ∃ J ⊆ columnAnchorFibre P k c, (J.card : Real)*delta ≤ 1 ∧
        ∃ classOf : ColumnAnchorTuple N k → ColumnAnchorTuple N k,
          (∀ j ∈ J, (columnListSpectrum T (columnAnchorList j)).card ≤ (k+1)*d ∧
            IsFreimanLinearOn (bohr (columnListSpectrum T (columnAnchorList j)) (1/(4*Real.pi)))
              (fun y => columnAnchorEval (fun x => L x y) (columnAnchorList j)) ∧
            columnAnchorEval (fun x => L x 0) (columnAnchorList j) = 0) ∧
          (∀ a ∈ columnAnchorFibre P k c, classOf a ∈ J ∧
            ColumnListIdentity T L s (columnAnchorList a) (columnAnchorList (classOf a))) ∧
          ∀ a ∈ columnAnchorFibre P k c, ∀ b ∈ columnAnchorFibre P k c,
            classOf a = classOf b → ColumnListIdentity T L t (columnAnchorList a) (columnAnchorList b) := by
  have hNword : globalColumnWordEndpointModulusBound alpha k ≤ N := (le_max_left _ _).trans hN
  have hN1 : refinementKernelCap (2*(k+1)*columnSpectrumCap (columnEightDensity alpha))
      (3*(k+1)*columnSpectrumCap (columnEightDensity alpha)) (1/(4*Real.pi))
      (globalColumnWordEndpointRadius alpha k) < N :=
    Nat.lt_of_succ_le ((le_max_left _ _).trans ((le_max_right _ _).trans hN))
  have hN2 : refinementKernelCap (2*(k+1)*columnSpectrumCap (columnEightDensity alpha))
      ((k+1)*columnSpectrumCap (columnEightDensity alpha)) (1/(4*Real.pi))
      (globalColumnTupleRepresentativeRadius alpha k) < N :=
    Nat.lt_of_succ_le ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨X, T, L, W, B, P, hX, hsys, hW, hcol, hPB, hBX, hP, hrich, hwords⟩ :=
    global_column_word_endpoint_system A phi ha ha1 hA hphi k hNword
  let d := columnSpectrumCap (columnEightDensity alpha)
  let delta := globalColumnTupleRepresentationDensity alpha k
  let r := globalColumnWordEndpointRadius alpha k
  let rho : Real := 1/(4*Real.pi)
  let R := columnZeroQ X T L d rho (globalColumnIdentityRadius alpha) 16
  have hrho : 0 < rho := by dsimp [rho]; positivity
  have hr : 0 < r := globalColumnWordEndpointRadius_pos ha ha1 k
  have hrle : r ≤ rho := refinementKernelRadius_le_base _ _ hrho
    (globalColumnWordZeroRadius_pos ha ha1)
  have hd : 0 < delta := globalColumnTupleRepresentationDensity_pos ha ha1 k
  have hcount : ∀ a : ColumnAnchorTuple N k, (∀ x ∈ columnAnchorList a, x ∈ P) →
      delta*(N : Real)^(3*k+2) ≤ (fixedRelationWordRepresentations B R a).card := by
    intro a haP
    rw [fixedRelationWordRepresentations_card]
    simpa only [columnAnchorList, List.length_ofFn, delta, globalColumnTupleRepresentationDensity, R, d, rho] using
      (hwords a.1 (List.ofFn a.2) haP (by simp)).1
  have hspec : ∀ a : ColumnAnchorTuple N k, (∀ x ∈ columnAnchorList a, x ∈ P) →
      ∀ w ∈ fixedRelationWordRepresentations B R a,
        (∀ x ∈ columnWordEntries w, x ∈ B) ∧
        columnWordValue w = columnAnchorEval id (columnAnchorList a) ∧
        ColumnListIdentity T L r (columnAnchorList a) (columnWordEntries w) := by
    intro a haP w hw
    exact fixedRelationWordRepresentations_spec B R T L r a
      (hwords a.1 (List.ofFn a.2) haP (by simp)).2 hw
  refine ⟨X, T, L, W, B, P, hsys, hW, hcol, hPB, hBX, hP, hd,
    globalColumnTupleRepresentativeRadius_pos ha ha1 k,
    globalColumnTupleClassRadius_pos ha ha1 k, hcount, ?_⟩
  intro c
  obtain ⟨J, hJA, hJ, classOf, hclass, hpair⟩ := column_tuple_class_cover
    (columnAnchorFibre P k c) X T L columnAnchorList (fixedRelationWordRepresentations B R) c
    hrho hr hrle hd (fun x hx => (hcol x hx).1) (fun x hx => (hcol x hx).2.1)
    (fun x hx => (hcol x hx).2.2) (fun a _ => columnAnchorList_length a)
    (fun a ha x hx => hBX (hPB ((Finset.mem_filter.mp ha).2.1 x hx)))
    (fun a ha w hw x hx => hBX ((hspec a (Finset.mem_filter.mp ha).2.1 w hw).1 x hx))
    (fun a ha w hw => (hspec a (Finset.mem_filter.mp ha).2.1 w hw).2.1.trans (Finset.mem_filter.mp ha).2.2)
    (fun a ha => hcount a (Finset.mem_filter.mp ha).2.1)
    (fun a ha w hw => (hspec a (Finset.mem_filter.mp ha).2.1 w hw).2.2) hN1 hN2
  refine ⟨J, hJA, hJ, classOf, ?_, hclass, hpair⟩
  intro j hj
  have hjX : ∀ x ∈ columnAnchorList j, x ∈ X :=
    fun x hx => hBX (hPB ((Finset.mem_filter.mp (hJA hj)).2.1 x hx))
  refine ⟨?_, columnAnchorEval_freiman _ L (columnAnchorList j) ?_,
    columnAnchorEval_zero _ _ (fun x hx => (hcol x (hjX x hx)).2.2)⟩
  · have h := columnListSpectrum_card_le T (columnAnchorList j) (fun x hx => (hcol x (hjX x hx)).1)
    simpa only [columnAnchorList_length] using h
  · intro x hx
    apply ((hcol x (hjX x hx)).2.1).mono
    intro y hy
    exact (mem_columnListSpectrum_bohr T (columnAnchorList j) rho y).mp hy x hx

end LeanProofs.GowersSzemeredi
