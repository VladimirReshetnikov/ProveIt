import GowersSzemeredi.Proofs16SparseTupleSampling

/-! The direct global column construction supplies Claim 6.3's sample.
Its retained density and modulus threshold do not depend on the allowed
exceptional fraction. Original witnesses and individual tuple classes
are retained for the subsequent character-selection step. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def globalColumnTupleBaseDensity (alpha : Real) : Real :=
  absBsgEps (globalColumnQuadrupleDensity alpha) 1

def globalColumnTupleSampleRadius (alpha : Real) (k r : Nat) : Real :=
  globalColumnTupleClassRadius alpha k/(100*r)

def globalColumnTupleSampleCells (alpha : Real) (k r : Nat) : Nat :=
  refinementCells (globalColumnTupleSampleRadius alpha k r)

def globalColumnTupleSampleDomainDensity (alpha : Real) (k r : Nat) : Real :=
  1/(globalColumnTupleSampleCells alpha k r : Real)^(columnSpectrumCap (columnEightDensity alpha))

def globalColumnTupleSampleDensity (alpha : Real) (k r : Nat) : Real :=
  globalColumnTupleBaseDensity alpha*(globalColumnTupleSampleDomainDensity alpha k r)^r/2

def globalColumnSparseKernelDensity (alpha : Real) (k r : Nat) (epsilon : Real) : Real :=
  epsilon*globalColumnTupleBaseDensity alpha*(globalColumnTupleSampleDomainDensity alpha k r)^r/
    (8*(3 : Real)^r)

def globalColumnTupleSampleModulusBound (alpha : Real) (k r : Nat) : Nat :=
  max 7 (max (globalColumnTupleClassModulusBound alpha k)
    (⌈8*(3 : Real)^r/(globalColumnTupleBaseDensity alpha*
      (globalColumnTupleSampleDomainDensity alpha k r)^r)⌉₊))

theorem globalColumnTupleBaseDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    0 < globalColumnTupleBaseDensity alpha := by
  have hgamma := globalColumnQuadrupleDensity_pos ha ha1
  unfold globalColumnTupleBaseDensity absBsgEps absBsgDelta2 absBsgDelta
  positivity

theorem globalColumnTupleSampleRadius_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (k : Nat) {r : Nat} (hr : 0 < r) : 0 < globalColumnTupleSampleRadius alpha k r := by
  have ht := globalColumnTupleClassRadius_pos ha ha1 k
  unfold globalColumnTupleSampleRadius
  positivity

theorem globalColumnTupleSampleCells_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (k : Nat) {r : Nat} (hr : 0 < r) : 0 < globalColumnTupleSampleCells alpha k r :=
  Nat.ceil_pos.mpr (by have ht := globalColumnTupleSampleRadius_pos ha ha1 k hr; positivity)

theorem globalColumnTupleSampleDomainDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (k : Nat) {r : Nat} (hr : 0 < r) : 0 < globalColumnTupleSampleDomainDensity alpha k r := by
  have hq : (0 : Real) < globalColumnTupleSampleCells alpha k r := by
    exact_mod_cast globalColumnTupleSampleCells_pos ha ha1 k hr
  unfold globalColumnTupleSampleDomainDensity
  positivity

theorem globalColumnTupleSampleDensity_pos {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (k : Nat) {r : Nat} (hr : 0 < r) : 0 < globalColumnTupleSampleDensity alpha k r := by
  have hb := globalColumnTupleBaseDensity_pos ha ha1
  have hbeta := globalColumnTupleSampleDomainDensity_pos ha ha1 k hr
  unfold globalColumnTupleSampleDensity
  positivity

theorem globalColumnSparseKernelDensity_pos {alpha epsilon : Real}
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon)
    (k : Nat) {r : Nat} (hr : 0 < r) : 0 < globalColumnSparseKernelDensity alpha k r epsilon := by
  have hb := globalColumnTupleBaseDensity_pos ha ha1
  have hbeta := globalColumnTupleSampleDomainDensity_pos ha ha1 k hr
  unfold globalColumnSparseKernelDensity
  positivity

/-- A sample for the original dense bihomomorphism, with few sparse-kernel
exceptions on all original additive tuples and the original class data. -/
theorem global_column_tuple_sample_system {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha epsilon : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1) (he : 0 < epsilon)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (k r : Nat) (hr : 0 < r) (hN : globalColumnTupleSampleModulusBound alpha k r ≤ N) :
    let d := columnSpectrumCap (columnEightDensity alpha)
    let delta := globalColumnTupleRepresentationDensity alpha k
    let s := globalColumnTupleRepresentativeRadius alpha k
    let t := globalColumnTupleClassRadius alpha k
    let tau := globalColumnTupleSampleRadius alpha k r
    let eta := globalColumnSparseKernelDensity alpha k r epsilon
    ∃ (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N))
      (B P V : Finset (ZMod N)) (e : Fin r → ZMod N),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      (∀ x ∈ X, (T x).card ≤ d ∧
        IsFreimanLinearOn (bohr (T x) (1/(4*Real.pi))) (L x) ∧ L x 0 = 0) ∧
      P ⊆ B ∧ B ⊆ X ∧ globalColumnTupleBaseDensity alpha*N ≤ (P.card : Real) ∧
      V ⊆ P ∧ globalColumnTupleSampleDensity alpha k r*N ≤ (V.card : Real) ∧
      (∀ x ∈ V, ∀ i, e i ∈ bohr (T x) tau) ∧
      Function.Injective (booleanSampleValue e) ∧
      (Finset.univ.image (booleanSampleValue e)).card = 2^r ∧
      ((sampleBadIndices (sparseColumnTuples (k := k) P T L t eta)
        (columnTupleZeroLevel T L t) e).card : Real) ≤ epsilon*(N : Real)^k/2 ∧
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
  have hNclasses : globalColumnTupleClassModulusBound alpha k ≤ N :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNsample : ⌈8*(3 : Real)^r/(globalColumnTupleBaseDensity alpha*
      (globalColumnTupleSampleDomainDensity alpha k r)^r)⌉₊ ≤ N :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  obtain ⟨X, T, L, W, B, P, hsys, hW, hcol, hPB, hBX, hP, hd, hs, ht, hwords, hclasses⟩ :=
    global_column_tuple_classes A phi ha ha1 hA hphi k hNclasses
  let q := globalColumnTupleSampleCells alpha k r
  let tau := globalColumnTupleSampleRadius alpha k r
  let b := globalColumnTupleBaseDensity alpha
  let beta := globalColumnTupleSampleDomainDensity alpha k r
  let eta := globalColumnSparseKernelDensity alpha k r epsilon
  have hq : 0 < q := globalColumnTupleSampleCells_pos ha ha1 k hr
  letI : NeZero q := ⟨ne_of_gt hq⟩
  have htau : 0 < tau := globalColumnTupleSampleRadius_pos ha ha1 k hr
  have hqdomain : 1 ≤ tau*q := by
    have hceil : 1/tau ≤ (q : Real) := Nat.le_ceil _
    exact (by simpa only [mul_comm] using (div_le_iff₀ htau).mp hceil)
  have hb : 0 < b := globalColumnTupleBaseDensity_pos ha ha1
  have hbeta : 0 < beta := globalColumnTupleSampleDomainDensity_pos ha ha1 k hr
  have heta : 0 < eta := globalColumnSparseKernelDensity_pos ha ha1 he k hr
  have hbadBudget : 8*(3 : Real)^r*eta ≤ epsilon*b*beta^r := by
    dsimp only [eta, globalColumnSparseKernelDensity, b, beta]
    have hden : (0 : Real) < 8*(3 : Real)^r := by positivity
    field_simp
    exact le_rfl
  have hcollisionBudget : 8*(3 : Real)^r ≤ b*beta^r*N := by
    have hceil : 8*(3 : Real)^r/(b*beta^r) ≤ (N : Real) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hNsample)
    have hraw := (div_le_iff₀ (mul_pos hb (pow_pos hbeta r))).mp hceil
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hraw
  obtain ⟨e, hinj, hcube, hretained, hbad⟩ := sparse_tuple_bohr_sample_selection
    (d := columnSpectrumCap (columnEightDensity alpha)) (q := q) (k := k) hr P T L
    (globalColumnTupleClassRadius alpha k) hqdomain
    (fun x hx => (hcol x (hBX (hPB hx))).1) hb heta.le he hP hbadBudget hcollisionBudget
  let V := retainedSampleIndices P (fun x => bohr (T x) tau) e
  refine ⟨X, T, L, W, B, P, V, e, hsys, hW, hcol, hPB, hBX, hP,
    Finset.filter_subset _ _, ?_, ?_, hinj, hcube, hbad, hclasses⟩
  · simpa only [globalColumnTupleSampleDensity, globalColumnTupleSampleDomainDensity, b, q, V, div_mul_eq_mul_div] using hretained
  · intro x hx
    exact (Finset.mem_filter.mp hx).2

end LeanProofs.GowersSzemeredi
