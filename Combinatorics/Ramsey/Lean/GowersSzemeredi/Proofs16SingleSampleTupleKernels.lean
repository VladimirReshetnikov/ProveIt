import GowersSzemeredi.Proofs16SparseTupleSampling

/-! One nonzero sample point suffices for the exact-class argument.
A tuple map vanishing there belongs to the already counted sparse-kernel
bad family whenever its zero level is sparse. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem single_boolean_sample_ne_zero {N : Nat} [NeZero N]
    (e : Fin 1 → ZMod N) (he : Function.Injective (booleanSampleValue e)) : e 0 ≠ 0 := by
  intro hz
  have hf : (fun _ : Fin 1 => true) = (fun _ : Fin 1 => false) := he (by
    simp [booleanSampleValue, hz])
  have h := congrFun hf 0
  simp at h

theorem single_sample_unit_coefficient_mem {N : Nat} [NeZero N] [Fact N.Prime] :
    (fun _ : Fin 1 => (1 : ZMod N)) ∈ nonzeroTernaryCoefficients N 1 := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(fun _ : Fin 1 => (1 : Fin 3)), Finset.mem_univ _, ?_⟩, ?_⟩
  · funext i
    norm_num [ternarySampleCoefficient]
  · intro h
    exact one_ne_zero (congrFun h 0)

theorem column_tuple_zero_at_single_sample_is_bad {N k : Nat} [NeZero N] [Fact N.Prime]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (t eta : Real) (e : Fin 1 → ZMod N)
    {a : ColumnAnchorTuple N k} (ha : a ∈ sparseColumnTuples P T L t eta)
    (hy : ∀ x ∈ columnAnchorList a, e 0 ∈ bohr (T x) t)
    (hzero : columnAnchorEval (fun x => L x (e 0)) (columnAnchorList a) = 0) :
    a ∈ sampleBadIndices (sparseColumnTuples P T L t eta) (columnTupleZeroLevel T L t) e := by
  have hlevel : e 0 ∈ columnTupleZeroLevel T L t a :=
    Finset.mem_filter.mpr ⟨(mem_columnListSpectrum_bohr T _ t (e 0)).mpr hy, hzero⟩
  refine Finset.mem_filter.mpr ⟨ha, (fun _ : Fin 1 => (1 : ZMod N)),
    single_sample_unit_coefficient_mem, ?_⟩
  simpa [linearSampleValue] using hlevel

/-- A dense tuple zero level bounds its image on the half-radius domain
by one common rank budget. The bound is independent of the modulus. -/
theorem column_tuple_image_card_le_of_dense_zero {N d k : Nat} [NeZero N]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho t eta : Real}
    (hrho : 0 < rho) (ht : t ≤ rho) (heta : 0 < eta)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (a : ColumnAnchorTuple N k) (ha : ∀ x ∈ columnAnchorList a, x ∈ X)
    (hlevel : eta*N ≤ ((columnTupleZeroLevel T L t a).card : Real)) :
    (((bohr (columnListSpectrum T (columnAnchorList a)) (rho/2)).image
      (fun y => columnAnchorEval (fun x => L x y) (columnAnchorList a))).card : Real) ≤
      (denseLevelCells rho : Real)^((k+1)*d)/eta := by
  let S := columnListSpectrum T (columnAnchorList a)
  let f := fun y => columnAnchorEval (fun x => L x y) (columnAnchorList a)
  have hM : 0 < denseLevelCells rho := Nat.ceil_pos.mpr (by positivity)
  letI : NeZero (denseLevelCells rho) := ⟨ne_of_gt hM⟩
  have hcell : 1 ≤ (rho/4)*denseLevelCells rho := by
    have h : 4/rho ≤ (denseLevelCells rho : Real) := Nat.le_ceil (4/rho)
    rw [div_le_iff₀ hrho] at h
    nlinarith
  have hf : IsFreimanLinearOn (bohr S rho) f := by
    apply columnAnchorEval_freiman
    intro x hx
    apply (hL x (ha x hx)).mono
    intro y hy
    exact (mem_columnListSpectrum_bohr T _ rho y).mp hy x hx
  have hZ : columnTupleZeroLevel T L t a ⊆ bohr S rho := by
    intro y hy
    exact bohr_mono_radius _ ht (Finset.mem_filter.mp hy).1
  have hzero : ∀ y ∈ columnTupleZeroLevel T L t a, f y = 0 :=
    fun _ hy => (Finset.mem_filter.mp hy).2
  have hbound := freiman_image_card_le_of_dense_level S hrho.le heta f hf
    (columnTupleZeroLevel T L t a) hZ hzero hlevel hcell
  have hS : S.card ≤ (k+1)*d := by
    have h := columnListSpectrum_card_le T (columnAnchorList a) (fun x hx => hT x (ha x hx))
    simpa only [columnAnchorList_length] using h
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ heta.le
  exact pow_le_pow_right₀ (by exact_mod_cast hM) hS

end LeanProofs.GowersSzemeredi
