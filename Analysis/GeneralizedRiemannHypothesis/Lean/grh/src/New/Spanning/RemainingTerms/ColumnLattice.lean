import New.Spanning.RemainingTerms.FrameCount

/-!
# The covolume of the lattice of columns

The tuples of vectors of the lattice `Λ ∩ X₀` of a class form a lattice in the product of the
complex places. The real inner product of two of its points is an integer, so its covolume is at
least `1`.

## Main definitions and results

* `New.Filling.columnLattice`, `New.Filling.exists_isAddFundamentalDomain_columnLattice`: the
  lattice of tuples of vectors of `Λ ∩ X₀` and its fundamental domain.

Notions from other files:

* `S : Filling E 𝔰`: the data of the filling theorem over the CM field `E` for the shape `𝔰`; the
  space `X₀` has a basis indexed by `𝔰.κ`, a set of `𝔰.k` elements.
* `c : S.Classes`: a class of the definite unitary group of `X₀`, with lattice `Λ`.
* `S.classCoordX₀ c`: the matrix that writes vectors of `X₀` in a basis of `Λ`; thus a vector lies
  in `Λ ∩ X₀` if its image under this matrix is integral.
* `Φ v`: the chosen complex embedding of `E` at the infinite place `v`.
* `Ô E`, `finAdeleMatrix q`: the integral finite adeles, and the matrix `q` over the finite adeles.

## Relation to the literature

See `New.Spanning.RemainingTerms.Sum` for related work.
-/

open MeasureTheory Matrix Module Fintype NumberField

namespace New.Filling

section Columns

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {ι : Type}

variable (E 𝔰 ι) in
/-- The point of the product of the complex places given by a matrix over `E` whose columns are
`ι` vectors of `X₀`: at the place `v`, the entry `q a l` goes to the conjugate of `Φ v (q a l)`. -/
def conjColumnsAtInfinity : Matrix 𝔰.κ ι E →+ (InfinitePlace E → ι → 𝔰.κ → ℂ) where
  toFun q v l a := star (Φ v (q a l))
  map_zero' := by simp [funext_iff]
  map_add' q q' := by simp [funext_iff]

@[simp]
lemma conjColumnsAtInfinity_apply (q : Matrix 𝔰.κ ι E) (v : InfinitePlace E) (l : ι) (a : 𝔰.κ) :
    conjColumnsAtInfinity E 𝔰 ι q v l a = star (Φ v (q a l)) :=
  rfl

lemma conjColumnsAtInfinity_injective : Function.Injective (conjColumnsAtInfinity E 𝔰 ι) := by
  intro q q' h_eq
  ext a l
  exact (Φ (Classical.arbitrary (InfinitePlace E))).injective
    (star_injective (congrFun₂ (congrFun h_eq _) l a))

/-- Let `Φ v` be the chosen complex embedding of `E` at the infinite place `v`. The map
`conjColumnsAtInfinity`, which sends a matrix `q` over `E` to the family of the complex conjugates
of its images `Φ v (q a l)`, indexed by the place `v`, the column `l` and the row `a`, has dense
range. -/
lemma denseRange_conjColumnsAtInfinity : DenseRange (conjColumnsAtInfinity E 𝔰 ι) := by
  -- `E` is dense in the product of the complex places; take one copy for each entry.
  let conjSwap (x : 𝔰.κ → ι → InfinitePlace E → ℂ) : InfinitePlace E → ι → 𝔰.κ → ℂ :=
    fun v l a ↦ star (x a l v)
  have h_surjective : Function.Surjective conjSwap :=
    fun y ↦ ⟨fun a l v ↦ star (y v l a), by simp [conjSwap]⟩
  have h_dense : DenseRange (Pi.map fun _ : 𝔰.κ ↦ Pi.map fun _ : ι ↦ RingHom.pi (Φ (E := E))) :=
    .piMap fun _ ↦ .piMap fun _ ↦ denseRange_Φ
  show DenseRange (conjSwap ∘ Pi.map fun _ : 𝔰.κ ↦ Pi.map fun _ : ι ↦ RingHom.pi (Φ (E := E)))
  exact h_surjective.denseRange.comp h_dense (by fun_prop)

variable (ι) in
/-- The tuples of vectors of `Λ ∩ X₀`, for the lattice `Λ` of the class `c`, as the columns of a
matrix. -/
def integralColumns (S : Filling E 𝔰) (c : S.Classes) : AddSubgroup (Matrix 𝔰.κ ι E) where
  carrier := {q : Matrix 𝔰.κ ι E | IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix q)}
  zero_mem' := by simp [IsIntMatrix]
  add_mem' hq hq' := by simpa [Matrix.map_add, Matrix.mul_add] using hq.add hq'
  neg_mem' hq := by simpa [Matrix.map_neg] using hq.neg

variable (ι) in
/-- The image of the tuples of vectors of `Λ ∩ X₀` in the product of the complex places. -/
def columnLattice (S : Filling E 𝔰) (c : S.Classes) :
    AddSubgroup (InfinitePlace E → ι → 𝔰.κ → ℂ) :=
  (S.integralColumns ι c).map (conjColumnsAtInfinity E 𝔰 ι)

/-- A point is in the lattice of columns if and only if it is the image under
`conjColumnsAtInfinity` of a matrix over `E` whose columns lie in the lattice of the class `c`. -/
lemma mem_columnLattice {S : Filling E 𝔰} {c : S.Classes} {x : InfinitePlace E → ι → 𝔰.κ → ℂ} :
    x ∈ S.columnLattice ι c ↔ ∃ q : Matrix 𝔰.κ ι E,
      IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix q) ∧ conjColumnsAtInfinity E 𝔰 ι q = x :=
  .rfl

variable [Fintype ι]

instance {S : Filling E 𝔰} {c : S.Classes} : Countable (S.columnLattice ι c) := by
  have : Countable (Matrix 𝔰.κ ι E) := inferInstanceAs (Countable (𝔰.κ → ι → E))
  exact ((Set.to_countable _).image _).to_subtype

omit [Fintype ι] in
/-- If `q` and `q'` are matrices whose columns lie in `Λ ∩ X₀`, for the lattice `Λ` of the class
`c`, then the hermitian products of their columns, the entries of `qᴴ * q'`, are algebraic
integers. Here `E` contains a primitive root of unity of order `5040`. -/
lemma isIntegral_conjTranspose_mul {S : Filling E 𝔰} {c : S.Classes} [HasPrimitiveRoot5040 E]
    {q q' : Matrix 𝔰.κ ι E} (hq : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix q))
    (hq' : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix q')) (l l' : ι) :
    IsIntegral ℤ ((qᴴ * q') l l') := by
  have h_gram : (S.classCoordX₀ c * finAdeleMatrix q)ᴴ * S.latticeMiddle (𝔸f E) *
      (S.classCoordX₀ c * finAdeleMatrix q') = finAdeleMatrix (qᴴ * q') := calc
    _ = (finAdeleMatrix q)ᴴ * ((S.classCoordX₀ c)ᴴ * S.latticeMiddle (𝔸f E) * S.classCoordX₀ c) *
        finAdeleMatrix q' := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = finAdeleMatrix (qᴴ * q') := by
      rw [gram_classCoordX₀, Matrix.mul_one, ← finAdeleMatrix_conjTranspose, ← Matrix.map_mul]
  have h_int : ((S.classCoordX₀ c * finAdeleMatrix q)ᴴ * S.latticeMiddle (𝔸f E) *
      (S.classCoordX₀ c * finAdeleMatrix q')) l l' ∈ Ô E :=
    (hq.conjTranspose.mul S.isUnimodular_latticeMiddle.isIntMatrix).mul hq' l l'
  rw [h_gram] at h_int
  exact algebraMap_mem_Ô.1 h_int

/-- A nonzero vector of `Λ ∩ X₀`, for the lattice `Λ` of the class `c`, has length at least `1` at
some place, so the lattice of columns is discrete. -/
instance {S : Filling E 𝔰} {c : S.Classes} [HasPrimitiveRoot5040 E] [S.IsAdmissible] :
    DiscreteTopology (S.columnLattice ι c) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  -- The tuples all of whose vectors are short at every place form a neighbourhood of zero.
  let U : Set (InfinitePlace E → ι → 𝔰.κ → ℂ) :=
    ⋂ (v : InfinitePlace E) (l : ι), {x | ∑ a : 𝔰.κ, ‖x v l a‖ ^ 2 < 1}
  have hU : IsOpen U := isOpen_iInter_of_finite fun v ↦ isOpen_iInter_of_finite fun l ↦
    isOpen_lt (by fun_prop) continuous_const
  suffices h_zero : ({0} : Set (S.columnLattice ι c)) = Subtype.val ⁻¹' U by
    rw [h_zero]
    exact hU.preimage continuous_subtype_val
  ext ⟨x, hx⟩
  obtain ⟨q, hq, rfl⟩ := mem_columnLattice.1 hx
  refine ⟨fun h_eq ↦ ?_, fun h_short ↦ Subtype.ext ?_⟩
  · have h_point : conjColumnsAtInfinity E 𝔰 ι q = 0 := congrArg Subtype.val h_eq
    change conjColumnsAtInfinity E 𝔰 ι q ∈ U
    rw [h_point]
    simp [U]
  · have h_col (l : ι) : q.col l = 0 := col_eq_zero_of_norm_lt_one hq fun v ↦ by
      simpa using Set.mem_iInter₂.1 h_short v l
    have hq_zero : q = 0 := ext fun a l ↦ congrFun (h_col l) a
    simp [hq_zero]

end Columns

/-- Let `S` be filling data of shape `𝔰` over the CM field `E`, let `c` be a class of the definite
unitary group of `X₀ = E ^ 𝔰.κ`, with lattice `Λ`, and let `ι` be a finite set. The subgroup
`S.columnLattice ι c` is the image of the `ι`-tuples of vectors of `Λ ∩ X₀`, under the conjugates
of the chosen complex embeddings of `E`, in the product over the infinite places of `E` of the
spaces of `ι`-tuples of vectors of `ℂ ^ 𝔰.κ`. It spans this product over `ℝ`. -/
lemma span_columnLattice {E : Type} [Field E] [CMType E] {𝔰 : Shape} {ι : Type} [Fintype ι]
    {S : Filling E 𝔰} {c : S.Classes} :
    Submodule.span ℝ (S.columnLattice ι c : Set (InfinitePlace E → ι → 𝔰.κ → ℂ)) = ⊤ := by
  -- Every tuple of vectors of `X₀` has a nonzero integer multiple in `Λ ∩ X₀`, so the span
  -- contains the image of all such tuples, which is dense.
  have h_range : Set.range (conjColumnsAtInfinity E 𝔰 ι) ⊆
      Submodule.span ℝ (S.columnLattice ι c : Set (InfinitePlace E → ι → 𝔰.κ → ℂ)) := by
    rintro _ ⟨q, rfl⟩
    -- A common denominator of the finitely many coordinates makes them all integral.
    obtain ⟨N, hN, h_mem⟩ : ∃ N : ℕ, N ≠ 0 ∧
        ∀ x ∈ Set.range (S.classCoordX₀ c * finAdeleMatrix q).uncurry, (N : 𝔸f E) • x ∈ Ô E :=
      exists_natCast_smul_mem_of_isCompact E (Set.finite_range _).isCompact
        (isOpen_Ô.mem_nhds (zero_mem _))
    have h_int : IsIntMatrix (Ô E) (S.classCoordX₀ c * finAdeleMatrix (N • q)) := fun a l ↦ by
      simpa [Function.uncurry, mul_apply, Finset.mul_sum, mul_left_comm] using
        h_mem _ ⟨(a, l), rfl⟩
    have h_point : conjColumnsAtInfinity E 𝔰 ι (N • q) ∈ S.columnLattice ι c :=
      mem_columnLattice.2 ⟨N • q, h_int, rfl⟩
    rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 hN : (N : ℝ) ≠ 0),
      Nat.cast_smul_eq_nsmul, ← map_nsmul]
    exact Submodule.subset_span h_point
  -- The span is closed and contains a dense set.
  have h_dense :
      Dense (Submodule.span ℝ (S.columnLattice ι c : Set (InfinitePlace E → ι → 𝔰.κ → ℂ)) :
        Set (InfinitePlace E → ι → 𝔰.κ → ℂ)) :=
    denseRange_conjColumnsAtInfinity.mono h_range
  rw [← Submodule.dense_iff_topologicalClosure_eq_top.1 h_dense,
    (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq]

/-- Let the CM field `E` contain a primitive root of unity of order `5040`, hence a square root of
`-1`. For an algebraic integer `x` of `E`, the sum over the infinite places `v` of the real parts of
the images `Φ v x` under the chosen embeddings, which is half the trace of `x`, is an integer. -/
lemma exists_int_eq_sum_re {E : Type} [Field E] [CMType E] [HasPrimitiveRoot5040 E] {x : E}
    (hx : IsIntegral ℤ x) :
    ∃ n : ℤ, ∑ v : InfinitePlace E, (Φ v x).re = n := by
  -- Let `i² = -1` in `E`, and let `t v` be the image of `x` under the embedding at `v` that sends
  -- `i` to `I`. The sum of the `t v` is an algebraic integer equal to `(p - q I) / 2`, for the
  -- traces `p` of `x` and `q` of `i x`. So its squared absolute value `(p² + q²) / 4` is an
  -- integer, and `p` is even.
  classical
  obtain ⟨i, hi, -⟩ : ∃ i : 𝓞 E, i * i = -1 ∧ star i = -i :=
    HasPrimitiveRoot5040.exists_mul_self_eq_neg_one
  have h_trace {y : E} (hy : IsIntegral ℤ y) :
      ∃ n : ℤ, ∑ v : InfinitePlace E, 2 * (Φ v y).re = n := by
    obtain ⟨n, hn⟩ : ∃ n : ℤ, algebraMap ℤ ℚ n = Algebra.trace ℚ E y :=
      IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_trace hy)
    exact ⟨n, by rw [← trace_eq_sum_Φ, ← hn, eq_intCast, Rat.cast_intCast]⟩
  obtain ⟨p, hp⟩ : ∃ p : ℤ, ∑ v : InfinitePlace E, 2 * (Φ v x).re = p := h_trace hx
  obtain ⟨q, hq⟩ : ∃ q : ℤ, ∑ v : InfinitePlace E, 2 * (Φ v (i * x)).re = q :=
    h_trace (i.2.mul hx)
  let t (v : InfinitePlace E) : ℂ := if Φ v i = Complex.I then Φ v x else star (Φ v x)
  have h_term (v : InfinitePlace E) : t v = (Φ v x).re - (Φ v (i * x)).re * Complex.I := by
    have h_sq : Φ v i ^ 2 = Complex.I ^ 2 := by
      simpa [sq] using congrArg (fun y : 𝓞 E ↦ Φ v y) hi
    obtain h_eq_I | h_eq_neg_I : Φ v i = Complex.I ∨ Φ v i = -Complex.I :=
      sq_eq_sq_iff_eq_or_eq_neg.1 h_sq
    · simp [t, h_eq_I, Complex.ext_iff]
    · simp [t, h_eq_neg_I, Complex.ext_iff, neg_eq_self]
  have h_int : IsIntegral ℤ (∑ v : InfinitePlace E, t v) := .sum _ fun v _ ↦ by
    unfold t
    split_ifs
    exacts [map_isIntegral_int _ hx, map_isIntegral_int (starRingEnd ℂ) (map_isIntegral_int _ hx)]
  have h_sum : ∑ v : InfinitePlace E, t v = ((p : ℝ) - (q : ℝ) * Complex.I) / 2 := by
    simp only [h_term, ← hp, ← hq, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    push_cast
    ring
  have h_norm : IsIntegral ℤ (algebraMap ℚ ℂ ((p ^ 2 + q ^ 2) / 4)) := by
    have h_eq : algebraMap ℚ ℂ ((p ^ 2 + q ^ 2) / 4) =
        (∑ v : InfinitePlace E, t v) * starRingEnd ℂ (∑ v : InfinitePlace E, t v) := by
      rw [h_sum, Complex.mul_conj, Complex.normSq_div]
      simp [Complex.normSq_apply, sq]
      norm_num
    rw [h_eq]
    exact h_int.mul (map_isIntegral_int (starRingEnd ℂ) h_int)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, algebraMap ℤ ℚ m = (p ^ 2 + q ^ 2) / 4 :=
    IsIntegrallyClosed.isIntegral_iff.1 h_norm.tower_bot_of_field
  have h_four : 4 * m = p ^ 2 + q ^ 2 := by
    rw [eq_intCast, eq_div_iff four_ne_zero, mul_comm] at hm
    exact_mod_cast hm
  obtain ⟨n, rfl⟩ : Even p := by
    obtain ⟨a, rfl | rfl⟩ := Int.even_or_odd' p
    · exact even_two_mul a
    · obtain ⟨b, rfl | rfl⟩ := Int.even_or_odd' q <;> lia
  rw [← Finset.mul_sum] at hp
  push_cast at hp
  exact ⟨n, by linarith⟩

/-- Let `E` be a CM field that contains a primitive root of unity of order `5040`. Let `S` be
admissible filling data over `E`: the level in `U(X₀)`, for `X₀ = E ^ 𝔰.κ`, is the preimage of the
principal congruence subgroup of level `S.M`, reduction at the chosen places is onto, and size
bounds in terms of `S.b` hold. The subgroup `S.columnLattice ι c` is the image of the `ι`-tuples of
vectors of `Λ ∩ X₀` under the conjugates of the chosen complex embeddings, one for each infinite
place. It has a measurable fundamental domain whose Lebesgue measure is finite and at least `1`. -/
theorem exists_isAddFundamentalDomain_columnLattice {E : Type} [Field E] [CMType E] {𝔰 : Shape}
    (ι : Type) [Fintype ι] (S : Filling E 𝔰) (c : S.Classes)
    [HasPrimitiveRoot5040 E] [S.IsAdmissible] :
    ∃ D : Set (InfinitePlace E → ι → 𝔰.κ → ℂ),
      MeasurableSet D ∧
      IsAddFundamentalDomain (S.columnLattice ι c) D volume ∧
      1 ≤ volume D ∧
      volume D ≠ ⊤ := by
  -- In the coordinates of the standard real basis `e`, the euclidean product of two lattice points
  -- is half the trace of an algebraic integer of `E`, hence an integer.
  let L : Submodule ℤ (InfinitePlace E → ι → 𝔰.κ → ℂ) := (S.columnLattice ι c).toIntSubmodule
  have : DiscreteTopology L := inferInstanceAs (DiscreteTopology (S.columnLattice ι c))
  have : IsZLattice ℝ L := ⟨span_columnLattice⟩
  let e : Basis (Σ _ : InfinitePlace E, Σ _ : ι, Σ _ : 𝔰.κ, Fin 2) ℝ
      (InfinitePlace E → ι → 𝔰.κ → ℂ) :=
    Pi.basis fun _ ↦ Pi.basis fun _ ↦ Pi.basis fun _ ↦ Complex.basisOneI
  have h_volume : volume (ZSpan.fundamentalDomain e) = 1 :=
    volume_fundamentalDomain_pi_basis _ fun _ ↦ volume_fundamentalDomain_pi_basis _ fun _ ↦
      volume_fundamentalDomain_pi_basis _ fun _ ↦ volume_fundamentalDomain_basisOneI
  refine exists_isAddFundamentalDomain_of_integral volume e h_volume L ?_
  intro x hx y hy
  obtain ⟨q, hq, rfl⟩ := mem_columnLattice.1 hx
  obtain ⟨q', hq', rfl⟩ := mem_columnLattice.1 hy
  have h_int : IsIntegral ℤ (∑ l : ι, (qᴴ * q') l l) :=
    .sum _ fun l _ ↦ isIntegral_conjTranspose_mul hq hq' l l
  obtain ⟨n, hn⟩ : ∃ n : ℤ, ∑ v : InfinitePlace E, (Φ v (∑ l : ι, (qᴴ * q') l l)).re = n :=
    exists_int_eq_sum_re h_int
  refine ⟨n, .trans ?_ hn⟩
  simp [e, Fintype.sum_sigma, mul_apply, Finset.sum_add_distrib]

end New.Filling
