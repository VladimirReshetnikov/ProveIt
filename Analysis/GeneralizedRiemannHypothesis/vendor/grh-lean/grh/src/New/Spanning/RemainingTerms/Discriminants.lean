import Lib.SiegelWeil.Mass
import New.Spanning.RemainingTerms.SiegelLemma

/-!
# Discriminants of lattices and sums over sublattices

Lattices of rational subspaces of a space with the standard hermitian form, written over `Ô`;
their discriminants; and a bound for the sum of a negative power of the index over all sublattices
of finite index.

The bound for the sum over sublattices is a consequence of Hey's formula for the zeta function of a
lattice. Here it is proved directly, by induction on the rank, over any
commutative ring whose ideals of finite index are principal.

The formula that compares the discriminant of `L ∩ W` with that of the dual lattice in `W^⊥` is
`New.Filling.jacobi_perp_discriminant`, stated for Gram determinants.
-/

noncomputable section

namespace New.Filling

open NumberField Matrix Module ENNReal

section SubmoduleZeta

variable {R N N' : Type*} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

variable (R N) in
/-- The sum of `[N : M] ^ (-s)` over the submodules `M` of finite index in `N`. -/
def submoduleZeta (s : ℕ) : ℝ≥0∞ :=
  ∑' M : {M : Submodule R N // M.cardQuot ≠ 0}, (M.1.cardQuot : ℝ≥0∞)⁻¹ ^ s

/-- The index of the preimage of `M` under `f` is the index of `M ⊓ range f` in the range of `f`. -/
lemma cardQuot_comap (f : N →ₗ[R] N') (M : Submodule R N') :
    (M.comap f).cardQuot = M.toAddSubgroup.relIndex (LinearMap.range f).toAddSubgroup :=
  M.toAddSubgroup.index_comap f.toAddMonoidHom

/-- Pulling back along a surjective linear map keeps the index. -/
lemma cardQuot_comap_of_surjective {f : N →ₗ[R] N'} (hf : Function.Surjective f)
    (M : Submodule R N') : (M.comap f).cardQuot = M.cardQuot :=
  M.toAddSubgroup.index_comap_of_surjective (f := f.toAddMonoidHom) hf

lemma submoduleZeta_anti {s t : ℕ} (hst : s ≤ t) : submoduleZeta R N t ≤ submoduleZeta R N s := by
  refine ENNReal.tsum_le_tsum fun M ↦ pow_le_pow_of_le_one zero_le ?_ hst
  exact ENNReal.inv_le_one.2 (Nat.one_le_cast.2 (Nat.pos_of_ne_zero M.2))

/-- The sum of `[range f : M] ^ (-s)` over the submodules `M` of finite index in the range of a
linear map `f` is at most the same sum over the submodules of finite index in its domain. -/
lemma tsum_relIndex_range_le_submoduleZeta (f : N →ₗ[R] N') (s : ℕ) :
    ∑' M : {M : Submodule R N' // M ≤ LinearMap.range f ∧
        M.toAddSubgroup.relIndex (LinearMap.range f).toAddSubgroup ≠ 0},
      (M.1.toAddSubgroup.relIndex (LinearMap.range f).toAddSubgroup : ℝ≥0∞)⁻¹ ^ s ≤
      submoduleZeta R N s := by
  let pull (M : {M : Submodule R N' // M ≤ LinearMap.range f ∧
      M.toAddSubgroup.relIndex (LinearMap.range f).toAddSubgroup ≠ 0}) :
      {M : Submodule R N // M.cardQuot ≠ 0} :=
    ⟨M.1.comap f, (cardQuot_comap f M.1).trans_ne M.2.2⟩
  have h_inj : Function.Injective pull := by
    rintro ⟨M₁, h₁_le, _⟩ ⟨M₂, h₂_le, _⟩ h_eq
    have h_comap : M₁.comap f = M₂.comap f := congrArg Subtype.val h_eq
    simpa [Submodule.map_comap_eq_self, h₁_le, h₂_le] using congrArg (Submodule.map f) h_comap
  calc _ = ∑' M, ((pull M).1.cardQuot : ℝ≥0∞)⁻¹ ^ s :=
        tsum_congr fun M ↦ by simp only [pull, cardQuot_comap]
    _ ≤ submoduleZeta R N s := tsum_comp_le_tsum_of_injective h_inj fun M ↦
      (M.1.cardQuot : ℝ≥0∞)⁻¹ ^ s

/-- If `N` maps onto `N'`, then the sum of `[N' : M] ^ (-s)` over the submodules `M` of finite
index in `N'` is at most the same sum for `N`. -/
lemma submoduleZeta_le_of_surjective {f : N →ₗ[R] N'} (hf : Function.Surjective f) (s : ℕ) :
    submoduleZeta R N' s ≤ submoduleZeta R N s := by
  let pull (M : {M : Submodule R N' // M.cardQuot ≠ 0}) : {M : Submodule R N // M.cardQuot ≠ 0} :=
    ⟨M.1.comap f, (cardQuot_comap_of_surjective hf M.1).trans_ne M.2⟩
  have h_inj : Function.Injective pull := fun M₁ M₂ h_eq ↦
    Subtype.ext (Submodule.comap_injective_of_surjective hf (congrArg Subtype.val h_eq))
  calc _ = ∑' M, ((pull M).1.cardQuot : ℝ≥0∞)⁻¹ ^ s :=
        tsum_congr fun M ↦ by simp only [pull, cardQuot_comap_of_surjective hf]
    _ ≤ submoduleZeta R N s :=
      tsum_comp_le_tsum_of_injective h_inj fun M ↦ (M.1.cardQuot : ℝ≥0∞)⁻¹ ^ s

/-- The index of a submodule of a product is the index of its projection to the first factor times
the index of its intersection with the second factor. -/
lemma cardQuot_eq_cardQuot_map_fst_mul_comap_inr (M : Submodule R (N × N')) :
    M.cardQuot = (M.map (.fst R N N')).cardQuot * (M.comap (.inr R N N')).cardQuot := by
  let K : Submodule R (N × N') := LinearMap.range (.inr R N N')
  have h_sup : (M.map (.fst R N N')).comap (.fst R N N') = M ⊔ K := by
    rw [Submodule.comap_map_eq, LinearMap.ker_fst]
  have h_fst : (M ⊔ K).cardQuot = (M.map (.fst R N N')).cardQuot := by
    rw [← h_sup, cardQuot_comap_of_surjective LinearMap.fst_surjective]
  have h_snd : M.toAddSubgroup.relIndex (M ⊔ K).toAddSubgroup =
      (M.comap (.inr R N N')).cardQuot := by
    rw [cardQuot_comap, Submodule.sup_toAddSubgroup, sup_comm, AddSubgroup.relIndex_sup_right]
  rw [← h_fst, ← h_snd, mul_comm]
  exact (AddSubgroup.relIndex_mul_index (Submodule.toAddSubgroup_mono le_sup_left)).symm

/-- Let `M` be a submodule of `R × N` whose first coordinates are the multiples of `g`, and let
`(g, n) ∈ M`. Then `M` is spanned by `(g, n)` and its intersection with `N`. -/
lemma eq_span_sup_of_map_fst_eq_span {M : Submodule R (R × N)} {g : R} {n : N} (hn : (g, n) ∈ M)
    (hg : M.map (.fst R R N) = R ∙ g) :
    M = R ∙ (g, n) ⊔ (M.comap (.inr R R N)).map (.inr R R N) := by
  refine le_antisymm ?_
    (sup_le ((Submodule.span_singleton_le_iff_mem _ _).2 hn) (Submodule.map_comap_le _ _))
  rintro ⟨a, x⟩ hax
  obtain ⟨c, rfl⟩ : ∃ c : R, c • g = a :=
    Submodule.mem_span_singleton.1 (hg.le (Submodule.mem_map_of_mem hax))
  have h_rest : ((0 : R), x - c • n) ∈ M := by simpa using M.sub_mem hax (M.smul_mem c hn)
  refine Submodule.mem_sup.2 ⟨c • (g, n), Submodule.mem_span_singleton.2 ⟨c, rfl⟩,
    (0, x - c • n), Submodule.mem_map_of_mem (f := .inr R R N) h_rest, ?_⟩
  simp

/-- For a submodule `M` of finite index in `N`, the sum of `[N : M] ^ (-(s + 1))` over the classes
modulo `M` is `[N : M] ^ (-s)`. -/
lemma tsum_quotient_cardQuot_inv_pow {M : Submodule R N} (hM : M.cardQuot ≠ 0) (s : ℕ) :
    ∑' _ : N ⧸ M, (M.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1) = (M.cardQuot : ℝ≥0∞)⁻¹ ^ s := by
  have : Finite (N ⧸ M) := Nat.finite_of_card_ne_zero hM
  have h_card : (ENat.card (N ⧸ M) : ℝ≥0∞) = M.cardQuot := by
    rw [ENat.card_eq_coe_natCard, Submodule.cardQuot_apply, ENat.toENNReal_coe]
  rw [ENNReal.tsum_const, h_card, pow_succ', ← mul_assoc,
    ENNReal.mul_inv_cancel (Nat.cast_ne_zero.2 hM) (natCast_ne_top _), one_mul]

/-- Write `ζ_X(s) = submoduleZeta R X s` for the sum of `[X : M] ^ (-s)` over the submodules `M` of
finite index in an `R`-module `X`. If the ideals of finite index of `R` are principal, then
`ζ_{R × N}(s + 1) ≤ ζ_R(s + 1) * ζ_N(s)`. -/
lemma submoduleZeta_prod_le (h_principal : ∀ I : Ideal R, I.cardQuot ≠ 0 → I.IsPrincipal) (s : ℕ) :
    submoduleZeta R (R × N) (s + 1) ≤ submoduleZeta R R (s + 1) * submoduleZeta R N s := by
  -- A submodule `M` is determined by the ideal `I = (g)` of its first coordinates, by its
  -- intersection `M'` with `N`, and by the class modulo `M'` of some `n` with `(g, n) ∈ M`.
  -- There are `[N : M']` classes, and `[R × N : M] = [R : I] [N : M']`.
  have h_generator (I : {I : Submodule R R // I.cardQuot ≠ 0}) : ∃ g : R, I.1 = R ∙ g :=
    (h_principal I.1 I.2).principal
  choose gen h_gen using h_generator
  let Data : Type _ := Σ (_ : {I : Submodule R R // I.cardQuot ≠ 0})
    (M' : {M' : Submodule R N // M'.cardQuot ≠ 0}), N ⧸ M'.1
  let build : Data → Submodule R (R × N) := fun ⟨I, M', c⟩ ↦
    R ∙ (gen I, c.out) ⊔ M'.1.map (.inr R R N)
  let weight : Data → ℝ≥0∞ := fun ⟨I, M', _⟩ ↦
    (I.1.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1) * (M'.1.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1)
  have h_data (M : {M : Submodule R (R × N) // M.cardQuot ≠ 0}) :
      ∃ d : Data, build d = M.1 ∧ weight d = (M.1.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1) := by
    have h_index : M.1.cardQuot =
        (M.1.map (.fst R R N)).cardQuot * (M.1.comap (.inr R R N)).cardQuot :=
      cardQuot_eq_cardQuot_map_fst_mul_comap_inr M.1
    obtain ⟨hI, hM'⟩ := mul_ne_zero_iff.1 (h_index.symm.trans_ne M.2)
    let I : {I : Submodule R R // I.cardQuot ≠ 0} := ⟨M.1.map (.fst R R N), hI⟩
    obtain ⟨⟨g, n⟩, hn, hg⟩ : gen I ∈ M.1.map (.fst R R N) :=
      (h_gen I).ge (Submodule.mem_span_singleton_self _)
    let M' : {M' : Submodule R N // M'.cardQuot ≠ 0} := ⟨M.1.comap (.inr R R N), hM'⟩
    let c : N ⧸ M'.1 := Submodule.Quotient.mk n
    have h_congr : c.out - n ∈ M'.1 := (Submodule.Quotient.eq _).1 c.out_eq
    have h_mem : (gen I, c.out) ∈ M.1 := by simpa [← hg] using M.1.add_mem hn h_congr
    have h_span : M.1 = build ⟨I, M', c⟩ := eq_span_sup_of_map_fst_eq_span h_mem (h_gen I)
    refine ⟨⟨I, M', c⟩, h_span.symm, ?_⟩
    rw [h_index, Nat.cast_mul, ENNReal.mul_inv (.inr (natCast_ne_top _)) (.inl (natCast_ne_top _)),
      mul_pow]
  choose data h_build h_weight using h_data
  have h_inj : Function.Injective data := fun M₁ M₂ h_eq ↦
    Subtype.ext (by rw [← h_build, h_eq, h_build])
  -- Summing over the classes modulo `M'` lowers the exponent of `[N : M']` by one.
  have h_classes (M' : {M' : Submodule R N // M'.cardQuot ≠ 0}) :
      ∑' _ : N ⧸ M'.1, (M'.1.cardQuot : ℝ≥0∞)⁻¹ ^ (s + 1) = (M'.1.cardQuot : ℝ≥0∞)⁻¹ ^ s :=
    tsum_quotient_cardQuot_inv_pow M'.2 s
  calc submoduleZeta R (R × N) (s + 1)
    _ = ∑' M, weight (data M) := tsum_congr fun M ↦ (h_weight M).symm
    _ ≤ ∑' d, weight d := tsum_comp_le_tsum_of_injective h_inj weight
    _ = submoduleZeta R R (s + 1) * submoduleZeta R N s := by
      simp only [Data, weight, ENNReal.tsum_sigma', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right,
        submoduleZeta, h_classes]

/-- If the ideals of finite index of `R` are principal, then the sum of `[R ^ r : M] ^ (-(r + μ))`
over the submodules `M` of finite index is at most the `r`th power of the sum of `[R : I] ^ (-μ)`
over the ideals `I` of finite index. -/
lemma submoduleZeta_pi_le (h_principal : ∀ I : Ideal R, I.cardQuot ≠ 0 → I.IsPrincipal)
    (r μ : ℕ) : submoduleZeta R (Fin r → R) (r + μ) ≤ submoduleZeta R R μ ^ r := by
  induction r with
  | zero =>
    let top : {M : Submodule R (Fin 0 → R) // M.cardQuot ≠ 0} := ⟨⊤, by simp⟩
    rw [submoduleZeta,
      tsum_eq_single top fun M hM ↦ absurd (Subtype.ext (Subsingleton.elim M.1 top.1)) hM]
    simp [top]
  | succ r ih =>
    calc submoduleZeta R (Fin (r + 1) → R) (r + 1 + μ)
      _ ≤ submoduleZeta R (R × (Fin r → R)) (r + μ + 1) := by
        rw [add_right_comm]
        exact submoduleZeta_le_of_surjective (Fin.consLinearEquiv R fun _ ↦ R).surjective _
      _ ≤ submoduleZeta R R (r + μ + 1) * submoduleZeta R (Fin r → R) (r + μ) :=
        submoduleZeta_prod_le h_principal _
      _ ≤ submoduleZeta R R μ * submoduleZeta R R μ ^ r :=
        mul_le_mul' (submoduleZeta_anti (by omega)) ih
      _ = submoduleZeta R R μ ^ (r + 1) := (pow_succ' _ r).symm

end SubmoduleZeta

section Columns

variable {A l m n : Type} [CommRing A] {R : Subring A} [Fintype m] [Fintype n]

/-- The lattice of the columns of `B * C` is the image under `B` of that of the columns of `C`. -/
lemma colLattice_mul (B : Matrix l m A) (C : Matrix m n A) :
    colLattice R (B * C) = (colLattice R C).map (B.mulVecLin.restrictScalars R) := by
  rw [colLattice, colLattice, ← Submodule.map_comp, mulVecLin_mul, LinearMap.restrictScalars_comp]

/-- If the lattice of the columns of `C` lies in that of the columns of `B`, then `C = B U` for
some matrix `U` with entries in `R`. -/
lemma exists_isIntMatrix_mul_eq {B : Matrix l m A} {C : Matrix l n A}
    (h_le : colLattice R C ≤ colLattice R B) :
    ∃ U : Matrix m n A, IsIntMatrix R U ∧ B * U = C := by
  classical
  have h_col (j : n) : ∃ v ∈ intVectors R m, B *ᵥ v = C.col j := h_le (col_mem_colLattice j)
  choose v hv_int hv using h_col
  exact ⟨(of v)ᵀ, fun i j ↦ hv_int j i, ext_col hv⟩

/-- If `U` has entries in `R`, then the lattice of the columns of `B * U` lies in that of the
columns of `B`. -/
lemma colLattice_mul_le (B : Matrix l m A) {U : Matrix m n A} (hU : IsIntMatrix R U) :
    colLattice R (B * U) ≤ colLattice R B := by
  classical
  rw [colLattice_mul]
  exact Submodule.map_mono (colLattice_le fun j i ↦ hU i j)

omit [Fintype m] in
/-- Let `R` be a subring of a commutative ring `A`. The `R`-span `colLattice R B` of the columns of
an `m × n` matrix `B` over `A` is the range of an `R`-linear map from `R ^ n` to `A ^ m`. -/
lemma exists_range_eq_colLattice (B : Matrix m n A) :
    ∃ f : (n → R) →ₗ[R] (m → A), LinearMap.range f = colLattice R B := by
  let coeVec : (n → R) →ₗ[R] (n → A) := (Algebra.linearMap R A).compLeft n
  have h_range : LinearMap.range coeVec = intVectors R n := by
    ext v
    refine ⟨?_, fun hv ↦ ⟨fun i ↦ ⟨v i, hv i⟩, rfl⟩⟩
    rintro ⟨w, rfl⟩ i
    exact (w i).2
  refine ⟨B.mulVecLin.restrictScalars R ∘ₗ coeVec, ?_⟩
  rw [LinearMap.range_comp, h_range, colLattice]

/-- Let `R` be a subring of a commutative ring `A` and suppose that any `a`, `b` in `A` are
`R`-multiples of `(1 - e) a + e b` for some idempotent `e` of `R` (`IsValuationPair R`). Then the
`R`-span `colLattice R Y` of the columns of an `m × n` matrix `Y` over `A` is the span of the
columns of a square `m × m` matrix `D`. -/
lemma _root_.New.IsValuationPair.exists_square_colLattice_eq (hR : IsValuationPair R)
    (Y : Matrix m n A) : ∃ D : Matrix m m A, colLattice R D = colLattice R Y := by
  classical
  -- Column operations over `R` on `(0 | Y)` clear the columns of the second block.
  let X : Matrix m (m ⊕ n) A := fromCols 0 Y
  obtain ⟨V, hV, h_clear⟩ : ∃ V ∈ intGL (m ⊕ n) R,
      ∀ᵉ (a : m) (j ∉ Set.range (Function.Embedding.inl : m ↪ m ⊕ n)), (X * V.val) a j = 0 :=
    hR.exists_mul_clear_cols X .inl
  let D : Matrix m m A := (X * V.1).toCols₁
  have hD : Y * V.1.toBlocks₂₁ = D := by
    ext i j
    simp [D, X, toCols₁, toBlocks₂₁, mul_apply]
  have hY : D * V⁻¹.1.toBlocks₁₂ = Y := by
    ext i j
    have h_cancel : (X * V.1 * V⁻¹.1) i (.inr j) = Y i j := by simp [X, Matrix.mul_assoc]
    have h_zero (b : n) : (X * V.1) i (.inr b) = 0 := h_clear i (.inr b) (by simp)
    rw [← h_cancel, mul_apply, mul_apply, Fintype.sum_sum_type]
    simp [h_zero, D, toCols₁, toBlocks₁₂]
  obtain ⟨hV_int, hV_inv_int⟩ := mem_intGL.1 hV
  refine ⟨D, le_antisymm ?_ ?_⟩
  · rw [← hD]
    exact colLattice_mul_le Y fun i j ↦ hV_int (.inr i) (.inl j)
  · rw [← hY]
    exact colLattice_mul_le D fun i j ↦ hV_inv_int (.inl i) (.inr j)

/-- If `R` is a valuation pair, that is, any `a`, `b` in `A` are `R`-multiples of `(1 - e) a + e b`
for some idempotent `e` of `R`, then every finitely generated ideal of `R` is principal. -/
lemma _root_.New.IsValuationPair.isBezout (hR : IsValuationPair R) : IsBezout R := by
  refine IsBezout.iff_span_pair_isPrincipal.2 fun a b ↦ ?_
  -- `a` and `b` are multiples of `a - e * (a - b)`, which lies in the ideal they generate
  obtain ⟨e, -, h_le⟩ : ∃ e : R, e.val * e = e ∧
      R ∙ a.1 ⊔ R ∙ b.1 ≤ R ∙ (a.1 - e * (a.1 - b.1)) :=
    hR a b
  have h_mem (c : R) (hc : c.1 ∈ R ∙ (a - e * (a - b) : A)) : c ∈ R ∙ (a - e * (a - b)) := by
    simpa [Submodule.mem_span_singleton, Subtype.ext_iff, Subring.smul_def] using hc
  have ha' : a ∈ R ∙ (a - e * (a - b)) :=
    h_mem a (h_le (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)))
  have hb' : b ∈ R ∙ (a - e * (a - b)) :=
    h_mem b (h_le (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  have ha : a ∈ Ideal.span {a, b} := Ideal.subset_span (by simp)
  have hb : b ∈ Ideal.span {a, b} := Ideal.subset_span (by simp)
  have h_gen : a - e * (a - b) ∈ Ideal.span {a, b} :=
    sub_mem ha (Ideal.mul_mem_left _ e (sub_mem ha hb))
  exact ⟨a - e * (a - b), le_antisymm (Ideal.span_le.2 (Set.pair_subset ha' hb'))
    ((Submodule.span_singleton_le_iff_mem _ _).2 h_gen)⟩

end Columns

variable {E κ P : Type} [Field E] [NumberField E] [IsCMField E] [HasPrimitiveRoot5040 E] [Fintype κ]
  [Fintype P] {r : ℕ}

/-- Let `𝔸f E` be the finite adeles of the number field `E` and `Ô E` the integral ones. An
`Ô E`-submodule `L` of `(𝔸f E) ^ κ` is a lattice of rank `r` if it is spanned over `Ô E` by the
columns of `x a`, where the `r` columns of `x` are independent vectors in `E ^ κ` and `a` is an
invertible `r × r` matrix over `𝔸f E`. -/
def IsLatticeOfRank (r : ℕ) (L : Submodule (Ô E) (κ → 𝔸f E)) : Prop :=
  ∃ (x : Matrix κ (Fin r) E) (a : GL (Fin r) (𝔸f E)),
    HasLeftInv x ∧ colLattice (Ô E) (finAdeleMatrix x * a.1) = L

open scoped Classical in
/-- The discriminant of a lattice `L` of rank `r`: the square root of `genIndex (det (Bᴴ * B))` for
some chosen basis `B = x a`. Here `ᴴ` is the conjugate transpose and `genIndex u` is the inverse of
the factor by which a unit `u` scales Haar measure on the finite adeles (`0` for a non-unit). The
value is `0` if `L` is not a lattice of rank `r`. -/
def discriminant (r : ℕ) (L : Submodule (Ô E) (κ → 𝔸f E)) : ℝ :=
  if h : IsLatticeOfRank r L then
    √(genIndex ((finAdeleMatrix h.choose * h.choose_spec.choose.1)ᴴ *
      (finAdeleMatrix h.choose * h.choose_spec.choose.1)).det)
  else 0

omit [IsCMField E] [HasPrimitiveRoot5040 E] in
/-- If `x` has a left inverse over `E` and `a` is an invertible matrix over the finite adeles
`𝔸f E`, then `finAdeleMatrix x * a` (with `x` read over `𝔸f E`) has a left inverse over `𝔸f E`. -/
lemma hasLeftInv_finAdeleMatrix_mul {x : Matrix κ (Fin r) E} (hx : HasLeftInv x)
    (a : GL (Fin r) (𝔸f E)) : HasLeftInv (finAdeleMatrix x * a.1) := by
  obtain ⟨l, hl⟩ := hx
  have h_map : finAdeleMatrix l * finAdeleMatrix x = 1 := by
    rw [← Matrix.map_mul (f := algebraMap E (𝔸f E)), hl, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨a⁻¹.1 * finAdeleMatrix l, ?_⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (finAdeleMatrix l), h_map, Matrix.one_mul, a.inv_mul]

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones. Let `B`, `C` be matrices over `𝔸f E` whose columns have the same `Ô E`-span, and
let `B` have a left inverse. Then the Gram determinants `det (Bᴴ * B)` and `det (Cᴴ * C)`, with `ᴴ`
the conjugate transpose, have the same generalised index: `genIndex a` is the inverse of the factor
by which a unit `a` scales Haar measure, and `0` for a non-unit. -/
lemma genIndex_det_gram_eq_of_colLattice_eq {B C : Matrix κ (Fin r) (𝔸f E)} (hB : HasLeftInv B)
    (h_eq : colLattice (Ô E) B = colLattice (Ô E) C) :
    genIndex (Bᴴ * B).det = genIndex (Cᴴ * C).det := by
  -- The bases differ by an integral matrix with integral inverse.
  obtain ⟨l, hl⟩ : ∃ l : Matrix (Fin r) κ (𝔸f E), l * B = 1 := hB
  obtain ⟨U, hU_int, rfl⟩ : ∃ U : Matrix (Fin r) (Fin r) (𝔸f E),
      IsIntMatrix (Ô E) U ∧ B * U = C :=
    exists_isIntMatrix_mul_eq h_eq.ge
  obtain ⟨V, hV_int, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) (𝔸f E),
      IsIntMatrix (Ô E) V ∧ B * U * V = B :=
    exists_isIntMatrix_mul_eq h_eq.le
  have hUV : U * V = 1 :=
    calc U * V = l * B * (U * V) := by rw [hl, Matrix.one_mul]
      _ = l * (B * U * V) := by rw [Matrix.mul_assoc l, Matrix.mul_assoc B]
      _ = 1 := by rw [hV, hl]
  have h_gram : (B * U)ᴴ * (B * U) = Uᴴ * (Bᴴ * B) * U := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [h_gram]
  exact genIndex_det_conj_of_isIntMatrix hU_int hV_int (mul_eq_one_comm.1 hUV) hUV

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones. Let `x` be a matrix over `E` with a left inverse, `a` an invertible matrix over
`𝔸f E`, and `B = finAdeleMatrix x * a`, with `x` read over `𝔸f E`. The discriminant of the
`Ô E`-span of the columns of `B`, defined from a chosen basis of this form, can be computed from
`B`: it is `√(genIndex (Bᴴ * B).det)`. -/
lemma discriminant_colLattice {x : Matrix κ (Fin r) E} (hx : HasLeftInv x) (a : GL (Fin r) (𝔸f E)) :
    discriminant r (colLattice (Ô E) (finAdeleMatrix x * a.1)) =
      √(genIndex ((finAdeleMatrix x * a.1)ᴴ * (finAdeleMatrix x * a.1)).det) := by
  have hL : IsLatticeOfRank r (colLattice (Ô E) (finAdeleMatrix x * a.1)) := ⟨x, a, hx, rfl⟩
  rw [discriminant, dite_eq_left hL]
  -- The discriminant is defined by a chosen basis `y b`, which spans the same lattice as `x a`.
  set y : Matrix κ (Fin r) E := hL.choose
  set b : GL (Fin r) (𝔸f E) := hL.choose_spec.choose
  obtain ⟨-, h_chosen⟩ : HasLeftInv y ∧
      colLattice (Ô E) (finAdeleMatrix y * b.1) = colLattice (Ô E) (finAdeleMatrix x * a.1) :=
    hL.choose_spec.choose_spec
  rw [genIndex_det_gram_eq_of_colLattice_eq (hasLeftInv_finAdeleMatrix_mul hx a) h_chosen.symm]

open ComplexOrder in
omit [HasPrimitiveRoot5040 E] in
/-- Let `E` be a CM field, with `ᴴ` the conjugate transpose for its complex conjugation. If the
columns of `x` are independent over `E` (`x` has a left inverse), then their Gram determinant
`det (xᴴ * x)` for the standard hermitian form is not zero. -/
lemma det_gram_ne_zero {x : Matrix κ (Fin r) E} (hx : HasLeftInv x) : (xᴴ * x).det ≠ 0 := by
  -- At a complex embedding the Gram matrix of independent vectors is positive definite.
  obtain ⟨l, hl⟩ := hx
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h_inj : (x.map φ).mulVec.Injective := HasLeftInv.injective_mulVec
    ⟨l.map φ, by rw [← Matrix.map_mul, hl, Matrix.map_one _ φ.map_zero φ.map_one]⟩
  have h_det : φ (xᴴ * x).det = ((x.map φ)ᴴ * x.map φ).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, map_conjTranspose]
  intro h_zero
  rw [h_zero, map_zero] at h_det
  exact (PosDef.conjTranspose_mul_self _ h_inj).det_pos.ne h_det

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones. Let `L` be a lattice of rank `r` in `(𝔸f E) ^ κ`: the `Ô E`-span of the columns
of `x a`, where `x` has `r` independent columns over `E` and `a` is invertible over `𝔸f E`. Then
the discriminant of `L`, the square root of the generalised index `genIndex` of the Gram
determinant of such a basis, is positive. -/
lemma IsLatticeOfRank.discriminant_pos {L : Submodule (Ô E) (κ → 𝔸f E)}
    (hL : IsLatticeOfRank r L) : 0 < discriminant r L := by
  obtain ⟨x, a, hx, rfl⟩ := hL
  have h_gram : (finAdeleMatrix x * a.1)ᴴ * (finAdeleMatrix x * a.1) =
      a.1ᴴ * finAdeleMatrix (xᴴ * x) * a.1 := by
    simp [finAdeleMatrix_conjTranspose, Matrix.mul_assoc]
  have h_unit : IsUnit (finAdeleMatrix (xᴴ * x)).det := by
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using
      (det_gram_ne_zero hx).isUnit.map (algebraMap E (𝔸f E))
  rw [discriminant_colLattice hx, h_gram, genIndex_det_conj]
  exact Real.sqrt_pos.2 (mul_pos (genIndex_pos h_unit.unit) (pow_pos (genIndex_pos a.det) 2))

omit [IsCMField E] [HasPrimitiveRoot5040 E] in
/-- Let `E` be a number field, `𝔸f E` its finite adeles and `Ô E` the integral ones. If an
`Ô E`-submodule `M` of `(𝔸f E) ^ n` contains the `Ô E`-span `colLattice (Ô E) C` of the columns of
`C` with finite index (`submoduleIndex` is not `0`), then `M` is spanned by the columns of `C` and
finitely many further vectors, the columns of `reps`. -/
lemma exists_colLattice_fromCols_eq {n : Type} [Fintype n] {M : Submodule (Ô E) (n → 𝔸f E)}
    (C : Matrix n n (𝔸f E)) (h_le : colLattice (Ô E) C ≤ M)
    (h_index : submoduleIndex (colLattice (Ô E) C) M ≠ 0) :
    ∃ (Q : Type) (_ : Fintype Q) (reps : Matrix n Q (𝔸f E)),
      colLattice (Ô E) (fromCols C reps) = M := by
  classical
  let K : AddSubgroup M.toAddSubgroup := (colLattice (Ô E) C).toAddSubgroup.addSubgroupOf _
  have : Fintype (M.toAddSubgroup ⧸ K) := AddSubgroup.fintypeOfIndexNeZero h_index
  let reps : Matrix n (M.toAddSubgroup ⧸ K) (𝔸f E) := of fun i q ↦ q.out.val i
  refine ⟨_, inferInstance, reps, le_antisymm (colLattice_le ?_) fun v hv ↦ ?_⟩
  · rintro (j | q)
    · exact h_le (col_mem_colLattice j)
    · exact q.out.2
  · obtain ⟨k, hk⟩ : ∃ k : K, (QuotientAddGroup.mk (s := K) ⟨v, hv⟩).out = ⟨v, hv⟩ + k.1 :=
      QuotientAddGroup.mk_out_eq_add K ⟨v, hv⟩
    have h_col : (fromCols C reps).col (.inr (QuotientAddGroup.mk ⟨v, hv⟩)) = v + k :=
      congrArg Subtype.val hk
    have hC_le : colLattice (Ô E) C ≤ colLattice (Ô E) (fromCols C reps) :=
      colLattice_le fun j ↦ col_mem_colLattice (M := fromCols C reps) (.inl j)
    have h_rep : v + k ∈ colLattice (Ô E) (fromCols C reps) := by
      rw [← h_col]
      exact col_mem_colLattice _
    exact (add_mem_cancel_right (hC_le k.2)).1 h_rep

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones. If an `Ô E`-submodule `M` of the module `intVectors (Ô E) n` of vectors in
`(𝔸f E) ^ n` with entries in `Ô E` has finite index, then it has a basis: it is the `Ô E`-span
`colLattice` of the columns of a matrix that is invertible over `𝔸f E`. -/
lemma exists_colLattice_eq_of_submoduleIndex_ne_zero {n : Type} [Fintype n] [DecidableEq n]
    {M : Submodule (Ô E) (n → 𝔸f E)} (h_le : M ≤ intVectors (Ô E) n)
    (h_index : submoduleIndex M (intVectors (Ô E) n) ≠ 0) :
    ∃ A : GL n (𝔸f E), colLattice (Ô E) A.val = M := by
  -- With `N` the index, `M` contains `N Ô ^ n`, spanned by the columns of `C = N • 1`, with finite
  -- index. So `M` is spanned by the columns of `C` and finitely many coset representatives, hence
  -- by the columns of a square matrix `D`; and `D` divides `C`.
  set N : ℕ := submoduleIndex M (intVectors (Ô E) n)
  obtain ⟨c, hc⟩ : IsUnit (N : 𝔸f E) := by
    simpa using (Nat.cast_ne_zero.2 h_index).isUnit.map (algebraMap E (𝔸f E))
  let C : GL n (𝔸f E) := c • 1
  have hC_le : colLattice (Ô E) C.val ≤ M := colLattice_le fun j ↦ by
    have h_col : C.val.col j = N • (Pi.single j 1 : n → 𝔸f E) := by
      ext i
      simp [C, Units.smul_def, one_apply, Pi.single_apply, hc]
    rw [h_col]
    exact M.toAddSubgroup.nsmul_relIndex_mem (K := (intVectors (Ô E) n).toAddSubgroup)
      (single_mem_intVectors j)
  have hC_index : submoduleIndex (colLattice (Ô E) C.val) (intVectors (Ô E) n) ≠ 0 := by
    rw [← Nat.cast_ne_zero (R := ℝ),
      submoduleIndex_colLattice_intVectors (.smul (by simp [hc]) .one)]
    exact (genIndex_pos C.det).ne'
  obtain ⟨Q, _, reps, h_reps⟩ := exists_colLattice_fromCols_eq C.val hC_le
    (mt (AddSubgroup.relIndex_eq_zero_of_le_right h_le) hC_index)
  obtain ⟨D, hD⟩ : ∃ D : Matrix n n (𝔸f E), colLattice (Ô E) D = M := by
    simpa [h_reps] using IsAdelic.isValuationPair.exists_square_colLattice_eq (fromCols C.val reps)
  obtain ⟨U, -, hU : D * U = C.val⟩ := exists_isIntMatrix_mul_eq (hC_le.trans hD.ge)
  obtain ⟨A, rfl⟩ : IsUnit D := isUnit_of_mul_isUnit_left (y := U) (by simp [hU])
  exact ⟨A, hD⟩

/-- For an adelic matrix `B` and an invertible adelic matrix `A`, passing from `B` to `B * A`
multiplies the square root of the generalised index `genIndex` of the Gram determinant by the
generalised index of `det A`. -/
lemma sqrt_genIndex_det_gram_mul (B : Matrix κ (Fin r) (𝔸f E)) (A : GL (Fin r) (𝔸f E)) :
    √(genIndex ((B * A.val)ᴴ * (B * A.val)).det) =
      √(genIndex (Bᴴ * B).det) * genIndex A.val.det := by
  have h_gram : (B * A.val)ᴴ * (B * A.val) = A.valᴴ * (Bᴴ * B) * A.val := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [h_gram, genIndex_det_conj, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq]
  exact (genIndex_pos A.det).le

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones. Let `B` be a matrix over `𝔸f E` with a left inverse, and `M` a submodule of
finite index in the `Ô E`-span `colLattice` of the columns of `B`. Then `M` is spanned by the
columns of `B * A` for some `A` invertible over `𝔸f E`, and the index of `M` is `genIndex (det A)`,
the inverse of the factor by which `det A` scales Haar measure. -/
lemma exists_colLattice_mul_eq_of_le {B : Matrix κ (Fin r) (𝔸f E)} (hB : HasLeftInv B)
    {M : Submodule (Ô E) (κ → 𝔸f E)} (h_le : M ≤ colLattice (Ô E) B)
    (h_index : submoduleIndex M (colLattice (Ô E) B) ≠ 0) :
    ∃ A : GL (Fin r) (𝔸f E), colLattice (Ô E) (B * A.val) = M ∧
      (submoduleIndex M (colLattice (Ô E) B) : ℝ) = genIndex A.val.det := by
  -- In the coordinates of `B` the submodule `M` has finite index in `Ô ^ r`, so it has a basis `A`.
  let M₀ : Submodule (Ô E) (Fin r → 𝔸f E) := M.comap (B.mulVecLin.restrictScalars (Ô E))
  have h₀_le : M₀ ≤ intVectors (Ô E) (Fin r) := fun v hv ↦ by
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ intVectors (Ô E) (Fin r), B *ᵥ w = B *ᵥ v := h_le hv
    obtain ⟨l, hl⟩ := hB
    have h_cancel (y : Fin r → 𝔸f E) : l *ᵥ B *ᵥ y = y := by rw [mulVec_mulVec, hl, one_mulVec]
    rwa [← h_cancel v, ← hwv, h_cancel]
  have h₀_index : submoduleIndex M₀ (intVectors (Ô E) (Fin r)) =
      submoduleIndex M (colLattice (Ô E) B) :=
    M.toAddSubgroup.relIndex_comap B.mulVecLin.toAddMonoidHom _
  obtain ⟨A, hA : colLattice (Ô E) A.val = M₀⟩ :=
    exists_colLattice_eq_of_submoduleIndex_ne_zero h₀_le (h₀_index.trans_ne h_index)
  have hA_int : IsIntMatrix (Ô E) A.val := fun i j ↦ h₀_le (hA.le (col_mem_colLattice j)) i
  refine ⟨A, ?_, ?_⟩
  · rw [colLattice_mul, hA, Submodule.map_comap_eq_self (h_le.trans LinearMap.map_le_range)]
  · rw [← h₀_index, ← hA, submoduleIndex_colLattice_intVectors hA_int]

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones. A lattice of rank `r` is the `Ô E`-span in `(𝔸f E) ^ κ` of the columns of `x a`,
with `r` independent columns of `x` over `E` and `a` invertible over `𝔸f E`. An `Ô E`-submodule `M`
of finite index (`submoduleIndex M L` is not `0`) in such a lattice `L` is again one. -/
lemma IsLatticeOfRank.of_submoduleIndex_ne_zero {L M : Submodule (Ô E) (κ → 𝔸f E)}
    (hL : IsLatticeOfRank r L) (h_le : M ≤ L) (h_index : submoduleIndex M L ≠ 0) :
    IsLatticeOfRank r M := by
  obtain ⟨x, a, hx, rfl⟩ := hL
  obtain ⟨A, hM, -⟩ :=
    exists_colLattice_mul_eq_of_le (hasLeftInv_finAdeleMatrix_mul hx a) h_le h_index
  exact ⟨x, a * A, hx, by rw [Units.val_mul, ← Matrix.mul_assoc, hM]⟩

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones. Let `L` be a lattice of rank `r` in `(𝔸f E) ^ κ`: the `Ô E`-span of the columns
of `B = x a`, with `r` independent columns of `x` over `E` and `a` invertible over `𝔸f E`. If `M` is
an `Ô E`-submodule of `L` of finite non-zero index `submoduleIndex M L`, then its discriminant is
that of `L` times this index. -/
lemma IsLatticeOfRank.discriminant_eq_mul_submoduleIndex {L M : Submodule (Ô E) (κ → 𝔸f E)}
    (hL : IsLatticeOfRank r L) (h_le : M ≤ L) (h_index : submoduleIndex M L ≠ 0) :
    discriminant r M = discriminant r L * submoduleIndex M L := by
  -- If `x a` is a basis of `L`, then `x a A` is a basis of `M`, and the index is that of `det A`.
  obtain ⟨x, a, hx, rfl⟩ := hL
  obtain ⟨A, hM, h_det⟩ : ∃ A : GL (Fin r) (𝔸f E),
      colLattice (Ô E) (finAdeleMatrix x * a.val * A.val) = M ∧
      (submoduleIndex M (colLattice (Ô E) (finAdeleMatrix x * a.val)) : ℝ) = genIndex A.val.det :=
    exists_colLattice_mul_eq_of_le (hasLeftInv_finAdeleMatrix_mul hx a) h_le h_index
  have h_basis : finAdeleMatrix x * (a * A).val = finAdeleMatrix x * a.val * A.val :=
    (Matrix.mul_assoc ..).symm
  rw [h_det, ← hM, ← h_basis, discriminant_colLattice hx, discriminant_colLattice hx, h_basis,
    sqrt_genIndex_det_gram_mul]

/-- An `Ô E`-submodule `M` of finite index in a lattice `L` of rank `r` is a lattice of the same
rank, and its discriminant is the discriminant of `L` times the index `submoduleIndex M L` of `M` in
`L`. -/
lemma IsLatticeOfRank.of_le_and_discriminant_eq_mul_index {L M : Submodule (Ô E) (κ → 𝔸f E)}
    (hL : IsLatticeOfRank r L) (h_le : M ≤ L) (h_index : submoduleIndex M L ≠ 0) :
    IsLatticeOfRank r M ∧ discriminant r M = discriminant r L * submoduleIndex M L :=
  ⟨hL.of_submoduleIndex_ne_zero h_le h_index, hL.discriminant_eq_mul_submoduleIndex h_le h_index⟩

omit [IsCMField E] [HasPrimitiveRoot5040 E] in
/-- The `Ô`-span `colLattice` of the columns of `B` lies in `preimageLattice (Ô E) H`, the vectors
that `H` maps to integral ones, if and only if `H * B` has all entries in `Ô`. -/
lemma colLattice_le_preimageLattice_iff {σ τ : Type} [Fintype τ] {H : Matrix σ κ (𝔸f E)}
    {B : Matrix κ τ (𝔸f E)} :
    colLattice (Ô E) B ≤ preimageLattice (Ô E) H ↔ IsIntMatrix (Ô E) (H * B) := by
  classical
  exact ⟨fun h_le i j ↦ h_le (col_mem_colLattice j) i,
    fun h_int ↦ colLattice_le fun j i ↦ h_int i j⟩

variable [DecidableEq κ]

omit [IsCMField E] [HasPrimitiveRoot5040 E] [DecidableEq κ] in
/-- The image under a rational matrix `η` of the lattice spanned by the columns of `x a` is the
lattice spanned by the columns of `(η x) a`. -/
lemma map_colLattice_finAdeleMatrix_mul (η : Matrix κ κ E) (x : Matrix κ (Fin r) E)
    (a : Matrix (Fin r) (Fin r) (𝔸f E)) :
    (colLattice (Ô E) (finAdeleMatrix x * a)).map
        ((finAdeleMatrix η).mulVecLin.restrictScalars (Ô E)) =
      colLattice (Ô E) (finAdeleMatrix (η * x) * a) := by
  have h_map : finAdeleMatrix (η * x) = finAdeleMatrix η * finAdeleMatrix x := Matrix.map_mul
  rw [h_map, Matrix.mul_assoc, colLattice_mul (finAdeleMatrix η)]

omit [IsCMField E] [HasPrimitiveRoot5040 E] in
/-- A matrix `η` over `E` with a left inverse maps a lattice of rank `r` in `(𝔸f E) ^ κ` (the
`Ô E`-span of the adelic basis `x a` of an `r`-dimensional subspace of `E ^ κ`) to a lattice of
rank `r`. -/
lemma IsLatticeOfRank.map_of_hasLeftInv {L : Submodule (Ô E) (κ → 𝔸f E)}
    (hL : IsLatticeOfRank r L) {η : Matrix κ κ E} (hη : HasLeftInv η) :
    IsLatticeOfRank r (L.map ((finAdeleMatrix η).mulVecLin.restrictScalars (Ô E))) := by
  obtain ⟨x, a, ⟨xInv, hxInv⟩, rfl⟩ := hL
  obtain ⟨ηInv, hηInv⟩ := hη
  refine ⟨η * x, a, ⟨xInv * ηInv, ?_⟩, (map_colLattice_finAdeleMatrix_mul η x a.val).symm⟩
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc ηInv, hηInv, Matrix.one_mul, hxInv]

/-- An isometry `η` of the standard hermitian form over `E` (`ηᴴ * η = 1`) keeps the discriminant
of a lattice of rank `r`, that is, the square root of the generalised index of the Gram determinant
of a basis of the lattice. -/
lemma IsLatticeOfRank.discriminant_map_of_unitary {L : Submodule (Ô E) (κ → 𝔸f E)}
    (hL : IsLatticeOfRank r L) {η : Matrix κ κ E} (hη : ηᴴ * η = 1) :
    discriminant r (L.map ((finAdeleMatrix η).mulVecLin.restrictScalars (Ô E))) =
      discriminant r L := by
  -- The basis `x a` is moved to `(η x) a`, which has the same Gram matrix.
  obtain ⟨x, a, ⟨xInv, hxInv⟩, rfl⟩ := hL
  have h_inv : xInv * ηᴴ * (η * x) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc ηᴴ, hη, Matrix.one_mul, hxInv]
  have hη_adelic : (finAdeleMatrix η)ᴴ * finAdeleMatrix η = 1 := by
    simp [← finAdeleMatrix_conjTranspose, ← Matrix.map_mul, hη]
  have h_gram : (finAdeleMatrix (η * x) * a.val)ᴴ * (finAdeleMatrix (η * x) * a.val) =
      (finAdeleMatrix x * a.val)ᴴ * (finAdeleMatrix x * a.val) := by
    simp [Matrix.mul_assoc, ← Matrix.mul_assoc (finAdeleMatrix η)ᴴ, hη_adelic]
  rw [map_colLattice_finAdeleMatrix_mul, discriminant_colLattice ⟨xInv * ηᴴ, h_inv⟩,
    discriminant_colLattice ⟨xInv, hxInv⟩, h_gram]

/-- An isometry `η` of the standard hermitian form over `E` (`ηᴴ * η = 1`) maps a lattice of rank
`r` to a lattice of rank `r` with the same discriminant. -/
lemma IsLatticeOfRank.map_of_unitary {L : Submodule (Ô E) (κ → 𝔸f E)}
    (hL : IsLatticeOfRank r L) {η : Matrix κ κ E} (hη : ηᴴ * η = 1) :
    IsLatticeOfRank r (L.map ((finAdeleMatrix η).mulVecLin.restrictScalars (Ô E))) ∧
    discriminant r (L.map ((finAdeleMatrix η).mulVecLin.restrictScalars (Ô E))) =
      discriminant r L :=
  ⟨hL.map_of_hasLeftInv ⟨ηᴴ, hη⟩, hL.discriminant_map_of_unitary hη⟩

section Saturated

variable {H' : Matrix κ P (𝔸f E)} {H : Matrix P κ (𝔸f E)}

/-- The saturated lattice of a subspace `V` of `E ^ κ` for a matrix `H` with left inverse `H'`: the
`Ô`-span of the chosen basis `sublatticeBasis u V`, where `u` is the identity `H' * H = 1`. Its
columns are adelic points of `V`, and their image under `H` is a primitive integral matrix. -/
def saturatedLattice (u : H' * H = 1) (V : Submodule E (κ → E)) : Submodule (Ô E) (κ → 𝔸f E) :=
  colLattice (Ô E) (sublatticeBasis u V).val

/-- The matrix `H`, which has the left inverse `H'`, maps the saturated lattice of `V` to integral
vectors. -/
lemma saturatedLattice_le (h_left_inv : H' * H = 1) (V : Submodule E (κ → E)) :
    saturatedLattice h_left_inv V ≤ preimageLattice (Ô E) H :=
  colLattice_le_preimageLattice_iff.2 (isPrimitiveMatrix_mul_sublatticeBasis h_left_inv V).left

/-- The saturated lattice of `V` is a lattice whose rank is the dimension of `V`. -/
lemma isLatticeOfRank_saturatedLattice (h_left_inv : H' * H = 1) (V : Submodule E (κ → E)) :
    IsLatticeOfRank (finrank E V) (saturatedLattice h_left_inv V) := by
  obtain ⟨y, a, hy_inv, -, h_basis⟩ := exists_sublatticeBasis_eq_finAdeleMatrix_mul h_left_inv V
  exact ⟨y, a, hy_inv, by rw [saturatedLattice, h_basis]⟩

/-- The discriminant of the saturated lattice of `V` is `sublatticeDiscriminant h_left_inv V`, the
square root of the generalised index of the Gram determinant of its chosen basis. -/
lemma discriminant_saturatedLattice (h_left_inv : H' * H = 1) (V : Submodule E (κ → E)) :
    discriminant (finrank E V) (saturatedLattice h_left_inv V) =
      sublatticeDiscriminant h_left_inv V := by
  obtain ⟨y, a, hy_inv, -, h_basis⟩ := exists_sublatticeBasis_eq_finAdeleMatrix_mul h_left_inv V
  rw [saturatedLattice, sublatticeDiscriminant, h_basis, discriminant_colLattice hy_inv]

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones. Let the matrix `H` over `𝔸f E` have the left inverse `H'`, and let `V` be a
subspace of `E ^ κ`. Suppose that, for every adelic matrix `m` with `finrank E V` columns, the Gram
matrix `mᴴ * m` has entries in `Ô E` whenever `H * m` has. Then the discriminant
`sublatticeDiscriminant h_left_inv V` is at least `1`. -/
lemma one_le_sublatticeDiscriminant (h_left_inv : H' * H = 1) (V : Submodule E (κ → E))
    (h_int : ∀ m : Matrix κ (Fin (finrank E V)) (𝔸f E),
      IsIntMatrix (Ô E) (H * m) → IsIntMatrix (Ô E) (mᴴ * m)) :
    1 ≤ sublatticeDiscriminant h_left_inv V := by
  -- The Gram determinant is integral, and it is a unit because the discriminant is positive.
  have h_pos : 0 < sublatticeDiscriminant h_left_inv V := by
    simpa [discriminant_saturatedLattice] using
      (isLatticeOfRank_saturatedLattice h_left_inv V).discriminant_pos
  set m : Matrix κ (Fin (finrank E V)) (𝔸f E) := (sublatticeBasis h_left_inv V).val with hm
  rw [sublatticeDiscriminant, ← hm] at h_pos ⊢
  have h_unit : IsUnit (mᴴ * m).det := genIndex.apply_ne_zero_iff.1 (Real.sqrt_pos.1 h_pos).ne'
  have h_gram_int : IsIntMatrix (Ô E) (mᴴ * m) :=
    h_int m (isPrimitiveMatrix_mul_sublatticeBasis h_left_inv V).left
  exact Real.one_le_sqrt.2 (one_le_genIndex h_gram_int.det_mem h_unit)

/-- Let `E` be a CM field with a primitive 5040th root of unity, `𝔸f E` its finite adeles and `Ô E`
the integral ones, and let the matrix `H` over `𝔸f E` have the left inverse `H'`. Let `L` be a
lattice of rank `r` that `H` maps to integral vectors: the `Ô E`-span in `(𝔸f E) ^ κ` of the columns
of `x a`, with `r` independent columns of `x` over `E` and `a` invertible over `𝔸f E`. Then `L` is
spanned by the columns of `S * A` for some subspace `W` of `E ^ κ` of dimension `r` and some
integral `A` invertible over `𝔸f E`. Here `S = sublatticeBasis h_left_inv W` is the chosen basis of
the saturated lattice of `W`. The discriminant of a lattice is the square root of `genIndex` of the
Gram determinant of a basis, with `genIndex u` the inverse of the factor by which a unit `u` scales
Haar measure; that of `L` is `sublatticeDiscriminant h_left_inv W`, the one of `S`, times
`genIndex (det A)`. -/
lemma IsLatticeOfRank.exists_eq_colLattice_sublatticeBasis_mul {L : Submodule (Ô E) (κ → 𝔸f E)}
    {H' : Matrix κ P (𝔸f E)} {H : Matrix P κ (𝔸f E)} (h_left_inv : H' * H = 1)
    (hL : IsLatticeOfRank r L) (h_le : L ≤ preimageLattice (Ô E) H) :
    ∃ (W : Submodule E (κ → E)) (A : GL (Fin (finrank E W)) (𝔸f E)),
      finrank E W = r ∧
      IsIntMatrix (Ô E) A.val ∧
      colLattice (Ô E) ((sublatticeBasis h_left_inv W).val * A.val) = L ∧
      discriminant r L = sublatticeDiscriminant h_left_inv W * genIndex A.val.det := by
  classical
  -- Let `x a` be a basis of `L`, and `S = y b` the basis of the saturated lattice of the span `W`
  -- of `x`. Then `x = y T` with `T` invertible, and `A = b⁻¹ T a`.
  obtain ⟨x, a, hx, rfl⟩ := hL
  obtain ⟨W, hW⟩ : ∃ W : Submodule E (κ → E), colSpan x = W := ⟨colSpan x, rfl⟩
  obtain rfl : finrank E W = r := by
    rw [← hW, LinearMap.finrank_range_of_inj hx.injective_mulVec, Module.finrank_fin_fun]
  obtain ⟨y, b, -, hy_span, h_basis⟩ := exists_sublatticeBasis_eq_finAdeleMatrix_mul h_left_inv W
  set S : Matrix κ (Fin (finrank E W)) (𝔸f E) := (sublatticeBasis h_left_inv W).val with hS
  obtain ⟨T, hT : y * T = x⟩ := exists_mul_eq_of_col_mem_range fun i ↦
    hy_span.ge (hW.le ⟨Pi.single i 1, x.mulVec_single_one i⟩)
  have ⟨xInv, hxInv⟩ := hx
  have hT_unit : IsUnit T := .of_mul_eq_one_right (xInv * y) (by rw [Matrix.mul_assoc, hT, hxInv])
  let A : GL (Fin (finrank E W)) (𝔸f E) :=
    b⁻¹ * GeneralLinearGroup.map (algebraMap E (𝔸f E)) hT_unit.unit * a
  have hA : S * A.val = finAdeleMatrix x * a.val := by simp [h_basis, ← hT, A, Matrix.mul_assoc]
  -- `A` is integral: it is an integral left inverse of `H S` times the integral matrix `H (x a)`.
  have hA_int : IsIntMatrix (Ô E) A.val := by
    obtain ⟨p, hp_int, hp : p * (H * S) = 1⟩ :=
      (isPrimitiveMatrix_mul_sublatticeBasis h_left_inv W).right
    have h_int : IsIntMatrix (Ô E) (p * (H * (finAdeleMatrix x * a.val))) :=
      hp_int.mul (colLattice_le_preimageLattice_iff.1 h_le)
    rwa [← hA, ← Matrix.mul_assoc H, ← Matrix.mul_assoc p, hp, Matrix.one_mul] at h_int
  refine ⟨W, A, rfl, hA_int, by rw [← hS, hA], ?_⟩
  rw [discriminant_colLattice hx, ← hA, sqrt_genIndex_det_gram_mul, sublatticeDiscriminant, ← hS]

end Saturated

/-- Let `E` be a CM field with a primitive 5040th root of unity. Every ideal of finite index in the
ring `Ô E` of integral finite adeles is principal. -/
lemma isPrincipal_of_cardQuot_ne_zero (I : Ideal (Ô E)) (hI : I.cardQuot ≠ 0) : I.IsPrincipal := by
  -- `I` contains its index, a non-zero integer, so it is generated by an ideal of `𝓞 E`.
  have h_mem : algebraMap (𝓞 E) (Ô E) I.cardQuot ∈ I := by
    simpa [Submodule.cardQuot] using AddSubgroup.nsmul_index_mem I.toAddSubgroup 1
  have h_fg : I.FG := by
    rw [← map_under_Ô (Nat.cast_ne_zero.2 hI) h_mem]
    exact Ideal.FG.map (IsNoetherian.noetherian _) _
  exact (IsAdelic.isValuationPair.isBezout (R := Ô E)).isPrincipal_of_FG I h_fg

omit [Fintype κ] [DecidableEq κ] in
/-- For an adelic matrix `B` with `r` columns, the sum of `[L : M] ^ (-(r + μ))` over the submodules
`M` of finite index in the span `L = colLattice (Ô E) B` of its columns is at most `ζ(μ) ^ r`, where
`ζ(μ) = idealZeta (Ô E) μ` is the sum of `[Ô : I] ^ (-μ)` over the ideals `I` of finite index. -/
lemma tsum_submoduleIndex_colLattice_inv_pow_le (B : Matrix κ (Fin r) (𝔸f E)) (μ : ℕ) :
    ∑' M : {M : Submodule (Ô E) (κ → 𝔸f E) // M ≤ colLattice (Ô E) B ∧
        submoduleIndex M (colLattice (Ô E) B) ≠ 0},
      (submoduleIndex M.1 (colLattice (Ô E) B) : ℝ≥0∞)⁻¹ ^ (r + μ) ≤ idealZeta (Ô E) μ ^ r := by
  obtain ⟨f, hf⟩ := exists_range_eq_colLattice (R := Ô E) B
  rw [← hf, show idealZeta (Ô E) μ = submoduleZeta (Ô E) (Ô E) μ from rfl]
  exact (tsum_relIndex_range_le_submoduleZeta f (r + μ)).trans
    (submoduleZeta_pi_le isPrincipal_of_cardQuot_ne_zero r μ)

omit [DecidableEq κ] in
/-- For a lattice `L` of rank `r`, the sum of `[L : M] ^ (-(r + μ))` over the sublattices `M` of
finite index is at most `ζ(μ) ^ r`, where `ζ(μ) = idealZeta (Ô E) μ` is the sum of
`[Ô : I] ^ (-μ)` over the ideals `I` of finite index in `Ô`. (Hey's formula would give the sum
exactly, as a product of zeta values; only this bound is used, and it is proved without the
formula.) -/
theorem IsLatticeOfRank.tsum_submoduleIndex_inv_pow_le {L : Submodule (Ô E) (κ → 𝔸f E)}
    (hL : IsLatticeOfRank r L) (μ : ℕ) :
    ∑' M : {M : Submodule (Ô E) (κ → 𝔸f E) // M ≤ L ∧ submoduleIndex M L ≠ 0},
      (submoduleIndex M.1 L : ℝ≥0∞)⁻¹ ^ (r + μ) ≤ idealZeta (Ô E) μ ^ r := by
  obtain ⟨x, a, -, rfl⟩ := hL
  exact tsum_submoduleIndex_colLattice_inv_pow_le _ μ

end New.Filling

end
