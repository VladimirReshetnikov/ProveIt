import Lib.Weil.DualPair.MixedModel

/-!
# Adapted splittings: hyperbolic polarisation, Hom spaces, composition and stages

A splitting `D : V'.Splitting V p` (`New.Space.Splitting`) writes a hermitian space `V'` as `V` plus
`p` hyperbolic planes, by dual isotropic frames `D.l`, `D.k` and an isometry `D.i`. An adelic matrix
is `New.Exchange.IsOrthoIntegral` if it has orthonormal columns at the infinite places and integral
finite part. The splitting `D` is adapted, `New.Exchange.IsBaseAdapted D`, if its adelic frame
`(l, k, i)` has this property.

## Main definitions and results

* `New.hyperbolicSplitting`: the hyperbolic space `New.hyperbolicSpace E p` splits
  (`New.Space.Splitting`) over the zero space `New.stdSpace E Empty`. Here `l` is the first `p`
  basis vectors and `k` is the last `p` basis vectors.
* `New.Exchange.removePlanes`: the tautological splitting over V of the sum
  `New.Exchange.hyperbolicSum` of hyperbolic planes and V. An instance shows that the tautological
  splitting is adapted.
* `New.Exchange.adaptedHomBasis`: the change of basis `(x⁻¹)ᴴ ⊗ 1` given by the adelic frame `x` of
  `T`.
* `New.Exchange.homSlice_eq_adapted_slice`: the term `A.homSlice T x` is a mixed term of
  `A.homSource T`, after the change of basis `adaptedHomBasis p T`.
* `New.Exchange.isAdapted_homSource`: if `A` is adapted, `A.homSource T` is adapted in the basis
  `adaptedHomBasis p T`.
* `New.Exchange.exists_isBaseAdapted_reindex`,
  `New.Exchange.exists_isBaseAdapted_comp_removePlanes`: an adapted splitting with a single plane
  (`e : Unit ≃ p`) can be reindexed by `Unit`. An adapted splitting can be factored through `V` plus
  some of the planes.

Notions from other files:
* `New.Space`: a hermitian space with a point, given by a matrix J over E and x in GL_n(𝔸) with xᴴJx
  equal to the diagonal matrix of its signs at the infinite places and 1 at the finite places.
* `New.Space.Splitting.IsAdapted`: `D.IsAdapted g t` says that the matrix g⁻¹(l tᴴ⁻¹, k t, ι) of
  adelic frames (`frameAt`) is `IsOrthoIntegral`.
* `New.Space.Splitting.homSource`: From a splitting (k, l, ι) of V over V₀, the splitting of
  Hom(V,T) over Hom(V₀,T) with frames J_T⁻¹⊗(kᴴJ)ᵀ, 1⊗(lᴴJ)ᵀ, 1⊗(J₀⁻¹ιᴴJ)ᵀ.
* `New.Space.Splitting.comp`: From splittings of V over V₀ (rank p) and V₀ over V₁ (rank q), the
  splitting of V over V₁ with frames (k, ik'), (l, il') and embedding ii'.
* `New.Space.Splitting.kCoord`, `lCoord`: the adelic matrices lᴴε, kᴴε (ε = `stdForm`), which send
  la + ιw + kb to b and to a; `iCoord`, built from ιᴴε and the signs, sends it to w.
* `New.Space.Splitting.homSlice`: `A.homSlice T x` is the zero term of `A.homSource T` after the
  Heisenberg operator of the map `x * A.kCoord` in `Hom(W', T)`.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

open Matrix in
/-- Restricting the Gram matrix `Mᴴ * J * M` to the rows and columns chosen by `e` gives the Gram
matrix of the columns of `M` chosen by `e`. -/
lemma Matrix.submatrix_conjTranspose_mul_mul {α m k l : Type*} [Fintype m]
    [NonUnitalNonAssocSemiring α] [Star α] (M : Matrix m k α) (J : Matrix m m α) (e : l → k) :
    (Mᴴ * J * M).submatrix e e = (M.submatrix id e)ᴴ * J * M.submatrix id e := rfl

/-! ## The hyperbolic space as a splitting over the zero space -/

/-- The splitting of hyperbolic space of rank 2p over the zero space. Here l is the first p basis
vectors and k is the last p basis vectors. -/
noncomputable def New.hyperbolicSplitting (E p : Type*) [Field E] [CMType E] [WeilData E]
    [Fintype p] [DecidableEq p] : (hyperbolicSpace E p).Splitting (stdSpace E Empty) p where
  k := Matrix.fromRows 0 1
  l := Matrix.fromRows 1 0
  i := 0
  gram_kk := by
    simp [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  gram_ll := by
    simp [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  gram_lk := by
    simp [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
  gram_ii := Subsingleton.elim ..
  gram_ik := by simp
  gram_il := by simp
  card_eq := by simp +arith

namespace New.Exchange

/-! ## Adapted splittings and the removal of all hyperbolic planes -/

section AdaptedSplitting

open Matrix Space Splitting

/-- The splitting `D` of `V'` over `V` (with `card p` hyperbolic planes) is adapted: the adelic
matrix with column blocks `lAdelic`, `kAdelic`, `iAdelic` has orthonormal columns at every infinite
place and integral entries at every finite place. -/
class IsBaseAdapted {E : Type} [Field E] [CMType E] {n m p : Type} [Fintype n]
    [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype p] [DecidableEq p] {s : n → ℤˣ}
    {t : m → ℤˣ} {V' : Space E m t} {V : Space E n s} (D : V'.Splitting V p) : Prop where
  /-- The block matrix of the three adelic frames is orthonormal at the infinite places and integral
  at the finite places. -/
  isOrthoIntegral : IsOrthoIntegral ((D.lAdelic.fromCols D.kAdelic).fromCols D.iAdelic)

variable {E : Type} [Field E] [CMType E] [WeilData E] {n : Type} (p : Type) [Fintype n]
  [DecidableEq n] [Fintype p] [DecidableEq p] {s : n → ℤˣ} (V : Space E n s)

/-- The tautological splitting over V of the sum of `card p` hyperbolic planes and V: the
frames l, k, i are the column blocks of the identity matrix. -/
noncomputable def removePlanes : (hyperbolicSum p V).Splitting V p := by
  use (fromRows 0 1).fromRows 0, (fromRows 1 0).fromRows 0, fromRows 0 1
  all_goals simp +arith [hyperbolicSum, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    fromCols_mul_fromBlocks, fromCols_mul_fromRows]

/-- The tautological splitting `removePlanes p V` is adapted. -/
instance : IsBaseAdapted (removePlanes p V) where
  isOrthoIntegral := by
    -- The frame is the block matrix of the inverse base point of hyperbolic space and `1`.
    refine (isOrthoIntegral_hyperbolicSpace.right.block_diag .one).of_eq_submatrix_mul id .one ?_
    simp [← ext_iff, Matrix.mul_apply, lAdelic, kAdelic, iAdelic, Space.ratMap, removePlanes,
      hyperbolicSum, sum, blockGL, fromRows_map, fromBlocks_mul_fromRows, Matrix.one_apply]

end AdaptedSplitting

/-!
## Adapted splittings of Hom spaces

Here `A` is a splitting of `W'` over `W`, `T` is a space, and `A.homSource T` is the induced
splitting of `Hom(W', T)`.
-/

section AdaptedHom

open Matrix Kronecker Space Splitting Equiv

variable {E : Type _} [Field E] [CMType E] {n n' r : Type _} {p : Type _}
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype r] [DecidableEq r]
  [Fintype p] [DecidableEq p] {s : n → ℤˣ} {s' : n' → ℤˣ} {t : r → ℤˣ} {W : Space E n s}
  {W' : Space E n' s'} (A : W'.Splitting W p) (T : Space E r t)

/-- The invertible adelic matrix (x⁻¹)ᴴ ⊗ 1, where x is the adelic frame of T and 1 is the p×p
identity. -/
noncomputable def adaptedHomBasis {E : Type*} [Field E] [CMType E] {r : Type*}
    (p : Type*) [Fintype r] [DecidableEq r] [Fintype p] [DecidableEq p] {t : r → ℤˣ}
    (T : Space E r t) : GL (r × p) (𝔸 E) := kroneckerGL (n := p) (star T.x⁻¹) 1

variable {M : Matrix n' n (𝔸 E)}

/-- In the basis `adaptedHomBasis p T`, the adelic frame of the induced splitting `A.homSource T`
(for the group element `1`) has the three column blocks `1 ⊗ₖ A.kCoordᵀ`,
`stdForm E t ⊗ₖ A.lCoordᵀ` and `1 ⊗ₖ A.iCoordᵀ`. -/
lemma frameAt_homSource :
    (A.homSource T).frameAt 1 (adaptedHomBasis p T) =
      ((1 ⊗ₖ A.kCoordᵀ).fromCols (stdForm E t ⊗ₖ A.lCoordᵀ)).fromCols (1 ⊗ₖ A.iCoordᵀ) := by
  simp [Splitting.frameAt, homSource_iAdelic, mul_assoc, dualFrame, homSource_lAdelic,
    adaptedHomBasis, kroneckerGL, star_eq_conjTranspose, conjTranspose_kronecker,
    ← mul_kronecker_mul, homSource_kAdelic, ← conjTranspose_mul]

/-- The term `A.homSlice T x` is the mixed term `slice` of the induced splitting
`A.homSource T` at the vector of entries of `x` (`matrixToVec x`), after the change of basis
`adaptedHomBasis p T`. -/
lemma homSlice_eq_adapted_slice [WeilData E] (x : Matrix r p (𝔸 E)) :
    A.homSlice T x = (A.homSource T).slice ((adaptedHomBasis p T)⁻¹.valᴴ *ᵥ matrixToVec x) := by
  simp [slice, homSlice, kronecker_mulVec_eq_matrixToVec, homSource_lAdelic, adaptedHomBasis,
    kroneckerGL, star_eq_conjTranspose, conjTranspose_kronecker, ← mul_kronecker_mul]

omit [Fintype n] [DecidableEq n'] [DecidableEq r] [Fintype p] in
/-- If `M` and `B` are `IsOrthoIntegral`, so is the Kronecker product of `M` and the entrywise
conjugate `Bᴴᵀ` of `B`. -/
lemma IsOrthoIntegral.kronecker {B : Matrix r p (𝔸 E)} (hM : IsOrthoIntegral M)
    (hB : IsOrthoIntegral B) : IsOrthoIntegral (M ⊗ₖ Bᴴᵀ) := by
  have hM_inf (w : NumberField.InfinitePlace E) : (M.map (evalInf w))ᴴ * M.map (evalInf w) = 1 :=
    hM.left w
  have hB_inf (w : NumberField.InfinitePlace E) : (B.map (evalInf w))ᴴ * B.map (evalInf w) = 1 :=
    hB.left w
  -- Evaluation at an infinite place commutes with `ᴴ`.
  have h_conj (w : NumberField.InfinitePlace E) : Bᴴ.map (evalInf w) = (B.map (evalInf w))ᴴ :=
    B.conjTranspose_map (evalInf w) fun _ ↦ rfl
  refine ⟨fun w ↦ ?_, fun i k ↦ ?_⟩
  · -- Evaluation at `w` commutes with `⊗ₖ`, so the product is `MᴴM ⊗ₖ (BᴴB)ᵀ = 1 ⊗ₖ 1`.
    simp [map_kronecker, h_conj, transpose_map, conjTranspose_kronecker,
      conjTranspose_transpose_eq_transpose_conjTranspose, ← mul_kronecker_mul, ← transpose_mul,
      hM_inf w, hB_inf w]
  · -- Each entry is an entry of `M` times the conjugate of an entry of `B`.
    simp [mul_mem, star_mem_Ô, hM.right, hB.right]

/-- If the splitting `A` of `W'` over `W` is adapted (`IsBaseAdapted`: its adelic frame is
orthonormal at the infinite places and integral at the finite places), then so is the induced
splitting `A.homSource T` of `Hom(W', T)` over `Hom(W, T)` (`Space.Splitting.IsAdapted`) for the
group element `1` and the change of basis `t = adaptedHomBasis p T = (x⁻¹)ᴴ ⊗ 1`, where `x` is the
adelic frame of `T`. That is, the matrix `(l (t⁻¹)ᴴ, k t, ι)` built from the frames of
`A.homSource T` has orthonormal columns at every infinite place and integral entries at every finite
place. -/
lemma isAdapted_homSource [h : IsBaseAdapted A] :
    (A.homSource T).IsAdapted 1 (adaptedHomBasis p T) := by
  -- Up to signs on rows and columns and a reordering `e` of the columns, the frame of the induced
  -- splitting is `1 ⊗ₖ Fᴴᵀ`, where `F` is the frame of `A`.
  let F : Matrix n' ((p ⊕ p) ⊕ n) (𝔸 E) := (A.lAdelic.fromCols A.kAdelic).fromCols A.iAdelic
  let e : ((r × p) ⊕ (r × p)) ⊕ (r × n) → r × ((p ⊕ p) ⊕ n) :=
    (prodSumDistrib r (p ⊕ p) n).symm ∘ Sum.map (prodSumDistrib r p p).symm id
  let ε : ((r × p) ⊕ (r × p)) ⊕ (r × n) → ℤˣ :=
    1 ⊕ᵥ (fun x : r × p ↦ t x.1) ⊕ᵥ fun x : r × n ↦ s x.2
  have h_kron : IsOrthoIntegral
      ((stdForm E fun x : r × n' ↦ s' x.2) * (1 : Matrix r r (𝔸 E)) ⊗ₖ Fᴴᵀ) :=
    .mul (.of_stdForm fun x : r × n' ↦ s' x.2) (.kronecker .one h.isOrthoIntegral)

  have h_frame : (A.homSource T).frameAt 1 (adaptedHomBasis p T) =
      ((stdForm E fun x : r × n' ↦ s' x.2) * (1 : Matrix r r (𝔸 E)) ⊗ₖ Fᴴᵀ).submatrix id e *
        stdForm E ε := by
    -- By `frameAt_homSource` the entries agree block by block, up to the order of the factors.
    rw [frameAt_homSource]
    ext ⟨i, j⟩ ((⟨a, b⟩ | ⟨a, b⟩) | ⟨a, b⟩) : 1
    · -- The `l` block `1 ⊗ₖ A.kCoordᵀ`: both sides are `δ i a * star (A.lAdelic j b)` times a sign.
      simp [F, e, ε, kCoord, stdForm, Matrix.one_apply, ← Pi.one_def, Prod.mk_one_one, mul_comm]
    · -- The `k` block `stdForm E t ⊗ₖ A.lCoordᵀ`: both sides are `δ i a * star (A.kAdelic j b)`
      -- times signs.
      simp +contextual [F, e, ε, lCoord, stdForm, Matrix.one_apply, diagonal_apply, mul_comm,
        mul_left_comm]
    · -- The `ι` block `1 ⊗ₖ A.iCoordᵀ`: both sides are `δ i a * star (A.iAdelic j b)` times signs.
      simp [F, e, ε, iCoord, stdForm, Matrix.one_apply, mul_comm, mul_left_comm]
  show IsOrthoIntegral ((A.homSource T).frameAt 1 (adaptedHomBasis p T))
  exact h_kron.of_eq_submatrix_mul e (.of_stdForm ε) h_frame (by simp [e, Function.Injective])

end AdaptedHom

/-!
## Composition, reindexing and staging of adapted splittings

Bookkeeping for removing hyperbolic planes from a hermitian space in several steps.
-/

section AdaptedStages

open Matrix Space Splitting Fintype Equiv

variable {E : Type} [Field E] [CMType E] [WeilData E]
  {n m p q n₁ : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype p]
  [DecidableEq p] [Fintype q] [DecidableEq q] [Fintype n₁] [DecidableEq n₁]
  {s : n → ℤˣ} {t : m → ℤˣ} {V' : Space E m t} {V : Space E n s} (D : V'.Splitting V p)

/-- If `D` is adapted, so is `D.symm`, the splitting with the frames `k` and `l` exchanged. -/
instance [hD : IsBaseAdapted D] : IsBaseAdapted D.symm where
  isOrthoIntegral := by
    -- Exchanging `k` and `l` permutes the columns of the adelic frame.
    have h_frame : (D.symm.lAdelic.fromCols D.symm.kAdelic).fromCols D.symm.iAdelic =
        ((D.lAdelic.fromCols D.kAdelic).fromCols D.iAdelic).submatrix id (Sum.map Sum.swap id) *
          (1 : Matrix ((p ⊕ p) ⊕ n) ((p ⊕ p) ⊕ n) (𝔸 E)) := by aesop
    exact hD.isOrthoIntegral.of_eq_submatrix_mul (Sum.map Sum.swap id) .one h_frame

omit [WeilData E] in
/-- For an adapted splitting `D`, the adelic matrices `D.kAdelic` (the frame `k` in standard
coordinates) and `D.lCoord` have integral entries: they lie in the ring `O` of adeles whose finite
part lies in `Ô E`, the integral finite adeles. -/
lemma isIntMatrix_kAdelic_and_lCoord [hD : IsBaseAdapted D] :
    let O := (Ô E).comap (RingHom.snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))
    IsIntMatrix O D.kAdelic ∧ IsIntMatrix O D.lCoord := by
  intro O
  have h_int : ∀ (i : m) (j : (p ⊕ p) ⊕ n),
      (((D.lAdelic.fromCols D.kAdelic).fromCols D.iAdelic) i j).2 ∈ Ô E :=
    hD.isOrthoIntegral.right
  -- The columns of `D.kAdelic` are among those of the adapted frame.
  have h_k (i : m) (j : p) : (D.kAdelic i j).2 ∈ Ô E := by simpa using h_int i (.inl (.inr j))
  -- `D.lCoord` is `D.kAdelicᴴ` times the diagonal matrix of signs; `star` keeps integrality.
  exact ⟨fun i j ↦ by simpa [O] using h_k i j,
    fun i j ↦ by simpa [O, lCoord, stdForm] using star_mem_Ô (h_k j i)⟩

/-- Let `D` be an adapted splitting of `V'` over `V` with a single hyperbolic plane, given by
`e : Unit ≃ p`. Then there is an adapted splitting indexed by `Unit` with the same embedding `i`,
whose frame `k` is that of `D` reindexed by `e`. -/
lemma exists_isBaseAdapted_reindex [hD : IsBaseAdapted D] (e : Unit ≃ p) :
    ∃ A' : V'.Splitting V Unit, IsBaseAdapted A' ∧ A'.k = D.k.submatrix id e ∧ A'.i = D.i := by
  -- Reindex the columns of the frame `(l, k, i)` of `D` along `e`.
  let ε : (Unit ⊕ Unit) ⊕ n ≃ (p ⊕ p) ⊕ n := (e.sumCongr e).sumCongr (.refl n)
  let M : Matrix m ((p ⊕ p) ⊕ n) E := (D.l.fromCols D.k).fromCols D.i
  have h_gram : (M.submatrix id ε)ᴴ * V'.J * M.submatrix id ε = (hyperbolicSum Unit V).J := by
    rw [← Matrix.submatrix_conjTranspose_mul_mul, D.gram_eq_hyperbolicSum]
    aesop (add simp hyperbolicSum)
  let A' : V'.Splitting V Unit :=
    splittingOfGram (M.submatrix id ε) h_gram (by rw [card_congr e, D.card_eq])
  have h_frame : (A'.lAdelic.fromCols A'.kAdelic).fromCols A'.iAdelic =
      ((D.lAdelic.fromCols D.kAdelic).fromCols D.iAdelic).submatrix id ε *
        (1 : Matrix ((Unit ⊕ Unit) ⊕ n) ((Unit ⊕ Unit) ⊕ n) (𝔸 E)) := by
    aesop
  exact ⟨A', ⟨hD.isOrthoIntegral.of_eq_submatrix_mul ε .one h_frame⟩, rfl, rfl⟩

/-- Let `D` be an adapted splitting (`IsBaseAdapted`) of `V'` over `V` with `card p` hyperbolic
planes. A splitting is a Witt decomposition with isotropic frames `l`, `k` and an embedding `i` of
`V`. Adapted means the adelic matrix of `l`, `k`, `i` has orthonormal columns at every infinite
place and integral entries at every finite place. For any `e : n₁ ⊕ q ≃ p`, there is an adapted
splitting `A₁` of `V'` over `hyperbolicSum q V` with `card n₁` planes such that
`A₁.comp (removePlanes q V)` has frame `k` equal to `D.k` reindexed by `e` and embedding `i` equal
to `D.i`, where `removePlanes q V` is the tautological splitting of `hyperbolicSum q V` over `V`
with `card q` planes. -/
lemma exists_isBaseAdapted_comp_removePlanes [hD : IsBaseAdapted D] (e : n₁ ⊕ q ≃ p) :
    ∃ A₁ : V'.Splitting (hyperbolicSum q V) n₁,
      IsBaseAdapted A₁ ∧
      (A₁.comp (removePlanes q V)).k = D.k.submatrix id e ∧
      (A₁.comp (removePlanes q V)).i = D.i := by
  -- Regroup the columns of the frame `(l, k, i)` of `D`: first the planes indexed by `n₁`, then
  -- those indexed by `q` together with `V`.
  let ε : (n₁ ⊕ n₁) ⊕ (q ⊕ q) ⊕ n ≃ (p ⊕ p) ⊕ n :=
    (sumAssoc (n₁ ⊕ n₁) (q ⊕ q) n).symm.trans
      (((sumSumSumComm n₁ n₁ q q).trans (e.sumCongr e)).sumCongr (Equiv.refl n))
  let M : Matrix m ((p ⊕ p) ⊕ n) E := (D.l.fromCols D.k).fromCols D.i
  have h_gram : (M.submatrix id ε)ᴴ * V'.J * M.submatrix id ε =
      (hyperbolicSum n₁ (hyperbolicSum q V)).J := by
    -- It is the Gram matrix of `(l, k, i)`, with rows and columns reordered by `ε`.
    rw [← Matrix.submatrix_conjTranspose_mul_mul, D.gram_eq_hyperbolicSum]
    simp [← ext_iff, ε, sum, hyperbolicSum, Matrix.one_apply]
  have h_card : card m = card ((q ⊕ q) ⊕ n) + 2 * card n₁ := by
    simp +arith [D.card_eq, ← card_congr e]
  let A₁ : V'.Splitting (hyperbolicSum q V) n₁ := splittingOfGram (M.submatrix id ε) h_gram h_card
  -- The change of frame: `1` on the planes indexed by `n₁`, the base point of hyperbolic space
  -- on the planes indexed by `q`, and `1` on `V`.
  let C : Matrix ((n₁ ⊕ n₁) ⊕ (q ⊕ q) ⊕ n) ((n₁ ⊕ n₁) ⊕ (q ⊕ q) ⊕ n) (𝔸 E) :=
    fromBlocks 1 0 0 (fromBlocks (hyperbolicSpace E q).x.val 0 0 1)
  have h_C : IsOrthoIntegral C := .block_diag .one
    (isOrthoIntegral_hyperbolicSpace.left.block_diag .one)
  have h_frame : (A₁.lAdelic.fromCols A₁.kAdelic).fromCols A₁.iAdelic =
      ((D.lAdelic.fromCols D.kAdelic).fromCols D.iAdelic).submatrix id ε * C := by
    simp [← ext_iff, Matrix.mul_apply, ε, A₁, M, C, sum, splittingOfGram, toCols₁, toCols₂, lAdelic,
      hyperbolicSum, kAdelic, iAdelic, ratMap, Matrix.one_apply]
  refine ⟨A₁, ⟨hD.isOrthoIntegral.of_eq_submatrix_mul ε h_C h_frame⟩, ?_⟩
  -- The composite has the frame `k` of `D`, reindexed by `e`, and the embedding `i` of `D`.
  simp [← ext_iff, Matrix.mul_apply, ε, A₁, M, removePlanes, splittingOfGram, toCols₁, toCols₂,
    Splitting.comp, Matrix.one_apply]

/-- If `D` (a splitting of `V'` over `V`) and `A` (a splitting of `V` over `W`) are adapted, so
is their composite `D.comp A`, a splitting of `V'` over `W`. -/
instance [hD : IsBaseAdapted D] {r : n₁ → ℤˣ} {W : Space E n₁ r} {A : V.Splitting W q}
    [hA : IsBaseAdapted A] : IsBaseAdapted (D.comp A) where
  isOrthoIntegral := by
    -- Up to the order of the columns, the frame of the composite is the frame of `D` times the
    -- block matrix of `1` and the frame of `A`.
    refine (hD.isOrthoIntegral.mul (.block_diag (.one (n := p ⊕ p))
      hA.isOrthoIntegral)).of_eq_submatrix_mul
      (sumAssoc (p ⊕ p) (q ⊕ q) n₁ ∘ Sum.map (sumSumSumComm p q p q) id) .one ?_
    -- The frames `k`, `l` of the composite are `(k, i k')`, `(l, i l')`, its embedding is `i i'`.
    aesop (add simp [lAdelic, Splitting.comp, fromCols_map, kAdelic, iAdelic, ratMap,
      Matrix.mul_assoc, fromCols_mul_fromBlocks])

end AdaptedStages

end New.Exchange
