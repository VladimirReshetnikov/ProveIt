import Lib.General.LinearAlgebra.Eigenvalues
import Lib.Weil.Construction.AdelicRepresentation

/-!
# Hyperbolic space and splittings of a hermitian space along isotropic subspaces

A hermitian space `V : New.Space E n s` has Gram matrix `V.J` over `E` and an adelic frame `V.x`
taking it to `New.stdForm E s`. `New.G E s` is the adelic unitary group of that form, and `V.Γ` is
its group of rational points. Here `E` is a CM field (`CMType E`), and `WeilData E` supplies the
purely imaginary `j` (`star j = -j`) used below. The file constructs hyperbolic space together with
its frame, and defines adelic matrices that are orthonormal at the infinite places and integral at
the finite ones. It then studies a splitting, or Witt decomposition,
`V = (range l ⊕ range k) ⊥ i V₀` with `l` and `k` isotropic and dual: it gives the frames and
coordinates of the splitting in adelic form, the Levi and unipotent elements of the stabiliser of
`range k`, the law of a mixed model, and points adapted to the splitting.

## Main definitions and results

* `New.hyperbolicSpace`: the hyperbolic space of rank `2 p` as a `New.Space`, that is, with an
  adelic frame that carries its Gram matrix to the standard form of signs `New.hyperbolicSigns p`
  (`p` times `+1`, `p` times `-1`).
* `New.Exchange.IsOrthoIntegral`: adelic matrices with orthonormal columns at the infinite places
  and integral finite part. The frame of `New.hyperbolicSpace` and its inverse are such
  (`New.Exchange.isOrthoIntegral_hyperbolicSpace`), and the property is stable under products, block
  sums and choice of columns.
* `New.Space.Splitting.levi`, `New.Space.Splitting.radicalElement`: Levi and unipotent elements;
  every `g` with `g k = k a` is a product of the two
  (`New.Space.Splitting.exists_eq_radicalElement_mul_levi`), and the unipotent elements make up the
  unipotent radical (`New.Space.Splitting.exists_eq_radicalElement_iff`).
* `New.Space.Splitting.IsAdapted`: elements of `G` adapted to a splitting and to `t` in `GL_p(𝔸)`;
  they exist (`New.Space.Splitting.exists_isAdapted_and_frame_eq`).
* `New.Space.Splitting.siegelParabolic_sup_symm_eq_top`: if `V₀` is zero, the stabilizers of the
  spans of `k` and of `l` generate the rational unitary group of `V`.
* `New.Space.Splitting.exists_isCompact_rat_mul_radicalElement_mem`: the rational points of the
  unipotent radical are cocompact.

Notions from other files:
* `New.stdForm E s`: the diagonal adelic matrix that is `diag s` at every infinite place and the
  identity at the finite places.
* `New.G.adeleMatrix`: the `n × n` adelic matrix of an element of the adelic unitary group
  `New.G E s`.
* `New.evalInf w`: evaluation of an adele at the infinite place `w`, a ring map to `ℂ`.
* `Ô E`: the integral finite adeles.

## Relation to the literature

Known; see `Lib.Adelic.Witt.IwasawaDecomposition` and `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

/-! ## Hyperbolic space; matrices orthonormal at infinity and integral -/

namespace New

open NumberField Matrix stdLattice Prod Weil

variable (E : Type _) [Field E] [CMType E] [WeilData E] {n : Type _} [DecidableEq n]
  (p : Type _) [Fintype p] [DecidableEq p] {m q : Type _} [DecidableEq q] [Fintype m]

/-- The sign function on two copies of p that is +1 on the first copy and −1 on the second. -/
abbrev hyperbolicSigns : p ⊕ p → ℤˣ := 1 ⊕ᵥ -1

/-- Hyperbolic space of rank `2 p`: the Gram matrix has blocks `(0, 1; 1, 0)`, and the adelic frame
carries it to the standard form with signs `+1` on the first `p` and `−1` on the last `p`
coordinates. The frame is `(1/√2) (1, −1; 1, 1)` at every infinite place and `(1, −c; ϵ, c ϵ̄)` at
the finite places, with `c` the integral unit `New.Weil.normNegOne` (`c̄ c = −1`) and
`ϵ = stdLattice.traceOneAdele` (`ϵ + ϵ̄ = 1`). -/
@[simps J]
noncomputable def hyperbolicSpace : Space E (p ⊕ p) (hyperbolicSigns p) :=
  -- The identities at the finite places use `star c * c = -1` and `ϵ + star ϵ = 1`, for the chosen
  -- integral adeles `c` of norm `-1` and `ϵ` of trace `1`.
  let c := normNegOne.1.1
  let ϵ : 𝔸f E := stdLattice.traceOneAdele
  { J := fromBlocks 0 1 1 0
    x := mkAdelicGL
      (fun _ ↦
        { val := (√2 : ℂ)⁻¹ • fromBlocks 1 (-1) 1 1
          inv := (√2 : ℂ)⁻¹ • fromBlocks 1 1 (-1) 1
          val_inv := by
            simp [fromBlocks_multiply, ← ext_iff, ← mul_assoc, ← mul_inv, ← Complex.ofReal_mul,
              Matrix.one_apply]
            grind
          inv_val := by
            simp [fromBlocks_multiply, ← ext_iff, ← mul_assoc, ← mul_inv, ← Complex.ofReal_mul,
              Matrix.one_apply]
            grind },
        { val := fromBlocks 1 (-c • 1) (ϵ • 1) ((c * star ϵ) • 1)
          inv := fromBlocks (star ϵ • 1) 1 ((star c * ϵ) • 1) (-star c • 1)
          val_inv := by
            simp [fromBlocks_multiply, ← ext_iff, Matrix.one_apply, ← mul_assoc]
            grind [star_normNegOne_mul_self]
          inv_val := by
            simp [fromBlocks_multiply, ← ext_iff, Matrix.one_apply, ← mul_assoc]
            grind [star_normNegOne_mul_self] })
    gram_point := by
      refine gram_mkAdelicGL ?_ ?_
      · simp [signMatrix, fromBlocks_conjTranspose, fromBlocks_map, fromBlocks_multiply, ← ext_iff,
          ← mul_assoc, ← mul_inv, ← Complex.ofReal_mul, diagonal_apply, Matrix.one_apply]
        grind
      · simp [fromBlocks_conjTranspose, fromBlocks_map, fromBlocks_multiply, ← ext_iff,
          Matrix.one_apply, ← mul_assoc]
        grind [star_normNegOne_mul_self] }

variable {E p}

lemma signs_comp_refl {m : Sort*} {t : m → ℤˣ} : t ∘ Equiv.refl m = t := rfl

/-- An adelic matrix `M` is orthonormal at infinity and integral: `M_wᴴ M_w = 1` at every infinite
place `w`, where `M_w` is the complex matrix of the components of `M` at `w`, and every entry of
`M` has its finite part in `Ô E`. -/
@[local simp]
def Exchange.IsOrthoIntegral {E : Type _} [Field E] [NumberField E] (M : Matrix m n (𝔸 E)) : Prop :=
  (∀ w : InfinitePlace E, (M.map (evalInf w))ᴴ * M.map (evalInf w) = 1) ∧
  ∀ (i : m) (k : n), (M i k).2 ∈ Ô E

/-- The adelic frame `x` of hyperbolic space is orthonormal at infinity and integral. -/
lemma Exchange.isOrthoIntegral_hyperbolicSpace_x : IsOrthoIntegral (hyperbolicSpace E p).x.val := by
  -- The entries are integral; at the infinite places the diagonal entries of
  -- `(1/√2)² (2 · 1)` are `2⁻¹ + 2⁻¹ = 1`.
  have h_half : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by norm_num
  refine ⟨fun w ↦ ?_, ?_⟩
  · simp [hyperbolicSpace, ← ext_iff, Matrix.mul_apply, Matrix.one_apply, ← mul_inv,
      ← Complex.ofReal_mul, ite_add_ite, h_half, eq_comm]
  · simp [hyperbolicSpace, ite_mem, star_mem_Ô, traceOneAdele_mem, mul_mem, Matrix.one_apply]

/-- The inverse `x⁻¹` of the adelic frame of hyperbolic space is orthonormal at infinity and
integral. -/
lemma Exchange.isOrthoIntegral_hyperbolicSpace_x_inv :
    IsOrthoIntegral (hyperbolicSpace E p).x⁻¹.val := by
  have h_half : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by norm_num
  refine ⟨fun w ↦ ?_, ?_⟩
  · simp [hyperbolicSpace, ← map_inv, ← ext_iff, Matrix.mul_apply, Matrix.one_apply, ← mul_inv,
      ← Complex.ofReal_mul, ite_add_ite, h_half, eq_comm]
  · simp [hyperbolicSpace, ← map_inv, ite_mem, star_mem_Ô, traceOneAdele_mem, mul_mem,
      Matrix.one_apply]

/-- For the hyperbolic space `hyperbolicSpace E p` of rank `2 p` (Gram matrix with blocks
`(0, 1; 1, 0)`), consider its adelic frame `x`, which carries the Gram matrix to the signed standard
form with signs `+1` on the first `p` and `−1` on the last `p` coordinates. Both `x` and its inverse
`x⁻¹` are orthonormal at infinity and integral: at each infinite place `w` the complex matrix `M_w`
of components satisfies `M_wᴴ M_w = 1` (unitary for the standard definite form), and every entry has
finite part in `Ô E`. -/
lemma Exchange.isOrthoIntegral_hyperbolicSpace :
    IsOrthoIntegral (hyperbolicSpace E p).x.val ∧ IsOrthoIntegral (hyperbolicSpace E p).x⁻¹.val :=
  ⟨isOrthoIntegral_hyperbolicSpace_x, isOrthoIntegral_hyperbolicSpace_x_inv⟩

namespace Exchange.IsOrthoIntegral

omit [WeilData E] in
lemma of_stdForm [Fintype n] (s : n → ℤˣ) : IsOrthoIntegral (stdForm E s) := by
  simp [stdForm, apply_ite, ← Int.cast_mul, diagonal_apply]

omit [WeilData E] in
lemma one [Fintype n] :
    IsOrthoIntegral (1 : Matrix n n (𝔸 E)) := by aesop (add simp Matrix.one_apply)

variable {A : Matrix m n (𝔸 E)} (hA : IsOrthoIntegral A)

include hA

section

omit [WeilData E]

/-- The first half of `IsOrthoIntegral A`: `A_wᴴ A_w = 1` at each infinite place `w`, where `A_w` is
the complex matrix `A.map (evalInf w)`. -/
lemma conjTranspose_map_mul_map (w : InfinitePlace E) :
    (A.map (evalInf w))ᴴ * A.map (evalInf w) = 1 := hA.left w

/-- The second half of `IsOrthoIntegral A`: every entry of `A` has its finite part in `Ô E`. -/
lemma snd_mem_Ô (i : m) (k : n) : (A i k).2 ∈ Ô E := hA.right i k

/-- A product of matrices orthonormal at infinity and integral is again such. -/
lemma mul [Fintype n]
    {B : Matrix n q (𝔸 E)} (hB : IsOrthoIntegral B) : IsOrthoIntegral (A * B) := by
  refine ⟨fun w ↦ ?_, fun i k ↦ ?_⟩
  · -- Evaluation at `w` is multiplicative, and `Bᴴ Aᴴ A B = Bᴴ B = 1`.
    rw [Matrix.map_mul, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (A.map _)ᴴ,
      hA.conjTranspose_map_mul_map w, Matrix.one_mul, hB.conjTranspose_map_mul_map w]
  · -- The finite part of an entry of `A * B` is a sum of products of integral finite parts.
    simp [Matrix.mul_apply, snd_sum, sum_mem, mul_mem, hA.snd_mem_Ô, hB.snd_mem_Ô]

omit [DecidableEq p] in
/-- A block sum of matrices orthonormal at infinity and integral is again such. -/
lemma block_diag {B : Matrix p q (𝔸 E)} (hB : IsOrthoIntegral B) :
    IsOrthoIntegral (fromBlocks A 0 0 B) := by
  refine ⟨fun w ↦ ?_, ?_⟩
  · -- At `w` the matrix is block diagonal with the blocks `A_w` and `B_w`.
    simp [fromBlocks_map, fromBlocks_conjTranspose, fromBlocks_multiply,
      hA.conjTranspose_map_mul_map w, hB.conjTranspose_map_mul_map w]
  · -- Each entry is an entry of `A`, an entry of `B`, or zero.
    simp [Sum.forall, hA.snd_mem_Ô, hB.snd_mem_Ô]

/-- If `B = A.submatrix id e * C`, that is, the matrix of the columns `e j` of `A` times `C`, where
`e` is injective, and `A` and `C` are orthonormal at infinity and integral, then so is `B`. -/
lemma of_eq_submatrix_mul_of_injective {C : Matrix p q (𝔸 E)} (e : p → n)
    (h_injective : e.Injective) (hC : IsOrthoIntegral C) {B : Matrix m q (𝔸 E)}
    (h_eq : B = A.submatrix id e * C) : IsOrthoIntegral B := by
  -- Selecting distinct columns of `A` keeps them orthonormal and integral: at `w` the Gram matrix
  -- of the chosen columns is the `(e, e)` block of that of `A`, which is `1` as `e` is injective.
  have h_cols : IsOrthoIntegral (A.submatrix id e) := by
    refine ⟨fun w ↦ ?_, fun i j ↦ hA.snd_mem_Ô i (e j)⟩
    rw [← submatrix_map, conjTranspose_submatrix, ← submatrix_mul _ _ e id e Function.bijective_id,
      hA.conjTranspose_map_mul_map w, submatrix_one e h_injective]
  subst h_eq
  exact h_cols.mul hC

/-- `of_eq_submatrix_mul_of_injective`, where `simp` proves that `e` is injective when `he` is not
given. -/
lemma of_eq_submatrix_mul {C : Matrix p q (𝔸 E)} (e : p → n) (hC : IsOrthoIntegral C)
    {B : Matrix m q (𝔸 E)} (h_eq : B = A.submatrix id e * C)
    (he : e.Injective := by simp [Function.Injective]) : IsOrthoIntegral B :=
  hA.of_eq_submatrix_mul_of_injective e he hC h_eq

end

end Exchange.IsOrthoIntegral

end New

/-! ## Splitting along isotropic subspaces: Levi and unipotent parts -/

section Splitting

namespace New

open NumberField Matrix WeilData Exchange Fintype G Function

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {n n₁ : Type*} [Fintype n]
  [DecidableEq n] {s : n → ℤˣ} (g : G E s)

/-- An element `g` of the adelic unitary group preserves the standard form: `gᴴ S g = S`, with
`S = stdForm E s`. -/
lemma G.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix :
    g.adeleMatrixᴴ * stdForm E s * g.adeleMatrix = stdForm E s := g.toUnitary.prop

omit [IsCMField E] in
/-- The standard form `S = stdForm E s` is its own inverse: `S (S a) = a`. -/
@[simp]
lemma stdForm_mul_stdForm_mul (a : Matrix n n₁ (𝔸 E)) : stdForm E s * (stdForm E s * a) = a := by
  simp [← Matrix.mul_assoc]

/-- The inverse of `g` has the matrix `S gᴴ S`, with `S = stdForm E s`. -/
lemma G.adeleMatrix_inv : g⁻¹.adeleMatrix = stdForm E s * g.adeleMatrixᴴ * stdForm E s :=
  U.coe_inv (by simp) g.toUnitary

end

variable {E : Type*} [Field E] [CMType E] {n n₁ : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ} (g : G E s) {V₁ : Space E n₁ s₁} (V : Space E n s)

/-- For a matrix `i` over `E`, its adelic form `V.ratMap V₁ i = x⁻¹ i x₁`, with `x`, `x₁` the adelic
frames of `V`, `V₁`, sends the adelic vector `x₁⁻¹ y` of a rational vector `y` to the adelic
vector `x⁻¹ (i y)`. -/
lemma Space.ratMap_mulVec_vecAtPoint (i : Matrix n n₁ E) (y : n₁ → E) :
    V.ratMap V₁ i *ᵥ V₁.vecAtPoint y = V.vecAtPoint (i *ᵥ y) := by
  simp [ratMap, vecAtPoint, comp_def, RingHom.map_mulVec]

/-- For matrices `A`, `B` over `E`, the Gram matrix of `x⁻¹ A` and `x⁻¹ B` for the standard form is
the adelic image of the Gram matrix `Aᴴ J B` of `V`; here `x` is the adelic frame of `V`. -/
lemma Space.gram_at_point_eq_map {a b : Type*} (A : Matrix n a E) (B : Matrix n b E) :
    (V.x⁻¹.val * A.map toAdele)ᴴ * stdForm E s * (V.x⁻¹.val * B.map toAdele) =
      (Aᴴ * V.J * B).map toAdele := by
  simp [map_J, Matrix.mul_assoc]

/-- A Gram matrix `Aᴴ J B` of `V`, mapped to the adeles, in the right-bracketed form of a product
of the mapped factors. -/
private lemma Space.map_conjTranspose_mul_map_J_mul_map {a b : Type*} (A : Matrix n a E)
    (B : Matrix n b E) :
    Aᴴ.map toAdele * (V.J.map toAdele * B.map toAdele) = (Aᴴ * V.J * B).map toAdele := by
  simp [Matrix.mul_assoc]

/-- `Space.map_conjTranspose_mul_map_J_mul_map` followed by a further factor `X`. -/
private lemma Space.map_conjTranspose_mul_map_J_mul_map_mul {a b c : Type*} [Fintype b]
    (A : Matrix n a E) (B : Matrix n b E) (X : Matrix b c (𝔸 E)) :
    Aᴴ.map toAdele * (V.J.map toAdele * (B.map toAdele * X)) = (Aᴴ * V.J * B).map toAdele * X := by
  simp [Matrix.mul_assoc]

variable [WeilData E] {n₀ p q : Type*} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p]
  {s₀ : n₀ → ℤˣ} (V₀ : Space E n₀ s₀)

/-! ### Splittings -/

/-- A Witt decomposition `V = (l E^p ⊕ k E^p) ⊥ i V₀` over `E`: isotropic frames `l`, `k` with
`lᴴ J k = 1`, an isometry `i` from `V₀` orthogonal to both, and `rk V = rk V₀ + 2 p`. -/
structure Space.Splitting (p : Type*) [Fintype p] [DecidableEq p] where
  /-- The frame k, whose columns span one isotropic subspace. -/
  k : Matrix n p E
  /-- The frame l, whose columns span the dual isotropic subspace. -/
  l : Matrix n p E
  /-- The matrix i of the embedding of V₀ into V. -/
  i : Matrix n n₀ E
  /-- `k` is isotropic: `kᴴ J k = 0`. -/
  gram_kk : kᴴ * V.J * k = 0
  /-- `l` is isotropic: `lᴴ J l = 0`. -/
  gram_ll : lᴴ * V.J * l = 0
  /-- `l` and `k` are dual: `lᴴ J k = 1`. -/
  gram_lk : lᴴ * V.J * k = 1
  /-- `i` is an isometry: `iᴴ J i` is the Gram matrix `V₀.J` of `V₀`. -/
  gram_ii : iᴴ * V.J * i = V₀.J
  /-- The image of i is orthogonal to k. -/
  gram_ik : iᴴ * V.J * k = 0
  /-- The image of i is orthogonal to l. -/
  gram_il : iᴴ * V.J * l = 0
  /-- The rank of V is the rank of V₀ plus twice the number of columns of k. -/
  protected card_eq : card n = card n₀ + 2 * card p

variable (p) in
/-- The orthogonal sum of hyperbolic space of rank 2p and V₀. -/
def Exchange.hyperbolicSum : Space E ((p ⊕ p) ⊕ n₀) (hyperbolicSigns p ⊕ᵥ s₀) :=
  (hyperbolicSpace E p).sum V₀

variable {V V₀}

/-- The splitting of `V` over `V₀` whose frames `l`, `k` and embedding `i` are the three column
blocks of a matrix `M` over `E`, given that `Mᴴ J M` is the Gram matrix of hyperbolic space plus
`V₀` (the hypothesis `h_gram`) and that the ranks agree (the hypothesis `h_card`). -/
def Exchange.splittingOfGram (M : Matrix n ((p ⊕ p) ⊕ n₀) E)
    (h_gram : Mᴴ * V.J * M = (hyperbolicSum p V₀).J) (h_card : card n = card n₀ + 2 * card p) :
    V.Splitting V₀ p where
  k := M.toCols₁.toCols₂
  l := M.toCols₁.toCols₁
  i := M.toCols₂
  -- Each relation is a block of the Gram matrix `h_gram`.
  gram_kk := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_ll := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_lk := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_ii := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_ik := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  gram_il := Matrix.ext fun _ _ ↦ congrFun₂ h_gram _ _
  card_eq := h_card

end New

namespace New

open NumberField Matrix WeilData Exchange Fintype G Function

variable {E : Type*} [Field E] [CMType E] {n n₁ : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  [Fintype n₁] [DecidableEq n₁] {s₁ : n₁ → ℤˣ} {g : G E s} {V₁ : Space E n₁ s₁} {V : Space E n s}
  [WeilData E] {n₀ p q : Type*} [Fintype n₀] [DecidableEq n₀] [Fintype p] [DecidableEq p]
  {s₀ : n₀ → ℤˣ} {V₀ : Space E n₀ s₀} (D : V.Splitting V₀ p) {a : Matrix p p (𝔸 E)}
  (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E))

namespace Space.Splitting

/-! ### Adelic frames and dual coordinates -/

/-- For a splitting of V, the adelic n×p matrix x⁻¹k, x the adelic frame of V: the isotropic
frame k in standard coordinates. -/
def kAdelic : Matrix n p (𝔸 E) := V.x⁻¹.val * D.k.map toAdele

/-- For a splitting of V, the adelic n×p matrix x⁻¹l, x the adelic frame of V: the isotropic
frame l in standard coordinates. -/
def lAdelic : Matrix n p (𝔸 E) := V.x⁻¹.val * D.l.map toAdele

/-- For a splitting of V over V₀, the adelic matrix ι = x⁻¹ i x₀, with x, x₀ the adelic frames:
the embedding i in standard coordinates. -/
def iAdelic : Matrix n n₀ (𝔸 E) := V.ratMap V₀ D.i

section

omit [WeilData E]

lemma gram_kl : D.kᴴ * V.J * D.l = 1 := by
  rw [V.conjTranspose_mul_J_mul_swap, D.gram_lk, conjTranspose_one]

lemma gram_ki : D.kᴴ * V.J * D.i = 0 := by
  rw [V.conjTranspose_mul_J_mul_swap, D.gram_ik, conjTranspose_zero]

/-- The splitting of V obtained from a given one by exchanging the two isotropic frames k and l
and keeping the embedding i. -/
def symm : V.Splitting V₀ p where
  k := D.l
  l := D.k
  i := D.i
  gram_kk := D.gram_ll
  gram_ll := D.gram_kk
  gram_lk := D.gram_kl
  gram_ii := D.gram_ii
  gram_ik := D.gram_il
  gram_il := D.gram_ik
  card_eq := D.card_eq

lemma gram_li : D.lᴴ * V.J * D.i = 0 := by
  rw [V.conjTranspose_mul_J_mul_swap, D.gram_il, conjTranspose_zero]

end

attribute [simp high] gram_kk gram_ll gram_lk gram_kl gram_ii gram_ik gram_il gram_ki gram_li

/-- For a splitting, the adelic `p × n` matrix `lAdelicᴴ ε`, with `ε = stdForm E s`; it sends
`lAdelic a + iAdelic w + kAdelic b` to `b`. -/
def kCoord : Matrix p n (𝔸 E) := D.lAdelicᴴ * stdForm E s

/-- For a splitting, the adelic `n₀ × n` matrix `ε₀ iAdelicᴴ ε`, the adjoint of the adelic embedding
`iAdelic` for the standard forms `ε`, `ε₀` of `V`, `V₀`; it sends
`lAdelic a + iAdelic w + kAdelic b` to `w`. -/
def iCoord : Matrix n₀ n (𝔸 E) := stdForm E s₀ * D.iAdelicᴴ * stdForm E s

/-- For a splitting, the adelic `p × n` matrix `kAdelicᴴ ε`, with `ε = stdForm E s`; it sends
`lAdelic a + iAdelic w + kAdelic b` to `a`. -/
def lCoord : Matrix p n (𝔸 E) := D.kAdelicᴴ * stdForm E s

-- The coordinates are dual to the frames: each product is the adelic image of a Gram matrix
-- `Aᴴ J B` of two of `k`, `l`, `i` (`Space.gram_at_point_eq_map`), which a relation of `D` gives.
-- For `iCoord`, the frame `x₀` of `V₀` and the standard form `ε₀` of `V₀` stand on the left;
-- then `x₀ᴴ J₀ x₀ = ε₀` and `ε₀ ε₀ = 1`.

section

omit [WeilData E]

lemma kCoord_mul_kAdelic : D.kCoord * D.kAdelic = 1 := by
  simpa [kCoord, lAdelic, kAdelic, D.gram_lk] using V.gram_at_point_eq_map D.l D.k

lemma kCoord_mul_lAdelic : D.kCoord * D.lAdelic = 0 := by
  simpa [kCoord, lAdelic, D.gram_ll] using V.gram_at_point_eq_map D.l D.l

lemma kCoord_mul_iAdelic : D.kCoord * D.iAdelic = 0 := by
  rw [kCoord, lAdelic, iAdelic, ratMap, ← Matrix.mul_assoc, V.gram_at_point_eq_map, D.gram_li]
  simp

lemma lCoord_mul_kAdelic : D.lCoord * D.kAdelic = 0 := by
  simpa [lCoord, kAdelic, D.gram_kk] using V.gram_at_point_eq_map D.k D.k

lemma lCoord_mul_lAdelic : D.lCoord * D.lAdelic = 1 := by
  simpa [lCoord, kAdelic, lAdelic, D.gram_kl] using V.gram_at_point_eq_map D.k D.l

lemma lCoord_mul_iAdelic : D.lCoord * D.iAdelic = 0 := by
  rw [lCoord, kAdelic, iAdelic, ratMap, ← Matrix.mul_assoc, V.gram_at_point_eq_map, D.gram_ki]
  simp

lemma iCoord_mul_kAdelic : D.iCoord * D.kAdelic = 0 := by
  simp [iCoord, kAdelic, iAdelic, ratMap, ← V.gram_point, conjTranspose_nonsing_inv,
    Matrix.mul_assoc, V.map_conjTranspose_mul_map_J_mul_map]

lemma iCoord_mul_lAdelic : D.iCoord * D.lAdelic = 0 := by
  simp [iCoord, lAdelic, iAdelic, ratMap, ← V.gram_point, conjTranspose_nonsing_inv,
    Matrix.mul_assoc, V.map_conjTranspose_mul_map_J_mul_map]

lemma iCoord_mul_iAdelic : D.iCoord * D.iAdelic = 1 := by
  have h_point₀ : V₀.x.valᴴ * (V₀.J.map toAdele * V₀.x.val) = stdForm E s₀ := by
    rw [← Matrix.mul_assoc, V₀.gram_point]
  simp [iCoord, iAdelic, ratMap, ← V.gram_point, conjTranspose_nonsing_inv, Matrix.mul_assoc,
    V.map_conjTranspose_mul_map_J_mul_map_mul, h_point₀]

/-- For a splitting, the three coordinate matrices along k, l and V₀ are dual to the adelic frames
k, l, ι: each times its own frame is the identity, and times either other frame is zero. -/
@[simp]
lemma coord_mul_frame :
    (D.kCoord * D.kAdelic = 1 ∧ D.kCoord * D.lAdelic = 0 ∧ D.kCoord * D.iAdelic = 0) ∧
    (D.lCoord * D.kAdelic = 0 ∧ D.lCoord * D.lAdelic = 1 ∧ D.lCoord * D.iAdelic = 0) ∧
    D.iCoord * D.kAdelic = 0 ∧ D.iCoord * D.lAdelic = 0 ∧ D.iCoord * D.iAdelic = 1 :=
  ⟨⟨D.kCoord_mul_kAdelic, D.kCoord_mul_lAdelic, D.kCoord_mul_iAdelic⟩,
    ⟨D.lCoord_mul_kAdelic, D.lCoord_mul_lAdelic, D.lCoord_mul_iAdelic⟩,
    D.iCoord_mul_kAdelic, D.iCoord_mul_lAdelic, D.iCoord_mul_iAdelic⟩

lemma conjTranspose_kCoord : D.kCoordᴴ = stdForm E s * D.lAdelic := by simp [kCoord]

lemma conjTranspose_lCoord : D.lCoordᴴ = stdForm E s * D.kAdelic := by simp [lCoord]

lemma conjTranspose_iCoord : D.iCoordᴴ = stdForm E s * D.iAdelic * stdForm E s₀ := by
  simp [iCoord, Matrix.mul_assoc]

end

omit [WeilData E] in
/-- The adjoints of the three coordinate matrices, written through the adelic frames and the
standard forms. -/
@[local simp]
lemma conjTranspose_coord :
    D.kCoordᴴ = stdForm E s * D.lAdelic ∧
    D.lCoordᴴ = stdForm E s * D.kAdelic ∧
    D.iCoordᴴ = stdForm E s * D.iAdelic * stdForm E s₀ :=
  ⟨D.conjTranspose_kCoord, D.conjTranspose_lCoord, D.conjTranspose_iCoord⟩

-- The relations above followed by a further factor `X`, in the right-bracketed form that `simp`
-- meets: a coordinate matrix applied to a combination of the columns of one frame gives its
-- coefficients.

section

omit [WeilData E]

lemma kCoord_mul_kAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.kCoord * (D.kAdelic * X) = X := by simp [← Matrix.mul_assoc, D.kCoord_mul_kAdelic]

lemma iCoord_mul_kAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.iCoord * (D.kAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.iCoord_mul_kAdelic]

lemma lCoord_mul_kAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.lCoord * (D.kAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.lCoord_mul_kAdelic]

lemma kCoord_mul_lAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.kCoord * (D.lAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.kCoord_mul_lAdelic]

lemma iCoord_mul_lAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.iCoord * (D.lAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.iCoord_mul_lAdelic]

lemma lCoord_mul_lAdelic_mul {m : Type*} (X : Matrix p m (𝔸 E)) :
    D.lCoord * (D.lAdelic * X) = X := by simp [← Matrix.mul_assoc, D.lCoord_mul_lAdelic]

lemma kCoord_mul_iAdelic_mul {m : Type*} (X : Matrix n₀ m (𝔸 E)) :
    D.kCoord * (D.iAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.kCoord_mul_iAdelic]

lemma iCoord_mul_iAdelic_mul {m : Type*} (X : Matrix n₀ m (𝔸 E)) :
    D.iCoord * (D.iAdelic * X) = X := by simp [← Matrix.mul_assoc, D.iCoord_mul_iAdelic]

lemma lCoord_mul_iAdelic_mul {m : Type*} (X : Matrix n₀ m (𝔸 E)) :
    D.lCoord * (D.iAdelic * X) = 0 := by simp [← Matrix.mul_assoc, D.lCoord_mul_iAdelic]

-- The pairings of the frames with the standard form are coordinate matrices.

/-- Pairing with `kAdelic` under the standard form is the `l`-coordinate matrix. -/
lemma conjTranspose_kAdelic_mul_stdForm_mul {m : Type*} (X : Matrix n m (𝔸 E)) :
    D.kAdelicᴴ * (stdForm E s * X) = D.lCoord * X := by rw [lCoord, Matrix.mul_assoc]

/-- Pairing with `lAdelic` under the standard form is the `k`-coordinate matrix. -/
lemma conjTranspose_lAdelic_mul_stdForm_mul {m : Type*} (X : Matrix n m (𝔸 E)) :
    D.lAdelicᴴ * (stdForm E s * X) = D.kCoord * X := by rw [kCoord, Matrix.mul_assoc]

/-- Pairing with `iAdelic` under the standard form is the `V₀`-coordinate matrix followed by the
standard form of `V₀`. -/
lemma conjTranspose_iAdelic_mul_stdForm_mul {m : Type*} (X : Matrix n m (𝔸 E)) :
    D.iAdelicᴴ * (stdForm E s * X) = stdForm E s₀ * (D.iCoord * X) := by
  simp [iCoord, ← Matrix.mul_assoc, stdForm_mul_self]

/-- The relations of `New.Space.Splitting.coord_mul_frame` followed by a further factor `X`, in the
right-bracketed form that `simp` meets. The first two groups say that a coordinate matrix applied to
a combination of the columns of one frame gives its coefficients. The last group says that the
pairing with `kAdelic` or `lAdelic` under the standard form is a coordinate matrix, and the pairing
with `iAdelic` is the `V₀` coordinate matrix followed by the standard form of `V₀`. -/
@[simp]
lemma coord_mul_frame_mul {m : Type*} :
    (∀ X : Matrix p m (𝔸 E),
      D.kCoord * (D.kAdelic * X) = X ∧
      D.iCoord * (D.kAdelic * X) = 0 ∧
      D.lCoord * (D.kAdelic * X) = 0 ∧
      D.kCoord * (D.lAdelic * X) = 0 ∧
      D.iCoord * (D.lAdelic * X) = 0 ∧
      D.lCoord * (D.lAdelic * X) = X) ∧
    (∀ X : Matrix n₀ m (𝔸 E),
      D.kCoord * (D.iAdelic * X) = 0 ∧
      D.iCoord * (D.iAdelic * X) = X ∧
      D.lCoord * (D.iAdelic * X) = 0) ∧
    ∀ X : Matrix n m (𝔸 E),
      D.kAdelicᴴ * (stdForm E s * X) = D.lCoord * X ∧
      D.lAdelicᴴ * (stdForm E s * X) = D.kCoord * X ∧
      D.iAdelicᴴ * (stdForm E s * X) = stdForm E s₀ * (D.iCoord * X) :=
  ⟨fun X ↦ ⟨D.kCoord_mul_kAdelic_mul X, D.iCoord_mul_kAdelic_mul X, D.lCoord_mul_kAdelic_mul X,
      D.kCoord_mul_lAdelic_mul X, D.iCoord_mul_lAdelic_mul X, D.lCoord_mul_lAdelic_mul X⟩,
    fun X ↦ ⟨D.kCoord_mul_iAdelic_mul X, D.iCoord_mul_iAdelic_mul X, D.lCoord_mul_iAdelic_mul X⟩,
    fun X ↦ ⟨D.conjTranspose_kAdelic_mul_stdForm_mul X, D.conjTranspose_lAdelic_mul_stdForm_mul X,
      D.conjTranspose_iAdelic_mul_stdForm_mul X⟩⟩

/-- The frames and coordinate matrices of a splitting resolve the identity, so every adelic vector
is the sum of its components along `kAdelic`, `iAdelic` and `lAdelic`. -/
lemma sum_frame_mul_coord_eq_one :
    D.kAdelic * D.kCoord + D.iAdelic * D.iCoord + D.lAdelic * D.lCoord = 1 := by
  -- The block matrices `(kAdelic iAdelic lAdelic)` and `(kCoord; iCoord; lCoord)` have product `1`
  -- in the order coordinates times frames, by `coord_mul_frame`. They are square by `D.card_eq`,
  -- so their product in the other order is `1` too, and that product is the sum in the claim.
  have h_card : card ((p ⊕ n₀) ⊕ p) = card n := by simp +arith [D.card_eq]
  have h_coord_frame : (D.kCoord.fromRows D.iCoord).fromRows D.lCoord *
      (D.kAdelic.fromCols D.iAdelic).fromCols D.lAdelic = 1 := by
    rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
    simp [coord_mul_frame]
  rwa [mul_eq_one_comm_of_card_eq _ _ _ h_card, fromCols_mul_fromRows,
    fromCols_mul_fromRows] at h_coord_frame

/-- `g` acts on the isotropic frame `k` of the splitting by the matrix `c`: `g k = k c` in adelic
coordinates. -/
@[simp]
abbrev ActsOnFrame (g : G E s) (c : Matrix p p (𝔸 E)) : Prop :=
  g.adeleMatrix * D.kAdelic = D.kAdelic * c

/-- If an element `g` of `G E s` acts on the adelic frame `kAdelic` by an invertible `a`
(`g k = k a`), then `g` multiplies the `l`-coordinate by `a⁻ᴴ`: `lCoord g = a⁻ᴴ lCoord`. -/
lemma lCoord_mul_adeleMatrix {a : GL p (𝔸 E)} (hk : D.ActsOnFrame g a.val) :
    D.lCoord * g.adeleMatrix = a⁻¹.valᴴ * D.lCoord := by
  -- As `g k = k a`, the frame `k` is `g k a⁻¹`; take the adjoint and use that `g` preserves the
  -- standard form.
  have h_k : D.kAdelic = g.adeleMatrix * D.kAdelic * a⁻¹.val := by simp [hk]
  calc D.lCoord * g.adeleMatrix
    _ = (g.adeleMatrix * D.kAdelic * a⁻¹.val)ᴴ * stdForm E s * g.adeleMatrix := by
      rw [← h_k, lCoord]
    _ = a⁻¹.valᴴ * D.kAdelicᴴ * (g.adeleMatrixᴴ * stdForm E s * g.adeleMatrix) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = a⁻¹.valᴴ * D.lCoord := by
      rw [g.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix, lCoord, Matrix.mul_assoc]

/-- If an element `g` of `G E s` acts on the adelic frame `kAdelic` by a matrix `a`
(`g k = k a`), then `a` is invertible. -/
lemma ActsOnFrame.isUnit (hk : D.ActsOnFrame g a) : IsUnit a := by
  -- `kCoord g⁻¹ k` is a left inverse of `a`: `kCoord g⁻¹ k a = kCoord g⁻¹ g k = kCoord k = 1`.
  have h_left_inv : D.kCoord * g.adeleMatrix⁻¹ * D.kAdelic * a = 1 := by
    rw [Matrix.mul_assoc, ← hk, Matrix.mul_assoc]
    simp [adeleMatrix, coord_mul_frame]
  exact .of_mul_eq_one_right _ h_left_inv

end

/-! ### The Levi subgroup, and composition of splittings -/

/-- The Levi homomorphism `GL_p(𝔸) × G(V₀) → G(V)` of a splitting. The pair `(m, g₀)` goes to the
element that sends the frame `k` to `k m`, the embedded copy `ι` of `V₀` to `ι g₀` and the frame `l`
to `l (m⁻¹)ᴴ`; its matrix is `k m kCoord + ι g₀ iCoord + l (m⁻¹)ᴴ lCoord`. -/
@[local simp]
def levi : GL p (𝔸 E) × G E s₀ →* G E s :=
  MonoidHom.mk'
    (fun x ↦ ofMatrix
      (D.kAdelic * x.fst.val * D.kCoord + D.iAdelic * x.snd.adeleMatrix * D.iCoord +
        D.lAdelic * (x.fst⁻¹).valᴴ * D.lCoord) <| by
      -- The matrix preserves the form: after the cross terms vanish, `sum_frame_mul_coord_eq_one`
      -- is left.
      simp [← Matrix.mul_assoc, conjTranspose_nonsing_inv, Matrix.add_mul, Matrix.mul_add]
      simp [↓conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix, Matrix.mul_assoc,
        eq_sub_of_add_eq' D.sum_frame_mul_coord_eq_one, Matrix.mul_sub, Matrix.mul_add])
    fun x y ↦ ext_adeleMatrix <| by
      simp [Matrix.mul_assoc, conjTranspose_nonsing_inv, Matrix.mul_add, Matrix.add_mul]

section

omit [WeilData E]

/-- The Levi element of `(a, g)` sends the adelic frame `l` to `l (a⁻¹)ᴴ`. -/
lemma levi_mul_lAdelic (a : GL p (𝔸 E)) (g : G E s₀) :
    (D.levi (a, g)).adeleMatrix * D.lAdelic = D.lAdelic * a⁻¹.valᴴ := by
  simp [Matrix.mul_assoc, Matrix.add_mul]

/-- The Levi element of `(a, g)` sends the embedded copy `ι` of `V₀` to `ι g`. -/
lemma levi_mul_iAdelic (a : GL p (𝔸 E)) (g : G E s₀) :
    (D.levi (a, g)).adeleMatrix * D.iAdelic = D.iAdelic * g.adeleMatrix := by
  simp [Matrix.mul_assoc, Matrix.add_mul]

/-- The Levi element of `(a, g)` acts on the adelic frame `k` by `a`. -/
lemma actsOnFrame_levi (a : GL p (𝔸 E)) (g : G E s₀) : D.ActsOnFrame (D.levi (a, g)) a.val := by
  simp [Matrix.mul_assoc, Matrix.add_mul]

end

/-- Composition of splittings. From a splitting `D` of `V` over `V₀` with frames of `p` columns and
a splitting `D'` of `V₀` over `V₁` with frames of `q` columns, the splitting of `V` over `V₁` with
frames `(k, i k')` and `(l, i l')` and embedding `i i'`. -/
def comp [Fintype q] [DecidableEq q] (D' : V₀.Splitting V₁ q) : V.Splitting V₁ (p ⊕ q) := by
  -- The frames are `k := (k, i k')`, `l := (l, i l')` and `i := i i'`. Each Gram matrix splits
  -- into blocks, which reduce to the relations of `D` and of `D'`; they become visible by
  -- bracketing the products to the left, then to the right.
  use D.k.fromCols (D.i * D'.k), D.l.fromCols (D.i * D'.l), D.i * D'.i <;>
    simp +arith [D.card_eq, D'.card_eq, ← Matrix.mul_assoc,
      conjTranspose_fromCols_eq_fromRows_conjTranspose] <;>
    simp [Matrix.mul_assoc]

/-- The three frames `l`, `k`, `i` of a splitting, side by side in one matrix `M`, have the Gram
matrix of the orthogonal sum of hyperbolic space of rank `2 p` and `V₀`. -/
lemma gram_eq_hyperbolicSum :
    let M : Matrix n ((p ⊕ p) ⊕ n₀) E := (D.l.fromCols D.k).fromCols D.i
    Mᴴ * V.J * M = (hyperbolicSum p V₀).J := by
  -- Block by block, this is one of the relations `gram_ll`, `gram_lk`, ... of the splitting.
  aesop (add simp [conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.mul_assoc])

/-! ### The unipotent radical and the Levi decomposition -/

/-- The unipotent element of `G` with parameters an adelic `n₀ × p` matrix `c` and an adelic `p × p`
matrix `b`. It fixes the frame `k`, sends the embedded copy `ι` of `V₀` to `ι + k cᴴ ε₀` and
the frame `l` to `l − ι c − k (½ j⁻¹ (b + bᴴ) + ½ cᴴ ε₀ c)`, where `ε₀` is the standard form of `V₀`
and `j` the purely imaginary element of the Weil data. Only the hermitian part `z = ½ (b + bᴴ)` of
`b` enters: in the basis `(k, ι, l)` the matrix has the rows `(1, c*, −j⁻¹ z − ½ c* c)`,
`(0, 1, −c)`, `(0, 0, 1)`, with `c* = cᴴ ε₀` the adjoint of `c` for the form of `V₀`. -/
@[local simp]
def radicalElement : G E s :=
  ofMatrix
      (1 - D.iAdelic * c * D.lCoord + D.kAdelic * (cᴴ * stdForm E s₀) * D.iCoord -
        D.kAdelic * (toAdele (2⁻¹ : E) • (toAdele (j⁻¹ : E) • (b + bᴴ) + cᴴ * stdForm E s₀ * c)) *
          D.lCoord) <| by
    -- The matrix preserves the form: the terms in `b + bᴴ` cancel as `star j = -j`, those in
    -- `cᴴ * c` as `2⁻¹ + 2⁻¹ = 1`.
    simp [↓coord_mul_frame_mul, iCoord, lCoord, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul,
      Matrix.sub_mul, Matrix.mul_sub]
    match_scalars <;> grind

/-- The unipotent element `radicalElement c b` depends continuously on the pair `(c, b)`. -/
@[fun_prop]
lemma continuous_radicalElement :
    Continuous fun q : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E) ↦ D.radicalElement q.fst q.snd := by
  -- The matrix of `radicalElement c b` is a polynomial expression in the entries of `c` and `b` and
  -- their conjugates.
  simp only [G.continuous_iff, radicalElement, adeleMatrix_ofMatrix]
  fun_prop

/-- The unipotent element `radicalElement c b` fixes the adelic frame `k`. -/
lemma actsOnFrame_radicalElement : D.ActsOnFrame (D.radicalElement c b) 1 := by
  simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul]

/-- The unipotent element `radicalElement c b` sends the embedded copy `ι` of `V₀` to `ι + k cᴴ ε₀`,
where `ε₀` is the standard form of `V₀`. -/
lemma radicalElement_mul_iAdelic :
    (D.radicalElement c b).adeleMatrix * D.iAdelic =
      D.iAdelic + D.kAdelic * (cᴴ * stdForm E s₀) := by
  simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul]

/-- The Heisenberg group law of the unipotent elements: the parameters `c` add, and the parameters
`b` add with the extra term `j cᴴ ε₀ c'`, where `ε₀` is the standard form of `V₀` and `j` the purely
imaginary element of the Weil data. -/
@[local simp↓]
lemma radicalElement_mul (c' : Matrix n₀ p (𝔸 E)) (b' : Matrix p p (𝔸 E)) :
    D.radicalElement c b * D.radicalElement c' b' =
      D.radicalElement (c + c') (b + toAdele (j : E) • cᴴ * stdForm E s₀ * c' + b') := by
  refine ext_adeleMatrix ?_
  -- Expand both sides in the frames and coordinates, then compare the scalar coefficients of each
  -- term.
  simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
  match_scalars <;> grind

lemma radicalElement_inv : (D.radicalElement c b)⁻¹ = D.radicalElement (-c) (-b) :=
  inv_eq_of_mul_eq_one_right (ext_adeleMatrix (by simp [Matrix.mul_assoc]))

/-- Conjugation by the Levi element of `(a, g)` sends `radicalElement c b` to
`radicalElement (g c aᴴ) (a b aᴴ)`. -/
lemma levi_conj_radicalElement (a : GL p (𝔸 E)) (g : G E s₀) :
    D.levi (a, g) * D.radicalElement c b =
      D.radicalElement (g.adeleMatrix * c * a.valᴴ) (a.val * b * a.valᴴ) * D.levi (a, g) := by
  refine ext_adeleMatrix ?_
  -- Both sides expand to the same sum of products of frames and coordinates.
  simp [adeleMatrix, ofMatrix, ← U.form_mul_inv_eq, Matrix.mul_assoc, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, conjTranspose_nonsing_inv]
  abel

/-- Every `radicalElement c b` is a commutator of a Levi element `m = levi (a, 1)` with a unipotent
element `u = radicalElement c b'`: `m * u = u * radicalElement c b * m`. -/
lemma exists_levi_mul_radicalElement_eq :
    ∃ (a : GL p (𝔸 E)) (b' : Matrix p p (𝔸 E)),
      D.levi (a, 1) * D.radicalElement c b' =
        D.radicalElement c b' * D.radicalElement c b * D.levi (a, 1) := by
  -- Conjugation by the scalar `2` sends `(c, b')` to `(2 c, 4 b')`, and
  -- `radicalElement c b' * radicalElement c b` is `radicalElement (2 c) (b' + b)` (the correction
  -- term of `radicalElement_mul` has hermitian part zero, as `star j = -j`); so take `b' = b / 3`.
  let two : GL p (𝔸 E) := .mkOfMulEqOne (1 + 1) (toAdele (2⁻¹ : E) • 1) <| by
    simp [← add_smul, ← map_add, ← two_mul (2⁻¹ : E)]
  refine ⟨two, toAdele (3⁻¹ : E) • b, ?_⟩
  rw [levi_conj_radicalElement, radicalElement_mul]
  -- Both sides are a unipotent element times `levi (two, 1)`; compare the unipotent factors.
  congr 1
  refine ext_adeleMatrix ?_
  -- Expand both matrices and compare the scalar coefficients of each term.
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, two]
  match_scalars <;> norm_num [mul_two, ← map_add, ← map_mul] <;> ring_nf

/-- For two unipotent elements, the first with `c = 0`, the product adds the parameters `b`. -/
lemma radicalElement_zero_mul (b' : Matrix p p (𝔸 E)) :
    D.radicalElement 0 b * D.radicalElement c b' = D.radicalElement c (b + b') := by
  simp [Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]

omit [WeilData E] in
/-- Two adelic `n × n` matrices are equal when they agree on each of the three adelic frames `k`,
`i` and `l` of a splitting. -/
private lemma eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic {M N : Matrix n n (𝔸 E)}
    (h_k : M * D.kAdelic = N * D.kAdelic) (h_i : M * D.iAdelic = N * D.iAdelic)
    (h_l : M * D.lAdelic = N * D.lAdelic) : M = N := by
  -- Multiply both by `1`, written as `k kCoord + i iCoord + l lCoord`.
  rw [← M.mul_one, ← N.mul_one, ← D.sum_frame_mul_coord_eq_one]
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, h_k, h_i, h_l]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Levi decomposition of the stabiliser of `range k`. Let `g` in `G` act on the adelic frame `k` by
an adelic `p × p` matrix `a`, that is `g k = k a`. Then `g = radicalElement c b * levi (t, g₀)` for
some parameters `c`, `b`, where `t` in `GL_p(𝔸)` has matrix `a` and `g₀` in `G(V₀)` has as matrix
the `V₀`-block `iCoord * g * iAdelic` of `g`. -/
lemma exists_eq_radicalElement_mul_levi (hk : D.ActsOnFrame g a) :
    ∃ (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E)) (t : GL p (𝔸 E)) (g₀ : G E s₀),
      g = D.radicalElement c b * D.levi (t, g₀) ∧
      t.val = a ∧
      g₀.adeleMatrix = D.iCoord * (g.adeleMatrix * D.iAdelic) := by
  -- Expand `g` in the frames `k`, `i`, `l`; the relations saying that `g` preserves the form then
  -- identify it with `radicalElement c b * levi (a, g₀)`.
  obtain ⟨a, rfl⟩ : ∃ u : GL p (𝔸 E), u.val = a := hk.isUnit
  obtain ⟨X, Y, hg⟩ : ∃ (X : Matrix p n (𝔸 E)) (Y : Matrix n₀ n (𝔸 E)),
      g.adeleMatrix = D.kAdelic * X + D.iAdelic * Y + D.lAdelic * (a.valᴴ⁻¹ * D.lCoord) := by
    refine ⟨D.kCoord * g.adeleMatrix, D.iCoord * g.adeleMatrix, ?_⟩
    -- Resolve the identity; the `l`-component of `g` is known from `lCoord_mul_adeleMatrix`.
    conv_lhs => rw [← g.adeleMatrix.one_mul, ← D.sum_frame_mul_coord_eq_one]
    simp [D.lCoord_mul_adeleMatrix hk, Matrix.add_mul, Matrix.mul_assoc, conjTranspose_nonsing_inv]
  -- `g` preserves the form; we use this on the columns `i` and `l`.
  have h_pres : g.adeleMatrixᴴ * stdForm E s * g.adeleMatrix = stdForm E s :=
    g.conjTranspose_adeleMatrix_mul_stdForm_mul_adeleMatrix
  have h_form_i : Yᴴ * (stdForm E s₀ * (Y * D.iAdelic)) =
      stdForm E s * D.iAdelic - stdForm E s * (D.kAdelic * (a.val⁻¹ * (X * D.iAdelic))) := by
    simpa [hg, ← eq_sub_iff_add_eq', Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add,
      conjTranspose_nonsing_inv] using congrArg (· * D.iAdelic) h_pres
  have h_form_l : Xᴴ * a.valᴴ⁻¹ = stdForm E s * D.lAdelic -
      (stdForm E s * (D.kAdelic * (a.val⁻¹ * (X * D.lAdelic))) +
        Yᴴ * (stdForm E s₀ * (Y * D.lAdelic))) := by
    simpa [hg, ← eq_sub_iff_add_eq', Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add,
      conjTranspose_nonsing_inv] using congrArg (· * D.lAdelic) h_pres
  let g₀ : G E s₀ :=
    ofMatrix (Y * D.iAdelic) (by simp [h_form_i, Matrix.mul_assoc, Matrix.mul_sub])
  refine ⟨-Y * D.lAdelic * a.valᴴ, -toAdele (j : E) • X * D.lAdelic * a.valᴴ, a, g₀,
    ext_adeleMatrix ?_, rfl, ?_⟩
  · -- Compare both sides on the frames `k`, `i` and `l`.
    refine D.eq_of_mul_kAdelic_of_mul_iAdelic_of_mul_lAdelic ?_ ?_ ?_
    · -- On `k` both act by `a`.
      simp [hk, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul]
    · -- On `i`: by `h_form_i`, the `k`-part of the right side is `X i`, as on the left.
      simp [hg, g₀, h_form_i, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
        Matrix.mul_sub]
      abel
    · -- On `l`: `h_form_l` removes `Xᴴ`, which enters the right side through `bᴴ`.
      simp [hg, g₀, h_form_l, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
        Matrix.mul_sub, conjTranspose_nonsing_inv]
      -- The coefficients of `k X l` and `k a lᴴ Yᴴ ε₀ Y l` agree as `j⁻¹ j = 1` and
      -- `2⁻¹ + 2⁻¹ = 1`.
      match_scalars <;> grind
  · -- The matrix of `g₀` is the `V₀`-block of `g`.
    simp [g₀, hg, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_add]

/-- The unipotent radical of the stabiliser of `A = range k` consists of the `radicalElement c b`:
an element `g` of the adelic unitary group of `V` is of this form exactly when it fixes the frame
`k` and acts as the identity on `A^⊥ / A`, that is, its `V₀`-block `iCoord * g * iAdelic` is `1`. -/
lemma exists_eq_radicalElement_iff :
    (∃ (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E)), g = D.radicalElement c b) ↔
      D.ActsOnFrame g 1 ∧ D.iCoord * (g.adeleMatrix * D.iAdelic) = 1 := by
  constructor
  · rintro ⟨c, b, rfl⟩
    exact ⟨D.actsOnFrame_radicalElement c b, by
      simp [↓radicalElement_mul_iAdelic, Matrix.mul_add]⟩
  · -- In the Levi decomposition of `g` both components of the Levi factor are `1`.
    rintro ⟨hk, hi⟩
    obtain ⟨c, b, t, g₀, hg, ht, hg₀⟩ := D.exists_eq_radicalElement_mul_levi hk
    obtain rfl : t = 1 := Units.ext ht
    obtain rfl : g₀ = 1 := ext_adeleMatrix (by rw [hg₀, hi, G.adeleMatrix_one])
    exact ⟨c, b, by rw [hg, Prod.mk_one_one, map_one, mul_one]⟩

/-! ### The law of the mixed model, and adapted points -/

/-- The law of a mixed Schrödinger model, for maps `T x : 𝒮 V → 𝒮 V₀` with `x` in `𝔸^p`. Write
`y = l a + ι w + k b`, so `a = lCoord y`, `w = iCoord y`, `b = kCoord y`. Then
`T x (ϱ y f) = β (2 x + a) b • ϱ w (T (x + a) f)`, with `β` the bicharacter of
`adelicHeisenberg E 1`: the `l`-part translates `x`, the `k`-part multiplies by a character, and the
`V₀`-part acts on the values. Here `𝒮 V` is the space of the Schrödinger model of `V`, and `V.ϱ y`
is the operator on it of the adelic vector `y`. In the code `2 x + a` is written `x + (x + a)`. -/
abbrev IsMixedLaw (T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀) : Prop :=
  ∀ (x : p → 𝔸 E) (y : n → 𝔸 E) (f : 𝒮 V),
    T x (V.ϱ y f) =
      -- `x + (x + a)` is the sum of the old and the new argument of `T`, where `a = D.lCoord *ᵥ y`
      (adelicHeisenberg E 1).β (x + (x + D.lCoord *ᵥ y)) (D.kCoord *ᵥ y) •
        V₀.ϱ (D.iCoord *ᵥ y) (T (x + D.lCoord *ᵥ y) f)

variable {D} in
/-- If the family `T` obeys the law of a mixed model, then translating by a vector `l c` along the
isotropic frame `l` of the splitting shifts the argument of `T` by `c`. -/
lemma IsMixedLaw.apply_rho_lAdelic_mulVec {T : (p → 𝔸 E) → 𝒮 V →L[ℂ] 𝒮 V₀} (hT : D.IsMixedLaw T)
    (x c : p → 𝔸 E) (f : 𝒮 V) : T x (V.ϱ (D.lAdelic *ᵥ c) f) = T (x + c) f := by
  -- The `k`- and `V₀`-coordinates of `l c` vanish and its `l`-coordinate is `c`.
  simp [hT x, mulVec_mulVec]

variable (g : G E s) (t : GL p (𝔸 E))

/-- For `g` in `G` and `t` in `GL_p(𝔸)`, the adelic matrix `g⁻¹ (l (t⁻¹)ᴴ, k t, ι)`, where `l`, `k`,
`ι` are `D.lAdelic`, `D.kAdelic`, `D.iAdelic`, with three column blocks. -/
def frameAt : Matrix n ((p ⊕ p) ⊕ n₀) (𝔸 E) :=
  g⁻¹.adeleMatrix * ((D.lAdelic * t⁻¹.valᴴ).fromCols (D.kAdelic * t.val)).fromCols D.iAdelic

omit [WeilData E] in
/-- The Gram matrix of `frameAt g t` for the standard form: the hyperbolic block `(0, 1; 1, 0)` for
`l` and `k`, and the standard form of `V₀`. -/
lemma gram_frameAt :
    (D.frameAt g t)ᴴ * stdForm E s * D.frameAt g t =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 (stdForm E s₀) := by
  -- `g⁻¹` preserves the form, so only the relations between `k`, `l` and `i` are left.
  refine (U.gram_invariant ..).trans ?_
  aesop (add simp [conjTranspose_nonsing_inv, conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.mul_assoc])

/-- An element `g` of `G` is adapted to `t` in `GL_p(𝔸)` when the matrix `g⁻¹ (l (t⁻¹)ᴴ, k t, ι)`
has orthonormal columns at every infinite place and integral finite entries. -/
def IsAdapted : Prop := IsOrthoIntegral (D.frameAt g t)

/-- Adapted points exist. Let `D` be a Witt decomposition `V = (l E^p ⊕ k E^p) ⊥ i V₀`, where `E` is
a CM field with Weil data, and let `t` be in `GL_p(𝔸)`. Then there are `γ` in `G` and a bijection
`e : (p ⊕ p) ⊕ n₀ ≃ n` of index sets such that: `γ` is adapted to `t` (`γ⁻¹ (l (t⁻¹)ᴴ, k t, i)`,
where `l`, `k`, `i` are the adelic frames `D.lAdelic`, `D.kAdelic`, `D.iAdelic`, has orthonormal
columns at every infinite place and integral finite entries); the signs `s` of `V` reordered by `e`
are `hyperbolicSigns p` followed by `s₀`; and the adelic matrix of `γ` with columns reordered by `e`
equals `((l (t⁻¹)ᴴ, k t) x, i)` (that is, `D.frameAt 1 t` times `x ⊕ 1`), with `x` the adelic frame
of `hyperbolicSpace E p`. -/
lemma exists_isAdapted_and_frame_eq :
    ∃ γ : G E s, D.IsAdapted γ t ∧
      ∃ e : (p ⊕ p) ⊕ n₀ ≃ n, s ∘ e = hyperbolicSigns p ⊕ᵥ s₀ ∧
        D.frameAt 1 t * fromBlocks (o := n₀) (hyperbolicSpace E p).x.val 0 0 1 =
          γ.adeleMatrix.submatrix id e := by
  -- The columns `m = ((l (t⁻¹)ᴴ, k t) x, i)`, with `x` the frame of `hyperbolicSpace E p`, have the
  -- Gram matrix of the signs `hyperbolicSigns p ⊕ᵥ s₀`. Sylvester's law of inertia reorders them by
  -- a bijection `e` under which these signs become those of `V`; the reordered `m` is then the
  -- matrix of `γ`.
  let m : Matrix n ((p ⊕ p) ⊕ n₀) (𝔸 E) :=
    D.frameAt 1 t * fromBlocks (hyperbolicSpace E p).x.val 0 0 (1 : Matrix n₀ n₀ (𝔸 E))
  have h_gram : mᴴ * stdForm E s * m = stdForm E (hyperbolicSigns p ⊕ᵥ s₀) := by
    -- The Gram matrix of `frameAt 1 t` is the hyperbolic block plus the standard form of `V₀`,
    -- and the frame `x` of hyperbolic space carries the hyperbolic block to its standard form.
    rw [gram_mul, gram_frameAt]
    simp [← stdForm_sum, ← (hyperbolicSpace E p).gram_point, fromBlocks_conjTranspose,
      fromBlocks_multiply, fromBlocks_map]
  have σ : n ≃ (p ⊕ p) ⊕ n₀ := equivOfCardEq (by simp +arith [D.card_eq])
  let w : InfinitePlace E := Classical.ofNonempty
  have h_gram_w : (m.map (evalInf w))ᴴ * signMatrix s * m.map (evalInf w) =
      signMatrix (hyperbolicSigns p ⊕ᵥ s₀) := by
    simpa [Matrix.map_mul, stdForm, signMatrix, ← conjTranspose_map (evalInf w) (fun _ ↦ rfl)]
      using congrArg (·.map (evalInf w)) h_gram
  obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm n, ∀ i : n, s (τ i) = (hyperbolicSigns p ⊕ᵥ s₀) (σ i) :=
    sylvester_law_of_inertia (h := (m.map (evalInf w)).submatrix id σ) <| by
      simpa [signMatrix, comp_def, submatrix_mul _ _ σ id _ bijective_id]
        using congrArg (·.submatrix σ σ) h_gram_w
  let e : (p ⊕ p) ⊕ n₀ ≃ n := σ.symm.trans τ
  have h_sign : s ∘ e = hyperbolicSigns p ⊕ᵥ s₀ := funext fun i ↦ by simp [e, hτ]
  have h_form : (m.reindex 1 e)ᴴ * stdForm E s * m.reindex 1 e = stdForm E s := by
    -- Reorder the Gram matrix by `e`; by `h_sign` the result is the standard form of `s`.
    refine (congrArg (Matrix.reindex e e) h_gram).trans ?_
    simp [← h_sign, stdForm, submatrix_diagonal_equiv, Function.comp_def]
  let γ : G E s := ofMatrix (m.reindex 1 e) h_form
  have hγ : m = γ.adeleMatrix.submatrix id e := by simp [γ, Equiv.Perm.one_def]
  -- `frameAt γ t` is `x⁻¹ ⊕ 1` with its rows reordered by `e`.
  have h_frame : D.frameAt γ t = (1 : Matrix n n (𝔸 E)).submatrix id e *
      fromBlocks (hyperbolicSpace E p).x⁻¹.val 0 0 (1 : Matrix n₀ n₀ (𝔸 E)) := by
    have h_cancel : γ⁻¹.adeleMatrix * m = (1 : Matrix n n (𝔸 E)).submatrix id e := by
      rw [hγ, ← G.adeleMatrix_one (s := s), ← inv_mul_cancel γ, G.adeleMatrix_mul,
        submatrix_mul _ _ id id e bijective_id, submatrix_id_id]
    rw [← h_cancel]
    simp [frameAt, m, fromCols_mul_fromBlocks, Matrix.mul_assoc]
  refine ⟨γ, ?_, e, h_sign, hγ⟩
  exact .of_eq_submatrix_mul_of_injective .one e e.injective
    (isOrthoIntegral_hyperbolicSpace_x_inv.block_diag .one) h_frame

/-! ### Rational elements -/

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
omit [WeilData E] in
/-- The Levi element of a rational matrix `a` in `GL_p(E)` and a rational point `g₀` of `V₀` is a
rational point of `V`. -/
lemma levi_mem_Gamma (a : GL p E) {g₀ : G E s₀} (hg₀ : g₀ ∈ V₀.Γ) :
    D.levi (GeneralLinearGroup.map toAdele a, g₀) ∈ V.Γ := by
  obtain ⟨γ, rfl⟩ := hg₀
  -- In the rational coordinates of V the Levi element is a matrix over E (the frames cancel).
  have h_rat : V.x.val * (D.levi (.map toAdele a, V₀.ratEmbed γ)).adeleMatrix * V.x⁻¹.val =
      (D.k * a.val * D.lᴴ * V.J + D.i * γ.val.val * V₀.J⁻¹ * D.iᴴ * V.J +
        D.l * a⁻¹.valᴴ * D.kᴴ * V.J).map toAdele := by
    have h_cancel (M : Matrix n₀ n (𝔸 E)) : V₀.x.val * (V₀.x⁻¹.val * M) = M := by simp
    -- `-coe_units_inv` keeps `x₀⁻¹` a unit, so that `h_cancel` cancels it against `x₀`.
    simp [adeleMatrix_ratEmbed, ← map_inv, map_J, map_J_inv, Matrix.map_add, -coe_units_inv,
      kAdelic, lAdelic, iAdelic, kCoord, lCoord, iCoord, ratMap, Matrix.mul_assoc, Matrix.mul_add,
      Matrix.add_mul, h_cancel]
  exact V.mem_Gamma_iff_range.mpr fun i j ↦ ⟨_, (congrFun₂ h_rat i j).symm⟩

/-- The unipotent element `radicalElement (x₀⁻¹ c) b`, for a matrix `c` over `E`, `x₀` the adelic
frame of `V₀` and `b` an adelic matrix with entries in `E` (hypothesis `hb`), lies in the rational
group `Γ` of `V`. -/
lemma radicalElement_mem_Gamma (c : Matrix n₀ p E) {b : Matrix p p (𝔸 E)}
    (hb : b ∈ ratMatrices E p p) : D.radicalElement (V₀.x⁻¹.val * c.map toAdele) b ∈ V.Γ := by
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : Matrix p p E, b₀.map toAdele = b := hb
  -- In the rational coordinates of V the unipotent element is a matrix over E: the adelic frames
  -- cancel or combine with the standard forms into J and J₀.
  have h_rat : V.x.val *
      (D.radicalElement (V₀.x⁻¹.val * c.map toAdele) (b₀.map toAdele)).adeleMatrix * V.x⁻¹.val =
      (1 - D.i * c * D.kᴴ * V.J + D.k * cᴴ * D.iᴴ * V.J - D.k *
        ((2⁻¹ : E) • ((j : E)⁻¹ • (b₀ + b₀ᴴ) + cᴴ * V₀.J * c)) * D.kᴴ * V.J).map toAdele := by
    simp [map_J, Matrix.map_add, Matrix.map_sub, Matrix.map_smul', iAdelic, ratMap,
      Matrix.mul_assoc, lCoord, kAdelic, conjTranspose_nonsing_inv, iCoord, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]
  exact V.mem_Gamma_iff_range.mpr fun i j ↦ ⟨_, (congrFun₂ h_rat i j).symm⟩

/-- The rational points of the unipotent radical are cocompact. For a splitting `D` of `V` over
`V₀` along an isotropic subspace of any rank, there is a compact set `K` such that every element
`D.radicalElement c b` of the radical is moved into `K` by left multiplication with some
`D.radicalElement y z` that lies in the group `V.Γ` of rational points. -/
lemma exists_isCompact_rat_mul_radicalElement_mem (D : V.Splitting V₀ p) :
    ∃ K : Set (G E s), IsCompact K ∧
      ∀ (c : Matrix n₀ p (𝔸 E)) (b : Matrix p p (𝔸 E)),
        ∃ (y : Matrix n₀ p (𝔸 E)) (z : Matrix p p (𝔸 E)),
          D.radicalElement y z ∈ V.Γ ∧ D.radicalElement y z * D.radicalElement c b ∈ K := by
  -- Move first `c`, then `b`, into a compact set by rational matrices; `D.radicalElement y z` lies
  -- in `V.Γ` when `V₀.x * y` and `z` are rational.
  obtain ⟨C, hC, h_coverC⟩ : ∃ C : Set (Matrix n₀ p (𝔸 E)), IsCompact C ∧
      ∀ x : Matrix n₀ p (𝔸 E), ∃ γ ∈ ratMatrices E n₀ p, γ + x ∈ C :=
    IsCovolOneLattice.exists_compact_cover (ratMatrices E n₀ p)
  obtain ⟨B, hB, h_coverB⟩ : ∃ B : Set (Matrix p p (𝔸 E)), IsCompact B ∧
      ∀ x : Matrix p p (𝔸 E), ∃ γ ∈ ratMatrices E p p, γ + x ∈ B :=
    IsCovolOneLattice.exists_compact_cover (ratMatrices E p p)
  let φ (x : Matrix n₀ p (𝔸 E) × Matrix p p (𝔸 E)) : G E s :=
    D.radicalElement (V₀.x⁻¹.val * x.fst) x.snd
  refine ⟨φ '' C ×ˢ B, (hC.prod hB).image (by fun_prop), fun c b ↦ ?_⟩
  obtain ⟨γ, ⟨y₀, hy₀⟩, h_memC⟩ : ∃ γ ∈ ratMatrices E n₀ p, γ + V₀.x.val * c ∈ C := h_coverC _
  obtain rfl : y₀.map toAdele = γ := hy₀
  let y : Matrix n₀ p (𝔸 E) := V₀.x⁻¹.val * y₀.map toAdele
  obtain ⟨z, hz, h_memB⟩ : ∃ z ∈ ratMatrices E p p,
      z + (toAdele (j : E) • yᴴ * stdForm E s₀ * c + b) ∈ B := h_coverB _
  refine ⟨y, z, D.radicalElement_mem_Gamma y₀ hz, (_, _), ⟨h_memC, h_memB⟩, ?_⟩
  -- The parameters of the product are those that were moved into `C` and `B`.
  have h_first : V₀.x⁻¹.val * (y₀.map toAdele + V₀.x.val * c) = y + c := by
    simp [y, Matrix.mul_add]
  simp only [φ, h_first, radicalElement_mul, add_assoc]

omit [WeilData E] in
/-- The adelic frame `k` sends vectors with entries in `E` to rational vectors of `V`. -/
lemma kAdelic_mulVec_mem_ratVectors {b : p → 𝔸 E} :
    b ∈ New.ratVectors E p → D.kAdelic *ᵥ b ∈ V.ratVectors := by
  rintro ⟨a, rfl⟩
  refine ⟨D.k *ᵥ a, ?_⟩
  aesop (add simp [kAdelic, vecAtPoint, comp_def, RingHom.map_mulVec])

end Space.Splitting

end New

end Splitting

/-! ## Two opposite parabolic subgroups generate the group of a split space -/

section SiegelParabolic

namespace New

open Matrix Polynomial

variable {E p : Type*} [Field E] [CMType E] [Fintype p]

/-- The standard hermitian form `xᴴ x` over the CM field `E` is anisotropic. -/
lemma eq_zero_of_star_dotProduct_self {x : p → E} (hx : star x ⬝ᵥ x = 0) : x = 0 := by
  -- Any complex embedding `φ` turns the conjugation of `E` into complex conjugation.
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h_image : star (φ ∘ x) ⬝ᵥ (φ ∘ x) = 0 := by
    simpa [dotProduct, map_star_complex] using congrArg φ hx
  open ComplexOrder in
  exact φ.injective.comp_left (by simpa using dotProduct_star_self_eq_zero.1 h_image)

/-- Let `a`, `c` be square matrices over the CM field `E` with `aᴴ c + cᴴ a = 0` and with no common
kernel. Then `a + t c` is invertible for some purely imaginary scalar `t`. -/
lemma exists_skew_isUnit_add_smul [WeilData E] [DecidableEq p] {a c : Matrix p p E}
    (h_iso : aᴴ * c + cᴴ * a = 0) (h_ker : ∀ v : p → E, a *ᵥ v = 0 → c *ᵥ v = 0 → v = 0) :
    ∃ t : E, star t = -t ∧ IsUnit (a + t • c) := by
  -- The polynomial `det (a + X c)` does not vanish at `1`, so it has finitely many roots.
  -- Indeed `(a + c)ᴴ (a + c) = aᴴ a + cᴴ c` is definite: `(a + c) v = 0` gives `a v = c v = 0`.
  have h_gram : (a + c)ᴴ * (a + c) = aᴴ * a + cᴴ * c :=
    calc (a + c)ᴴ * (a + c)
      _ = aᴴ * a + cᴴ * c + (aᴴ * c + cᴴ * a) := by
        rw [conjTranspose_add]
        noncomm_ring
      _ = aᴴ * a + cᴴ * c := by rw [h_iso, add_zero]
  have h_one : (a + c).det ≠ 0 := by
    rw [Ne, ← exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv_ne, hv⟩
    have h_form (m : Matrix p p E) : star (m *ᵥ v) ⬝ᵥ m *ᵥ v = star v ⬝ᵥ (mᴴ * m) *ᵥ v := by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    let u : p ⊕ p → E := Sum.elim (a *ᵥ v) (c *ᵥ v)
    have h_zero : u = 0 := eq_zero_of_star_dotProduct_self <|
      calc star u ⬝ᵥ u
        _ = star (a *ᵥ v) ⬝ᵥ a *ᵥ v + star (c *ᵥ v) ⬝ᵥ c *ᵥ v := by simp [u, dotProduct]
        _ = star ((a + c) *ᵥ v) ⬝ᵥ (a + c) *ᵥ v := by
          simp only [h_form, h_gram, add_mulVec (aᴴ * a), dotProduct_add]
        _ = 0 := by rw [hv, dotProduct_zero]
    exact hv_ne (h_ker v (congrArg (· ∘ Sum.inl) h_zero) (congrArg (· ∘ Sum.inr) h_zero))
  let P : E[X] := (a.map C + (X : E[X]) • c.map C).det
  have h_eval (t : E) : P.eval t = (a + t • c).det := by
    rw [← coe_evalRingHom, RingHom.map_det]
    exact congrArg det (Matrix.ext fun i j ↦ by simp [mul_comm t])
  have h_ne : P ≠ 0 := fun h_zero ↦ h_one (by simpa [h_zero] using (h_eval 1).symm)
  -- The multiples of `j` by natural numbers are infinitely many purely imaginary scalars.
  have h_inf : (Set.range fun m : ℕ ↦ (m : E) * WeilData.j).Infinite :=
    Set.infinite_range_of_injective
      ((mul_left_injective₀ WeilData.j_ne_zero).comp Nat.cast_injective)
  obtain ⟨t, ⟨m, rfl⟩, h_root⟩ : ∃ t ∈ Set.range fun m : ℕ ↦ (m : E) * WeilData.j, ¬P.IsRoot t :=
    h_inf.exists_notMem_finite (finite_setOfPred_isRoot h_ne)
  have h_det : (a + ((m : E) * WeilData.j) • c).det ≠ 0 := by rwa [← h_eval]
  exact ⟨m * WeilData.j, by simp [WeilData.star_j], (isUnit_iff_isUnit_det _).2 h_det.isUnit⟩

namespace Space.Splitting

variable [DecidableEq p] {n : Type*} [Fintype n] [DecidableEq n] {s : n → ℤˣ}
  {V : Space E n s} (D : V.Splitting (stdSpace E Empty) p)

/-- The parabolic subgroup of a splitting `D` without middle part: the rational unitary `γ` that
map the maximal isotropic subspace spanned by the frame `D.k` onto itself. The opposite parabolic
subgroup, of the dual frame `D.l`, is `D.symm.siegelParabolic`. -/
def siegelParabolic : Subgroup (U V.J) where
  carrier := {γ : U V.J | ∃ a : GL p E, γ.val.val * D.k = D.k * a.val}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro γ δ ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by simp [Matrix.mul_assoc, hb, ← Matrix.mul_assoc γ.val.val, ha]⟩
  inv_mem' := by
    rintro γ ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    calc γ⁻¹.val.val * D.k
      _ = γ⁻¹.val.val * (γ.val.val * D.k) * a⁻¹.val := by simp [ha, Matrix.mul_assoc]
      _ = D.k * a⁻¹.val := by simp

/-- For a skew-hermitian matrix `b`, the translation `k ↦ k`, `l ↦ l + k b` of the frames of `D` is
given by an element of the parabolic subgroup of `D`. -/
lemma exists_mem_siegelParabolic_mul_l_eq {b : Matrix p p E} (hb : bᴴ = -b) :
    ∃ u ∈ D.siegelParabolic, u.val.val * D.k = D.k ∧ u.val.val * D.l = D.l + D.k * b := by
  have h_kk (X : Matrix p n E) : D.kᴴ * (V.J * (D.k * X)) = 0 := by simp [← Matrix.mul_assoc]
  have h_form : (1 + D.k * b * (D.kᴴ * V.J))ᴴ * V.J * (1 + D.k * b * (D.kᴴ * V.J)) = V.J := by
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, V.conjTranspose_J, hb, h_kk]
  let u : U V.J := U.of V.isUnit_J _ h_form
  have hu (X : Matrix n p E) : u.val.val * X = X + D.k * b * (D.kᴴ * V.J * X) := by
    simp [u, Matrix.add_mul, Matrix.mul_assoc]
  have h_k : u.val.val * D.k = D.k := by rw [hu, D.gram_kk, Matrix.mul_zero, add_zero]
  exact ⟨u, ⟨1, by simpa using h_k⟩, h_k, by rw [hu, D.gram_kl, Matrix.mul_one]⟩

variable {D} {g : U V.J} {a c : Matrix p p E}

/-- If `g k = k a + l c` for a unitary `g`, then `aᴴ c + cᴴ a = 0`, as `g k` is isotropic. -/
lemma conjTranspose_mul_add_eq_zero (hg : g.val.val * D.k = D.k * a + D.l * c) :
    aᴴ * c + cᴴ * a = 0 := by
  have h_gram (X Y : Matrix n p E) (x y : Matrix p p E) :
      (X * x)ᴴ * V.J * (Y * y) = xᴴ * (Xᴴ * V.J * Y) * y := by simp [Matrix.mul_assoc]
  calc aᴴ * c + cᴴ * a
    _ = (D.k * a + D.l * c)ᴴ * V.J * (D.k * a + D.l * c) := by
      simp [Matrix.add_mul, Matrix.mul_add, h_gram, add_comm, -conjTranspose_mul]
    _ = 0 := by rw [← hg, U.gram_invariant, D.gram_kk]

/-- The big cell: if `g k = k a + l c` with `a` invertible, then some element of the opposite
parabolic subgroup moves `g` into the parabolic subgroup of `D`. -/
lemma exists_mul_mem_siegelParabolic (hg : g.val.val * D.k = D.k * a + D.l * c) (ha : IsUnit a) :
    ∃ v ∈ D.symm.siegelParabolic, v * g ∈ D.siegelParabolic := by
  -- Take the translation `l ↦ l`, `k ↦ k - l c a⁻¹`.
  obtain ⟨a, rfl⟩ := ha
  have h_iso : cᴴ * a = -(a.valᴴ * c) :=
    eq_neg_of_add_eq_zero_right (conjTranspose_mul_add_eq_zero hg)
  have h_skew : (-(c * a⁻¹.val))ᴴ = -(-(c * a⁻¹.val)) :=
    calc (-(c * a⁻¹.val))ᴴ
      _ = -(a⁻¹.valᴴ * (cᴴ * a) * a⁻¹.val) := by simp [Matrix.mul_assoc]
      _ = -(-(c * a⁻¹.val)) := by simp [h_iso, ← Matrix.mul_assoc, ← conjTranspose_mul]
  obtain ⟨v, hv, hv_l, hv_k⟩ : ∃ v ∈ D.symm.siegelParabolic,
      v.val.val * D.l = D.l ∧ v.val.val * D.k = D.k + D.l * -(c * a⁻¹.val) :=
    D.symm.exists_mem_siegelParabolic_mul_l_eq h_skew
  refine ⟨v, hv, a, ?_⟩
  calc (v * g).val.val * D.k
    _ = v.val.val * D.k * a.val + v.val.val * D.l * c := by
      simp [hg, Matrix.mul_assoc, Matrix.mul_add]
    _ = D.k * a.val := by simp [hv_k, hv_l, Matrix.add_mul, Matrix.mul_assoc]

variable (D)

/-- In a splitting without middle part every vector is the sum of its components along the frames
`k` and `l`. -/
lemma k_mul_add_l_mul_eq_one : D.k * (D.lᴴ * V.J) + D.l * (D.kᴴ * V.J) = 1 := by
  have h_card : Fintype.card n = Fintype.card (p ⊕ p) := by simp [D.card_eq, two_mul]
  rw [← fromCols_mul_fromRows, mul_eq_one_comm_of_card_eq _ _ _ h_card, fromRows_mul_fromCols,
    D.gram_lk, D.gram_ll, D.gram_kk, D.gram_kl, fromBlocks_one]

/-- Let `D` be a splitting of `V` without middle part. The stabilizers of the spans of the two
isotropic frames `D.k` and `D.l` generate the rational unitary group of `V`. -/
lemma siegelParabolic_sup_symm_eq_top [WeilData E] :
    D.siegelParabolic ⊔ D.symm.siegelParabolic = ⊤ := by
  -- Write `g k = k a + l c`. A translation `u : l ↦ l + t k` turns `a` into `a + t c`, which is
  -- invertible for a suitable `t`; then `u g` lies in the big cell.
  refine eq_top_iff.2 fun g _ ↦ ?_
  obtain ⟨a, c, hg⟩ : ∃ a c : Matrix p p E, g.val.val * D.k = D.k * a + D.l * c := by
    refine ⟨D.lᴴ * V.J * (g.val.val * D.k), D.kᴴ * V.J * (g.val.val * D.k), ?_⟩
    rw [← Matrix.mul_assoc D.k, ← Matrix.mul_assoc D.l, ← Matrix.add_mul, k_mul_add_l_mul_eq_one,
      Matrix.one_mul]
  have h_ker (v : p → E) (hav : a *ᵥ v = 0) (hcv : c *ᵥ v = 0) : v = 0 :=
    calc v
      _ = ((g.val.val * D.l)ᴴ * V.J) *ᵥ (g.val.val * D.k) *ᵥ v := by
        rw [mulVec_mulVec, U.gram_invariant, D.gram_lk, one_mulVec]
      _ = 0 := by simp [hg, add_mulVec, ← mulVec_mulVec, hav, hcv]
  obtain ⟨t, ht, h_unit⟩ : ∃ t : E, star t = -t ∧ IsUnit (a + t • c) :=
    exists_skew_isUnit_add_smul (conjTranspose_mul_add_eq_zero hg) h_ker
  obtain ⟨u, hu, hu_k, hu_l⟩ : ∃ u ∈ D.siegelParabolic,
      u.val.val * D.k = D.k ∧ u.val.val * D.l = D.l + D.k * (t • 1) :=
    D.exists_mem_siegelParabolic_mul_l_eq (by simp [ht])
  have h_ug : (u * g).val.val * D.k = D.k * (a + t • c) + D.l * c := by
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, hg, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu_k, hu_l]
    simp [Matrix.add_mul, Matrix.mul_add, add_assoc, add_comm (D.l * c)]
  obtain ⟨v, hv, h_vug⟩ : ∃ v ∈ D.symm.siegelParabolic, v * (u * g) ∈ D.siegelParabolic :=
    exists_mul_mem_siegelParabolic h_ug h_unit
  rw [← mul_mem_cancel_left (Subgroup.mem_sup_left hu),
    ← mul_mem_cancel_left (Subgroup.mem_sup_right hv)]
  exact Subgroup.mem_sup_left h_vug

end Space.Splitting

end New

end SiegelParabolic

end
