import Lib.LocalGL.Green.LabelCharacters
import New.Reduction.Data.LevelAndTwists

/-!
# Good labels, index types of hermitian spaces, the group 𝖦 and idempotent e₀

This file introduces primitive polynomials and good tuples of labels at one prime. Then, for
admissible data D, it introduces the index types and signs for the bases of the hermitian spaces
X_j, Y_j and W_j.

## Main definitions and results

* `New.IsPrimitivePolynomial`: irreducible labels with a root of order |k|^r − 1. They are stable
  under scaling the roots by an M-th root of unity if M² ∣ |k| − 1
  (`New.IsPrimitivePolynomial.scaleRoots`). The product of their roots has order |k| − 1
  (`New.IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots_and_exists_pow_eq`).
* `New.goodTuples`: tuples of labels, each without roots among the M-th roots of unity of its base
  field, of which at least one is primitive.
* `New.Data.X`, `New.Data.RowIndex`, `New.Data.Y`: the basis indices of X_j (rank `New.Data.n`), of
  Y_0 (rank r, `New.Data.card_rowIndex`) and of Y_j (`New.Data.RowIndex` and j blocks of size
  `New.Data.t`).
* `New.Data.chosenGL`, `New.Data.e₀`: the product of the groups GL_r over the residue fields at the
  chosen places above p₀, p₁, and the good idempotent in its group algebra. The idempotent is the
  sum of the idempotents `New.tupleIdem` over `New.Data.goodTupleFamilies`.
* `New.Data.isCentralProj_e₀`: `e₀` is a central idempotent.
* `New.Data.hyperplaneSum_mul_e₀`: `e₀` kills pure tensors with a factor `New.hyperplaneSum χ l`,
  `l ≠ 0`, `χ ^ q₂ = 1`.

Notions from other files:
* `New.Data`: the data D, with m lifts, block size t and ranks k, n_j = k + j (t + 1) and
  r = k + m − 1; s is its parameter `D.towerExp`, and q₂ = q₂(s) the integer `New.Parameters.q₂`.
* `New.Data.ChosenPlace`: the chosen places above the level prime p_i (i = 0, 1), the finite places
  of E that divide both p_i and the conjugate `D.piM` of an integer of K of norm p₀p₁.
* `New.IsLabel`: a label of degree r is a monic squarefree polynomial c of degree r with c(0) ≠ 0.
* `New.tupleIdem`: the tensor product of the label idempotents e_c of a tuple of polynomials.
* `New.piTensorElem`: the pure tensor ⊗ x_i in ℂ[∏ G_i] of elements x_i of ℂ[G_i].
-/

noncomputable section

/-! ## Primitive polynomials and good tuples at one prime -/

namespace New

open Polynomial Finset Nat

attribute [local instance low] Fintype.ofFinite

variable {k : Type*} [Field k] [Finite k] {c : k[X]} {r : ℕ}

/-- The polynomial `c` is a primitive polynomial: an irreducible label of degree `r` over `k` with a
root of order `|k| ^ r - 1`, that is, a root that generates the units of the field with `|k| ^ r`
elements. -/
def IsPrimitivePolynomial (r : ℕ) (c : k[X]) : Prop :=
  IsLabel r c ∧ Irreducible c ∧
    ∃ ξ : AlgebraicClosure k, c.aeval ξ = 0 ∧ IsPrimitiveRoot ξ (Nat.card k ^ r - 1)

/-- If there is a primitive polynomial of degree `r` over `k`, then `|k| ^ r ≥ 2`. -/
lemma IsPrimitivePolynomial.two_le_card_pow (hc : IsPrimitivePolynomial r c) :
    2 ≤ Nat.card k ^ r := by
  obtain ⟨⟨-, -, h_deg, h_coeff⟩, h_irr, ξ, h_root, -⟩ := hc
  obtain ⟨-, h_two_le⟩ := root_pow_card_pow_pred_eq_one h_irr h_coeff h_root
  rwa [h_deg] at h_two_le

/-- Let `k` be a finite field and `c : k[X]` a primitive polynomial of degree `r`: a monic
irreducible polynomial of degree `r` with `c(0) ≠ 0` that has a root of order `|k| ^ r - 1` in the
algebraic closure of `k`. If `M ^ 2` divides `|k| - 1` and `a` is an `M`-th root of unity of `k`,
then `c.scaleRoots a`, whose roots are those of `c` multiplied by `a`, is again a primitive
polynomial of degree `r`. -/
lemma IsPrimitivePolynomial.scaleRoots {c : k[X]} (a : kˣ) {r M : ℕ} (ha : (a : k) ^ M = 1)
    (hM : M ^ 2 ∣ Nat.card k - 1) (hc : IsPrimitivePolynomial r c) :
    IsPrimitivePolynomial r (c.scaleRoots a) := by
  have h_two_le : 2 ≤ Nat.card k ^ r := hc.two_le_card_pow
  obtain ⟨h_label, h_irr, ξ, h_root, h_prim⟩ := hc
  set b : AlgebraicClosure k := algebraMap k (AlgebraicClosure k) a with hb
  refine ⟨h_label.scaleRoots a, h_irr.map (scaleRootsEquiv a),
    b * ξ, scaleRoots_aeval_eq_zero h_root, ?_⟩
  -- It remains to see that the root `a ξ` has the order `|k| ^ r - 1` of `ξ`.
  rw [h_prim.eq_orderOf, IsPrimitiveRoot.iff_orderOf]
  refine (Commute.all _ ξ).orderOf_mul_eq_right_of_forall_prime_mul_dvd
    (h_prim.isOfFinOrder (Nat.sub_ne_zero_of_lt h_two_le)) fun p _ hp ↦ ?_
  -- A prime `p` dividing `ord a` has `p * ord a ∣ (ord a) ^ 2 ∣ M ^ 2 ∣ |k| - 1 ∣ ord ξ`.
  calc p * orderOf b ∣ orderOf b ^ 2 := by simpa [sq] using mul_dvd_mul_right hp (orderOf b)
    _ ∣ M ^ 2 := pow_dvd_pow_of_dvd (orderOf_dvd_of_pow_eq_one (by simp [hb, ← map_pow, ha])) 2
    _ ∣ Nat.card k - 1 := hM
    _ ∣ Nat.card k ^ r - 1 := Nat.sub_one_dvd_pow_sub_one _ _
    _ = orderOf ξ := h_prim.eq_orderOf

/-- With `q = |k|`, the product of the roots of a primitive polynomial of degree `r` is
`ξ ^ (1 + q + ⋯ + q ^ (r - 1))` for each root `ξ`. -/
lemma IsPrimitivePolynomial.pow_geom_sum_eq_prod_aroots (hc : IsPrimitivePolynomial r c)
    {ξ : AlgebraicClosure k} (hξ : c.aeval ξ = 0) :
    ξ ^ ∑ i ∈ range r, Nat.card k ^ i = (c.aroots (AlgebraicClosure k)).prod := by
  -- The roots of `c` are the conjugates `ξ ^ q ^ i` for `i < r`.
  obtain ⟨⟨-, -, h_deg, -⟩, h_irr, -⟩ := hc
  rw [aroots_eq_frobenius_orbit h_irr hξ, h_deg, ← prod_pow_eq_pow_sum, prod_eq_multiset_prod,
    range_val]

/-- The norm of a generator is a generator: the product of the roots of a primitive polynomial has
order `|k| - 1`. -/
lemma IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots (hc : IsPrimitivePolynomial r c) :
    IsPrimitiveRoot (c.aroots (AlgebraicClosure k)).prod (Nat.card k - 1) := by
  -- With `q = |k|`, the product is `ξ ^ e` for a root `ξ` of order `q ^ r - 1` and the
  -- geometric sum `e`, and `e * (q - 1) = q ^ r - 1`.
  obtain ⟨-, -, ξ, hξ, h_prim⟩ := id hc
  rw [← hc.pow_geom_sum_eq_prod_aroots hξ]
  exact h_prim.pow (Nat.sub_pos_of_lt hc.two_le_card_pow)
    (geom_sum_mul_of_one_le Nat.card_pos r).symm

/-- The product of the roots of a primitive polynomial has order `|k| - 1`, and it is one and the
same power of every root. This power is the norm from the field with `|k| ^ r` elements to `k`; see
`New.IsPrimitivePolynomial.pow_geom_sum_eq_prod_aroots` for the exponent. -/
lemma IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots_and_exists_pow_eq
    (hc : IsPrimitivePolynomial r c) :
    IsPrimitiveRoot (c.aroots (AlgebraicClosure k)).prod (Nat.card k - 1) ∧
    ∃ e : ℕ, ∀ ξ ∈ c.aroots (AlgebraicClosure k), ξ ^ e = (c.aroots (AlgebraicClosure k)).prod :=
  ⟨hc.isPrimitiveRoot_prod_aroots, ∑ i ∈ range r, Nat.card k ^ i,
    fun _ hξ ↦ hc.pow_geom_sum_eq_prod_aroots (mem_aroots.1 hξ).2⟩

/-- The polynomial `c` is an allowed polynomial: a label of degree `r` over `k` that has no root `x`
in `k` with `x ^ M = 1`. -/
def IsAllowedPolynomial (M r : ℕ) (c : k[X]) : Prop :=
  IsLabel r c ∧ ∀ x : k, x ^ M = 1 → ¬c.IsRoot x

omit [Finite k] in
lemma IsAllowedPolynomial.isLabel {M : ℕ} (hc : IsAllowedPolynomial M r c) : IsLabel r c := hc.1

omit [Finite k] in
/-- An allowed polynomial does not vanish at an `M`-th root of unity of `k`. -/
lemma IsAllowedPolynomial.not_isRoot {M : ℕ} (hc : IsAllowedPolynomial M r c) {x : k}
    (hx : x ^ M = 1) :
    ¬c.IsRoot x := hc.2 x hx

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → Type*} [∀ w, Field (k w)]
  [∀ w, Finite (k w)]

open scoped Classical in
/-- The good tuples of labels of degree `r`, one label over each field `k w`: every label is
allowed (no root of it in its base field is an `M`-th root of unity), and at least one is
primitive. -/
noncomputable def goodTuples (M r : ℕ) : Finset (∀ w : ι, (k w)[X]) :=
  {c ∈ Fintype.piFinset fun w ↦ monicsOfDegree (k w) r |
    (∀ w : ι, IsAllowedPolynomial M r (c w)) ∧ ∃ w : ι, IsPrimitivePolynomial r (c w)}

/-- A tuple `(c_w)` of polynomials over finite fields `k w` is good for `M` and `r` exactly when
every `c_w` is allowed and some `c_w` is primitive. -/
lemma mem_goodTuples {M r : ℕ} {c : ∀ w : ι, (k w)[X]} :
    c ∈ goodTuples M r ↔ (∀ w : ι, IsAllowedPolynomial M r (c w)) ∧
      ∃ w : ι, IsPrimitivePolynomial r (c w) := by
  classical
  refine mem_filter.trans <| and_iff_right_of_imp fun ⟨h_allowed, _⟩ ↦
    Fintype.mem_piFinset.2 fun w ↦ ?_
  obtain ⟨h_monic, -, h_deg, -⟩ := (h_allowed w).isLabel
  simp [monicsOfDegree, h_monic, h_deg]

end

end New

/-!
## Basis indices and signs of the hermitian spaces, the group 𝖦 and the idempotent e₀
For admissible data D, the spaces X_j, Y_j and W_j (`New.Data.spaceY`, `New.Data.spaceW`; W_j has
rank r) are hermitian spaces whose bases are indexed by the types defined here.
-/

section IndexTypes

open Fintype

namespace New

variable {S T α : Type}

/-! ### A block followed by j equal blocks -/

/-- The disjoint union of S and j copies of T, the index type of Y_j. -/
@[instance_reducible]
def BlockIndex (S T : Type) : ℕ → Type
  | 0 => S
  | j + 1 => BlockIndex S T j ⊕ T

/-- The inclusion of the first block S into the union of S and j copies of T. -/
def BlockIndex.firstBlock : ∀ j : ℕ, S ↪ BlockIndex S T j
  | 0 => Function.Embedding.refl S
  | j + 1 => (firstBlock j).trans Function.Embedding.inl

/-- If `S` is in bijection with `α`, then `BlockIndex S T j` is in bijection with
`α ⊕ Fin j × T`. -/
lemma BlockIndex.nonempty_equiv_sum {S T α : Type} (ν : S ≃ α) (j : ℕ) :
    Nonempty (BlockIndex S T j ≃ α ⊕ Fin j × T) := by
  induction j with
  | zero => exact ⟨ν.trans (Equiv.sumEmpty α (Fin 0 × T)).symm⟩
  | succ j ih =>
    obtain ⟨e⟩ := ih
    -- The last copy of `T` becomes the block with the number `j`.
    let split_last : (Fin j × T) ⊕ T ≃ Fin (j + 1) × T :=
      calc (Fin j × T) ⊕ T ≃ (Fin j × T) ⊕ (Fin 1 × T) :=
            Equiv.sumCongr (.refl _) (Equiv.uniqueProd T (Fin 1)).symm
        _ ≃ (Fin j ⊕ Fin 1) × T := (Equiv.sumProdDistrib (Fin j) (Fin 1) T).symm
        _ ≃ Fin (j + 1) × T := finSumFinEquiv.prodCongr (.refl T)
    exact ⟨calc BlockIndex S T j ⊕ T ≃ (α ⊕ Fin j × T) ⊕ T := e.sumCongr (.refl T)
      _ ≃ α ⊕ (Fin j × T) ⊕ T := Equiv.sumAssoc α (Fin j × T) T
      _ ≃ α ⊕ Fin (j + 1) × T := Equiv.sumCongr (.refl α) split_last⟩

/-- A bijection from `BlockIndex S T j`, the union of `S` and `j` copies of `T`, to
`α ⊕ Fin j × T`, for a bijection `ν : S ≃ α`. For `j = 0` it is given by `ν`
(`New.BlockIndex.equivSum_zero_apply`); for `j > 0` it is an arbitrary such bijection, chosen from
`New.BlockIndex.nonempty_equiv_sum`, and need not respect the blocks. -/
def BlockIndex.equivSum (ν : S ≃ α) : (j : ℕ) → BlockIndex S T j ≃ α ⊕ Fin j × T
  | 0 => ν.trans (Equiv.sumEmpty α (Fin 0 × T)).symm
  | j + 1 => (nonempty_equiv_sum ν (j + 1)).some

/-- For `j = 0` the bijection `equivSum ν 0` from `BlockIndex S T 0` to `α ⊕ Fin 0 × T` sends `x` to
`Sum.inl (ν x)`, that is, it is `ν` followed by the left inclusion. -/
lemma BlockIndex.equivSum_zero_apply (ν : S ≃ α) (x : S) :
    (equivSum ν 0 : BlockIndex S T 0 ≃ α ⊕ Fin 0 × T) x = Sum.inl (ν x) :=
  rfl

variable [Fintype S] [Fintype T]

/-- The index type `BlockIndex S T j` is finite. -/
instance instFintypeBlockIndex : ∀ j : ℕ, Fintype (BlockIndex S T j)
  | 0 => ‹Fintype S›
  | j + 1 => @instFintypeSum (BlockIndex S T j) T (instFintypeBlockIndex j) ‹Fintype T›

/-- Equality in `BlockIndex S T j` is decidable if it is in `S` and `T`, by recursion on `j`. -/
instance decEqBlockIndex [DecidableEq S] [DecidableEq T] :
    ∀ j : ℕ, DecidableEq (BlockIndex S T j)
  | 0 => ‹DecidableEq S›
  | j + 1 => @instDecidableEqSum (BlockIndex S T j) T (decEqBlockIndex j) ‹DecidableEq T›

/-- The union of `S` and `j` copies of `T` has `|S| + j |T|` elements. -/
@[simp]
lemma BlockIndex.card {S T : Type} [Fintype S] [Fintype T] (j : ℕ) :
    card (BlockIndex S T j) = card S + j * card T := by
  simp [card_congr (equivSum (.refl S) j)]

namespace Data

variable {P : Parameters} (D : Data P) (j : ℕ) (τ : D.Φ) (i : Fin 2)

/-! ### Index types -/

/-- The number ϱ = ⌊m/2⌋ − 1 of hyperbolic planes of Y₀, where m is the number of lifts. -/
def ϱ : ℕ := D.m / 2 - 1

/-- The basis indices of X_j other than the last: a set with n_j − 1 elements. -/
abbrev InitIndex : Type := Fin (D.n j - 1)

/-- The basis index set of X_j: n_j − 1 indices together with one extra point for the last basis
vector. -/
abbrev X : Type := D.InitIndex j ⊕ Unit

/-- The shape of Y₀: ϱ = `New.Data.ϱ` hyperbolic planes, the basis indices of X₀, and the last
of them as distinguished index. -/
abbrev shape : Shape where
  ϱ := D.ϱ
  κ := D.X 0
  k₀ := Sum.inr ()

/-- The basis index set of Y₀: e₁, …, e_ϱ, the indices of X₀, the middle vector z, and e*₁, …,
e*_ϱ. -/
@[reducible]
def RowIndex : Type := D.shape.BesselIndex
  deriving DecidableEq, Fintype

/-- The basis index set of Y_j: `New.Data.RowIndex` followed by j blocks of t indices each. -/
abbrev Y : Type := BlockIndex D.RowIndex (Fin D.t) j

/-- The index set `New.Data.RowIndex` of the basis of the hermitian space Y₀ over E has `r = D.r`
elements. For the admissible data `D`, Y₀ is the first space of the chain of `m = D.m` theta lifts
from U(Y₀) to U(Y_m). -/
lemma card_rowIndex : card D.RowIndex = D.r := by
  -- The basis of Y₀ consists of two times ϱ vectors, the n₀ basis vectors of X₀, and z.
  have h_card : card D.RowIndex = D.ϱ + (D.n 0 - 1 + 1 + 1 + D.ϱ) := by simp
  -- Here ϱ = m/2 - 1 for an even m ≥ 2, and n₀ = k > 0.
  grind [ϱ, n, D.m_even, D.k_pos]

/-- A logarithmic bound on the rank `r` (`New.Data.HasLogBound`: `r ≤ exp l` if `u` is `true`,
`exp l ≤ r` if `u` is `false`) also holds for the number of basis indices of Y₀, which is `r`. -/
instance {u : Bool} {l : ℝ} [D.HasLogBound u D.r l] : D.HasLogBound u (card D.RowIndex) l := by
  rwa [D.card_rowIndex]

/-! ### Parameters and signs -/

/-- A chosen numbering of the basis indices of Y₀: a bijection from `New.Data.RowIndex` to
{0, …, r − 1}. -/
def basisNumber : D.RowIndex ≃ Fin D.r := equivFinOfCardEq D.card_rowIndex

/-- Twice the entry numbered `D.basisNumber i` of the target parameter `New.Data.targetParameter` at
the place τ: the doubled parameter on W_j and on Y₀. The entries of the target parameter at τ are
k/2 − 1, k/2 − 2, … (k − 1 of them), then h₂ − w₁(τ), …, h₂ − w_m(τ), with
w_a = `New.Data.liftWeight` a the weights of the lifts and h₂ = `D.halfGap` half the gap between
consecutive weights. -/
def paramW (i : D.RowIndex) : ℤ := 2 * D.targetParameter τ (D.basisNumber i)

/-- The sign `(-1) ^ (o + a + min (a - o) j)`, with the subtraction truncated at zero
(`New.Data.entrySign_eq_neg_one_pow`). In `New.Data.gridSigns` it is the sign, at the node `(i, j)`
with offset `o`, of the base index with number `n`, where `a = n + 1 - k` (truncated at zero) and
`k` is the rank `D.k`. The first branch, for `j = 0` and positive `o`, agrees with the formula. It
makes the signs for `o + 1` the negatives of those for `o` by definition, as the passage to the
opposite space in `New.Data.gridSpace` requires. -/
def entrySign : (o j a : ℕ) → ℤˣ
  | o + 1, 0, a => -entrySign o 0 a
  | o, j, a => (-1) ^ (o + a + min (a - o) j)

/-- Closed form of `entrySign`, the sign `±1` of a basis vector of the hermitian space at a node
`(i, j)` of a grid or triangle. Here `offset` is the offset of the node, `j` is its second
coordinate, and `excess = n + 1 - k` for the basis vector with number `n` and the rank `k = D.k`.
The sign is `(-1) ^ (offset + excess + min (excess - offset) j)`, with subtraction truncated at
zero. -/
lemma entrySign_eq_neg_one_pow (offset j excess : ℕ) :
    entrySign offset j excess = (-1) ^ (offset + excess + min (excess - offset) j) := by
  cases j with
  | succ j => cases offset <;> rfl
  | zero =>
    induction offset with
    | zero => rfl
    | succ offset ih =>
      calc entrySign (offset + 1) 0 excess = -entrySign offset 0 excess := rfl
        _ = (-1) ^ (offset + 1 + excess + min (excess - (offset + 1)) 0) := by
          simp [ih, add_right_comm offset 1, pow_succ]

/-- The signs ±1 of W_j on the indices i in `New.Data.RowIndex`: −1 when the number
`D.basisNumber i` in {0, …, r − 1} is at least `D.posRank j` = k + j − 1, and +1 otherwise. -/
def signsW (i : D.RowIndex) : ℤˣ := if D.posRank j ≤ D.basisNumber i then (-1 : ℤˣ) else 1

/-- The map sending a pair (i, w), with w a chosen place above the prime p_i = `D.levelPrime i`, to
the underlying finite place w of E. The chosen places above p_i (`New.Data.ChosenPlace`) are the
finite places of E that divide both p_i and `D.piM`, the complex conjugate of the integer
`D.piMBar` of K of norm p₀p₁. -/
def chosenPlace (x : Σ i : Fin 2, D.ChosenPlace i) : New.FinPlace D.E := x.2.val

/-! ### The finite group and the good idempotent -/

/-- The finite group 𝖦 = ∏ GL_r(𝔽_w), over the chosen places w (`New.Data.ChosenPlace`) above the
two level primes p₀ and p₁ (`D.levelPrime`), where 𝔽_w is the residue field at w and the r rows are
indexed by `New.Data.RowIndex`. -/
abbrev chosenGL : Type := ∀ x : (i : Fin 2) × D.ChosenPlace i,
  GL D.RowIndex (ResField (D.chosenPlace x))

/-- There are only finitely many chosen places above the prime p_i = `D.levelPrime i`. -/
instance : Fintype (D.ChosenPlace i) := (D.finite_isChosen.sep _).fintype

open scoped Classical in
/-- The finite set of families (c_w) of polynomials over the residue fields at the chosen places w
above p₀, p₁. For each p_i, the tuple of the c_w with w above p_i lies in `New.goodTuples` for the
integer `New.Parameters.q₂` at s and the rank r. -/
def goodTupleFamilies :
    Finset
      ((x : (i : Fin 2) × D.ChosenPlace i) → Polynomial
        (ResField (D.chosenPlace ⟨x.fst, x.snd⟩))) :=
  (piFinset fun _ ↦ goodTuples (P.q₂ D.towerExp) (card D.RowIndex)).map
    (Equiv.piCurry fun i w ↦ Polynomial (ResField (D.chosenPlace ⟨i, w⟩))).symm.toEmbedding

open scoped Classical in
/-- Let `c = (c_w)` be a family of polynomials over the residue fields at the chosen places `w`, the
finite places of E that divide `D.piM` and one of the two level primes p₀, p₁ of the data `D`. Then
`c` lies in `New.Data.goodTupleFamilies` exactly when, for `i = 0, 1`, the `c_w` with `w` above p_i
form a good tuple (`New.goodTuples`): each is a label of degree `r = card D.RowIndex` with no
`q₂`-th root of unity of the residue field as a root, and at least one is primitive. -/
lemma mem_goodTupleFamilies
    {c : (x : (i : Fin 2) × D.ChosenPlace i) → Polynomial (ResField
      (D.chosenPlace ⟨x.fst, x.snd⟩))} :
    c ∈ D.goodTupleFamilies ↔
      ∀ i : Fin 2, (fun w : D.ChosenPlace i ↦ c ⟨i, w⟩) ∈
        goodTuples (P.q₂ D.towerExp) (card D.RowIndex) := by
  rw [goodTupleFamilies, Finset.mem_map_equiv, mem_piFinset]
  rfl

open scoped Classical in
/-- The element e₀ of ℂ[𝖦]: the sum of the idempotents `New.tupleIdem` over the families in
`New.Data.goodTupleFamilies`. -/
def e₀ :
    MonoidAlgebra ℂ ((i : (i : Fin 2) × D.ChosenPlace i) →
      GL D.RowIndex (ResField (D.chosenPlace ⟨i.fst, i.snd⟩))) :=
  ∑ c ∈ D.goodTupleFamilies, tupleIdem D.RowIndex c

end Data

end New

end IndexTypes

/-! ## Centrality of e₀ and hyperplane sums -/

namespace New.Data

open Finset

variable {P : Parameters} (D : Data P)

open scoped Classical in
/-- The element `D.e₀` of the group algebra ℂ[𝖦], the sum of the idempotents `New.tupleIdem` over
the families in `D.goodTupleFamilies`, is a central idempotent (self-adjoint by
`New.IsCentralProj.self_adjoint`). -/
lemma isCentralProj_e₀ : IsCentralProj D.e₀ := isCentralProj_sum_tupleIdem

open scoped Classical in
/-- The idempotent `e₀` kills a pure tensor that has a hyperplane sum as a factor. Let `x = (x_v)`
be a family of elements of the group algebras ℂ[GL_r(𝔽_v)], where `v` runs over the chosen places
(the finite places of E that divide `D.piM` and one of the two level primes p₀, p₁) and 𝔽_v is the
residue field. Suppose that at one place `v` the member `x_v` is `New.hyperplaneSum χ l`, the sum of
`χ(det h)⁻¹ h` over the invertible `h = 1 + u lᵀ`, where `l ≠ 0` and `χ` is a character of 𝔽_v with
`χ ^ q₂ = 1` for `q₂ = (q₀ d) ^ (s + 6)` (`q₀`, `d` the parameters of `P`, `s = D.towerExp`). Then
`(⊗ x_v) * e₀ = 0`. -/
lemma hyperplaneSum_mul_e₀
    {x : ∀ v : Σ i : Fin 2, D.ChosenPlace i,
      MonoidAlgebra ℂ (GL D.RowIndex (ResField (D.chosenPlace v)))}
    (v : Σ i : Fin 2, D.ChosenPlace i) {χ : MulChar (ResField (D.chosenPlace v)) ℂ}
    {l : D.RowIndex → ResField (D.chosenPlace v)} (hχ : χ ^ P.q₂ D.towerExp = 1) (hl : l ≠ 0)
    (hx : x v = hyperplaneSum χ l) : piTensorElem x * D.e₀ = 0 := by
  obtain ⟨i, w⟩ := v
  rw [e₀, mul_sum]
  refine sum_eq_zero fun c hc ↦ ?_
  rw [tupleIdem]
  refine piTensorElem_mul_eq_zero ⟨i, w⟩ ?_
  -- A good label has no `q₂`-th root of unity of the residue field as a root, and the unit
  -- `charName χ`, the image of `χ` under the isomorphism of characters with units, is such a root.
  obtain ⟨h_allowed, -⟩ := mem_goodTuples.1 (D.mem_goodTupleFamilies.1 hc i)
  rw [hx]
  exact hyperplaneSum_mul_labelIdem ((h_allowed w).not_isRoot (charName_pow_eq_one hχ)) hl
end New.Data

end
