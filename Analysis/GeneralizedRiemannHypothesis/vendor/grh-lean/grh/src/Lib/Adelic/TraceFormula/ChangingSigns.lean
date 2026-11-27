import Lib.ClassField.Global.CMSplittingCharacters
import Lib.General.LinearAlgebra.Eigenvalues
import Lib.General.NumberTheory.CMFields
import Lib.Shimura.HeckeTower.HeckeData

/-!
# Types of frames with a similitude, and the permutation of orbits that changes signs

Let E be a CM field with CM type Φ and y ∈ GL_n(E). If the characteristic polynomial of y is
separable, its roots under an embedding into ℂ are numbered by `New.Variety.numberedRoots`.
`New.Variety.MarkedTriple` K Z is the set of triples (xK, y, μ), x ∈ GL_n(𝔸_f), y ∈ GL_n(E) and
μ ∈ Z; z ∈ GL_n(E) acts on it by (xK, y, μ) ↦ (zxK, zyz⁻¹, μ).

* `New.Variety.IsEllipticSimilitude`: y has irreducible characteristic polynomial and is a
  similitude of a form β with multiplier ν, all of whose eigenvalues r satisfy r r̄ = ν.
* `New.Variety.HasSignType`: y is an elliptic similitude of a form β whose Gram matrix in the finite
  frame x satisfies a given condition, with signs ε on the eigenvectors of y at each infinite place.
* `New.Variety.exists_hasSignType_mul_iff`: for signs η of product 1, moving the frame by a suitable
  finite adelic matrix U changes the signs by η, and these moves permute the orbits of marked
  triples.

Notions from other files:
* `Φ w`: the embedding of E into ℂ that the CM type chooses at the infinite place w.
* `𝔸f E`: the ring of finite adeles of E.

## Relation to the literature

Known; see `Lib.Adelic.TraceFormula.TraceComparison` for sources.
-/

open Equiv NumberField Matrix Polynomial ComplexOrder Algebra InfinitePlace MulAction AdjoinRoot
  Finset RingHom Lagrange IsAlgClosed Function

namespace New.Variety

variable {E n Z : Type} [Field E] [Fintype n] [DecidableEq n] {y : GL n E}

/-- For y in GL_n(E) with separable characteristic polynomial P and an embedding t of E into ℂ,
the numbering `New.Variety.numberedRoots` lists the complex roots of t(P), each once. -/
lemma roots_eq_map_numberedRoots (h_sep : y.val.charpoly.Separable) (t : E →+* ℂ) :
    (y.val.charpoly.map t).roots = (univ : Finset n).val.map (numberedRoots t y.val.charpoly) := by
  -- A separable polynomial of degree `card n` has `card n` distinct complex roots, so they can be
  -- numbered by `n`, and `roots_map_eq_map_numberedRoots` applies.
  obtain ⟨r, hr⟩ : ∃ r : n ↪ ℂ,
      univ.map r = ⟨(y.val.charpoly.map t).roots, nodup_roots h_sep.map⟩ :=
    Embedding.exists_of_card_eq_finset (by simp [card_roots_eq_natDegree])
  exact roots_map_eq_map_numberedRoots ⟨r, (congrArg Finset.val hr).symm⟩

/-- If the characteristic polynomial of y is separable, then each numbered root of its image under t
is a root of the characteristic polynomial of the image of y under t. -/
lemma isRoot_numberedRoots (h_sep : y.val.charpoly.Separable) (t : E →+* ℂ) (i : n) :
    (y.map t).val.charpoly.IsRoot (numberedRoots t y.val.charpoly i) :=
  isRoot_of_mem_roots (by simp [roots_eq_map_numberedRoots h_sep, charpoly_map])

variable [CMType E]

lemma eval_interpolate_univ_node (r : n ↪ ℂ) (f : n → ℂ) (i : n) :
    (interpolate univ r f).eval (r i) = f i :=
  eval_interpolate_at_node _ r.injective.injOn (mem_univ i)

/-- The element y is an elliptic similitude of β with multiplier ν: its characteristic polynomial is
irreducible, ν ≠ 0, yᴴβy = νβ, and under each embedding of the CM type every complex root r of the
characteristic polynomial satisfies r r̄ = ν. -/
structure IsEllipticSimilitude (ν : ℚ) (y : GL n E) (β : Matrix n n E) : Prop where
  /-- The characteristic polynomial of y is irreducible. -/
  irreducible_charpoly : Irreducible y.val.charpoly
  /-- The multiplier is not zero. -/
  ne_zero : ν ≠ 0
  /-- The element y multiplies the form β by ν. -/
  conjTranspose_mul_mul : y.valᴴ * β * y.val = (ν : E) • β
  /-- Under each embedding of the CM type, every complex root r satisfies r r̄ = ν. -/
  root_mul_star_Φ (w : InfinitePlace E) (r : ℂ) (hr : r ∈ (y.val.charpoly.map (Φ w)).roots) :
    r * star r = ν

/-- The pair (y, x) has type ε for the multiplier ν and the condition F if there is a matrix β over
E such that (a) y is an elliptic similitude of β with multiplier ν
(`New.Variety.IsEllipticSimilitude`); (b) F holds for the Gram matrix xᴴβx over the finite adeles;
(c) at each infinite place w, βp_w(y) is positive definite, p_w the polynomial interpolating the
signs ε_w at the roots numbered by `New.Variety.numberedRoots`. -/
def HasSignType (ε : InfinitePlace E → n → ℤˣ) (ν : ℚ) (y : GL n E) (F : Set (Matrix n n (𝔸f E)))
    (x : GL n (𝔸f E)) : Prop :=
  ∃ β : Matrix n n E,
    IsEllipticSimilitude ν y β ∧
    x.valᴴ * β.map (↑) * x.val ∈ F ∧
    ∀ w : InfinitePlace E,
      (β.map (Φ w) * (interpolate univ (numberedRoots (Φ w) y.val.charpoly)
        fun i : n ↦ (ε w i : ℂ)).aeval (y.val.map (Φ w))).PosDef

/-- Let `y` be an elliptic similitude of `β` with multiplier `ν`: its characteristic polynomial is
irreducible, `ν ≠ 0`, `yᴴβy = νβ`, and under each embedding of the CM type every root `r` satisfies
`r r̄ = ν`. Let `w` be an infinite place and `σ` a permutation of the index set. Write `g` and `B`
for the images of `y` and `β` under the embedding of the CM type at `w`. Write `x_i` for the root
numbered `σ(i)` by `New.Variety.numberedRoots`. There are an invertible `k` and numbers `d_i` with
three properties. (a) `kᴴBk = diag(d)`. (b) For every polynomial `q`, `B·q(g)` is positive definite
iff all `d_i q(x_i) > 0`. (c) For signs `t` with all `d_i t_i > 0`, some invertible `k` has
`kᴴBk = diag(t)` and `k⁻¹gk = diag(x)`. -/
lemma exists_eigenbasis_diag_form {ν : ℚ} {β : Matrix n n E} (h : IsEllipticSimilitude ν y β)
    (w : InfinitePlace E) (σ : Perm n) :
    let x (i : n) := numberedRoots (Φ w) y.val.charpoly (σ i)
    let g := y.val.map (Φ w)
    let B := β.map (Φ w)
    ∃ (k : GL n ℂ) (d : n → ℂ),
      k.valᴴ * B * k = diagonal d ∧
      (∀ q : ℂ[X], (B * aeval g q).PosDef ↔ ∀ i : n, 0 < d i * q.eval (x i)) ∧
      ∀ t : n → ℤˣ, (∀ i : n, 0 < d i * t i) → ∃ k : GL n ℂ,
        k.valᴴ * B * k = signMatrix t ∧ k⁻¹.val * g * k = diagonal x := by
  intro x g B
  obtain ⟨k, hk⟩ : ∃ k : GL n ℂ, k.val * diagonal x = g * k :=
    isConj_diagonal_of_isRoot_charpoly (x := σ.toEmbedding.trans _) fun i ↦
      isRoot_numberedRoots h.irreducible_charpoly.separable _ (σ i)
  have hx (i : n) : x i * star (x i) = ν := h.root_mul_star_Φ w (x i)
    (by simp [x, roots_eq_map_numberedRoots h.irreducible_charpoly.separable])
  have hx_inj : x.Injective := (numberedRoots (Φ w) y.val.charpoly).injective.comp σ.injective
  -- In the eigenbasis `k` the similitude relation reads `x̄ i * G i j * x j = ν * G i j` for the
  -- Gram matrix `G`. As `x̄ i * x i = ν` and the roots are distinct, `G` is diagonal.
  let G : Matrix n n ℂ := k.valᴴ * B * k
  have h_gram : (diagonal x)ᴴ * G * diagonal x = (ν : ℂ) • G := by
    have h_map : gᴴ * B * g = (ν : ℂ) • B := by
      simp [g, B, ← map_conjTranspose_mul_mul, h.conjTranspose_mul_mul, map_smul']
    rw [← gram_mul, hk, gram_mul, h_map, Matrix.mul_smul, Matrix.smul_mul]
  have h_offDiag (i j : n) (hij : i ≠ j) : G i j = 0 := by
    have h_entry : star (x i) * G i j * x j = ν * G i j := by
      simpa [diagonal_conjTranspose] using congrFun₂ h_gram i j
    have h_zero : ν * (x j - x i) * G i j = 0 := by
      linear_combination x i * h_entry - G i j * x j * hx i
    simpa [h.ne_zero, sub_eq_zero, hx_inj.ne hij.symm] using h_zero
  obtain ⟨d, hd⟩ : ∃ d : n → ℂ, k.valᴴ * B * k = diagonal d :=
    ⟨G.diag, (IsDiag.diagonal_diag h_offDiag).symm⟩
  refine ⟨k, d, hd, fun q ↦ ?_, fun t ht ↦ ?_⟩
  · -- conjugating by `k` turns `B q(g)` into `diagonal d * q(diagonal x)`
    have h_conjugate : k.valᴴ * (B * aeval g q) * k = diagonal fun i ↦ d i * q.eval (x i) := by
      rw [← mul_assoc, mul_assoc, ← aeval_semiconj hk q, ← mul_assoc, hd]
      have h_diagonal : aeval (diagonal x) q = diagonal (aeval x q) :=
        aeval_algHom_apply (diagonalAlgHom ℂ) x q
      simp [h_diagonal]
    rw [← k.isUnit.posDef_star_left_conjugate_iff, star_eq_conjTranspose, h_conjugate,
      posDef_diagonal_iff]
  · -- rescale the eigenvectors by `t / c`, where `d t = c̄ c`
    have h_sq (i : n) : ∃ c : ℂ, d i * t i = star c * c :=
      CStarAlgebra.nonneg_iff_eq_star_mul_self.1 (ht i).le
    choose c hc using h_sq
    have hc_ne (i : n) : c i ≠ 0 := fun h_zero ↦ by simpa [hc, h_zero] using ht i
    let s : GL n ℂ := diagGL fun i ↦ .mk0 (t i / c i) (by simp [hc_ne])
    refine ⟨k * s, gram_mul_of_gram_eq hd ?_, ?_⟩
    · -- entrywise `t / c̄ * (d * t / c) = t / c̄ * (c̄ * c / c) = t`
      simp [s, signMatrix, ← mul_div_assoc, hc, mul_assoc]
      intro i
      field [hc_ne]
    · simp [s, ← mul_assoc g, ← hk, ← map_inv, mul_assoc]
      intro i
      field [hc_ne]

/-- Let y be an elliptic similitude of β with multiplier ν and let c be a polynomial with
y c(y) = ν. Then c(y) is the adjoint of y for β, that is, β c(y) = yᴴ β. -/
lemma mul_aeval_eq_conjTranspose_mul {ν : ℚ} {β : Matrix n n E}
    (h : IsEllipticSimilitude ν y β) {c : E[X]}
    (h_mul : y.val * aeval y.val c = (ν : E) • (1 : Matrix n n E)) :
    β * aeval y.val c = y.valᴴ * β := by
  refine smul_right_injective (Matrix n n E) (Rat.cast_ne_zero.2 h.ne_zero : (ν : E) ≠ 0) ?_
  calc (ν : E) • (β * aeval y.val c) = y.valᴴ * β * (y.val * aeval y.val c) := by
        rw [← smul_mul, ← h.conjTranspose_mul_mul, mul_assoc]
    _ = (ν : E) • (y.valᴴ * β) := by simp [h_mul]

/-- Let y be an elliptic similitude of β with multiplier ν, w an infinite place, and r_i the
numbered roots of its characteristic polynomial at w. If η_i δ(r_i) > 0 for a polynomial δ and
signs η_i, then β has signs ε at w iff β δ(y) has signs εη there. That is, at w the matrix β p(y)
is positive definite iff β δ(y) q(y) is, where p interpolates ε and q interpolates εη at the
roots. -/
lemma posDef_mul_interpolate_iff {ν : ℚ} {β : Matrix n n E} (h : IsEllipticSimilitude ν y β)
    (w : InfinitePlace E) {δ : E[X]} {η : n → ℤˣ}
    (h_sign : ∀ i : n,
      0 < (η i : ℂ) * (δ.map (Φ w)).eval (numberedRoots (Φ w) y.val.charpoly i))
    (ε : n → ℤˣ) :
    let r : n ↪ ℂ := numberedRoots (Φ w) y.val.charpoly
    let g : Matrix n n ℂ := y.val.map (Φ w)
    (β.map (Φ w) * (interpolate univ r fun i : n ↦ (ε i : ℂ)).aeval g).PosDef ↔
      ((β * aeval y.val δ).map (Φ w) *
        (interpolate univ r fun i : n ↦ ((ε * η) i : ℂ)).aeval g).PosDef := by
  intro r g
  -- for a suitable `d`, positivity of `β q(y)` is positivity of all `d i * q (r i)`
  obtain ⟨k, d, -, h_diag, -⟩ := exists_eigenbasis_diag_form h w 1
  have h_scalar (i : n) : 0 < d i * (ε i : ℂ) ↔
      0 < d i * ((δ.map (Φ w)).eval (r i) * ((ε i : ℂ) * (η i : ℂ))) := by
    rw [← mul_pos_iff_of_pos_right (h_sign i)]
    simp only [r, mul_assoc, mul_comm, mul_left_comm]
  rw [Matrix.map_mul, map_aeval_matrix, mul_assoc, ← map_mul, h_diag, h_diag]
  simpa [r, -interpolate_apply, eval_interpolate_univ_node] using forall_congr' h_scalar

/-- Let y be an elliptic similitude of a form with multiplier ν
(`New.Variety.IsEllipticSimilitude`). Then every complex root r of the characteristic polynomial
satisfies r r̄ = ν, under every embedding of E into ℂ. -/
lemma IsEllipticSimilitude.root_mul_star {ν : ℚ} {β : Matrix n n E}
    (h : IsEllipticSimilitude ν y β) (σ : E →+* ℂ) (r : ℂ)
    (hr : r ∈ (y.val.charpoly.map σ).roots) : r * star r = ν := by
  rcases Φ_mk_eq_or_star_eq σ with hσ | hσ
  · exact h.root_mul_star_Φ (.mk σ) r (by rwa [hσ])
  · rw [← hσ, roots_map_conjugate, Multiset.mem_map] at hr
    obtain ⟨s, hs, rfl⟩ := hr
    rw [star_star, mul_comm, h.root_mul_star_Φ (.mk σ) s hs]

/-- Let δ be a polynomial with δ(y) invertible. Then y is an elliptic similitude of β δ(y) with
multiplier ν if and only if it is one of β, because δ(y) commutes with y. -/
lemma isEllipticSimilitude_mul_aeval_iff {ν : ℚ} {β : Matrix n n E} {δ : E[X]}
    (h_unit : IsUnit (aeval y.val δ)) :
    IsEllipticSimilitude ν y (β * aeval y.val δ) ↔ IsEllipticSimilitude ν y β := by
  have h_sim : y.valᴴ * β * y.val = (ν : E) • β ↔
      y.valᴴ * (β * aeval y.val δ) * y.val = (ν : E) • (β * aeval y.val δ) := by
    rw [← h_unit.mul_left_inj]
    simp [aeval_semiconj, mul_assoc]
  exact ⟨fun h ↦ { h with conjTranspose_mul_mul := h_sim.2 h.conjTranspose_mul_mul },
    fun h ↦ { h with conjTranspose_mul_mul := h_sim.1 h.conjTranspose_mul_mul }⟩

/-- Let P, the characteristic polynomial of y, be irreducible. For each infinite place w let Φ w be
the embedding of the CM type at w and r_w the numbering of the complex roots of P under Φ w. Then
the embeddings of E[X]/(P) that extend Φ w and send the root to r_w i give different infinite
places for different pairs (w, i). -/
lemma eq_of_mk_lift_numberedRoots_eq [Fact (Irreducible y.val.charpoly)]
    (h_root : ∀ (w : InfinitePlace E) (i : n),
      y.val.charpoly.eval₂ (Φ w) (numberedRoots (Φ w) y.val.charpoly i) = 0)
    (w w' : InfinitePlace E) (i i' : n) (h_eq :
      InfinitePlace.mk (lift (Φ w') (numberedRoots (Φ w') y.val.charpoly i') (h_root w' i')) =
        InfinitePlace.mk (lift (Φ w) (numberedRoots (Φ w) y.val.charpoly i) (h_root w i))) :
    (w', i') = (w, i) := by
  let r (w : InfinitePlace E) : n ↪ ℂ := numberedRoots (Φ w) y.val.charpoly
  obtain ⟨h_emb, h_root_eq⟩ | ⟨h_emb, -⟩ : Φ w' = Φ w ∧ r w' i' = r w i ∨
      ComplexEmbedding.conjugate (Φ w') = Φ w ∧ starRingEnd ℂ (r w' i') = r w i := by
    simpa [r, InfinitePlace.mk_eq_iff, AdjoinRoot.ringHom_ext_iff] using h_eq
  · -- `Φ w` determines `w`, and the numbering of the roots is injective
    obtain rfl : w' = w := by rw [← mk_Φ w', h_emb, mk_Φ]
    rw [(r w').injective h_root_eq]
  · -- here too `w' = w`, so `Φ w` would be a real embedding of a CM field
    obtain rfl : w' = w := by rw [← mk_Φ w', ← mk_conjugate_eq, h_emb, mk_Φ]
    exact absurd h_emb (IsTotallyComplex.complexEmbedding_not_isReal (Φ w'))

/-- If the characteristic polynomial of y divides the difference of ḡ(c) g and δ, then
ḡ(c(y)) g(y) = δ(y) over the finite adeles, by the Cayley–Hamilton theorem. Here ḡ has the
conjugate coefficients of g. -/
lemma aeval_conj_comp_mul_aeval_eq {c δ : E[X]} {g : (𝔸f E)[X]}
    (hg : y.val.charpoly.map (algebraMap E (𝔸f E)) ∣
      (g.map (starRingEnd (𝔸f E))).comp (c.map (algebraMap E (𝔸f E))) * g -
        δ.map (algebraMap E (𝔸f E))) :
    aeval (y.val.map (algebraMap E (𝔸f E)))
        ((g.map (starRingEnd (𝔸f E))).comp (c.map (algebraMap E (𝔸f E)))) *
        aeval (y.val.map (algebraMap E (𝔸f E))) g =
      (aeval y.val δ).map (algebraMap E (𝔸f E)) := by
  rw [map_aeval_matrix, ← sub_eq_zero, ← map_mul, ← map_sub]
  exact aeval_eq_zero_of_dvd_aeval_eq_zero (by rwa [charpoly_map]) (aeval_self_charpoly _)

/-- Let y be an elliptic similitude with multiplier ν₀ and characteristic polynomial P, and let η be
signs of total product 1. There are polynomials δ, c over E and g over the finite adeles with four
properties: δ is prime to P; δ has the signs η at the numbered roots of P; modulo P the product
X c is the constant ν for each ν that is r r̄ for all complex roots r of P; and modulo P the product
of ḡ(c) and g is δ, where ḡ has the conjugate coefficients. -/
lemma exists_coprime_sign_dvd_norm_sub {ν₀ : ℚ} {β : Matrix n n E}
    (h : IsEllipticSimilitude ν₀ y β) {η : InfinitePlace E → n → ℤˣ}
    (hη : ∏ w : InfinitePlace E, ∏ i : n, η w i = 1) :
    ∃ (δ c : E[X]) (g : (𝔸f E)[X]),
      IsCoprime y.val.charpoly δ ∧
      (∀ (w : InfinitePlace E) (i : n),
        0 < (η w i : ℂ) * (δ.map (Φ w)).eval (numberedRoots (Φ w) y.val.charpoly i)) ∧
      (∀ ν : ℚ, (∀ σ : E →+* ℂ, ∀ r ∈ (y.val.charpoly.map σ).roots, r * star r = ν) →
        y.val.charpoly ∣ X * c - C (ν : E)) ∧
      y.val.charpoly.map (algebraMap E (𝔸f E)) ∣
        (g.map (starRingEnd (𝔸f E))).comp (c.map (algebraMap E (𝔸f E))) * g -
          δ.map (algebraMap E (𝔸f E)) := by
  -- In the CM field `L = E[X]/(P)`, class field theory gives `x ∈ Lˣ` with the signs `η` and a
  -- finite idele `u` with `x u ū = 1`. Then `δ` represents `x` and `g` represents `u⁻¹`.
  let P : E[X] := y.val.charpoly
  have hP : Fact (Irreducible P) := ⟨h.irreducible_charpoly⟩
  have : IsCMField (AdjoinRoot P) := isCMField_adjoinRoot_of_forall_root_mul_star_eq h.root_mul_star
  let : CMType (AdjoinRoot P) := ⟨⟩ -- `Φ` comes from the default `PlaceEmbedding` instance
  have h_root_eval (w : InfinitePlace E) (i : n) : P.eval₂ (Φ w) (numberedRoots (Φ w) P i) = 0 := by
    simpa [charpoly_map, eval_map] using isRoot_numberedRoots hP.out.separable (Φ w) i
  -- the embeddings of `L` over `Φ w`, one for each root; they give distinct infinite places
  let φ (w : InfinitePlace E) (i : n) : AdjoinRoot P →+* ℂ := lift _ _ (h_root_eval w i)
  let s (v : InfinitePlace (AdjoinRoot P)) : ℤˣ := ∏ (w) (i) with .mk (φ w i) = v, η w i
  have hs : ∏ v, s v = 1 := by rw [prod_fiberwise, prod_product, hη]
  obtain ⟨x, u, h_pos, h_norm⟩ := Cohomology.exists_sign_principalIdele_mul_norm_eq_one hs
  obtain ⟨δ, hδ⟩ : ∃ δ : E[X], AdjoinRoot.mk P δ = x.val := mk_surjective _
  obtain ⟨c, hc⟩ : ∃ c : E[X], AdjoinRoot.mk P c = star (root P) := mk_surjective _
  obtain ⟨g, hg⟩ : ∃ g : (𝔸f E)[X], aeval (algebraMap _ (𝔸f (AdjoinRoot P)) (root P)) g = ↑u⁻¹ :=
    aeval_root_finAdele_surjective y.val.charpoly_monic _
  refine ⟨δ, c, g, ?_, fun w i ↦ ?_, fun ν h_circle ↦ ?_, ?_⟩
  · rw [hP.out.coprime_iff_not_dvd, ← mk_eq_zero, hδ]
    exact x.ne_zero
  · -- only `(w, i)` lies over the place of `φ w i`
    have hs_eq : s (.mk (φ w i)) = η w i :=
      prod_eq_single_of_mem (w, i) (by simp) fun p hp hp_ne ↦ absurd
        (eq_of_mk_lift_numberedRoots_eq h_root_eval w p.1 i p.2 (by simpa [φ] using hp)) hp_ne
    simpa [← hδ, φ, eval_map, hs_eq] using h_pos (φ w i)
  · rw [← mk_eq_mk, map_mul, hc]
    simpa using adjoinRoot_root_mul_star h_circle
  · -- in the adeles of `L` the difference is `ū⁻¹ u⁻¹ - x = 0`
    have h_idele : star (u⁻¹) * u⁻¹ = principalIdele x := by
      rw [star_inv, ← mul_inv, mul_comm, inv_eq_of_mul_eq_one_left h_norm]
    rw [← aeval_root_finAdele_eq_zero_iff y.val.charpoly_monic, map_sub, map_mul,
      aeval_root_finAdele_map_conj_comp hc, aeval_root_finAdele_map, hg, hδ, sub_eq_zero]
    exact congrArg Units.val h_idele

/-- Let y be an elliptic similitude of β with multiplier ν and let P be its characteristic
polynomial. Let c, δ over E and g over the finite adeles be polynomials with X c = ν and
ḡ(c) g = δ modulo P. Then the Gram matrix of β in the frame g(y) is β δ(y). -/
lemma gram_aeval_eq_map_mul_aeval {ν : ℚ} {β : Matrix n n E}
    (h : IsEllipticSimilitude ν y β) {c δ : E[X]} {g : (𝔸f E)[X]}
    (hc : y.val.charpoly ∣ X * c - C (ν : E))
    (hg : y.val.charpoly.map (algebraMap E (𝔸f E)) ∣
      (g.map (starRingEnd (𝔸f E))).comp (c.map (algebraMap E (𝔸f E))) * g -
        δ.map (algebraMap E (𝔸f E))) :
    (aeval (y.val.map (algebraMap E (𝔸f E))) g)ᴴ * β.map (algebraMap E (𝔸f E)) *
        aeval (y.val.map (algebraMap E (𝔸f E))) g =
      (β * aeval y.val δ).map (algebraMap E (𝔸f E)) := by
  let j : E →+* 𝔸f E := algebraMap E (𝔸f E)
  let Y : Matrix n n (𝔸f E) := y.val.map j
  -- by Cayley–Hamilton the congruences become equations at `y`
  have h_mul : y.val * aeval y.val c = (ν : E) • (1 : Matrix n n E) := by
    simpa [sub_eq_zero, algebraMap_eq_smul_one] using
      aeval_eq_zero_of_dvd_aeval_eq_zero hc y.val.aeval_self_charpoly
  -- `c(y)` is the adjoint of `y`, hence `ḡ(c(y))` is that of `g(y)`
  have h_adj : β.map j * aeval Y (c.map j) = Yᴴ * β.map j := by
    rw [← map_aeval_matrix, ← Matrix.map_mul, mul_aeval_eq_conjTranspose_mul h h_mul,
      Matrix.map_mul, conjTranspose_map j fun a : E ↦ by simp [j]]
  calc (aeval Y g)ᴴ * β.map j * aeval Y g
      = β.map j * (aeval Y ((g.map (starRingEnd (𝔸f E))).comp (c.map j)) * aeval Y g) := by
        rw [← star_eq_conjTranspose, star_aeval, star_eq_conjTranspose, ← aeval_semiconj h_adj,
          aeval_comp, mul_assoc]
    _ = (β * aeval y.val δ).map j := by rw [aeval_conj_comp_mul_aeval_eq hg, Matrix.map_mul]

/-- For signs `η` of total product one and a polynomial `P` over `E` there is a polynomial `υ` over
the finite adeles of `E` such that, for every `y` with characteristic polynomial `P`, the matrix
`υ(y)` is a unit `U`, and for all `ν`, `ε`, `F` and `x` the pair `(y, x)` has type `εη`
(`New.Variety.HasSignType`: an elliptic similitude with multiplier `ν` of some form whose Gram
matrix in the frame lies in `F` and whose signs at infinity are given) iff `(y, U x)` has type
`ε`. -/
lemma exists_aeval_hasSignType_mul_iff (P : E[X]) {η : InfinitePlace E → n → ℤˣ}
    (hη : ∏ w : InfinitePlace E, ∏ i : n, η w i = 1) :
    ∃ υ : (𝔸f E)[X], ∀ y : GL n E, y.val.charpoly = P → ∃ U : GL n (𝔸f E),
      U.val = aeval (y.val.map (↑)) υ ∧
      ∀ (ν : ℚ) (ε : InfinitePlace E → n → ℤˣ) (F : Set (Matrix n n (𝔸f E))) (x : GL n (𝔸f E)),
        HasSignType (ε * η) ν y F x ↔ HasSignType ε ν y F (U * x) := by
  -- With `δ`, `c`, `g` as in `exists_coprime_sign_dvd_norm_sub` take `υ = g`: the map
  -- `β ↦ β δ(y)` takes the forms for `(y, U x)` and `ε` to those for `(y, x)` and `ε η`.
  by_cases! h_none : ∀ (z : GL n E) (ν₀ : ℚ) (β₀ : Matrix n n E),
      z.val.charpoly = P → ¬IsEllipticSimilitude ν₀ z β₀
  · -- no type occurs for `P`, so `1` will do
    exact ⟨1, fun y hy ↦ ⟨1, by simp, fun ν ε F x ↦ by simp [HasSignType, h_none y ν _ hy]⟩⟩
  obtain ⟨z, ν₀, β₀, rfl, hz⟩ := h_none
  obtain ⟨δ, c, g, h_coprime, h_sign, hc, hg⟩ := exists_coprime_sign_dvd_norm_sub hz hη
  refine ⟨g, fun y hy ↦ ?_⟩
  rw [← hy] at h_coprime h_sign hc hg
  have h_unit : IsUnit (aeval y.val δ) := isUnit_aeval_iff_isCoprime.mpr h_coprime
  obtain ⟨U, hU⟩ : IsUnit (aeval (y.val.map (algebraMap E (𝔸f E))) g) := by
    -- `ḡ(c(y)) g(y) = δ(y)` is a unit
    apply isUnit_of_mul_isUnit_right
    rw [aeval_conj_comp_mul_aeval_eq hg]
    exact h_unit.map (algebraMap E (𝔸f E)).mapMatrix
  -- compare the form `β` for `(y, U x)` with the form `β δ(y)` for `(y, x)`
  refine ⟨U, hU, fun ν ε F x ↦ (h_unit.unit.mulRight.exists_congr fun β ↦ ?_).symm⟩
  have h_ell : IsEllipticSimilitude ν y (β * aeval y.val δ) ↔ IsEllipticSimilitude ν y β :=
    isEllipticSimilitude_mul_aeval_iff h_unit
  rw [Units.mulRight_apply, h_unit.unit_spec, h_ell]
  refine and_congr_right fun h ↦ and_congr ?_
    (forall_congr' fun w ↦ posDef_mul_interpolate_iff h w (h_sign w) (ε w))
  -- the Gram matrix of `β` in the frame `U x` is that of `β δ(y)` in the frame `x`
  have h_frame : (U * x).valᴴ * β.map (algebraMap E (𝔸f E)) * (U * x).val =
      x.valᴴ * (β * aeval y.val δ).map (algebraMap E (𝔸f E)) * x.val := by
    rw [Units.val_mul, gram_mul, hU, gram_aeval_eq_map_mul_aeval h (hc ν h.root_mul_star) hg]
  rw [h_frame]

/-- Change of signs. Let η assign a sign to each mark μ, infinite place w and index i, with product
1 for each μ. A marked triple (q, y, μ) is a coset q ∈ GL_n(𝔸_f)/`K`, y ∈ GL_n(E) and a mark μ;
GL_n(E) acts by left translation on q and by conjugation on y. There is a permutation e of the
orbits such that for every y ∈ GL_n(E) and mark μ some U ∈ GL_n(𝔸_f) satisfies: (a) for all ν, ε, F
and x, the pair (y, x) has type εη_μ iff (y, Ux) has type ε (`New.Variety.HasSignType`: for some β,
y is an elliptic similitude of β with multiplier ν, F holds for xᴴβx, and signs ε hold at infinity);
(b) U commutes with the image of every z ∈ GL_n(E) that commutes with y; (c) e sends the orbit of
(q, y, μ) to the orbit of (Uq, y, μ). -/
lemma exists_hasSignType_mul_iff (η : Z → InfinitePlace E → n → ℤˣ)
    (hη : ∀ μ : Z, ∏ w : InfinitePlace E, ∏ i : n, η μ w i = 1) (K : Subgroup (GL n (𝔸f E))) :
    ∃ e : Perm (orbitRel.Quotient (GL n E) (MarkedTriple K Z)), ∀ (y : GL n E) (μ : Z),
      ∃ U : GL n (𝔸f E),
      (∀ (ν : ℚ) (ε : InfinitePlace E → n → ℤˣ) (F : Set (Matrix n n (𝔸f E))) (x : GL n (𝔸f E)),
        HasSignType (ε * η μ) ν y F x ↔ HasSignType ε ν y F (U * x)) ∧
      (∀ z : GL n E, Commute y z → Commute (toFinGL z) U) ∧
      ∀ q : GL n (𝔸f E) ⧸ K, e ⟦(q, y, μ)⟧ = ⟦(U • q, y, μ)⟧ := by
  -- For each polynomial `P` and each `μ` one polynomial `υ` gives `U = υ(y)` for all `y` with
  -- characteristic polynomial `P`.
  choose υ U hU h_typ using fun (P : E[X]) (μ : Z) ↦ exists_aeval_hasSignType_mul_iff P (hη μ)
  let V (μ : Z) (y : GL n E) : GL n (𝔸f E) := U y.val.charpoly μ y rfl
  -- so `U` is compatible with conjugation by rational matrices
  have h_conj (z y : GL n E) (μ : Z) : SemiconjBy (toFinGL z) (V μ y) (V μ (z * y * z⁻¹)) := by
    have h_semiconj : SemiconjBy (toFinGL z) (toFinGL y) (toFinGL (z * y * z⁻¹)) :=
      (SemiconjBy.conj_mk z y).map toFinGL
    -- `V μ y` and `V μ (z * y * z⁻¹)` are values of one polynomial
    have h_charpoly : (z * y * z⁻¹).val.charpoly = y.val.charpoly := by simp
    refine .units_of_val ?_
    simp only [V, hU, h_charpoly]
    exact aeval_semiconj h_semiconj.units_val (υ y.val.charpoly μ)
  -- hence `(q, y, μ) ↦ (U • q, y, μ)` is equivariant and passes to the orbits
  let σ : Perm (MarkedTriple K Z) := prodCongrLeft fun (y, μ) ↦ toPerm (V μ y)
  have h_equiv (z : GL n E) : ∀ p : MarkedTriple K Z, σ (z • p) = z • σ p := fun (q, y, μ) ↦ by
    change (V μ (z * y * z⁻¹) • toFinGL z • q, z * y * z⁻¹, μ) =
      (toFinGL z • V μ y • q, z * y * z⁻¹, μ)
    rw [← mul_smul, ← mul_smul, (h_conj z y μ).eq]
  have h_orbit (p q) : orbitRel (GL n E) _ p q ↔ orbitRel (GL n E) _ (σ p) (σ q) := by
    simp only [orbitRel_apply, MulAction.mem_orbit_iff, ← h_equiv, σ.apply_eq_iff_eq]
  refine ⟨Quotient.congr σ h_orbit,
    fun y μ ↦ ⟨V μ y, h_typ y.val.charpoly μ y rfl, fun z h_comm ↦ ?_, fun q ↦ rfl⟩⟩
  -- commutation is `h_conj` for a `z` with `z * y * z⁻¹ = y`
  simpa [← h_comm.eq, Commute] using h_conj z y μ

end New.Variety
