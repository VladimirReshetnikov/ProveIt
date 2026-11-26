import Lib.Adelic.Hecke.Basic
import Lib.General.Groups.BesselGroups

/-!
# Integral matrices over subrings: Smith normal form, Gelfand's condition and lattices

This file studies matrices over a commutative ring `A` that are integral with respect to a subring
`R`. The model is the ring of integral adeles inside the finite adeles. `New.IsIntMatrix R M` says
that all entries of `M` lie in `R`. The property `New.IsValuationPair R` says that of two elements
of `A` one divides the other over `R`, piece by piece along an idempotent of `R`. The file also
defines column lattices and indices of lattices, and studies principal congruence subgroups of
unitary groups.

## Main definitions and results

* `New.IsValuationPair.smith_normal_form`: a square matrix over `A` is diagonalized by row and
  column operations over a subring `R` that satisfies `New.IsValuationPair`.
* `New.exists_invTransposeGL_inv_eq`: for such a subring `O` of `R`, `gᵀ` lies in the double coset
  `GL n O * g * GL n O`.
* `New.IsHeckeFunction.heckeFun_adjoint`, `New.IsHeckeFunction.heckeFun_comm`: adjoints and
  commutativity of Hecke operators for `K = GL n O`, with `O` a valuation subring of a field.
* `New.submoduleIndex`, `New.denomIndex`: the relative index of two `R`-modules, and the index of
  the denominator of `a`. An infinite index is read as `0`.
* `New.colLattice`, `New.preimageLattice`: the span of the columns of `M`, and the vectors `M` makes
  integral.
* `New.unitaryLevel`: the principal congruence subgroup of the unitary group `New.U J`.

Notions from other files:
* `New.intGL n O`: for a subring `O` of `R`, the subgroup of `GL n R` of matrices that have,
  together with their inverse, all entries in `O`.
* `New.U J`: the unitary group of `J`, the `g` in `GL n R` with `gᴴ * J * g = J`.
* `New.heckeFun π K f`: the operator `∑ f g • π g`, summed over chosen representatives `g` of
  `G ⧸ K` (zero if infinitely many terms are nonzero).
* `New.IsHeckeFunction K f`: `f` is left and right `K`-invariant and supported on finitely many
  cosets `g K`.
* `New.levelSpace π K`: the vectors of the representation `π` that are fixed by `K`.

## Relation to the literature

Known result: Commutativity of the spherical Hecke algebra of GL_n. This file proves the case that
is used, by Gelfand's trick: over a valuation subring of a field the Hecke operators commute on
fixed vectors of a representation. Source: J. Tits, Reductive groups over local fields, Corvallis
1979, 3.3.3; T. Tamagawa, On the zeta functions of a division algebra, Ann. Math. 77 (1963).

Part of a known result: the valuation pairs and integral matrices of this file are groundwork for
Witt's extension theorem for unimodular hermitian lattices and for the Iwasawa decomposition (see
`Lib.Adelic.Witt.IwasawaDecomposition`).
-/

noncomputable section

/-!
## Generalised inverses and matrix factorisations over a field

* `New.exists_mul_add_mul_eq_one`: if the kernel of `x` lies in the column space of `y`, then
  `y * e + b * x = 1` for some matrices `e` and `b`.

`x.mulVecLin.range` is the column space of `x`.
-/

section GeneralizedInverse

open Matrix

variable {k l m n : Type*} [Field k] [Fintype n] {x : Matrix m n k}

/-- Let `f` be a linear map between vector spaces over a field. Then `f` has a generalised inverse:
a linear map `s` with f(s(f x)) = f x for all x. -/
lemma New.exists_generalized_inverse {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module k M]
    [Module k N] (f : M →ₗ[k] N) :
    ∃ s : N →ₗ[k] M, ∀ x : M, f (s (f x)) = f x := by
  -- extend a right inverse of `f`, viewed as a map onto its range, to all of `N`
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective (by simp)
  obtain ⟨s, rfl⟩ := g.exists_extend
  exact ⟨s, fun x ↦ congrArg Subtype.val (LinearMap.congr_fun hg ⟨f x, x, rfl⟩)⟩

/-- Let `x` and `y` be matrices over a field. If every column of `y` lies in the column space of
`x`, then y = x * s for some matrix s. -/
lemma New.Filling.exists_mul_eq_of_col_mem_range {y : Matrix m l k}
    (h_col : ∀ b : l, y.col b ∈ x.mulVecLin.range) : ∃ s : Matrix n l k, x * s = y := by
  choose c hc using h_col
  exact ⟨of fun i b ↦ c b i, ext_col hc⟩

/-- Let `x` and `y` be matrices over a field. If the kernel of `x` lies in the column space of `y`,
then `y * e + b * x = 1` for some matrices `e` and `b`. -/
lemma New.exists_mul_add_mul_eq_one [Fintype l] [Fintype m] [DecidableEq n] {y : Matrix n l k}
    (h_range : x.mulVecLin.ker ≤ y.mulVecLin.range) :
    ∃ (e : Matrix l n k) (b : Matrix n m k), y * e + b * x = 1 := by
  classical
  -- Take a generalised inverse `b` of `x`. Then `v - b (x v)` is killed by `x`, so it lies in the
  -- column space of `y`; that is, the columns of `1 - b x` lie there.
  obtain ⟨b, hb⟩ : ∃ b : (m → k) →ₗ[k] n → k, ∀ v : n → k, x *ᵥ b (x *ᵥ v) = x *ᵥ v :=
    exists_generalized_inverse x.toLin'
  have h_ker (v : n → k) : v - b (x *ᵥ v) ∈ x.mulVecLin.ker := by simp [mulVec_sub, hb]
  obtain ⟨e, he⟩ : ∃ e : Matrix l n k, y * e = 1 - b.toMatrix' * x := by
    refine Filling.exists_mul_eq_of_col_mem_range fun j ↦ ?_
    rw [← mulVec_single_one, sub_mulVec, one_mulVec, ← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    exact h_range (h_ker (Pi.single j 1))
  exact ⟨e, b.toMatrix', add_eq_of_eq_sub he⟩

end GeneralizedInverse

/-!
## Valuation pairs and cutting along idempotents

Cutting along an idempotent `e` of `A` replaces a matrix `g` by `e g + (1 - e)`.
-/

namespace New

variable {A : Type*} [CommRing A] (R : Subring A) {n : Type*} [Fintype n] [DecidableEq n] {e : A}

/-- For all `a b : A` there is an idempotent `e` of `R` such that `a` and `b` are `R`-multiples of
`(1 - e) a + e b`. For a valuation ring take `e = 0` or `e = 1`. -/
abbrev IsValuationPair : Prop :=
  ∀ a b : A, ∃ e : R, e.val * e = e ∧ R ∙ a ⊔ R ∙ b ≤ R ∙ (a - e * (a - b))

/-- A valuation subring `O` of a field `F` satisfies `New.IsValuationPair`: of two elements of `F`
one is an `O`-multiple of the other. -/
lemma isValuationPair_valuationSubring {F : Type*} [Field F] (O : ValuationSubring F) :
    IsValuationPair O.toSubring := by
  intro a b
  suffices ∃ e : F, e * e = e ∧ (∃ y ∈ O, a = (a - e * (a - b)) * y) ∧ e ∈ O ∧
      ∃ y ∈ O, b = (a - e * (a - b)) * y by simpa
  -- one of `a`, `b` divides the other; the idempotent `1` picks `b`, the idempotent `0` picks `a`
  have h_dvd : (∃ y ∈ O, a = b * y) ∨ ∃ y ∈ O, b = a * y := by
    grind [O.mem_or_inv_mem (a / b), O.zero_mem]
  rcases h_dvd with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · exact ⟨1, one_mul 1, ⟨y, hy, by ring⟩, O.one_mem, 1, O.one_mem, by ring⟩
  · exact ⟨0, zero_mul 0, ⟨1, O.one_mem, by ring⟩, O.zero_mem, y, hy, by ring⟩

/-- If `R ⊆ A` satisfies `New.IsValuationPair`, so does `R` as a subring of itself. -/
lemma IsValuationPair.top : IsValuationPair R → IsValuationPair (⊤ : Subring R) := by
  simp_all [Subtype.ext_iff, IsValuationPair]

/-- For an idempotent e of the commutative ring A, the endomorphism g ↦ e·g + (1−e)·1 of GL_n(A). -/
def cutGL (he : IsIdempotentElem e) : GL n A →* GL n A :=
  Units.map
    { toFun g := e • g + (1 - e) • 1
      map_one' := by simp
      map_mul' := by simp [he.eq, mul_add, add_mul, smul_smul, mul_sub, sub_mul] }

/-- Cutting patches two invertible matrices `c` and `d` to the invertible matrix
`e • d + (1 - e) • c`. -/
lemma val_mul_cutGL_inv_mul (he : IsIdempotentElem e) (c d : GL n A) :
    (c * cutGL he (c⁻¹ * d)).val = e • d.val + (1 - e) • c.val := by
  have cut_val (g : GL n A) : (cutGL he g).val = e • g.val + (1 - e) • 1 := rfl
  rw [Units.val_mul, cut_val]
  simp [mul_add, -Matrix.coe_units_inv]

/-- For a self-adjoint idempotent e of A, the endomorphism g ↦ e·g + (1−e)·1 of the unitary group of
the identity form, the g in GL_n(A) with gᴴg = 1. -/
def U.cutAt (he : IsIdempotentElem e) [StarRing A] (hs : star e = e) :
    U (1 : Matrix n n A) →* U (1 : Matrix n n A) :=
  ((cutGL he).comp (U 1).subtype).codRestrict (U 1) <| by
    simp_all [mem_U, cutGL, he.eq, mul_add, add_mul, smul_smul, mul_sub]

end New

/-! ## Smith normal form over valuation pairs -/

section Smith

open Matrix Submodule Fintype GeneralLinearGroup

/-- Let `R ⊆ A` satisfy `New.IsValuationPair`. As `a`, `b` run through the invertible matrices over
`R`, the `R`-modules generated by the `(p, p)` entry of `a * y * b` form a directed family. -/
lemma New.IsValuationPair.directed_span_pivot {A n : Type*} [CommRing A] {R : Subring A}
    [Fintype n] [DecidableEq n] (hR : IsValuationPair R) (y : Matrix n n A) (p : n) :
    Directed (· ≤ ·) fun c : GL n R × GL n R ↦
      R ∙ ((map R.subtype c.fst).val * y * (map R.subtype c.snd).val) p p := by
  -- Patch `c` and `d` to `(1 - e) c + e d` along the idempotent `e` given by `hR`.
  rintro ⟨c, c'⟩ ⟨d, d'⟩
  let B (a b : GL n R) : A := ((map R.subtype a).val * y * (map R.subtype b).val) p p
  obtain ⟨e, he, h_le⟩ : ∃ e : R, e.val * e = e ∧
      R ∙ B c c' ⊔ R ∙ B d d' ≤ R ∙ (B c c' - e * (B c c' - B d d')) := hR _ _
  have he_idem : IsIdempotentElem e := Subtype.ext he
  let patch (a b : GL n R) : GL n R := a * cutGL he_idem (a⁻¹ * b)
  have patch_val (a b : GL n R) : (map R.subtype (patch a b)).val =
      e.val • (map R.subtype b).val + (1 - e.val) • (map R.subtype a).val := by
    ext
    simp only [patch, val_map_apply, val_mul_cutGL_inv_mul]
    simp
  -- The mixed terms carry the factor `e * (1 - e) = 0`.
  have patch_entry : B (patch c d) (patch c' d') = B c c' - e * (B c c' - B d d') := by
    simp only [B, patch_val, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    grind
  rw [← patch_entry, sup_le_iff] at h_le
  exact ⟨(patch c d, patch c' d'), h_le⟩

/-- Existence of a pivot: if `R ⊆ A` satisfies `New.IsValuationPair`, then for suitable invertible
matrices `a`, `b` over `R` every entry of `a * y * b` is an `R`-multiple of its `(p, p)` entry. -/
lemma New.IsValuationPair.exists_pivot_dvd {A n : Type*} [CommRing A] {R : Subring A} [Fintype n]
    [DecidableEq n] (hR : IsValuationPair R) (y : Matrix n n A) (p : n) :
    ∃ a b : GL n R, ∀ i j : n, ∃ w : R,
      w * ((map R.subtype a).val * y * (map R.subtype b).val) p p =
        ((map R.subtype a).val * y * (map R.subtype b).val) i j := by
  let B (c : GL n R × GL n R) : Matrix n n A :=
    (map R.subtype c.fst).val * y * (map R.subtype c.snd).val
  -- Swapping rows and columns brings any entry `y i j` to the place `(p, p)`, so a common upper
  -- bound `R ∙ B c p p` of these finitely many modules contains all entries of `y`.
  obtain ⟨c, hc⟩ : ∃ c : GL n R × GL n R,
      ∀ ij : n × n, R ∙ B (.swap R p ij.fst, .swap R p ij.snd) p p ≤ R ∙ B c p p :=
    (hR.directed_span_pivot y p).finite_le fun ij : n × n ↦ (.swap R p ij.fst, .swap R p ij.snd)
  have y_mem (i j : n) : y i j ∈ R ∙ B c p p := by
    simpa [B, -val_map_apply] using hc (i, j)
  -- The entries of `B c` are `R`-linear combinations of those of `y`, so the pivot divides them.
  refine ⟨c.fst, c.snd, fun i j ↦ mem_span_singleton.1 ?_⟩
  change B c i j ∈ R ∙ B c p p
  rw [show B c i j = ∑ s : n, c.snd s j • ∑ r : n, c.fst i r • y r s by
    simp [B, mul_apply, R.smul_def, mul_comm]]
  exact sum_smul_mem _ _ fun s _ ↦ sum_smul_mem _ _ fun r _ ↦ y_mem r s

/-- One elimination step. Let every entry `M i j` be the multiple `w i j * M p p` of the pivot, with
`w i j` in the subring `R`. Subtract `w i p` times row `p` from each row `i`. If the block of the
result away from `p` is diagonalized by invertible matrices over `R`, then so is `M`. -/
lemma New.exists_eq_mul_diagonal_mul_of_pivot_dvd {A n : Type*} [CommRing A] {R : Subring A}
    [Fintype n] [DecidableEq n] {M : Matrix n n A} {p : n} {w : n → n → R}
    (hw : ∀ i j : n, w i j * M p p = M i j) {k l : GL {i : n // i ≠ p} R} {d : {i : n // i ≠ p} → A}
    (h_block : (M - of fun i : n ↦ w i p • M p).toBlock (· ≠ p) (· ≠ p) =
      (map R.subtype k).val * diagonal d * (map R.subtype l).val) :
    ∃ (lower upper : GL n R) (D : n → A),
      M = (map R.subtype lower).val * diagonal D * (map R.subtype upper).val := by
  let e : {i : n // i = p} ⊕ {i : n // i ≠ p} ≃ n := Equiv.sumCompl (· = p)
  let lower : GL n R := .mk'' (reindex e e (fromBlocks 1 0 (of fun i j ↦ w i j) k)) (by simp)
  let upper : GL n R := .mk'' (reindex e e (fromBlocks 1 (of fun i j ↦ w i j) 0 l)) (by simp)
  let D : n → A := Sum.elim (fun _ ↦ M p p) d ∘ e.symm
  have block_entry (i j : {i : n // i ≠ p}) :
      M i j - w i p * M p j = ∑ s : {i : n // i ≠ p}, k i s * d s * l s j := by
    simpa [↓mul_diagonal, mul_apply, R.smul_def] using congrFun₂ h_block i j
  have default_val : ((default : {i : n // i = p}) : n) = p := rfl
  refine ⟨lower, upper, D, (reindex e.symm e.symm).injective ?_⟩
  suffices M.submatrix e e =
      fromBlocks 1 0 ((of fun i j ↦ w i.val j.val).map R.subtype) (map R.subtype k).val *
        diagonal (Sum.elim (fun _ : {i : n // i = p} ↦ M p p) d) *
        fromBlocks 1 ((of fun i j ↦ w i.val j.val).map R.subtype) 0 (map R.subtype l).val by
    -- reindexing along `e` turns `lower`, `diagonal D` and `upper` into these three block matrices
    simp [this, lower, upper, D, ← submatrix_mul_equiv _ _ _ e, fromBlocks_map, submatrix_map,
      Function.comp_assoc]
  rw [← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply]
  -- Block by block: the pivot; its row and column by `hw`; the rest by `block_entry` and
  -- `w i p * M p j = w i p * M p p * w p j`.
  ext (i | i) (j | j)
  · simp [e, Unique.eq_default, default_val]
  · simp [e, mul_comm (M p p), Unique.eq_default i, default_val, hw]
  · simp [e, Unique.eq_default j, default_val, hw]
  · suffices M i j = w i p * M p p * w p j + ∑ s : {i : n // i ≠ p}, k i s * d s * l s j by
      -- `↓`: the product with a diagonal matrix is simplified before `mul_apply` expands it
      simpa [e, ↓mul_diagonal, mul_apply, default_val]
    rw [← block_entry, ← hw p j]
    ring

/-- Smith normal form: if the subring `R` of `A` satisfies `New.IsValuationPair`, every square
matrix `y` over `A` is `k * diagonal d * k'`, where `d : n → A` and `k`, `k'` and their inverses
have entries in `R`. No divisibility among the entries of `d` is stated. -/
lemma New.IsValuationPair.smith_normal_form {A n : Type*} [CommRing A] {R : Subring A} [Fintype n]
    [DecidableEq n] (hR : IsValuationPair R) (y : Matrix n n A) :
    ∃ᵉ (k ∈ intGL n R) (k' ∈ intGL n R) (d : n → A), y = k.val * diagonal d * k'.val := by
  -- Elimination, by induction on the size: bring a pivot that divides all entries to the place
  -- `(p, p)`, clear its row and column, and diagonalize the smaller block that is left.
  suffices ∃ (k k' : GL n R) (d : n → A),
      y = (map R.subtype k).val * diagonal d * (map R.subtype k').val by
    simpa only [intGL, MonoidHom.mem_range, exists_exists_eq_and]
  induction h : card n generalizing n with
  | zero => exact ⟨1, 1, 0, ext fun i ↦ ((card_eq_zero_iff.1 h).false i).elim⟩
  | succ m ih =>
    obtain ⟨p⟩ : Nonempty n := card_pos_iff.1 (by omega)
    obtain ⟨a, b, pivot_dvd⟩ := hR.exists_pivot_dvd y p
    set M : Matrix n n A := (map R.subtype a).val * y * (map R.subtype b).val with hM
    choose w hw using pivot_dvd
    obtain ⟨k, l, d, h_block⟩ :=
      ih ((M - of fun i : n ↦ w i p • M p).toBlock (· ≠ p) (· ≠ p)) (by simp [h])
    obtain ⟨lower, upper, D, factor⟩ := exists_eq_mul_diagonal_mul_of_pivot_dvd hw h_block
    refine ⟨a⁻¹ * lower, upper * b⁻¹, D, ?_⟩
    simp only [map_mul, map_inv, Units.val_mul, mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    simpa only [← mul_assoc, Units.eq_mul_inv_iff_mul_eq, hM] using factor

end Smith

/-!
## The inverse transpose and Gelfand's condition for GL_n at a place

The automorphism `g ↦ (gᵀ)⁻¹` of `GL n R`, written `transposeGL g⁻¹` (here `transposeGL g` is the
transpose `gᵀ` as an element of `GL n R`), preserves `GL n O`. When `O` satisfies
`New.IsValuationPair`, it sends `g⁻¹` into the double coset `GL n O * g * GL n O`. This is Gelfand's
condition for `K = GL n O`, where `O` is a valuation subring of a field.
-/

namespace New

open QuotientGroup Matrix Units

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] {O : Subring R}

/-- The automorphism g ↦ (gᵀ)⁻¹ of the group GL_n(R). -/
noncomputable def invTransposeGL : GL n R ≃* GL n R :=
  ⟨Equiv.mk (fun g ↦ transposeGL g⁻¹) (fun g ↦ transposeGL g⁻¹), by simp [← val_inj]⟩

lemma transposeGL_mem_intGL_iff (k : GL n R) : transposeGL k ∈ intGL n O ↔ k ∈ intGL n O := by
  rw [mem_intGL, mem_intGL]
  exact and_congr forall_comm forall_comm

lemma invTransposeGL_apply (g : GL n R) : invTransposeGL g = transposeGL g⁻¹ := rfl

@[simp]
lemma invTransposeGL_mem_intGL (k : GL n R) : invTransposeGL k ∈ intGL n O ↔ k ∈ intGL n O := by
  rw [invTransposeGL_apply, transposeGL_mem_intGL_iff, inv_mem_iff]

/-- If `O ⊆ R` satisfies `New.IsValuationPair`, the transpose `invTransposeGL g⁻¹` of any
`g ∈ GL n R` is `(kᵀ)⁻¹ * g * k` for some `k` in the subgroup `intGL n O` of integral points. -/
lemma exists_invTransposeGL_inv_eq (hO : IsValuationPair O) (g : GL n R) :
    ∃ k ∈ intGL n O, invTransposeGL g⁻¹ = invTransposeGL k * g * k := by
  -- `invTransposeGL g⁻¹` is the transpose of `g`. In Smith normal form `g = k * d * l` with `d`
  -- diagonal, the transpose is `lᵀ * d * kᵀ = (lᵀ * k⁻¹) * g * (l⁻¹ * kᵀ)`, and `lᵀ * k⁻¹` is the
  -- inverse transpose of `l⁻¹ * kᵀ`.
  obtain ⟨k, hk, l, hl, d, h_smith⟩ := hO.smith_normal_form g.val
  refine ⟨l⁻¹ * transposeGL k, mul_mem (inv_mem hl) ((transposeGL_mem_intGL_iff k).2 hk),
    Units.ext ?_⟩
  simp [invTransposeGL, transposeGL, h_smith, mul_assoc, -coe_units_inv]

variable {A W W' F : Type*} [CommSemiring A] [AddCommMonoid W] [Module A W] [AddCommMonoid W']
  [Module A W'] [Field F]
  {O : ValuationSubring F} {π : Representation A (GL n F) W} {π' : Representation A (GL n F) W'}
  {f f' : GL n F → A} {v : W}

/-! ### Gelfand's trick -/

/-- The adjoint of `f` is `g ↦ σ (f g⁻¹)`. Let `O` be a valuation subring of a field `F` and
`K = GL n O` in `GL n F`. Let `π`, `π'` be representations of `GL n F` over a commutative semiring
`A` on `W`, `W'`. For `f : GL n F → A`, `heckeFun π K f` is the operator `∑ f g • π g` over
representatives `g` of the cosets `g K`. Let `f` be left and right `K`-invariant and supported on
finitely many cosets `g K`. Let `B` be a `GL n F`-invariant pairing of `W` with `W'` that is
`σ`-semilinear in the first argument and linear in the second, and let `v`, `v'` be vectors fixed by
`K`. Then (a) `g ↦ σ (f g⁻¹)` is again left and right `K`-invariant and supported on finitely many
cosets, and (b) `B (heckeFun π K f v) v' = B v (heckeFun π' K (g ↦ σ (f g⁻¹)) v')`. -/
lemma IsHeckeFunction.heckeFun_adjoint (hf : IsHeckeFunction (intGL n O.toSubring) f) {σ : A →+* A}
    {Z : Type*} [AddCommMonoid Z] [Module A Z] (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v' : W'}
    (hv : v ∈ levelSpace (A := A) π (intGL n O.toSubring))
    (hB : ∀ (g : GL n F) (x : W) (y : W'), B (π g x) (π' g y) = B x y)
    (hv' : v' ∈ levelSpace π' (intGL n O.toSubring)) :
    letI K : Subgroup (GL n F) := intGL n O.toSubring
    IsHeckeFunction K (fun g : GL n F ↦ σ (f g⁻¹)) ∧
      B (heckeFun π K f v) v' = B v (heckeFun π' K (fun g : GL n F ↦ σ (f g⁻¹)) v') := by
  -- `invTransposeGL` permutes the cosets `g K` and sends `g` into `K g⁻¹ K`, so the
  -- `invTransposeGL g` serve as representatives in the sum for the adjoint.
  obtain ⟨hf_fin, hf_inv⟩ := hf
  set K : Subgroup (GL n F) := intGL n O.toSubring
  have transpose_term_eq (g : GL n F) :
      f (invTransposeGL g)⁻¹ = f g ∧ B v (π' (invTransposeGL g) v') = B (π g v) v' := by
    obtain ⟨k, hk, hg⟩ : ∃ k ∈ K, invTransposeGL g = invTransposeGL k * g⁻¹ * k := by
      simpa using exists_invTransposeGL_inv_eq (isValuationPair_valuationSubring O) g⁻¹
    have hk' : invTransposeGL k ∈ K := (invTransposeGL_mem_intGL k).2 hk
    -- Move `invTransposeGL k` and `g⁻¹` to the left side of `B`; `k` fixes `v'` and
    -- `(invTransposeGL k)⁻¹` fixes `v`.
    have move (g : GL n F) (x : W) (y : W') : B x (π' g y) = B (π g⁻¹ x) y := by simp [← hB g⁻¹ x]
    have fix_v : π (invTransposeGL k)⁻¹ v = v := by
      simpa using mem_levelSpace.1 hv ⟨_, inv_mem hk'⟩
    have fix_v' : π' k v' = v' := by simpa using mem_levelSpace.1 hv' ⟨k, hk⟩
    exact ⟨by simp [hg, hf_inv, hk, hk'],
      by simp only [hg, map_mul, Module.End.mul_apply, fix_v', move, fix_v, inv_inv]⟩
  obtain ⟨adjoint_finite, sum_eq⟩ : HasFiniteCosets K (fun g : GL n F ↦ σ (f g⁻¹)) ∧
      heckeFun π' K (fun g : GL n F ↦ σ (f g⁻¹)) v' = ∑ q ∈ hf_fin.toFinset,
        σ (f (invTransposeGL q.out)⁻¹) • π' (invTransposeGL q.out) v' :=
    heckeFun_eq_sum_pullback (by simp [hf_inv]) hv' hf_fin.toFinset invTransposeGL
      (fun g _ ↦ ⟨invTransposeGL.symm g, by simp⟩)
      (fun a b ↦ by rw [← map_inv, ← map_mul, invTransposeGL_mem_intGL])
      (by simp +contextual [transpose_term_eq])
  refine ⟨⟨adjoint_finite, fun g k hk ↦ by simp [hf_inv, hk]⟩, ?_⟩
  simp [sum_eq, heckeFun_eq_sum_toFinset hf_fin, transpose_term_eq]

/-- Let `O` be a valuation subring of a field `F`. A function `f` on `GL n F` that is left and right
invariant under `K = GL n O` and supported on finitely many cosets `g K` takes the same value at `g`
and at its transpose `invTransposeGL g⁻¹`. -/
lemma IsHeckeFunction.apply_invTransposeGL_inv (hf : IsHeckeFunction (intGL n O.toSubring) f)
    (g : GL n F) : f (invTransposeGL g⁻¹) = f g := by
  obtain ⟨k, hk, hg⟩ := exists_invTransposeGL_inv_eq (isValuationPair_valuationSubring O) g
  obtain ⟨-, hf_inv⟩ := hf
  simp [hg, hf_inv, hk, -map_inv]

/-- Let `K` be a subgroup of `GL n F`, let `f`, `f'` be left and right `K`-invariant and supported
on finitely many cosets `g K`, and let `v` be fixed by `K` in the representation `π`. The operator
of `f'` applied after the operator of `f` acts on `v` as the operator of the convolution
`x ↦ ∑ f' q * f (q⁻¹ * x)`, here written as a sum over representatives `q` of all cosets. -/
lemma IsHeckeFunction.heckeFun_heckeFun_eq_finsum {K : Subgroup (GL n F)} (hf : IsHeckeFunction K f)
    (hf' : IsHeckeFunction K f') (hv : v ∈ levelSpace π K) :
    heckeFun π K f' (heckeFun π K f v) =
      heckeFun π K (fun x : GL n F ↦ ∑ᶠ q : GL n F ⧸ K, f' q.out * f (q.out⁻¹ * x)) v := by
  obtain ⟨hf'_fin, -⟩ := hf'
  obtain ⟨hf_fin, hf_inv⟩ := hf
  have sum_eq (x : GL n F) : ∑ᶠ q : GL n F ⧸ K, f' q.out * f (q.out⁻¹ * x) =
      ∑ q ∈ hf'_fin.toFinset, f' q.out * f (q.out⁻¹ * x) :=
    finsum_eq_sum_of_support_subset _ fun q hq ↦ by simpa using left_ne_zero_of_mul hq
  simp only [sum_eq]
  exact heckeFun_heckeFun hf_fin (fun g k ↦ by simp [hf_inv]) hv hf'_fin

/-- Gelfand's trick. Let `O` be a valuation subring of a field `F`, `K = GL n O` in `GL n F`, and
`π` a representation of `GL n F` over a commutative semiring `A` on `W`. For `f : GL n F → A`,
`heckeFun π K f` is the operator `∑ f g • π g` over representatives `g` of the cosets `g K`. If `f`
and `f'` are left and right `K`-invariant and each is supported on finitely many cosets `g K`, then
their operators commute on every vector `v` fixed by `K`.

This is the commutativity of the spherical Hecke algebra (Gelfand, Satake) for `GL n` and
`K = GL n O`, stated for its action on `K`-fixed vectors. -/
lemma IsHeckeFunction.heckeFun_comm (hf : IsHeckeFunction (intGL n O.toSubring) f)
    (hf' : IsHeckeFunction (intGL n O.toSubring) f')
    (hv : v ∈ levelSpace (A := A) π (intGL n O.toSubring)) :
    letI T : (GL n F → A) → Module.End A W := heckeFun π (intGL n O.toSubring)
    T f (T f' v) = T f' (T f v) := by
  set K : Subgroup (GL n F) := intGL n O.toSubring
  -- Both composites are operators of convolutions; compare these at each `x`.
  rw [hf'.heckeFun_heckeFun_eq_finsum hf hv, hf.heckeFun_heckeFun_eq_finsum hf' hv]
  congr with x
  obtain ⟨b, hb_mem, hb_eq⟩ : ∃ b ∈ K, invTransposeGL x⁻¹ = invTransposeGL b * x * b :=
    exists_invTransposeGL_inv_eq (isValuationPair_valuationSubring O) x
  have hb_mem' : invTransposeGL b ∈ K := (invTransposeGL_mem_intGL b).2 hb_mem
  -- The bijection `e : q ↦ x * b * invTransposeGL q` of the coset space exchanges the two
  -- convolutions term by term.
  let e : GL n F ⧸ K ≃ GL n F ⧸ K :=
    Quotient.congr (invTransposeGL.toEquiv.trans (.mulLeft (x * b))) fun g g' ↦ by
      simp [leftRel_apply, K, ← invTransposeGL_mem_intGL (g⁻¹ * g'), mul_assoc]
  have e_mk (g : GL n F) : e ↑g = ↑(x * b * invTransposeGL g) := rfl
  refine .trans (finsum_congr fun q ↦ ?_) (finsum_comp_equiv e)
  obtain ⟨k, hk⟩ : ∃ k : K, (e q).out = x * b * invTransposeGL q.out * k := by
    simpa [← e_mk] using mk_out_eq_mul K (x * b * invTransposeGL q.out)
  -- By invariance under the transpose the right sides are
  -- `f' (invTransposeGL x⁻¹ * invTransposeGL q.out)` and `f (invTransposeGL q.out)⁻¹`.
  have hf'_eq : f' (x * b * invTransposeGL q.out * k) = f' (q.out⁻¹ * x) := by
    rw [← hf'.apply_invTransposeGL_inv (q.out⁻¹ * x), _root_.mul_inv_rev, map_mul, hb_eq]
    simp [hf'.right, mul_assoc (invTransposeGL b), hb_mem']
  have hf_eq : f ((x * b * invTransposeGL q.out * k)⁻¹ * x) = f q.out := by
    rw [← hf.apply_invTransposeGL_inv q.out]
    simp [mul_assoc, hf.right, hb_mem]
  rw [hk, hf'_eq, hf_eq, mul_comm]

end New

/-!
## Lattices over adelic pairs: indices, column lattices, unitary levels

* `New.IsAdelic`: the properties of `Ô ⊂ 𝔸f` that are used, as a class on `R ⊂ A`.
-/

section AdelicRingDefs

open Matrix

namespace New

variable {A : Type*} [CommRing A] (R : Subring A) {l m : Type*} {n : Type*} (M N : Matrix m n A)

/-! ### Integral vectors and matrices -/

/-- The R-module R^n of vectors in A^n with all entries in R. -/
def intVectors (n : Type*) : Submodule R (n → A) where
  carrier := {v : n → A | ∀ i : n, v i ∈ R}
  add_mem' := by aesop
  zero_mem' := by simp
  smul_mem' := by simp_all [mul_mem, R.smul_def]

/-- All entries of the matrix M lie in R. -/
def IsIntMatrix : Prop := ∀ (i : m) (j : n), M i j ∈ R

variable {R M N}

/-- The index of M ∩ M' in M', as additive groups (0 if infinite). -/
abbrev submoduleIndex (M M' : Submodule R (m → A)) : ℕ := M.toAddSubgroup.relIndex M'.toAddSubgroup

lemma IsIntMatrix.add (hM : IsIntMatrix R M) (hN : IsIntMatrix R N) : IsIntMatrix R (M + N) :=
  fun i j ↦ R.add_mem (hM i j) (hN i j)

lemma IsIntMatrix.sub (hM : IsIntMatrix R M) (hN : IsIntMatrix R N) : IsIntMatrix R (M - N) :=
  fun i j ↦ R.sub_mem (hM i j) (hN i j)

lemma IsIntMatrix.smul {a : A} (ha : a ∈ R) (hM : IsIntMatrix R M) : IsIntMatrix R (a • M) :=
  fun i j ↦ R.mul_mem ha (hM i j)

lemma IsIntMatrix.transpose (hM : IsIntMatrix R M) : IsIntMatrix R Mᵀ :=
  fun i j ↦ hM j i

lemma IsIntMatrix.one [DecidableEq n] : IsIntMatrix R (1 : Matrix n n A) :=
  fun i j ↦ by by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- Let `R` be a subring of the commutative ring `A` and `g` a unit of `A`. An element `x` of `A` is
an `R`-multiple of `g` if and only if `g⁻¹ * x` lies in `R`. -/
lemma Filling.mem_span_unit_iff {g : Aˣ} {x : A} : x ∈ R ∙ g.val ↔ g⁻¹.val * x ∈ R := by
  simp [← g.inv_mul_eq_iff_eq_mul]

variable [Fintype n]

lemma IsIntMatrix.mulVec {v : n → A} (hM : IsIntMatrix R M) (hv : v ∈ intVectors R n) :
    M *ᵥ v ∈ intVectors R m :=
  fun i ↦ R.sum_mem fun j _ ↦ R.mul_mem (hM i j) (hv j)

lemma IsIntMatrix.mul {N : Matrix n l A} (hM : IsIntMatrix R M) (hN : IsIntMatrix R N) :
    IsIntMatrix R (M * N) :=
  fun i j ↦ R.sum_mem fun k _ ↦ R.mul_mem (hM i k) (hN k j)

variable [DecidableEq n] (R M) (g : Aˣ) [StarRing A] [TopologicalSpace A]

/-- The subring R is stable under the involution of A. -/
class IsStarStable : Prop where
  /-- The conjugate of an element of `R` lies in `R`. -/
  star_mem {a : A} : a ∈ R → star a ∈ R

/-! ### Adelic pairs, indices, lattices and levels -/

/-- The properties of the pair Ô ⊂ 𝔸_f abstracted to R ⊂ A: R is open, compact and stable under
conjugation, locally a valuation ring, contains a skew element i with −i·i = 1 and an element of
trace 1, and −1 is a norm from R. -/
class IsAdelic (R : outParam (Subring A)) : Prop extends IsStarStable R where
  /-- `R` is open and compact in `A`. -/
  isOpen_isCompact : IsOpen (R : Set A) ∧ IsCompact (R : Set A)
  /-- Any two elements `a`, `b` of `A` are `R`-multiples of `(1 - e) * a + e * b` for some
  idempotent `e` of `R`, as in a product of valuation rings. -/
  isValuationPair : IsValuationPair R
  /-- Some `i ∈ R` has `-i * i = 1` and `star i = -i`, and some `τ ∈ R` has `τ + star τ = 1`. -/
  exists_skew_unit : ∃ i ∈ R, ∃ τ ∈ R, -i * i = 1 ∧ star i = -i ∧ τ + star τ = 1
  /-- `-1` is the norm `star c * c` of some `c ∈ R`. -/
  exists_norm_neg_one : ∃ c ∈ R, star c * c = -1

/-- The denominator of a: the index in R of the additive subgroup of the r ∈ R with ar ∈ R
(0 if infinite). -/
def denomIndex (a : A) : ℕ :=
  (R.toAddSubgroup.comap (AddMonoidHom.mulLeft a)).relIndex R.toAddSubgroup

/-- The R-module spanned by the columns of M. -/
def colLattice : Submodule R (m → A) := (intVectors R n).map (M.mulVecLin.restrictScalars R)

/-- The R-module of vectors v over A such that Mv has entries in R. -/
def preimageLattice : Submodule R (n → A) := (intVectors R m).comap (M.mulVecLin.restrictScalars R)

/-- The subgroup of the unitary group U(J) over A of elements lying in GL_n(R) and congruent to
1 modulo the unit g of A, that is, with g⁻¹(k − 1) integral. -/
def unitaryLevel (J : Matrix n n A) : Subgroup (U J) :=
  ((congruenceGL (R ∙ (g : A)) id).subgroupOf (U J)).copy
      {k : U J | k.val ∈ intGL n R ∧ IsIntMatrix R (g⁻¹ • ((k.val : Matrix n n A) - 1))} <| by
    ext k
    change k.val ∈ intGL n R ∧ (∀ i j : n, (g⁻¹ • ((k.val : Matrix n n A) - 1)) i j ∈ R) ↔
      k.val ∈ intGL n R ∧ ∀ i j : n, ((k.val : Matrix n n A) - 1) i j ∈ R ∙ (g : A)
    -- An entry `a` lies in `R ∙ g` if and only if `g⁻¹ * a ∈ R`.
    simp only [Filling.mem_span_unit_iff, Matrix.smul_apply, Units.smul_def, smul_eq_mul]

/-- The property of a square matrix T over A that it is hermitian and lies in GL_n(R). -/
def IsUnimodular (T : Matrix n n A) : Prop := Tᴴ = T ∧ ∃ u ∈ intGL n R, u.val = T

/-- The matrix J is hermitian and invertible. -/
class Floors.IsHermitianUnit (J : Matrix n n A) : Prop where
  /-- `J` is hermitian. -/
  conjTranspose_eq : Jᴴ = J
  /-- `J` is invertible. -/
  isUnit : IsUnit J

end New

end AdelicRingDefs

namespace New

/-!
## Integral matrices, congruence subgroups of U(J), unimodular forms

`New.unitaryLevel R u J` is the group of integral isometries of `J` congruent to `1` modulo `u`. A
shape `𝔰` gives a number `ϱ` of hyperbolic planes and the index set of a middle space. For a Gram
matrix `T : 𝔰.Form A` of the middle space, `T.splitGram` is the Gram matrix of its orthogonal sum
with the `ϱ` planes.

* `New.IsUnimodular.mem_unitaryLevel`: let `J` be unimodular, let `R` be stable under the
  involution, and let `u` lie in `R`. Then the congruence alone gives membership in the level.
-/

section UnimodularForms

open Matrix BesselIndex

variable {A l n μ : Type*} [CommRing A] {R : Subring A} {M : Matrix l μ A}
  [Fintype n] [DecidableEq n] {𝔰 : Shape} {k : GL n A}

lemma _root_.Membership.mem.isIntMatrix (hk : k ∈ intGL n R) : IsIntMatrix R k.val :=
  (mem_intGL.1 hk).1

lemma _root_.Membership.mem.isIntMatrix_inv (hk : k ∈ intGL n R) : IsIntMatrix R k⁻¹.val :=
  (inv_mem hk).isIntMatrix

/-- For `k` in GL_n(R), the vector `k w` has entries in `R` if and only if `w` has. -/
lemma mulVec_mem_intVectors_iff (hk : k ∈ intGL n R) {w : n → A} :
    k *ᵥ w ∈ intVectors R n ↔ w ∈ intVectors R n :=
  ⟨fun hw ↦ by simpa using hk.isIntMatrix_inv.mulVec hw, hk.isIntMatrix.mulVec⟩

variable {u : Aˣ} [StarRing A] {J : Matrix n n A} {T : 𝔰.Form A} {x : U J}

/-- If `R` is stable under the involution, the conjugate transpose of a matrix with entries in `R`
has entries in `R`. -/
lemma IsIntMatrix.conjTranspose [IsStarStable R] (hM : IsIntMatrix R M) : IsIntMatrix R Mᴴ :=
  fun i j ↦ IsStarStable.star_mem (hM j i)

/-- An isometry `x` of `J` lies in the principal congruence subgroup of level `u` if and only if
`x` lies in GL_n(R) and `u⁻¹ (x - 1)` has entries in `R`. -/
lemma mem_unitaryLevel_def :
    x ∈ unitaryLevel R u J ↔ x.val ∈ intGL n R ∧
      IsIntMatrix R (u⁻¹ • ((x.val : Matrix n n A) - 1)) := .rfl

/-- The integral points of U(J), the level `1`, normalise the principal congruence subgroup of U(J)
of level u. -/
lemma conj_mem_unitaryLevel {y : U J} (hy : y ∈ unitaryLevel R 1 J) (hx : x ∈ unitaryLevel R u J) :
    y * x * y⁻¹ ∈ unitaryLevel R u J := by
  obtain ⟨hy_int, -⟩ := mem_unitaryLevel_def.1 hy
  obtain ⟨hx_int, hx_cong⟩ := mem_unitaryLevel_def.1 hx
  refine mem_unitaryLevel_def.2 ⟨mul_mem (mul_mem hy_int hx_int) (inv_mem hy_int), ?_⟩
  -- `u⁻¹ • (y x y⁻¹ - 1)` is `y (u⁻¹ • (x - 1)) y⁻¹`, a product of integral matrices.
  simpa [Matrix.mul_sub, Matrix.sub_mul] using
    (hy_int.isIntMatrix.mul hx_cong).mul hy_int.isIntMatrix_inv

/-- Let `T.G` be the unitary group of `T.splitGram`, the Gram matrix `T` of a middle space with `ϱ`
hyperbolic planes added. Its basis indices (`SplitIndex`) are `ϱ` first, the middle and `ϱ` last
indices, graded by the natural number `level`. An element `x` lies in the Bessel unipotent group
`T.besselU` if and only if its entries `(i, j)` with `level j ≤ level i` are those of the identity
matrix. -/
lemma mem_besselU {x : T.G} :
    x ∈ T.besselU ↔
      ∀ i j : SplitIndex 𝔰.ϱ 𝔰.MiddleIndex, level j ≤ level i →
        x.val i j =
          (1 : Matrix (SplitIndex 𝔰.ϱ 𝔰.MiddleIndex) (SplitIndex 𝔰.ϱ 𝔰.MiddleIndex) A) i j :=
  .rfl

section

omit [StarRing A]

lemma IsIntMatrix.neg (hM : IsIntMatrix R M) : IsIntMatrix R (-M) :=
  fun i j ↦ R.neg_mem (hM i j)

/-- Adding `ϱ` hyperbolic planes respects inverses: if `T'` is a right inverse of `T`, then
`T'.splitGram` is a right inverse of `T.splitGram`. -/
lemma splitGram_mul_splitGram_eq_one {T' : 𝔰.Form A} (h_inv : T * T' = 1) :
    T.splitGram * T'.splitGram = 1 := by
  -- Multiply block by block: the hyperbolic blocks swap twice, the middle block is `T * T'`.
  aesop (add simp [splitGram, fromBlocks_multiply, fromCols_mul_fromRows, fromCols_mul_fromBlocks,
    fromBlocks_mul_fromRows, Matrix.one_apply])

/-- If the Gram matrix `T` of the middle space has entries in `R`, then so has the Gram matrix
`T.splitGram` with `ϱ` hyperbolic planes added: its entries are `0`, `1` or entries of `T`. -/
lemma IsIntMatrix.isInt_splitGram (hT : IsIntMatrix R T) : IsIntMatrix R T.splitGram := by
  aesop (add simp [IsIntMatrix, splitGram, Matrix.one_apply])

end

/-! ### Congruence subgroups and unimodular forms -/

/-- The principal congruence subgroup of level `1` is the group of isometries of `J` in GL_n(R). -/
lemma unitaryLevel_one : unitaryLevel R 1 J = (intGL n R).subgroupOf (U J) := by
  ext x
  simpa [mem_unitaryLevel_def, Subgroup.mem_subgroupOf] using fun hx ↦ hx.isIntMatrix.sub .one

namespace IsUnimodular

lemma isIntMatrix (hJ : IsUnimodular R J) : IsIntMatrix R J := by
  obtain ⟨-, g, hg, rfl⟩ := hJ
  exact hg.isIntMatrix

/-- A unimodular matrix (hermitian and in GL_n(R)) has a unit as determinant, and its inverse has
entries in `R`. -/
lemma isUnit_det_and_isIntMatrix_inv (hJ : IsUnimodular R J) :
    IsUnit J.det ∧ IsIntMatrix R J⁻¹ := by
  obtain ⟨-, g, hg, rfl⟩ := hJ
  exact ⟨isUnits_det_units g, by simpa using hg.isIntMatrix_inv⟩

/-- Let J be unimodular (hermitian and in GL_n(R)) over a conjugation-stable subring R, and let
u ∈ R be a unit of A. An isometry x of J with u⁻¹(x − 1) integral lies in the principal congruence
subgroup of level u. -/
lemma mem_unitaryLevel [IsStarStable R] (hJ : IsUnimodular R J) (hu : u.val ∈ R)
    (h_cong : IsIntMatrix R (u⁻¹ • ((x.val : Matrix n n A) - 1))) :
    x ∈ unitaryLevel R u J := by
  obtain ⟨hJ_det, hJ_inv⟩ := hJ.isUnit_det_and_isIntMatrix_inv
  have hx_int : IsIntMatrix R (x.val : Matrix n n A) := by
    simpa [← Units.smul_def] using (h_cong.smul hu).add .one
  -- Since `x` is an isometry, its inverse is a product of integral matrices.
  have hx_inv_eq : (x.val⁻¹).val = J⁻¹ * ((x.val : Matrix n n A)ᴴ * J) := by
    simp [← U.form_mul_inv_eq, hJ_det]
  refine mem_unitaryLevel_def.2 ⟨mem_intGL.2 ⟨hx_int, ?_⟩, h_cong⟩
  rw [hx_inv_eq]
  exact hJ_inv.mul (hx_int.conjTranspose.mul hJ.isIntMatrix)

/-- If the Gram matrix T of the middle space is unimodular (hermitian and invertible over the
subring R), then so is the Gram matrix `T.splitGram` of the space obtained by adding ϱ hyperbolic
planes. -/
lemma splitGram (hT : IsUnimodular R T) : IsUnimodular R T.splitGram := by
  obtain ⟨hT_herm, g, hg, rfl⟩ := hT
  -- The inverse of `splitGram g` is `splitGram` of the inverse of `g`.
  let g' : GL 𝔰.BesselIndex A :=
    ⟨Shape.Form.splitGram g.val, Shape.Form.splitGram g⁻¹.val,
      splitGram_mul_splitGram_eq_one g.mul_inv, splitGram_mul_splitGram_eq_one g.inv_mul⟩
  have hg' : g' ∈ intGL _ R :=
    mem_intGL.2 ⟨hg.isIntMatrix.isInt_splitGram, hg.isIntMatrix_inv.isInt_splitGram⟩
  refine ⟨?_, g', hg', rfl⟩
  simpa [New.splitGram, fromBlocks_conjTranspose, conjTranspose_fromRows_eq_fromCols_conjTranspose,
    conjTranspose_fromCols_eq_fromRows_conjTranspose] using hT_herm

end IsUnimodular

end UnimodularForms

/-!
## Functions of integral matrices and column lattices

* `New.liftIntegralFn`: a function of matrices over `B`, pulled back along `π : R → B` to integral
  matrices over `A` and extended by zero.
* `New.liftIntegralFn_mul`: multiplying the argument on both sides by invertible matrices over `R`
  corresponds to multiplying the argument of the function by their images under `π`.
-/

section ColumnLattices

open Matrix

variable {A : Type*} [CommRing A] {R : Subring A} {m n : Type*} [Fintype n] {M : Matrix m n A}

open scoped Classical in
/-- For π : R → B, the ℂ-linear map sending a function f on matrices over B to the function on
matrices S over A that is f(πS) for S integral, else 0. -/
noncomputable def liftIntegralFn {B : Type*} (π : R → B) [Fintype m] :
    (Matrix m n B → ℂ) →ₗ[ℂ] Matrix m n A → ℂ :=
  IsLinearMap.mk'
    (fun (f : Matrix m n B → ℂ) (S : Matrix m n A) ↦
      if h : ∀ (i : m) (j : n), S i j ∈ R then f (of fun i j ↦ π ⟨S i j, h i j⟩) else 0)
    ⟨by aesop, by aesop⟩

/-- The lift of `f` along `π` takes the value `f (π M₀)` at a matrix `M₀` over `R`, viewed as a
matrix over `A`. -/
lemma liftIntegralFn_map_subtype {B : Type*} (π : R → B) [Fintype m] (f : Matrix m n B → ℂ)
    (M₀ : Matrix m n R) : liftIntegralFn π f (M₀.map R.subtype) = f (M₀.map π) :=
  dite_eq_left fun i j ↦ (M₀ i j).property

/-- The lift of `f` along `π` vanishes at a matrix with an entry outside `R`. -/
lemma liftIntegralFn_of_not_isIntMatrix {B : Type*} (π : R → B) [Fintype m]
    (f : Matrix m n B → ℂ) (hM : ¬IsIntMatrix R M) : liftIntegralFn π f M = 0 :=
  dite_eq_right hM

/-- If `R` is open in `A`, then `Rⁿ` is open in `Aⁿ` for the product topology. -/
lemma isOpen_intVectors [TopologicalSpace A] (hR : IsOpen (R : Set A)) :
    IsOpen (intVectors R n : Set (n → A)) := by
  -- `Rⁿ` is the product set of copies of `R`.
  simpa [intVectors, Set.pi] using isOpen_set_pi Set.finite_univ fun (_ : n) _ ↦ hR

/-- The `R`-span of the columns of `M` lies in every `R`-module that contains the columns. -/
lemma colLattice_le {L : Submodule R (m → A)} (h_col : ∀ j : n, M.col j ∈ L) :
    colLattice R M ≤ L := by
  rintro _ ⟨v, hv, rfl⟩
  -- `M *ᵥ v` is the combination of the columns of `M` with the coefficients `v j ∈ R`.
  have h_sum : M *ᵥ v = ∑ j : n, (⟨v j, hv j⟩ : R) • M.col j := by
    ext i
    simp [mulVec, dotProduct, R.smul_def, mul_comm]
  simpa [h_sum] using L.sum_mem fun j _ ↦ L.smul_mem ⟨v j, hv j⟩ (h_col j)

variable [DecidableEq n]

/-- If `b M a` has entries in `R` for some `a` in GL_n(R) and `b` in GL_m(R), then so has
`M = b⁻¹ (b M a) a⁻¹`. -/
lemma IsIntMatrix.of_intGL_mul_mul [Fintype m] [DecidableEq m] {a : GL n A} {b : GL m A}
    (ha : a ∈ intGL n R) (hb : b ∈ intGL m R) (h_int : IsIntMatrix R (b.val * M * a.val)) :
    IsIntMatrix R M := by
  simpa [Matrix.mul_assoc, ← Matrix.mul_assoc b⁻¹.val, -coe_units_inv] using
    hb.isIntMatrix_inv.mul (h_int.mul ha.isIntMatrix_inv)

/-- For a ring homomorphism π : R → B, a ∈ GL_n(R), b ∈ GL_m(R) and an m × n matrix M over A, the
value of `New.liftIntegralFn` π f (the function that is f(πS) at integral S, else 0) at bMa equals
the value at M of the lift of S ↦ f(π(b)Sπ(a)). -/
lemma liftIntegralFn_mul {B : Type*} [CommRing B] (π : R →+* B) [Fintype m] [DecidableEq m]
    (f : Matrix m n B → ℂ) (a : GL n R) (b : GL m R) :
    liftIntegralFn π f ((b.map R.subtype).val * M * (a.map R.subtype).val) =
      liftIntegralFn π (fun S : Matrix m n B ↦ f ((b.map π).val * S * (a.map π).val)) M := by
  by_cases hM : IsIntMatrix R M
  · -- An integral `M` comes from a matrix over `R`, and both `R.subtype` and `π` respect products.
    obtain ⟨M₀, rfl⟩ : ∃ M₀ : Matrix m n R, M = M₀.map R.subtype :=
      ⟨of fun i j ↦ ⟨M i j, hM i j⟩, rfl⟩
    simp only [GeneralLinearGroup.val_map_apply, ← Matrix.map_mul, liftIntegralFn_map_subtype]
  · -- If `M` is not integral, neither is `b M a`, so both sides are `0`.
    rw [liftIntegralFn_of_not_isIntMatrix π _ hM, liftIntegralFn_of_not_isIntMatrix π _]
    exact fun h_int ↦ hM (h_int.of_intGL_mul_mul ⟨a, rfl⟩ ⟨b, rfl⟩)

omit [Fintype n] in
lemma single_mem_intVectors (j : n) : Pi.single j 1 ∈ intVectors R n :=
  fun i ↦ by by_cases hij : i = j <;> simp [hij]

lemma col_mem_colLattice (j : n) : M.col j ∈ colLattice R M :=
  ⟨Pi.single j 1, single_mem_intVectors j, by simp⟩

end ColumnLattices

end New

/-!
## A duality step for common vectors of two flags

`New.exists_mulVec_eq_of_annihilator`: a duality statement. If every linear form that kills certain
columns of two matrices `P`, `P'` takes the same value on `P X` and `P' Y`, then `X` and `Y` can be
changed in the coordinates of those columns so that the two vectors become equal. It is used to pass
from a vector common to two flags at one level to a common vector one level higher.
-/

section ClimbStep

open Matrix Submodule Pi

/-- Let `s`, `s'` be sets of column indices. Suppose that every row vector `l` such that `l P`
vanishes on `s` and `l P'` vanishes on `s'` has `l P X = l P' Y`. Then `P x = P' y` for some `x`
equal to `X` outside `s` and some `y` equal to `Y` outside `s'`. -/
lemma New.exists_mulVec_eq_of_annihilator {F ι α : Type*} [Field F] [Fintype ι] [Fintype α]
    (P P' : Matrix ι α F) (s s' : Set α) (X Y : α → F)
    (h_agree : ∀ l : ι → F,
      (∀ b ∈ s, (l ᵥ* P) b = 0) → (∀ b ∈ s', (l ᵥ* P') b = 0) → l ᵥ* P ⬝ᵥ X = l ᵥ* P' ⬝ᵥ Y) :
    ∃ x y : α → F, P *ᵥ x = P' *ᵥ y ∧
      (∀ b : α, b ∉ s → x b = X b) ∧ ∀ b : α, b ∉ s' → y b = Y b := by
  classical
  -- By duality `P *ᵥ X - P' *ᵥ Y` lies in the span `W` of the columns of `P` in `s` and of `P'` in
  -- `s'`: otherwise a linear form killing `W` would separate `P *ᵥ X` from `P' *ᵥ Y`. Here `W` is
  -- written as the space of the `P' *ᵥ u - P *ᵥ v` with `u` zero off `s'` and `v` zero off `s`.
  let W : Submodule F (ι → F) :=
    map (P'.toLin'.coprod (-P).toLin') ((spanSubset F s').prod (spanSubset F s))
  have h_mem : P *ᵥ X - P' *ᵥ Y ∈ W := by
    by_contra h_not
    obtain ⟨f, hf_ne, hf_ker⟩ := exists_le_ker_of_notMem h_not
    -- The form `f` is the product with a row vector `l`.
    obtain ⟨l, rfl⟩ := (dotProductEquiv F ι).surjective f
    obtain ⟨hl', hl⟩ : (∀ b ∈ s', (l ᵥ* P') b = 0) ∧ ∀ b ∈ s, (l ᵥ* P) b = 0 := by
      simpa [W, map_span_le, spanSubset, dotProduct_mulVec] using hf_ker
    exact hf_ne (by simpa [dotProduct_mulVec, sub_eq_zero] using h_agree l hl hl')
  obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, huv⟩ := h_mem
  have hu_zero : ∀ b ∉ s', u b = 0 := mem_spanSubset_iff.1 hu
  have hv_zero : ∀ b ∉ s, v b = 0 := mem_spanSubset_iff.1 hv
  replace huv : P' *ᵥ u - P *ᵥ v = P *ᵥ X - P' *ᵥ Y := by simpa [sub_eq_add_neg] using huv
  refine ⟨v + X, u + Y, ?_, fun b hb ↦ by simp [hv_zero b hb], fun b hb ↦ by simp [hu_zero b hb]⟩
  simp only [mulVec_add]
  linear_combination -huv

end ClimbStep

end
