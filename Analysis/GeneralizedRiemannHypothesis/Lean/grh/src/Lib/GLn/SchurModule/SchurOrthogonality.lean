import Lib.DiscreteSeries.FlenstedJensen.PsiKTypes
import Lib.GLn.SchurModule.GramMatrix

/-!
# Algebraic representations of GL(n) on unitary groups: Schur orthogonality

A weight `(κ, e)` consists of the numbers `κ τ h` of columns of height `h` and an exponent `e τ` of
the determinant. Only the heights below `card n` enter the index type `New.WeylIndex n κ` and, for
square matrices, `New.schur`. `New.weylRep κ e g` is `∏ τ, det (g τ) ^ e τ` times `schur κ g`. These
representations are restricted to products of unitary groups `U(s)^Φ`. The file defines the
hermitian Gram form, which is invariant when all signs are `1` (`New.gramForm_conjWeylRep`, in
`Lib.GLn.SchurModule.SchurNorm`), and the highest vectors.

## Main definitions and results

* `New.conjWeylMatrix`, `New.conjWeylRep`: the conjugate action of weight `(κ, e)`, as matrices and
  as a representation: `g` acts by `New.weylRep κ e` at the entrywise complex conjugate of `g`.
* `New.gramForm`: the hermitian form `ξ* G η` of the Gram matrix `G = weylGramOver`.
* `New.decreasingPosition`, `New.highestVector`: the order that a vector `l` puts on the rows, and
  the evaluation vector at the frame of that order.
* `New.weylRep_coeff_eq_prod_weightMinors`: the matrix coefficient of `New.weylRep κ e` at a highest
  vector is a product of the functions `New.weightMinors`, products of principal minors.
* `New.schur_orthogonality`: Schur's orthogonality relations on the compact group U(n)^Φ.

Notions from other files:
* `New.schur`: The Schur matrix S_κ(z) of matrices z_τ of size n'_τ×n_τ. Row i holds chosen
  coordinates of b'_i(zy) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}. Here b'_i and b_j are the
  standard basis polynomials in the rows n' and n, and d is given by `New.schurDetExp`.
* `New.WeylIndex`: The type of families of chosen standard fillings over the places, in the case
  where the row type is the same finite type n at every place, that is
  `WeylIndexFamily (fun _ ↦ n) κ`; `WeylIndexFamily` allows a row type n_τ at each place τ.
* `New.nablaBasis`: For a family i of chosen standard fillings, the polynomial b_i, the product over
  the places τ of the minor products of the fillings i_τ.
* `New.weylEval`: For an array y, the vector of the values b_i(y).
* `New.weightMinors`: For a matrix `g` and integer weights `l`, the product over integers `t` of the
  principal minor of `g` on `{i | t ≤ l i}`, each factor with `t ≤ 0` divided by `det g`.

## Relation to the literature

Known; see `Lib.GLn.SchurModule.SchurNorm` and `Lib.GLn.SchurModule.MinorBasis` for sources.
-/

noncomputable section

/-!
## The conjugate representation, Gram form and highest vector

* `New.hcParameter`, `New.IsHCParam`: twice the Harish-Chandra parameter of a weight.
* `New.Exchange.schur_eq_one`: the Schur matrix when all columns have full height.
-/

section CompactRep

open Matrix Finset Fintype

namespace New

variable {Φ n : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n] [DecidableEq n]
  {R : Type} [CommRing R] (κ : Φ → ℕ → ℕ) (e : Φ → ℤ) (l : Φ → n → ℤ) {s : n → ℤˣ}

/-- The matrix representation of the product over places of the unitary groups of the diagonal
form of signs s: g acts by `New.weylRep` at the entrywise complex conjugate of g. -/
abbrev conjWeylMatrix :
    (Φ → USign s) →* Matrix (WeylIndexFamily (fun _ ↦ n) κ) (WeylIndexFamily (fun _ ↦ n) κ) ℂ :=
  (weylRep κ e).comp
    (MonoidHom.pi
      ((GeneralLinearGroup.map (starRingEnd ℂ)).comp <|
        (USign s).subtype.comp <| Pi.evalMonoidHom _ ·))

/-- The complex linear representation of the product over places of the unitary groups of signs
s on coordinate vectors of weight κ, acting by the matrices `New.conjWeylMatrix`. -/
def conjWeylRep : Representation ℂ (Φ → USign s) (WeylIndex n κ → ℂ) :=
  toLinAlgEquiv'.toMonoidHom.comp (conjWeylMatrix κ e)

/-! ### Highest vector and Harish-Chandra parameter -/

/-- For an integer vector l and an index i, the number of indices j with l_j > l_i. -/
def decreasingPosition (l : n → ℤ) (i : n) : ℕ := #{j : n | l i < l j}

/-- The complex evaluation vector of weight κ at the array with entry 1 in row a of block w
exactly in column #{j : l_w(j) > l_w(a)}, and 0 elsewhere. -/
def highestVector : WeylIndex n κ → ℂ := weylEval _ κ
  (permArray fun τ i ↦ decreasingPosition (l τ) i)

/-- The integer 2μ_p + N − 1 − 2p, entry p (counted from 0) of twice the Harish-Chandra parameter
μ + ρ in rank N, where μ_p = e_w + Σ_{p<h<N} κ_w(h) is the highest weight at the place w; the sum is
`diagramWeight (fun _ ↦ N) κ (w, p)`. -/
def hcParameter (N : ℕ) (w : Φ) (p : ℕ) : ℤ :=
  2 * (e w + diagramWeight (fun _ ↦ N) κ (w, p)) + N - 1 - 2 * p

/-- `l` lists twice the Harish-Chandra parameter of the weight `(κ, e)`, in some order: at each
place `w` the numbers `l w i` are distinct, and each of them is `hcParameter κ e (card n) w p` for
some position `p < card n`. As `hcParameter` is strictly decreasing in `p`, the position of `i` is
necessarily `decreasingPosition (l w) i`, the number of `j` with `l w i < l w j`. -/
def IsHCParam : Prop :=
  ∀ w : Φ,
    (l w).Injective ∧ ∀ i : n, ∃ p < Fintype.card n, l w i = hcParameter κ e (Fintype.card n) w p

variable {κ}

/-- The sesquilinear form (ξ,η) ↦ ξ* G η on complex coordinate vectors of weight κ, conjugate
linear in ξ, with G the integer Gram matrix. -/
def gramForm : (WeylIndex n κ → ℂ) →ₗ⋆[ℂ] (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ :=
  (dotProductBilin ℂ ℂ).compl₂ weylGramOver.mulVecLin ∘ₛₗ (starLinearEquiv ℂ).toLinearMap

/-- The Gram form at `ξ` and `η` is `ξ* G η` for the Gram matrix `G = weylGramOver`. -/
lemma gramForm_apply (ξ η : WeylIndex n κ → ℂ) : gramForm ξ η = star ξ ⬝ᵥ weylGramOver *ᵥ η := rfl

omit [DecidableEq Φ] in
/-- If all columns of `κ` have height `card n` (`κ τ k = 0` for `k ≠ card n`), every basis
polynomial `nablaBasis R _ κ j` is the empty product `1`. -/
lemma Exchange.nablaBasis_eq_one (hκ : ∀ τ : Φ, ∀ k ≠ Fintype.card n, κ τ k = 0)
    (j : WeylIndexFamily (fun _ : Φ ↦ n) κ) :
    nablaBasis R (fun _ : Φ ↦ n) κ j = 1 := by
  -- There is no column of height `h < card n`, so all the products of minors are empty.
  have no_column (τ : Φ) (h : Fin (card n)) : IsEmpty (Fin (κ τ h)) := by
    rw [hκ τ h h.isLt.ne]
    infer_instance
  simp [nablaBasis, tableauPoly, univ_eq_empty]

/-- If all columns of `κ` have height `card n` (`κ τ k = 0` for `k ≠ card n`), the Schur matrix of
every tuple `z` of square matrices is the `1 × 1` identity matrix. -/
lemma Exchange.schur_eq_one (hκ : ∀ τ : Φ, ∀ k ≠ Fintype.card n, κ τ k = 0)
    (z : Φ → Matrix n n R) : schur κ z = 1 := by
  -- Both sides expand the constant basis polynomial `1` in the same way.
  have h_expansion (i : WeylIndexFamily (fun _ : Φ ↦ n) κ) :
      ∑ j : WeylIndexFamily (fun _ : Φ ↦ n) κ, (1 : Matrix _ _ R) i j •
          (nablaBasis R (fun _ : Φ ↦ n) κ j *
            detPow R (fun _ : Φ ↦ n) (schurDetExp (fun _ : Φ ↦ n) (fun _ : Φ ↦ n) κ)) =
        rowSubst z (nablaBasis R (fun _ : Φ ↦ n) κ i) := by
    simp [nablaBasis_eq_one hκ, Matrix.one_apply]
  exact GL.schur_eq_of_expansion h_expansion

end New

end CompactRep

/-!
## Matrix coefficients and Schur's orthogonality relations on U(n)^Φ

* `New.exists_intertwining_mean`: averaging a matrix over a compact group gives an intertwiner.
-/

section SchurOrthogonality

open MeasureTheory Matrix ComplexConjugate Finset Fintype Fin Norms.Operator New.GL

namespace New

variable {Φ n : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n] [DecidableEq n]
  {κ : Φ → ℕ → ℕ} {e : Φ → ℤ} {l : Φ → n → ℤ} {s : n → ℤˣ}

/-- The index type `WeylIndex n κ` is never empty: it indexes the coordinates of a vector of norm
one. -/
instance : Nonempty (WeylIndex n κ) := by
  by_contra! h_empty
  simpa [weylNormSq] using weylNormSq_weylEval_permArray (κ := κ) (rowEquivFin fun _ ↦ n)

omit [DecidableEq Φ] in
/-- For any integer labels `l w : n → ℤ` of the rows at each place `w`, `highestVector κ l` is the
complex evaluation vector of weight `κ` at the array whose block `w` has entry 1 in row `a` exactly
at column `#{j : l w j > l w a}`, and 0 elsewhere. This highest vector has real (integer)
coordinates: it is its own complex conjugate. -/
lemma star_highestVector : star (highestVector κ l) = highestVector κ l := by
  refine (star_weylEval _).trans ?_
  rcongr
  simp [permArray]

/-- The form `gramForm` is hermitian: swapping the arguments conjugates the value. -/
lemma conj_gramForm (ξ η : WeylIndex n κ → ℂ) : conj (gramForm ξ η) = gramForm η ξ :=
  star_dotProduct_mulVec_comm weylGramOver_posDef.1 ξ η

open ComplexOrder in
/-- The Gram form is non-degenerate: a vector is determined by its pairings with all vectors. -/
lemma ext_gramForm_left {ξ η : WeylIndex n κ → ℂ}
    (h : ∀ ζ : WeylIndex n κ → ℂ, gramForm ζ ξ = gramForm ζ η) : ξ = η := by
  have h_self : star (ξ - η) ⬝ᵥ weylGramOver *ᵥ (ξ - η) = 0 := by
    rw [← gramForm_apply, map_sub, h, sub_self]
  by_contra h_ne
  exact (weylGramOver_posDef.dotProduct_mulVec_pos (sub_ne_zero.2 h_ne)).ne' h_self

omit [DecidableEq n] in
/-- For injective l, the position in decreasing order is a bijection onto {0, …, |n| − 1}, and
that for −l is the reversed one. -/
lemma exists_equiv_decreasingPosition {l : n → ℤ} (hl : l.Injective) :
    ∃ e : n ≃ Fin (Fintype.card n), ∀ a : n,
      decreasingPosition l a = e a ∧ decreasingPosition (-l) a = (e a).rev := by
  -- Enumerate `n` by `e` in the decreasing order of `l`; then `a` indices precede `e a` and
  -- `card n - 1 - a` follow it.
  obtain ⟨e, he⟩ : ∃ e : Fin (card n) ≃ n, ∀ a b, l (e b) < l (e a) ↔ a < b := by
    simpa using exists_equiv_fin_lt_iff (neg_injective.comp hl)
  refine ⟨e.symm, e.forall_congr_right.1 fun a ↦ ?_⟩
  simp [decreasingPosition, card_filter, ← e.sum_comp, filter_gt_eq_Iio, he, filter_lt_eq_Ioi,
    Nat.sub_sub, add_comm 1]

/-- For each vector `ξ`, the map `g ↦ conjWeylRep κ e g ξ` is continuous on the product of unitary
groups of signs `s`. -/
@[fun_prop]
lemma continuous_conjWeylRep (ξ : WeylIndex n κ → ℂ) :
    Continuous (conjWeylRep (s := s) κ e · ξ) := by
  simp [conjWeylRep, weylRep, smul_mulVec]
  fun_prop

/-- For matrix representations S, R of a compact group with a Haar measure ν and a matrix M such
that g ↦ S(g)MR(g⁻¹) is continuous, there is B with BR(y) = S(y)B for all y and ∫ L(S(g) M R(g⁻¹))
dν = L(B) for every linear L. -/
lemma exists_intertwining_mean {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [Measure.IsHaarMeasure ν]
    (S : G →* Matrix Φ Φ ℂ) (R : G →* Matrix n n ℂ) (M : Matrix Φ n ℂ)
    (h_cont : Continuous fun g : G ↦ S g * M * R g⁻¹) :
    ∃ B : Matrix Φ n ℂ,
      (∀ y : G, B * R y = S y * B) ∧
      ∀ L : Matrix Φ n ℂ →ₗ[ℂ] ℂ, ∫ g : G, L (S g * M * R g⁻¹) ∂ν = L B := by
  let B : Matrix Φ n ℂ := ∫ g, S g * M * R g⁻¹ ∂ν
  -- Linear maps commute with the integral of a continuous function on a compact group.
  have h_lin (L : Matrix Φ n ℂ →ₗ[ℂ] Matrix Φ n ℂ) : ∫ g, L (S g * M * R g⁻¹) ∂ν = L B :=
    L.toContinuousLinearMap.integral_comp_comm DiscreteSeries.integrable_of_compactSpace
  refine ⟨B, fun y ↦ ?_,
    fun L ↦ L.toContinuousLinearMap.integral_comp_comm DiscreteSeries.integrable_of_compactSpace⟩
  -- Substitute `y * g` for `g`: then `S y` comes out on the left and `R y⁻¹ * R y` cancels.
  calc
    B * R y = ∫ g, S g * M * R g⁻¹ * R y ∂ν := (h_lin (mulRightLinearMap _ ℂ (R y))).symm
    _ = ∫ g, S (y * g) * M * R (y * g)⁻¹ * R y ∂ν := (integral_mul_left_eq_self _ y).symm
    _ = ∫ g, S y * (S g * M * R g⁻¹) ∂ν := by simp [Matrix.mul_assoc, ← R.map_mul y⁻¹]
    _ = S y * B := h_lin (mulLinearMap ℂ (S y))

/-- The function `weightMinors` for the weight `c + ∑ h ∈ t, k h • 1_{p < h}` at an invertible
matrix `x`: `x.det ^ c` times the product of the principal minors on `{i | p i < h}` to the powers
`k h`. -/
lemma weightMinors_add_sum_ite {N : ℕ} (p : n → Fin N) {x : Matrix n n ℂ} (hx : x.det ≠ 0) (c : ℤ)
    (k : Fin N → ℕ) (t : Finset (Fin N)) :
    weightMinors (fun i : n ↦ c + ∑ h ∈ t, if p i < h then (k h : ℤ) else 0) x =
      x.det ^ c * ∏ h ∈ t, principalMinor x (p · < h) ^ k h := by
  induction t using cons_induction with
  | empty => simp [weightMinors_const hx]
  | cons h t ht ih =>
    -- The weight for `t` decreases along `p`, so by `weightMinors_add_ite` adding `k h` on
    -- `{i | p i < h}` multiplies by the `k h`-th power of the principal minor on that set.
    have h_anti (i j : n) (hi : p i < h) (hj : ¬p j < h) :
        c + ∑ h' ∈ t, (if p j < h' then (k h' : ℤ) else 0) ≤
          c + ∑ h' ∈ t, if p i < h' then (k h' : ℤ) else 0 := by
      gcongr
      lia
    calc weightMinors (fun i : n ↦ c + ∑ h' ∈ cons h t ht, if p i < h' then (k h' : ℤ) else 0) x
        = weightMinors (fun i : n ↦ c + ∑ h' ∈ t, if p i < h' then (k h' : ℤ) else 0) x *
            principalMinor x (p · < h) ^ k h := by
          simp [add_comm (ite ..), ← add_assoc, weightMinors_add_ite hx (k h).cast_nonneg h_anti,
            ht]
      _ = x.det ^ c * ∏ h' ∈ cons h t ht, principalMinor x (p · < h') ^ k h' := by
          rw [ih, Finset.prod_cons]
          ring

/-- Let v be the evaluation vector of weight κ at the array `permArray` with entry 1 in row i of
block τ exactly in column p_τ(i), for bijections p_τ : n_τ ≃ Fin (rankAt n τ), so rankAt n
τ = |n_τ|. Let ρ = `New.weylRep` of weight (κ, e) and μ = `New.diagramWeight`. For g in ∏_τ GL(n_τ,
ℂ), the coefficient (v, ρ(g)v) for the bilinear Gram form is the product over τ of
`New.weightMinors` at g_τ for the weight i ↦ e_τ + μ(τ, p_τ(i)). -/
lemma weylRep_coeff_eq_prod_weightMinors {n : Φ → Type} [∀ τ, Fintype (n τ)]
    [∀ τ, DecidableEq (n τ)] (p : ∀ τ : Φ, n τ ≃ Fin (rankAt n τ)) (g : (τ : Φ) → GL (n τ) ℂ) :
    let v := weylEval n κ (permArray fun (τ : Φ) (i : n τ) ↦ (p τ i : ℕ))
    v ⬝ᵥ weylGramOver *ᵥ weylRep κ e g *ᵥ v =
      ∏ τ : Φ, weightMinors (fun i : n τ ↦ e τ + diagramWeight (rankAt n) κ ⟨τ, p τ i⟩) (g τ) := by
  -- The coefficient is `∏ τ, det (g τ) ^ e τ` times the value of the highest weight polynomial
  -- `highestPoly`, a product of powers of leading minors, at `g` read in the orderings `p`. The
  -- right side takes the same shape by `weightMinors_add_sum_ite`.
  simp [weylKernel, eval_rowSubst, minor, highestPoly, tableauPoly, diagramWeight,
    RingHom.map_det, Units.smul_def, ← prod_mul_distrib, Finsupp.single_apply, ite_and,
    sum_range (n := rankAt n _), weightMinors_add_sum_ite, weylRep, smul_mulVec,
    GeneralLinearGroup.det_ne_zero]
  congr! 4 with τ _ h
  -- The leading `h × h` minor is, after transposing, the principal minor on `{i | p τ i < h}`.
  let ε : Fin h ≃ {i // p τ i < h} :=
    (castLEquiv h.is_le').trans ((p τ).subtypeEquiv fun _ ↦ .rfl).symm
  rw [← det_reindex_self ε, ← det_transpose]
  congr with i j
  simp [permArray, ε, val_eq_val]

/-- Schur orthogonality for the representation ρ = `New.conjWeylRep` of weight (κ, e) of the compact
group U(n)^Φ: for f linear into ℂ and any vectors a, b, c, ∫ ⟨a, ρ(x⁻¹)b⟩ f(ρ(x)c) dx = (dim ρ)⁻¹
⟨a, c⟩ f(b), with ⟨·,·⟩ = `New.gramForm`, and dx the Haar measure `volume`, of total mass one. -/
lemma schur_orthogonality (e : Φ → ℤ) (f : (WeylIndex n κ → ℂ) →ₗ[ℂ] ℂ)
    (a b c : WeylIndex n κ → ℂ) :
    ∫ x : Φ → USign (1 : n → ℤˣ),
        f (conjWeylRep κ e x c) * gramForm a (conjWeylRep κ e x⁻¹ b) =
      (Fintype.card (WeylIndex n κ) : ℂ)⁻¹ * gramForm a c * f b := by
  -- Average the rank-one map `v ↦ gramForm a v • c` over the group. The mean `B` commutes with
  -- the representation, so by Schur's lemma it is a scalar `z`; the trace determines `z`.
  have h_cont : Continuous fun x : Φ → USign (1 : n → ℤˣ) ↦
      conjWeylMatrix κ e x * ((gramForm a).smulRight c).toMatrix' * conjWeylMatrix κ e x⁻¹ := by
    -- Both factors are, by definition, products of determinant powers and Schur matrices.
    simp [-Pi.inv_apply, weylRep]
    fun_prop
  obtain ⟨B, h_comm : ∀ y : Φ → USign (1 : n → ℤˣ),
      B * conjWeylMatrix κ e y = conjWeylMatrix κ e y * B, h_mean⟩ :=
    exists_intertwining_mean volume (conjWeylMatrix κ e) (conjWeylMatrix κ e)
      ((gramForm a).smulRight c).toMatrix' h_cont
  -- For unitary `g`, each `(g τ).map conj` is unitary, and `conjWeylMatrix` there is a unit
  -- multiple of `schur κ g`; so `B` commutes with `schur κ g`.
  have h_commute (g : (τ : Φ) → Matrix n n ℂ) (hg : ∀ τ : Φ, (g τ)ᴴ * g τ = 1) :
      Commute B (schur κ g) := by
    have h_conj_unitary (τ : Φ) :
        ((g τ).map conj)ᴴ * signMatrix (1 : n → ℤˣ) * (g τ).map conj = signMatrix 1 := by
      simpa [← conjTranspose_map (conj : ℂ → ℂ) fun _ ↦ rfl, Matrix.map_mul] using
        congrArg (Matrix.map · conj) (hg τ)
    let u : Φ → USign (1 : n → ℤˣ) := fun τ ↦ U.of (by simp) ((g τ).map conj) (h_conj_unitary τ)
    show B * schur κ g = schur κ g * B
    simpa [u, smul_left_cancel_iff, weylRep, Function.comp_def] using h_comm u
  obtain ⟨z, rfl⟩ : B ∈ Set.range (scalar _) := mem_range_scalar_of_commute_schur h_commute
  -- The trace of the integrand is `gramForm a c` at every point, and the group has volume one.
  have hz : gramForm a c = z * card (WeylIndex n κ) := by
    simpa [trace_mul_cycle (weylRep κ e _), ← map_mul, ← trace_toLin'_eq, ← smul_one_eq_diagonal]
      using h_mean (traceLinearMap _ ℂ ℂ)
  calc
    _ = z * f b := by
      simpa [← smul_one_eq_diagonal, mul_comm, conjWeylRep] using
        h_mean (f ∘ₗ toLin'.toLinearMap.flip b)
    _ = _ := by simp [hz, inv_mul_eq_div, -Fintype.card_pi]

/-- For integer labels `l w : n → ℤ` of the rows at each place `w`, `highestVector κ l` is the
complex evaluation vector of weight `κ` at the array whose block `w` has entry 1 in row `a` exactly
at column `#{j : l w j > l w a}`, and 0 elsewhere. If each `l w` is injective, this highest vector
v⁺ is a unit vector for `gramForm`, the form `(ξ, η) ↦ ξ* G η` with `G` the integer Gram matrix:
⟨v⁺, v⁺⟩ = 1. -/
lemma gramForm_highestVector_self (hl : ∀ w : Φ, (l w).Injective) :
    gramForm (highestVector κ l) (highestVector κ l) = 1 := by
  -- The highest vector is the evaluation at a permutation array, and these have norm one.
  choose p hp using fun w : Φ ↦ exists_equiv_decreasingPosition (hl w)
  simp [← coe_weylNormSq, highestVector, hp, weylNormSq_weylEval_permArray, gramForm_apply]

end New

end SchurOrthogonality

end
