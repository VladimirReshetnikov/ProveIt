import Lib.GLn.SchurModule.SchurOrthogonality

/-!
# Irreducibility under U(n)^Φ, polarisation and averaging of determinant polynomials

The representations `New.conjWeylRep κ e` of the compact group U(n)^Φ are irreducible, and so is the
module `New.nablaFamily` of semi-invariant polynomials.

## Main definitions and results

* `New.span_conjWeylRep_eq_top`, `New.mem_span_rowSubst_unitary`: irreducibility under U(n)^Φ, for
  coordinate vectors and for semi-invariant polynomials.
* `New.exists_pairedDetProd_eq_sum_unitary`: for `card p < card n`, a product of determinants
  `det (η τ k * Y τ)` is a combination of unitary translates of one product of powers of minors,
  with coefficients independent of `Y`.
* `New.exists_forall_eq_mul_map_det_pow`: a linear form `M` that takes the unitary translates of a
  polynomial `q` in square matrices to `t * ∏ τ, det (u τ) ^ c τ` has
  `t = a * M (∏ τ, det (z τ) ^ c τ)`, with `a` depending only on `q` and `c`.

Notions from other files:
* `New.conjWeylRep κ e`: the action of U(n)^Φ on the coordinate vectors `WeylIndex n κ → ℂ` by the
  Schur matrices of the conjugate matrices, times the powers `e` of their determinants;
  `USign (1 : n → ℤˣ)` is the unitary group U(n).
* `New.nablaFamily`: the module of Borel semi-invariant polynomials in rows (τ,a), coloured by τ,
  whose weight has `κ τ h` columns of height `h` at τ, for the heights below |n_τ|.
* `New.rowSubst`: for matrices z_τ, the substitution f ↦ f(zy).
* `New.pairedDetProd`: the element ∏_τ ∏_k det(η_{τk} Y_τ) of a ℂ-algebra S, for n×p matrices Y_τ
  over S and complex p×n matrices η_{τk}.
* `New.Rows.variableMinor`: the minor det(x_{τ,i(a),j(b)}) of the matrix of variables at τ, in rows
  i and columns j.

## Relation to the literature

Irreducibility under U(n) is part of the known theory of the contravariant form on Weyl's lattice.
See `Lib.GLn.SchurModule.SchurNorm`.
-/

noncomputable section

/-!
## Irreducibility and polarisation of products of determinants

Let `card p < card n`. A product of `d τ` maximal minors of each `n × p` matrix of variables lies in
the module `New.nablaFamily` whose diagram at `τ` has `d τ` columns of height `card p`. This module
is irreducible under U(n)^Φ, so the unitary translates of one product of powers of minors span it.
-/

section Polarisation

open Matrix MvPolynomial Submodule Fintype ComplexOrder New.GL

namespace New

variable {Φ n : Type} [Fintype Φ] [DecidableEq Φ] [Fintype n] [DecidableEq n] {κ : Φ → ℕ → ℕ}

/-- The representation `New.conjWeylRep κ e` of the product over `Φ` of copies of U(n) (`USign 1`),
acting on complex coordinate vectors `WeylIndex n κ → ℂ` (`WeylIndex n κ` indexes a basis of the
Weyl module below, whose dimension is `card (WeylIndex n κ)`) by the matrices `New.conjWeylMatrix`,
is irreducible: the translates of any non-zero vector `v` span the whole space. This is the Weyl
module with `κ τ h` columns of height `h` at `τ`, twisted by the powers `e` of the determinants. -/
lemma span_conjWeylRep_eq_top (e : Φ → ℤ) {v : WeylIndex n κ → ℂ} (hv : v ≠ 0) :
    span ℂ (Set.range fun x : Φ → USign (1 : n → ℤˣ) ↦ conjWeylRep κ e x v) = ⊤ := by
  -- If `w` is outside the span, some linear form `f` kills all translates of `v` and has `f w ≠ 0`.
  -- By Schur orthogonality `(dim ρ)⁻¹ ⟨v, v⟩ f w` is the integral of `f (ρ(x) v) ⟨v, ρ(x⁻¹) w⟩`.
  refine eq_top_iff'.2 fun w ↦ by_contra fun hw ↦ ?_
  obtain ⟨f, hf_ne : f w ≠ 0, hf_ker⟩ := exists_le_ker_of_notMem hw
  have h_kill (x : Φ → USign (1 : n → ℤˣ)) : f (conjWeylRep κ e x v) = 0 :=
    hf_ker (subset_span ⟨x, rfl⟩)
  have h_norm : gramForm v v ≠ 0 := (weylGramOver_posDef.dotProduct_mulVec_pos hv).ne'
  have h_zero : (card (WeylIndex n κ) : ℂ)⁻¹ * gramForm v v * f w = 0 := by
    simp [-card_pi, ← schur_orthogonality e f v w v, h_kill]
  simp [-card_pi, h_norm, hf_ne] at h_zero

/-- The module `New.nablaFamily` of Borel semi-invariant polynomials of weight `κ` is irreducible
under U(n)^Φ: if `f` is a non-zero member (a polynomial in `MatrixPoly (Σ _ : Φ, n) ℂ`, whose
variables are `X (⟨τ, i⟩, t)` with row `(τ, i)` and column `t : ℕ`), each member `g` is a linear
combination of the polynomials `y ↦ f (uᵀ y)` with `u` in U(n)^Φ = `Φ → USign 1`. Here
`New.rowSubst z f` is `y ↦ f (z y)`.

This is Weyl's theorem that the highest weight modules of GL_n(ℂ) are irreducible under the compact
group U(n), for polynomial weights and products of copies of U(n). -/
lemma mem_span_rowSubst_unitary {f g : MatrixPoly (Σ _ : Φ, n) ℂ}
    (hf : f ∈ nablaFamily ℂ (fun _ : Φ ↦ n) κ) (hf_ne : f ≠ 0)
    (hg : g ∈ nablaFamily ℂ (fun _ : Φ ↦ n) κ) :
    g ∈ span ℂ (Set.range fun u : Φ → USign (1 : n → ℤˣ) ↦
      rowSubst (fun τ : Φ ↦ (u τ).val.valᵀ) f) := by
  -- `toPoly` maps the coordinate vectors onto `nablaFamily` and turns the action of `x` into
  -- substitution of the transpose of the conjugate of `x`, which is again unitary.
  rw [← range_toPoly] at hf hg
  obtain ⟨v, rfl⟩ := hf
  obtain ⟨w, rfl⟩ := hg

  let bar : USign (1 : n → ℤˣ) →* USign (1 : n → ℤˣ) := U.map (starRingEnd ℂ)
  have h_translate (x : Φ → USign (1 : n → ℤˣ)) :
      toPoly (fun _ : Φ ↦ n) κ (conjWeylRep κ 0 x v) =
        rowSubst (fun τ : Φ ↦ (bar (x τ)).val.valᵀ) (toPoly (fun _ : Φ ↦ n) κ v) := by
    have h_rep : conjWeylRep κ 0 x v = schur κ (fun τ : Φ ↦ (bar (x τ)).val.val) *ᵥ v := by
      simp [conjWeylRep, weylRep, bar, U.map]
    rw [h_rep, toPoly_schur FitsRanks.refl]
    simp [schurDetExp, detPow]
  have hw : w ∈ span ℂ (Set.range fun x : Φ → USign (1 : n → ℤˣ) ↦ conjWeylRep κ 0 x v) := by
    simp [span_conjWeylRep_eq_top 0 (ne_zero_of_map hf_ne)]
  refine span_mono ?_ (apply_mem_span_image_of_mem_span (toPoly (fun _ : Φ ↦ n) κ) hw)
  rintro _ ⟨-, ⟨x, rfl⟩, rfl⟩
  exact ⟨bar ∘ x, (h_translate x).symm⟩

variable {p : Type} [Fintype p] [DecidableEq p] {ι : Φ → Type} [∀ τ : Φ, Fintype (ι τ)]

omit [DecidableEq Φ] [DecidableEq n] in
/-- An algebra map `φ` carries `pairedDetProd Y η`, the product over `τ` and `k` of the
`det (η τ k * Y τ)`, to the same product for the images of the matrices `Y τ` under `φ`. -/
lemma map_pairedDetProd {S S' : Type} [CommRing S] [Algebra ℂ S] [CommRing S'] [Algebra ℂ S']
    (φ : S →ₐ[ℂ] S') (Y : Φ → n → p → S) (η : (τ : Φ) → ι τ → Matrix p n ℂ) :
    φ (pairedDetProd Y η) = pairedDetProd (fun (τ : Φ) (i : n) (k : p) ↦ φ (Y τ i k)) η := by
  simp [pairedDetProd, det_apply', mul_apply]

omit [DecidableEq Φ] [DecidableEq n] in
/-- Let `card p < card n` and let `Y τ` be the `n × p` matrix formed by the first `card p` columns
of the variables at `τ`, numbered by `equivFin p`. The product `pairedDetProd Y η` of the
`det (η τ k * Y τ)` lies in the module `New.nablaFamily` of Borel semi-invariants whose diagram at
`τ` has `card (ι τ)` columns of height `card p`. -/
lemma pairedDetProd_mem_nablaFamily (hp : card p < card n) (η : (τ : Φ) → ι τ → Matrix p n ℂ) :
    pairedDetProd (fun (τ : Φ) (i : n) (k : p) ↦ X (⟨τ, i⟩, (equivFin p k : ℕ))) η ∈
      nablaFamily ℂ (fun _ : Φ ↦ n) fun τ : Φ ↦ Pi.single (card p) (card (ι τ)) := by
  -- By the Cauchy–Binet formula each factor is a combination of maximal minors of `Y τ`.
  let Y (τ : Φ) (i : n) (k : p) : MatrixPoly (Σ _ : Φ, n) ℂ := X (⟨τ, i⟩, (equivFin p k : ℕ))
  have h_factor (τ : Φ) (c : Matrix p n ℂ) :
      (c.map (algebraMap ℂ (MatrixPoly (Σ _ : Φ, n) ℂ)) * of (Y τ)).det ∈
        nabla ℂ (Sigma.fst (β := fun _ : Φ ↦ n))
          (∑ i ∈ Finset.range (card p), Finsupp.single (τ, i) 1) := by
    have h_det : (c.map (algebraMap ℂ (MatrixPoly (Σ _ : Φ, n) ℂ)) * of (Y τ)).det =
        (of fun s t : Fin (card p) ↦ ∑ i : n, c.submatrix (equivFin p).symm id s i •
          X (R := ℂ) ((⟨τ, i⟩ : Σ _ : Φ, n), (t : ℕ))).det := by
      rw [← det_submatrix_equiv_self (equivFin p).symm]
      simp [Y, mul_apply, smul_eq_C_mul, Matrix.submatrix]
    rw [h_det, det_sum_smul_X]
    exact sum_mem fun I _ ↦ smul_mem _ _ (minor_mem_nabla fun _ ↦ rfl)
  have h_weight :
      diagramWeight (rankAt fun _ : Φ ↦ n) (fun τ : Φ ↦ Pi.single (card p) (card (ι τ))) =
        ∑ τ : Φ, ∑ _k : ι τ, ∑ i ∈ Finset.range (card p), Finsupp.single (τ, i) 1 := by
    simp [diagramWeight, Pi.single_apply, hp]
  rw [nablaFamily, h_weight]
  -- Semi-invariants multiply and their weights add.
  exact SetLike.prod_mem_graded _ _ _ fun τ _ ↦
    SetLike.prod_mem_graded _ _ _ fun k _ ↦ h_factor τ (η τ k)

omit [DecidableEq Φ] [DecidableEq n] in
/-- Let `Y τ` be the `n × p` matrix formed by the first `card p` columns of the variables at `τ`,
numbered by `equivFin p`. The substitution `rowSubst z` of `z y` for `y` takes `pairedDetProd Y η`,
the product of the `det (η τ k * Y τ)`, to the product of the `det (η τ k * z τ * Y τ)`. -/
lemma rowSubst_pairedDetProd_X (z : Φ → Matrix n n ℂ) (η : (τ : Φ) → ι τ → Matrix p n ℂ) :
    rowSubst z (pairedDetProd (fun (τ : Φ) (i : n) (k : p) ↦ X (⟨τ, i⟩, (equivFin p k : ℕ))) η) =
      pairedDetProd (fun (τ : Φ) (i : n) (k : p) ↦ X (⟨τ, i⟩, (equivFin p k : ℕ)))
        fun (τ : Φ) (k : ι τ) ↦ η τ k * z τ := by
  rw [map_pairedDetProd]
  simp only [pairedDetProd, Matrix.map_mul, Matrix.mul_assoc]
  congr! 4
  -- Entry by entry, the substitution takes the matrix `Y τ` of variables to `z τ * Y τ`.
  ext : 2
  simp [rowSubst, mul_apply, smul_eq_C_mul]

/-- Polarisation. Let `card p < card n`, and let `η₀` be the `p × n` matrix whose row `k` is the
standard basis vector at `r k`, for an injective `r`. For all complex `p × n` matrices `η τ k`, the
product `pairedDetProd Y η` of the `det (η τ k * Y τ)` is a finite combination of the products
`∏ τ, det (η₀ * (u τ)ᵀ * Y τ) ^ card (ι τ)` with `u τ` unitary (`USign 1` is U(n)). The
coefficients do not depend on the matrices `Y τ` or on the algebra `S` that holds their entries. -/
theorem exists_pairedDetProd_eq_sum_unitary (hp : card p < card n) {r : p → n}
    (hr : r.Injective) (η : (τ : Φ) → ι τ → Matrix p n ℂ) :
    ∃ c : (Φ → USign (1 : n → ℤˣ)) →₀ ℂ,
      ∀ (S : Type) [CommRing S] [Algebra ℂ S] (Y : Φ → n → p → S),
        pairedDetProd Y η =
          c.sum fun (u : Φ → USign (1 : n → ℤˣ)) (z : ℂ) ↦ z • pairedDetProd Y
            fun (τ : Φ) (_ : ι τ) ↦ (1 : Matrix n n ℂ).submatrix r id * (u τ).val.valᵀ := by
  -- Prove the identity for matrices of variables, in the irreducible module `nablaFamily`; then put
  -- `Y` in for the variables.
  let P (ξ : (τ : Φ) → ι τ → Matrix p n ℂ) : MatrixPoly (Σ _ : Φ, n) ℂ :=
    pairedDetProd (fun (τ : Φ) (i : n) (k : p) ↦ X (⟨τ, i⟩, (equivFin p k : ℕ))) ξ
  let η₀ (τ : Φ) (_ : ι τ) : Matrix p n ℂ := (1 : Matrix n n ℂ).submatrix r id
  -- Substituting `Y τ` for the first `card p` columns of variables gives `P ξ ↦ pairedDetProd Y ξ`.
  have h_eval {S : Type} [CommRing S] [Algebra ℂ S] (Y : Φ → n → p → S) :
      ∃ φ : MatrixPoly (Σ _ : Φ, n) ℂ →ₐ[ℂ] S,
        ∀ ξ : (τ : Φ) → ι τ → Matrix p n ℂ, φ (P ξ) = pairedDetProd Y ξ := by
    let value : (Σ _ : Φ, n) × ℕ → S := fun (⟨τ, i⟩, t) ↦
      if ht : t < card p then Y τ i ((equivFin p).symm ⟨t, ht⟩) else 0
    exact ⟨aeval value, fun ξ ↦ by simp [P, value, map_pairedDetProd]⟩
  -- `P η₀` is not zero: its value at `η₀ᵀ` is `1`.
  have h_ne : P η₀ ≠ 0 := by
    obtain ⟨φ, hφ⟩ := h_eval fun (_ : Φ) (i : n) (k : p) ↦ (1 : Matrix n n ℂ) i (r k)
    have h_frame : (1 : Matrix n n ℂ).submatrix r id *
        (of fun (i : n) (k : p) ↦ (1 : Matrix n n ℂ) i (r k)) = 1 := by
      ext
      simp [mul_apply, one_apply, hr.eq_iff]
    have h_one : φ (P η₀) = 1 := by simp [hφ, pairedDetProd, η₀, h_frame]
    exact ne_zero_of_map (f := φ) (by simp [h_one])
  have h_subst (u : Φ → USign (1 : n → ℤˣ)) :
      rowSubst (fun τ ↦ (u τ).val.valᵀ) (P η₀) = P fun τ k ↦ η₀ τ k * (u τ).val.valᵀ :=
    rowSubst_pairedDetProd_X _ η₀
  have h_span : P η ∈ span ℂ (Set.range fun u : Φ → USign (1 : n → ℤˣ) ↦
      rowSubst (fun τ ↦ (u τ).val.valᵀ) (P η₀)) :=
    mem_span_rowSubst_unitary (pairedDetProd_mem_nablaFamily hp η₀) h_ne
      (pairedDetProd_mem_nablaFamily hp η)
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h_span
  refine ⟨c, fun S _ _ Y ↦ ?_⟩
  obtain ⟨φ, hφ⟩ := h_eval Y
  simp only [← hφ, ← hc, map_finsuppSum, map_smul, h_subst, η₀]

end New

end Polarisation

/-!
## Averaging polynomials in square matrices

A tuple `u` of unitary matrices carries a polynomial `q (z)` to `q (uᵀ z)`.
-/

section Averaging

open Matrix MvPolynomial MeasureTheory New.GL New.Rows

namespace New

variable {Φ n : Type} [Fintype Φ] [Fintype n] [DecidableEq n]

/-- The mean over U(n)^Φ (here `Φ → USign 1`), with a continuous weight `w`, of the translates
`q (uᵀ z)` of a polynomial `q` in square matrices `z τ` is a polynomial: there is one whose value
under each linear form `M` is the integral of `w u * M (q (uᵀ z))` for the Haar probability measure
`volume`. -/
lemma exists_forall_map_eq_integral_translate (q : MvPolynomial (Φ × n × n) ℂ)
    {w : (Φ → USign (1 : n → ℤˣ)) → ℂ} (hw : Continuous w) :
    ∃ mean : MvPolynomial (Φ × n × n) ℂ, ∀ M : MvPolynomial (Φ × n × n) ℂ →ₗ[ℂ] ℂ,
      M mean = ∫ u : Φ → USign (1 : n → ℤˣ), w u *
        M (aeval (fun ((τ, j, k) : Φ × n × n) ↦ ∑ i : n, (u τ).val.val i j • X (τ, i, k)) q) := by
  -- The coefficients of `q (uᵀ z)` are the values at `u` of the finitely many coefficients of the
  -- generic translate `Q`; integrate each of them.
  let Q : MvPolynomial (Φ × n × n) (MvPolynomial (Φ × n × n) ℂ) :=
    aeval (fun ((τ, j, k) : Φ × n × n) ↦ ∑ i : n, X (R := ℂ) (τ, i, j) • X (τ, i, k)) q
  let φ (u : Φ → USign (1 : n → ℤˣ)) : MvPolynomial (Φ × n × n) ℂ →ₐ[ℂ] ℂ :=
    aeval fun ((τ, i, j) : Φ × n × n) ↦ (u τ).val.val i j
  have h_expand (u : Φ → USign (1 : n → ℤˣ)) :
      aeval (fun ((τ, j, k) : Φ × n × n) ↦ ∑ i : n, (u τ).val.val i j • X (R := ℂ) (τ, i, k)) q =
        ∑ d ∈ Q.support, φ u (Q.coeff d) • monomial d 1 :=
    calc _ = mapAlgHom (φ u) Q := by simp [Q, φ, comp_aeval_apply, smul_eq_C_mul]
      _ = ∑ d ∈ Q.support, φ u (Q.coeff d) • monomial d 1 := by
        conv_lhs => rw [Q.as_sum, map_sum]
        simp [smul_monomial]
  refine ⟨∑ d ∈ Q.support, (∫ u, w u * φ u (Q.coeff d)) • monomial d 1, fun M ↦ ?_⟩
  have h_cont (d : Φ × n × n →₀ ℕ) :
      Continuous fun u ↦ w u * φ u (Q.coeff d) * M (monomial d 1) := by
    simp only [φ, aeval_def, eval₂_eq']
    fun_prop
  simp only [h_expand, map_sum, map_smul, smul_eq_mul, Finset.mul_sum, ← mul_assoc,
    ← integral_mul_const]
  exact (integral_finsetSum Q.support fun d _ ↦
    (h_cont d).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).symm

/-- A polynomial `f` in square matrices whose value at `xᵀ` is `a * ∏ τ, det (x τ) ^ c τ` for all
`x` in U(n)^Φ = `Φ → USign 1` is `a * ∏ τ, det (z τ) ^ c τ`, where `det (z τ)` is
`variableMinor τ id id`. -/
lemma eq_smul_det_pow_of_unitary (c : Φ → ℕ) {f : MvPolynomial (Φ × n × n) ℂ} {a : ℂ}
    (hf : ∀ x : Φ → USign (1 : n → ℤˣ),
      f.eval (fun ((τ, i, j) : Φ × n × n) ↦ (x τ).val.val j i) =
        a * ∏ τ : Φ, (x τ).val.val.det ^ c τ) :
    f = a • ∏ τ : Φ, variableMinor τ id id ^ c τ := by
  -- The unitary group is Zariski dense. The value `evalMatrix x P` of `P` at `x` is the difference
  -- of the two sides at `xᵀ`.
  let P : MvPolynomial ((_ : Φ) × n × n) ℂ :=
    rename (fun ((τ, i, j) : Φ × n × n) ↦ ⟨τ, j, i⟩) (f - a • ∏ τ : Φ, variableMinor τ id id ^ c τ)
  have h_unitary (g : Φ → Matrix n n ℂ) (hg : ∀ τ : Φ, (g τ)ᴴ * g τ = 1) : evalMatrix g P = 0 := by
    have h_det (τ : Φ) :
        (variableMinor τ id id).eval (fun ((σ, i, j) : Φ × n × n) ↦ g σ j i) = (g τ).det := by
      simp [variableMinor, RingHom.map_det, ← det_transpose (g τ), transpose, Matrix.map]
    have h_value : f.eval (fun ((σ, i, j) : Φ × n × n) ↦ g σ j i) =
        a * ∏ τ : Φ, (g τ).det ^ c τ := by
      simpa using hf fun τ ↦ U.of (by simp) (g τ) (by simp [hg])
    simp [P, eval_rename, Function.comp_def, h_det, h_value]
  -- A polynomial that vanishes at all tuples of unitary matrices is zero.
  refine MvPolynomial.funext fun z ↦ sub_eq_zero.1 ?_
  simpa [P, eval_rename, Function.comp_def] using
    zariski_dense_unitary (fun τ : Φ ↦ of fun i j : n ↦ z (τ, j, i)) P h_unitary

/-- Averaging over U(n)^Φ = `Φ → USign 1`. Let `q` be a polynomial in square matrices `z τ`. There
is a number `a` such that every linear form `M` with `M (q (uᵀ z)) = t * ∏ τ, det (u τ) ^ c τ` for
all unitary `u` has `t = a * M (∏ τ, det (z τ) ^ c τ)`. Here `t = M q`, by `u = 1`, and `det (z τ)`
is `variableMinor τ id id`. -/
lemma exists_forall_eq_mul_map_det_pow (c : Φ → ℕ) (q : MvPolynomial (Φ × n × n) ℂ) :
    ∃ a : ℂ, ∀ (M : MvPolynomial (Φ × n × n) ℂ →ₗ[ℂ] ℂ) (t : ℂ),
      (∀ u : Φ → USign (1 : n → ℤˣ),
        M (aeval (fun ((τ, j, k) : Φ × n × n) ↦ ∑ i : n, (u τ).val.val i j • X (τ, i, k)) q) =
          t * ∏ τ : Φ, (u τ).val.val.det ^ c τ) →
      t = a * M (∏ τ : Φ, variableMinor τ id id ^ c τ) := by
  -- The mean of `χ u⁻¹ • q (uᵀ z)` over the group, with `χ u = ∏ τ, det (u τ) ^ c τ`, has value `t`
  -- under `M`. Its value at a unitary `xᵀ` is `a * χ x`, so it is `a` times the product of
  -- determinants.
  let χ (u : Φ → USign (1 : n → ℤˣ)) : ℂ := ∏ τ : Φ, (u τ).val.val.det ^ c τ
  have hχ_mul (u v : Φ → USign (1 : n → ℤˣ)) : χ (u * v) = χ u * χ v := by
    simp [χ, mul_pow, Finset.prod_mul_distrib]
  have hχ_inv (u : Φ → USign (1 : n → ℤˣ)) : χ u⁻¹ * χ u = 1 := by
    simpa [χ] using (hχ_mul u⁻¹ u).symm
  obtain ⟨mean, h_mean⟩ :=
    exists_forall_map_eq_integral_translate q (w := fun u ↦ χ u⁻¹) (by fun_prop)
  let value (x : Φ → USign (1 : n → ℤˣ)) : MvPolynomial (Φ × n × n) ℂ →ₐ[ℂ] ℂ :=
    aeval fun ((τ, i, j) : Φ × n × n) ↦ (x τ).val.val j i
  let a : ℂ := ∫ u, χ u⁻¹ * value u q
  -- At the point `xᵀ` with `x` unitary use `uᵀ xᵀ = (x * u)ᵀ` and substitute `x * u` for `u`.
  have h_point (x u : Φ → USign (1 : n → ℤˣ)) : value x (aeval
      (fun ((τ, j, k) : Φ × n × n) ↦ ∑ i : n, (u τ).val.val i j • X (τ, i, k)) q) =
      value (x * u) q := by
    simp [value, aeval_bind₁, mul_apply, mul_comm]
  have h_value (x : Φ → USign (1 : n → ℤˣ)) : value x mean = a * χ x :=
    calc value x mean = ∫ u, χ u⁻¹ * value (x * u) q := by
          simpa only [AlgHom.toLinearMap_apply, h_point] using h_mean (value x).toLinearMap
      _ = ∫ u, χ (x * u)⁻¹ * value (x * u) q * χ x := by
        congr with u
        simp only [_root_.mul_inv_rev, hχ_mul]
        linear_combination -(χ u⁻¹ * value (x * u) q) * hχ_inv x
      _ = a * χ x := by
        rw [integral_mul_const, integral_mul_left_eq_self fun u ↦ χ u⁻¹ * value u q]
  refine ⟨a, fun M t hM ↦ ?_⟩
  calc t = ∫ u, χ u⁻¹ * (t * χ u) := by simp [mul_left_comm _ t, hχ_inv]
    _ = M mean := by simp only [h_mean, hM, χ]
    _ = a * M (∏ τ : Φ, variableMinor τ id id ^ c τ) := by
      simp [eq_smul_det_pow_of_unitary c h_value]

end New

end Averaging

end
