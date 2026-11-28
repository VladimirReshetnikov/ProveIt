import Lib.GaloisRep.Pseudocharacter.SemisimpleRepresentations
import Lib.General.NumberTheory.PadicLimitsValuation

/-!
# Spanning criteria, limits of traces and pseudorepresentations

This file gives a criterion for the image of a lattice to span the matrix algebra over the
coefficient ring `O`, using a tame pair with incongruent eigenvalues. It studies uniform
approximation of eigensystems through `New.IsApproximatingMonoid`, and Newton's identities through
`New.newtonPoly`. It proves that over an algebraically closed field of characteristic `0`, a
function obeying every polynomial identity among traces is the trace of a representation. It also
proves that a limit of traces of continuous representations is such a trace.

## Main definitions and results

* `New.exists_rep_of_trace_identities`: over an algebraically closed field of characteristic `0`, a
  function on `G` that obeys every polynomial identity among traces of homomorphisms `G → GL n k` is
  the trace of such a homomorphism with non-degenerate trace form (`New.IsTraceNondeg`).
* `New.GaloisRep.exists_continuous_isTraceNondeg_of_tendsto_trace`: a limit, in the sense of
  `IsApproximatingMonoid` (uniform approximation by linear combinations), of traces of continuous
  representations is the trace of a continuous representation.

Notions from other files:
* `New.IsTraceNondeg`: Non-degeneracy of the trace form on the span of r(G): any x in that span with
  tr(x r(g)) = 0 for all g is zero.
* `New.CoeffRing`: Rings of integers of finite Galois extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, where the
  class `ThePrime ℓ` records that ℓ is the fixed prime.
* `New.Selmer.IsLatticeIn`: an `O`-valued representation `u` is conjugate in `GL n ℚ̄_ℓ` to a given
  ℓ-adic representation `r`.

## Relation to the literature

Known result: a function obeying the trace identities is the trace of a representation
(pseudocharacters), and the lattice stable under a family spanning the matrix algebra is unique up
to scalars. Here all polynomial identities among traces are assumed, not only the Frobenius
identity, so no invariant theory is needed.
Semisimple means a non-degenerate trace form on the span of the image, in characteristic 0. The file
also proves that a limit of traces of continuous representations is the trace of a continuous
representation. Source: R. Taylor, Galois representations associated to Siegel modular forms of low
weight, Duke Math. J. 63 (1991), Theorem 1; R. Rouquier, Caractérisation des caractères et
pseudo-caractères, J. Algebra 180 (1996); K. Conrad, Compact subgroups of GL_n(Qbar_p) (note).

See also `Lib.GaloisRep.WeightCongruence`.
-/

noncomputable section

/-!
## A spanning criterion from a tame pair with incongruent eigenvalues

A criterion for residual absolute irreducibility, in the strong form that the image of the group
spans the matrix algebra over the coefficient ring
(`New.Selmer.IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj`). In the application `γ` and `φ`
come from tame inertia and Frobenius at an auxiliary place. A spanning family has an absolutely
irreducible reduction (`New.Selmer.eq_bot_or_eq_top_of_span_eq_top`), and its stable lattice is
unique up to scalars (`New.Selmer.exists_eq_smul_of_conj_eq`).
-/

section ResidualIrreducibility

open Matrix IsLocalRing Fintype Module Submodule Set End

/-- The coordinates of a matrix in the standard basis are its entries. -/
private lemma Matrix.stdBasis_repr_apply {R m : Type*} [CommRing R] [Fintype m]
    (M : Matrix m m R) (i j : m) : (stdBasis R m m).repr M (i, j) = M i j :=
  rfl

/-- In a group, if `x ^ q = y⁻¹ * x * y`, then `x * y ^ k = y ^ k * x ^ q ^ k` for every `k`. -/
private lemma mul_pow_eq_pow_mul_pow_pow_of_pow_eq_inv_mul_mul {M : Type*} [Group M] {x y : M}
    {q : ℕ} (h : x ^ q = y⁻¹ * x * y) (k : ℕ) : x * y ^ k = y ^ k * x ^ q ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc x * y ^ (k + 1) = y ^ k * x ^ q ^ k * y := by rw [pow_succ, ← mul_assoc, ih]
      _ = y ^ (k + 1) * (y⁻¹ * x ^ q ^ k * y) := by simp [pow_succ, mul_assoc]
      _ = y ^ (k + 1) * (y⁻¹ * x * y) ^ q ^ k := by simpa using (conj_pow (a := y⁻¹)).symm
      _ = y ^ (k + 1) * x ^ q ^ (k + 1) := by rw [← h, ← pow_mul, ← pow_succ']

/-- Let `R : G →* M` be a homomorphism of groups and `R (γ * φ ^ d) = R (φ ^ d * γ)`. Then every
`R (φ ^ a * γ ^ b)` commutes with `R (φ⁻¹ ^ d)`. -/
private lemma commute_map_pow_mul_pow_map_inv_pow {G M : Type*} [Group G] [Group M] (R : G →* M)
    {γ φ : G} {d : ℕ} (h_comm : R (γ * φ ^ d) = R (φ ^ d * γ)) (a b : ℕ) :
    Commute (R (φ ^ a * γ ^ b)) (R (φ⁻¹ ^ d)) := by
  have h_γ : Commute (R γ) (R (φ ^ d)) := by simpa only [map_mul, commute_iff_eq] using h_comm
  simp only [map_mul, map_pow, map_inv, inv_pow] at h_γ ⊢
  exact ((Commute.pow_pow_self (R φ) a d).mul_left (h_γ.pow_left b)).inv_right

/-- If the differences `ζ ^ q ^ i - ζ ^ q ^ j` for distinct `i, j < d` have norm `1`, then the
residues of the `ζ ^ q ^ i`, `i < d`, are pairwise distinct: a difference of norm `1` is a unit of
`O`, so its residue is not zero. -/
private lemma New.injective_residue_pow_pow_of_norm_sub_eq_one {ℓ : ℕ} [ThePrime ℓ]
    {O : CoeffRing ℓ} {ζ : ↑O} {q d : ℕ}
    (h_dist : ∀ i < d, ∀ j < d, i ≠ j → ‖ζ.val ^ q ^ i - ζ ^ q ^ j‖ = 1) :
    Function.Injective fun j : Fin d ↦ residue O ζ ^ q ^ (j : ℕ) := by
  refine .of_lt_imp_ne fun i j h_lt ↦ ?_
  have h_unit : IsUnit (ζ ^ q ^ (i : ℕ) - ζ ^ q ^ (j : ℕ)) := by
    rw [O.isUnit_iff_norm_eq_one]
    simpa using h_dist i i.isLt j j.isLt (Fin.val_ne_of_ne h_lt.ne)
  simpa [sub_ne_zero] using (residue_ne_zero_iff_isUnit _).2 h_unit

/-- A square matrix that commutes with every member of a family spanning all matrices is a scalar
multiple of `1`. -/
private lemma Matrix.exists_eq_smul_one_of_commute_of_span_eq_top {R n ι : Type*} [CommRing R]
    [Fintype n] [DecidableEq n] {v : ι → Matrix n n R} (h_span : Submodule.span R (range v) = ⊤)
    {M : Matrix n n R} (h_comm : ∀ i : ι, Commute (v i) M) : ∃ α : R, M = α • 1 := by
  have h_scalar : M ∈ range (scalar n) := by
    refine mem_range_scalar_of_commute_single fun i j _ ↦ ?_
    exact .span_left (forall_mem_range.mpr h_comm) _ (h_span.ge Submodule.mem_top)
  simpa [eq_comm, smul_one_eq_diagonal] using h_scalar

/-- A tame pair with incongruent conjugate eigenvalues spans all matrices. Let `u` be an
`O`-lattice in `R`, `d = card n`, let conjugation by `φ` raise `R γ` to the power `q`, let
`R (γ ^ q ^ d) = R γ`, and let `R γ` have an eigenvalue `ζ ∈ O` whose powers `ζ ^ q ^ i`, `i < d`,
differ by elements of norm `1`. Then (a) `u` spans all matrices over `O` and (b) `u (φ⁻¹ ^ d)` is
a scalar: a case of Burnside's theorem, lifted to `O` by Nakayama's lemma. -/
lemma New.Selmer.IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj {G n : Type} [Group G]
    [Fintype n] [DecidableEq n] {γ φ : G} {q ℓ : ℕ} [ThePrime ℓ] {O : CoeffRing ℓ}
    {R : G →* GL n (PadicAlgCl ℓ)} {u : G →* Matrix n n O} {ζ : ↑O} (h_lattice : IsLatticeIn R u)
    (h_tame : R γ ^ q = R (φ⁻¹ * γ * φ))
    (h_dist : ∀ i < card n, ∀ j < card n, i ≠ j → ‖ζ.val ^ q ^ i - ζ ^ q ^ j‖ = 1)
    (h_root : (R γ).val.charpoly.IsRoot ζ) (h_fix : R (γ ^ q ^ card n) = R γ) :
    -- (a) the image of `u` spans all matrices
    span O (range u) = ⊤ ∧
    -- (b) `φ⁻¹ ^ card n` acts by a scalar
    ∃ α : ↑O, u (φ⁻¹ ^ card n) = α • 1 := by
  -- Modulo the maximal ideal, `γ` has the eigenvectors `φ ^ j v` with the distinct eigenvalues
  -- `ζ ^ q ^ j`. A Vandermonde argument makes the `(card n)²` matrices of `φ ^ a * γ ^ b`
  -- independent, so they form a basis over `O`; and `φ⁻¹ ^ card n` commutes with all of them.
  have hζ_u : ((u γ).charpoly.map O.val.val).IsRoot (ζ : PadicAlgCl ℓ) := by
    rwa [h_lattice.charpoly_eq_map γ] at h_root
  obtain ⟨P, hP⟩ := h_lattice
  -- `u` is determined by `R`: `u a` is `R a` conjugated by `P`, read in `O`.
  have u_congr {a b : G} (hab : R a = R b) : u a = u b :=
    map_injective (f := O.val.val) Subtype.val_injective (by simp only [← hP, hab])
  -- `τ` is the residual representation, `v` an eigenvector of `τ γ`.
  let τ : G →* End (ResidueField O) (n → ResidueField O) :=
    (toLinAlgEquiv'.toRingHom.comp (residue _).mapMatrix).toMonoidHom.comp u
  obtain ⟨v, hv⟩ : ∃ v : n → ResidueField O, HasEigenvector (τ γ) (residue O ζ) v := by
    refine ((hasEigenvalue_iff_isRoot_charpoly (τ γ) _).2 ?_).exists_hasEigenvector
    show (toLin' ((u γ).map (residue O))).charpoly.IsRoot (residue O ζ)
    rw [charpoly_toLin', charpoly_map]
    exact .map (.of_map hζ_u O.val.subtype_injective)
  -- Iterating `h_tame`: conjugation by `φ ^ k` raises `R γ` to the power `q ^ k`.
  have h_conj (k : ℕ) : R (γ * φ ^ k) = R (φ ^ k * γ ^ q ^ k) := by
    simpa [map_mul, map_pow] using mul_pow_eq_pow_mul_pow_pow_of_pow_eq_inv_mul_mul
      (x := R γ) (y := R φ) (h_tame.trans (by simp)) k
  have hφ_inj (j : ℕ) : Function.Injective (τ φ ^ j) := by
    simpa [← map_pow] using (Representation.apply_bijective τ (φ ^ j)).injective
  let μ (j : ℕ) : ResidueField O := residue O ζ ^ q ^ j
  have h_eig (j : ℕ) : HasEigenvector (τ γ) (μ j) ((τ φ ^ j) v) := by
    have h_act : τ (γ * φ ^ j) v = τ (φ ^ j * γ ^ q ^ j) v := by
      simp only [τ, MonoidHom.comp_apply, u_congr (h_conj j)]
    refine ⟨?_, (map_ne_zero_iff _ (hφ_inj j)).2 hv.right⟩
    simpa [hv.pow_apply] using h_act
  -- A difference of norm `1` is a unit of `O`, so it has non-zero residue.
  have hμ_inj : Function.Injective fun j : Fin (card n) ↦ μ j :=
    injective_residue_pow_pow_of_norm_sub_eq_one h_dist
  let w (p : Fin (card n) × Fin (card n)) : G := φ ^ (p.fst : ℕ) * γ ^ (p.snd : ℕ)
  have h_indep (c : Fin (card n) × Fin (card n) → ResidueField O)
      (hc : ∑ p, c p • τ (w p) = 0) (a b : Fin (card n)) : c (a, b) = 0 := by
    -- Apply the relation to the eigenvector `φ ^ l v` and cancel `φ ^ l`.
    have h_rel (l : Fin (card n)) :
        ∑ a : Fin (card n), (∑ k, c (a, k) * μ l ^ (k : ℕ)) • (τ φ ^ (a : ℕ)) v = 0 := by
      apply hφ_inj l
      simpa [w, sum_prod_type, Finset.sum_smul, mul_smul, (h_eig l).pow_apply,
        ← mul_apply (_ ^ (l : ℕ)), pow_mul_comm _ l] using
        LinearMap.congr_fun hc ((τ φ ^ (l : ℕ)) v)
    -- The eigenvectors are independent, so a polynomial of degree `< card n` vanishes at all `μ l`.
    have h_poly (l : Fin (card n)) : ∑ k, c (a, k) * μ l ^ (k : ℕ) = 0 := linearIndependent_iff.mp
      (eigenvectors_linearIndependent' (τ γ) _ hμ_inj _ fun l ↦ h_eig l) _ (h_rel l) a
    exact congrFun (eq_zero_of_forall_index_sum_mul_pow_eq_zero hμ_inj h_poly) b
  -- The determinant of the `u (w p)` in the standard basis is a unit, as its residue is not zero.
  let e : Basis (Fin (card n) × Fin (card n)) O (Matrix n n O) :=
    (stdBasis O n n).reindex ((equivFin n).prodCongr (equivFin n))
  have h_det : IsUnit (e.det (u ∘ w)) := by
    have h_col : LinearIndependent (ResidueField O) ((e.toMatrix (u ∘ w)).map (residue O)).col := by
      refine linearIndependent_iff.mpr fun c hc (a, b) ↦ h_indep c ?_ a b
      ext i j
      simpa [τ, e, Basis.toMatrix_apply, Matrix.stdBasis_repr_apply] using
        congrFun hc (equivFin n j, equivFin n i)
    rw [← isUnit_map_iff (residue O), Basis.det_apply, RingHom.map_det]
    exact (linearIndependent_col_iff_isUnit.mp h_col).map detMonoidHom
  have h_span : Submodule.span O (range (u ∘ w)) = ⊤ := (e.is_basis_iff_det.mpr h_det).right
  refine ⟨eq_top_mono (span_mono (range_comp_subset_range w u)) h_span, ?_⟩
  -- By `h_conj` and `h_fix`, `R γ` commutes with `R φ ^ card n`, so `R (φ⁻¹ ^ card n)` commutes
  -- with every `R (w p)`. As `u` is `R` conjugated by `P`, read in `O`, also `u (φ⁻¹ ^ card n)`
  -- commutes with every `u (w p)`.
  have h_comm_φ : R (γ * φ ^ card n) = R (φ ^ card n * γ) := by
    rw [h_conj, map_mul, map_mul, h_fix]
  have h_comm (p : Fin (card n) × Fin (card n)) : Commute (u (w p)) (u (φ⁻¹ ^ card n)) := by
    have h_R : R (w p * φ⁻¹ ^ card n) = R (φ⁻¹ ^ card n * w p) := by
      simpa only [w, map_mul] using (commute_map_pow_mul_pow_map_inv_pow R h_comm_φ _ _).eq
    simpa only [map_mul, commute_iff_eq] using u_congr h_R
  exact Matrix.exists_eq_smul_one_of_commute_of_span_eq_top h_span h_comm

/-- If the matrices `T g` span all of `M_n(O)` over a commutative ring `O`, then for every ring map
`f` from `O` to a field `k`, the only subspaces of `kⁿ` stable under all `f (T g)` are `0` and `kⁿ`.
For a local ring `O` this says that the reduction of `T` is absolutely irreducible. -/
theorem New.Selmer.eq_bot_or_eq_top_of_span_eq_top {X n O k : Type} [Fintype n] [DecidableEq n]
    [CommRing O] [Field k] (f : O →+* k) {T : X → Matrix n n O}
    (h_span : span O (range T) = ⊤) (U : Submodule k (n → k))
    (h_stable : ∀ g : X, ∀ v ∈ U, (T g).map f *ᵥ v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  -- Every matrix over `O` is a combination of the `T g`, so its image under `f` also preserves `U`.
  have h_all (x : Matrix n n O) : ∀ v ∈ U, x.map f *ᵥ v ∈ U := by
    induction eq_top_iff'.1 h_span x using span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact h_stable g
    | zero => simp
    | add x y _ _ hx hy =>
      intro v hv
      simpa [Matrix.map_add, add_mulVec] using U.add_mem (hx v hv) (hy v hv)
    | smul c x _ hx =>
      intro v hv
      simpa [Matrix.map_smul', smul_mulVec] using U.smul_mem (f c) (hx v hv)
  -- If `v ∈ U` has `v j ≠ 0`, the matrix units move `v` to multiples of all basis vectors.
  refine or_iff_not_imp_left.2 fun h_ne ↦ eq_top_iff'.2 fun w ↦ ?_
  obtain ⟨v, hv, hv_ne⟩ := U.ne_bot_iff.1 h_ne
  obtain ⟨j, hj⟩ : ∃ j : n, v j ≠ 0 := Function.ne_iff.1 hv_ne
  have h_single (i : n) : Pi.single i (w i) =
      (w i / v j) • ((Matrix.single i j 1 : Matrix n n O).map f *ᵥ v) := by
    ext l
    simp [single_mulVec, Pi.single_apply, Function.update_apply, hj]
  rw [← Finset.univ_sum_single w]
  simp only [h_single]
  exact sum_mem fun i _ ↦ U.smul_mem _ (h_all _ v hv)

/-- Let the matrices `T g` span all of `M_n(O)` over a coefficient ring `O`, and let `a` in
`GL_n(ℚ̄_ℓ)` conjugate each `T g` to a matrix `T' g` over `O`. Then `a` is a scalar times an element
of `GL_n(O)`. So the lattice `a Oⁿ` is a multiple of `Oⁿ`. -/
theorem New.Selmer.exists_eq_smul_of_conj_eq {X n : Type} [Fintype n] [DecidableEq n] {ℓ : ℕ}
    [ThePrime ℓ] {O : CoeffRing ℓ} {T T' : X → Matrix n n O} (h_span : span O (range T) = ⊤)
    (a : GL n (PadicAlgCl ℓ))
    (h_conj : ∀ g : X, a⁻¹.val * (T g).map O.val.val * a.val = (T' g).map O.val.val) :
    ∃ (α : (PadicAlgCl ℓ)ˣ) (k : GL n O), a.val = α.val • k.val.map O.val.val := by
  -- All products of an entry of `a⁻¹` with an entry of `a` lie in `O`. For an entry `α` of `a` of
  -- largest norm, both `α⁻¹ a` and its inverse `α a⁻¹` then have entries in `O`.
  rcases isEmpty_or_nonempty n with h_empty | h_nonempty
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  -- Conjugation by `a` preserves `M_n(O)`, which is spanned by the `T g`.
  have h_int (x : Matrix n n O) :
      ∃ y : Matrix n n O, a⁻¹.val * x.map O.val.val * a.val = y.map O.val.val := by
    induction eq_top_iff'.1 h_span x using span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨T' g, h_conj g⟩
    | zero => exact ⟨0, by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy⟩ := hx
      obtain ⟨y', hy'⟩ := hx'
      exact ⟨y + y', by rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), mul_add,
        add_mul, hy, hy']⟩
    | smul c x _ hx =>
      obtain ⟨y, hy⟩ := hx
      have h_map (z : Matrix n n O) : (c • z).map O.val.val = c.val • z.map O.val.val := rfl
      exact ⟨c • y, by rw [h_map, h_map, Matrix.mul_smul, Matrix.smul_mul, hy]⟩
  -- The product `a⁻¹ p i * a j q` is an entry of the conjugate of a matrix unit.
  have h_prod (p i j q : n) : a⁻¹.val p i * a.val j q ∈ O.val := by
    obtain ⟨y, hy⟩ := h_int (Matrix.single i j 1)
    convert (y p q).prop
    simpa [Matrix.mul_apply, Matrix.single_apply, ite_and, apply_ite Subtype.val] using
      congrFun (congrFun hy p) q
  obtain ⟨⟨j, q⟩, h_max⟩ := Finite.exists_max fun x : n × n ↦ ‖a.val x.1 x.2‖
  have h_ne : a.val j q ≠ 0 := fun h_zero ↦
    a.ne_zero (Matrix.ext fun u v ↦ by simpa [h_zero] using h_max (u, v))
  obtain ⟨p, i, h_inv_ne⟩ : ∃ p i : n, a⁻¹.val p i ≠ 0 := by
    by_contra! h_zero
    exact a⁻¹.ne_zero (Matrix.ext h_zero)
  -- In `O`, the product with the largest entry divides the products with the other entries.
  have h_quot (u v : n) : (a.val j q)⁻¹ * a.val u v ∈ O.val := by
    have h_le : ‖a⁻¹.val p i * a.val u v‖ ≤ ‖a⁻¹.val p i * a.val j q‖ := by
      simpa only [norm_mul] using mul_le_mul_of_nonneg_left (h_max (u, v)) (norm_nonneg _)
    obtain ⟨c, hc⟩ := (O.dvd_iff_norm_le ⟨_, h_prod p i j q⟩ ⟨_, h_prod p i u v⟩).2 h_le
    have h_mul : a.val u v = a.val j q * c :=
      mul_left_cancel₀ h_inv_ne ((congrArg Subtype.val hc).trans (mul_assoc _ _ _))
    simp [h_mul, h_ne]
  let k : Matrix n n O := .of fun u v ↦ ⟨(a.val j q)⁻¹ * a.val u v, h_quot u v⟩
  let k' : Matrix n n O := .of fun u v ↦ ⟨a⁻¹.val u v * a.val j q, h_prod u v j q⟩
  have hk : k.map O.val.val = (a.val j q)⁻¹ • a.val := rfl
  have hk' : k'.map O.val.val = a.val j q • a⁻¹.val := Matrix.ext fun _ _ ↦ mul_comm _ _
  have h_inv : k * k' = 1 := by
    refine Matrix.map_injective (f := O.val.val) Subtype.val_injective ?_
    change (k * k').map O.val.val = (1 : Matrix n n O).map O.val.val
    rw [Matrix.map_mul, hk, hk', Matrix.map_one _ (map_zero _) (map_one _), smul_mul_smul_comm,
      inv_mul_cancel₀ h_ne, one_smul, a.mul_inv]
  refine ⟨Units.mk0 (a.val j q) h_ne, ⟨k, k', h_inv, mul_eq_one_comm.1 h_inv⟩, ?_⟩
  rw [hk, Units.val_mk0, smul_inv_smul₀ h_ne]

end ResidualIrreducibility

/-!
## Uniform approximation of eigensystems and pseudorepresentations

* `New.IsApproximatingMonoid`: a closed submonoid of pairs of a value and a family of values, in
  which each value is a uniform limit of linear combinations of the family.
* `New.exists_isApproximatingMonoid_of_mem_uniformClosure`: an eigenfunction in the closure of the
  span of eigenfunctions of operators that do not increase the sup norm gives such an approximation
  of its eigenvalues.
-/

section Pseudorepresentation

open Filter MvPolynomial Finset Submodule Metric Matrix MonoidAlgebra Ideal.Quotient LinearMap
  Module IsAlgClosed IsUniformAddGroup

namespace New

variable {k K G n ι : Type} [Field k] [NormedField K] [Group G] [Fintype n] [DecidableEq n]

/-- For a set `S` of functions `ι → K`, `K` a normed field, the closure of the `K`-span of `S` in
the topology of uniform convergence. -/
def uniformClosure (S : Set (ι → K)) : Submodule K (ι → K) :=
  (topologicalClosure (M := UniformFun ι K) (span K S) :)

variable {S : Set (ι → K)} {f : ι → K}

/-- A function lies in the uniform closure of the span of `S` exactly when, for every `ε > 0`, some
element of the span is within `ε` of it at all points. -/
lemma mem_uniformClosure :
    f ∈ uniformClosure S ↔ ∀ ε > (0 : ℝ), ∃ g ∈ span K S, ∀ x : ι, ‖f x - g x‖ ≤ ε := by
  -- The closure in `UniformFun ι K`, read through the basis of entourages `‖a - b‖ ≤ ε`.
  simpa [dist_eq_norm] using!
    mem_closure_iff_nhds_basis (UniformFun.hasBasis_nhds_of_basis _ _ f uniformity_basis_dist_le)

/-- Approximation of a submonoid `N` of pairs `(t, φ)`, with `t` in `K` and `φ` a family indexed by
pairs `(η, i)` with `i < s η`. The set `N` is closed. As `η > 0` tends to `0`, the sum over `i` of
`c η i * φ (η, i)` tends to `t`, uniformly over `(t, φ) ∈ N`. -/
def IsApproximatingMonoid (s : Set.Ioi (0 : ℝ) → ℕ) (c : ∀ η : Set.Ioi (0 : ℝ), Fin (s η) → K)
    (N : Submonoid (K × ((Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K))) :
    Prop :=
  IsClosed N.carrier ∧
  TendstoUniformly (fun (η : Set.Ioi (0 : ℝ)) (p : N) ↦ ∑ i : Fin (s η), c η i * p.val.snd ⟨η, i⟩)
    (fun p : N ↦ p.val.fst) atBot

/-- The monoid `N` of an approximation `New.IsApproximatingMonoid s c N` is closed. -/
lemma IsApproximatingMonoid.isClosed_carrier {s : Set.Ioi (0 : ℝ) → ℕ}
    {c : (η : Set.Ioi (0 : ℝ)) → Fin (s η) → K}
    {N : Submonoid (K × ((η : Set.Ioi (0 : ℝ)) × Fin (s η) → K))}
    (h_apx : IsApproximatingMonoid s c N) : IsClosed N.carrier :=
  And.left h_apx

/-- In an approximation `New.IsApproximatingMonoid s c N`, the sum over `i` of
`c η i * p.val.snd (η, i)` tends to `p.val.fst` as `η > 0` tends to `0`, uniformly over `p ∈ N`. -/
lemma IsApproximatingMonoid.tendstoUniformly {s : Set.Ioi (0 : ℝ) → ℕ}
    {c : (η : Set.Ioi (0 : ℝ)) → Fin (s η) → K}
    {N : Submonoid (K × ((η : Set.Ioi (0 : ℝ)) × Fin (s η) → K))}
    (h_apx : IsApproximatingMonoid s c N) :
    TendstoUniformly (fun (η : Set.Ioi (0 : ℝ)) (p : N) ↦ ∑ i : Fin (s η), c η i * p.val.snd ⟨η, i⟩)
      (fun p : N ↦ p.val.fst) atBot :=
  And.right h_apx

/-- Let `S` be a set of functions `ι → K`, with `K` a normed field, and let `f ≠ 0` lie in the
closure of the `K`-span of `S` for uniform convergence. Then there exist `s : (η > 0) → ℕ`,
coefficients `c η i ∈ K`, a closed submonoid `N` of pairs `(t, φ)` (with `t ∈ K` and `φ` a family
indexed by pairs `(η, i)`, `i < s η`) such that `∑_i c η i * φ (η, i) → t` as `η → 0` uniformly on
`N`, and functions `y (η, i)` in `S`, with the following property. If a linear operator that does
not increase the sup norm has `f` as eigenfunction with eigenvalue `t` and each `y (η, i)` as
eigenfunction with eigenvalue `φ (η, i)`, then `(t, φ) ∈ N`. -/
lemma exists_isApproximatingMonoid_of_mem_uniformClosure (hf : f ≠ 0)
    (hf_mem : f ∈ uniformClosure S) :
    ∃ (s : Set.Ioi (0 : ℝ) → ℕ) (c : (η : Set.Ioi (0 : ℝ)) → Fin (s η) → K)
        (N : Submonoid (K × ((η : Set.Ioi (0 : ℝ)) × Fin (s η) → K))),
      IsApproximatingMonoid s c N ∧
      ∃ y : (Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → S,
        ∀ p : K × ((Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K),
        (∃ T : End K (ι → K),
          -- (a) `T` is a contraction for the supremum norm
          (∀ (g : ι → K) (r : ℝ), (∀ x : ι, ‖g x‖ ≤ r) → ∀ x : ι, ‖T g x‖ ≤ r) ∧
          -- (b) `f` and the `y i` are eigenvectors, with eigenvalues `p.fst` and `p.snd i`
          T f = p.fst • f ∧
          ∀ i : (η : Set.Ioi (0 : ℝ)) × Fin (s η), T (y i) = p.snd i • y i) →
        p ∈ N := by
  -- Normalise `f z = 1` and approximate `f` within `η` by a combination of vectors of `S`. A
  -- contraction `T` keeps the error `≤ η`; evaluating at `z` puts the eigenvalue at `f` within
  -- `η` of a combination of the other eigenvalues. The bound passes to the closure of the monoid
  -- `N` of such eigenvalue systems.
  obtain ⟨z, hz : f z ≠ 0⟩ := Function.ne_iff.mp hf
  have h_approx (η : Set.Ioi (0 : ℝ)) : ∃ (m : ℕ) (a : Fin m → K) (y : Fin m → S),
      ∀ w : ι, ‖((f z)⁻¹ • f - ∑ j, a j • (y j).val) w‖ ≤ η := by
    simpa [mem_span_set'] using mem_uniformClosure.1 (smul_mem _ (f z)⁻¹ hf_mem) η η.prop
  choose s a y hy using h_approx
  -- `N`: the eigenvalue systems of contractions with eigenvectors `f` and all `y η j`.
  let N : Submonoid (K × ((Σ η : Set.Ioi (0 : ℝ), Fin (s η)) → K)) :=
    { carrier := {p | ∃ T : End K (ι → K),
        (∀ (g : ι → K) (r : ℝ), (∀ x : ι, ‖g x‖ ≤ r) → ∀ x : ι, ‖T g x‖ ≤ r) ∧
        T f = p.fst • f ∧ ∀ i, T (y i.fst i.snd) = p.snd i • y i.fst i.snd}
      mul_mem' := by
        rintro p p' ⟨T, hT_le, hT_f, hT_y⟩ ⟨T', hT'_le, hT'_f, hT'_y⟩
        exact ⟨T' * T, fun g r hg x ↦ hT'_le _ _ (hT_le g r hg) x,
          by simp [hT_f, hT'_f, mul_smul], fun i ↦ by simp [hT_y, hT'_y, mul_smul]⟩
      one_mem' := ⟨1, by simp⟩ }
  -- Evaluating at `z` the image under `T` of the approximation of `f / f z`.
  have h_dist (η : Set.Ioi (0 : ℝ)) :
      ∀ p ∈ N, dist p.fst (∑ j, a η j * (y η j).val z * p.snd ⟨η, j⟩) ≤ η := by
    rintro p ⟨T, hT, hTf, hTy⟩
    have h_bound : ‖T ((f z)⁻¹ • f - ∑ j, a η j • (y η j).val) z‖ ≤ η := hT _ _ (hy η) z
    simpa [hTy ⟨η, _⟩, hTf, hz, ← dist_eq_norm, mul_comm, ← mul_assoc] using h_bound
  refine ⟨s, fun η j ↦ a η j * (y η j).val z, N.topologicalClosure,
    ⟨isClosed_closure, tendstoUniformly_iff.2 fun ε hε ↦ ?_⟩, fun i ↦ y i.fst i.snd,
    subset_closure⟩
  filter_upwards [eventually_lt_atBot (⟨ε, hε⟩ : Set.Ioi (0 : ℝ))] with η hη p
  exact (le_on_closure (h_dist η) (by fun_prop) (by fun_prop) p.prop).trans_lt hη

/-- Given `New.IsApproximatingMonoid s c N`, let `B` be a polynomial in the variables `ι`, and let
`f p x` be elements of `N`. Then the sum over `i` of `c η i` times the value of `B` at the `(η, i)`
components of the `f p x` tends to the value of `B` at their first components, uniformly in `p`. -/
lemma IsApproximatingMonoid.tendstoUniformly_eval {P : Type*} {s : Set.Ioi (0 : ℝ) → ℕ}
    {c : (η : Set.Ioi (0 : ℝ)) → Fin (s η) → K}
    {N : Submonoid (K × ((η : Set.Ioi (0 : ℝ)) × Fin (s η) → K))}
    (h_apx : IsApproximatingMonoid s c N) (B : MvPolynomial ι K) (f : P → ι → N) :
    TendstoUniformly
      (fun (η : Set.Ioi (0 : ℝ)) (p : P) ↦
        ∑ i : Fin (s η), c η i * B.eval fun x : ι ↦ (f p x).val.snd ⟨η, i⟩)
      (fun p : P ↦ B.eval fun x : ι ↦ (f p x).val.fst) atBot := by
  induction B using MvPolynomial.induction_on' with
  | monomial m a =>
    -- the monomial `m` is evaluated at a product of points of the monoid `N`; scale by `a`
    have h_prod : TendstoUniformly
        (fun (η : Set.Ioi (0 : ℝ)) (p : P) ↦
          ∑ i : Fin (s η), c η i * (m.prod fun x e ↦ f p x ^ e).val.snd ⟨η, i⟩)
        (fun p : P ↦ (m.prod fun x e ↦ f p x ^ e).val.fst) atBot :=
      h_apx.tendstoUniformly.comp fun p ↦ m.prod fun x e ↦ f p x ^ e
    simpa [mul_left_comm, eval_monomial, Finsupp.prod, Function.comp_def, Prod.snd_prod, mul_sum,
      Prod.fst_prod] using (uniformContinuous_mul_left' a).comp_tendstoUniformly h_prod
  | add B B' hB hB' => simpa [mul_add, sum_add_distrib, Pi.add_def] using hB.add hB'

/-- The polynomials `newtonPoly j m` over k in X_0, X_1, … are defined by `newtonPoly 0 m = 1` and
`newtonPoly (j + 1) m = X m * newtonPoly j 1 - j • newtonPoly j (m + 1)`. At the power sums,
`newtonPoly j 1` equals j! times the j-th elementary symmetric function. -/
noncomputable def newtonPoly : ℕ → ℕ → MvPolynomial ℕ k :=
  Nat.rec 1 fun j b m ↦ X m * b 1 - j • b (m + 1)

private lemma newtonPoly_zero (m : ℕ) : newtonPoly 0 m = (1 : MvPolynomial ℕ k) := rfl

/-- The recursion that defines `newtonPoly`. -/
private lemma newtonPoly_succ (j m : ℕ) :
    newtonPoly (j + 1) m = (X m * newtonPoly j 1 - j • newtonPoly j (m + 1) : MvPolynomial ℕ k) :=
  rfl

/-- The polynomials `newtonPoly j m` over `k` in variables X_0, X_1, … are defined by
`newtonPoly 0 m = 1` and `newtonPoly (j + 1) m = X m * newtonPoly j 1 - j • newtonPoly j (m + 1)`.
Newton's identities: for a multiset `s` in `k`, evaluating `newtonPoly j 1` at X_m ↦ ∑_{a ∈ s} a ^ m
(the power sums of `s`) gives `j!` times the `j`-th elementary symmetric function of `s`. -/
lemma eval_newtonPoly (s : Multiset k) :
    ∀ j : ℕ, eval (fun m : ℕ ↦ (s.map fun a : k ↦ a ^ m).sum) (newtonPoly j 1) =
      j.factorial * s.esymm j := by
  -- Newton's identities, by induction on `s`: `add_pow_eval` says how `newtonPoly` changes when a
  -- new element `a` adds `a ^ m` to each power sum `p m`.
  have add_pow_eval (a : k) (p : ℕ → k) (j m : ℕ) :
      eval (fun m ↦ a ^ m + p m) (newtonPoly (j + 1) m) =
        eval p (newtonPoly (j + 1) m) + j * a * eval p (newtonPoly j m) +
          a ^ m * eval p (newtonPoly j 1) := by
    induction j generalizing m with
    | zero => simp [newtonPoly_succ, newtonPoly_zero, add_comm]
    | succ j ih =>
      -- unfold `newtonPoly (j + 2) m` and apply `ih` at `1` and at `m + 1`
      simp only [newtonPoly_succ (j + 1), map_sub, map_mul, map_nsmul, eval_X, ih]
      -- unfold `newtonPoly (j + 1) m` from the right-hand side
      simp only [newtonPoly_succ j, map_sub, map_mul, eval_X, nsmul_eq_mul, map_natCast]
      push_cast
      ring
  have const_coeff (j m : ℕ) : (newtonPoly (j + 1) m).constantCoeff = (0 : k) := by
    induction j generalizing m <;> simp_all [newtonPoly_succ]
  intro j
  induction s using Multiset.induction generalizing j with
  | empty =>
    -- all power sums are zero, so only the constant coefficient is left
    cases j <;>
      simp [newtonPoly_zero, const_coeff, Multiset.powersetCard_zero_right, Multiset.esymm]
  | cons a s ih =>
    rcases j with _ | j
    · simp [newtonPoly_zero, Multiset.esymm]
    -- The power sums of `a ::ₘ s` are `a ^ m` plus those of `s`; `add_pow_eval` and `ih` expand
    -- the left side, and `esymm (j + 1)` of `a ::ₘ s` is `esymm (j + 1) + a * esymm j` of `s`.
    simp only [Multiset.map_cons, Multiset.sum_cons, add_pow_eval, ih]
    simp [Nat.factorial_succ, Multiset.sum_map_mul_left, Multiset.esymm, mul_assoc]
    ring

/-- Let `τ` be a linear form on a `k`-algebra `A` and `y : A` with `y ^ (m + 1) = l ^ m • y` for all
`m`. At the values `τ (y ^ i)`, the Newton polynomial `newtonPoly (j + 1) (m + 1)` takes the value
`l ^ m` times the product of `τ y - i * l` over `i ≤ j`. -/
private lemma eval_newtonPoly_eq_pow_mul_prod_of_pow_succ_eq_smul {A : Type*} [Ring A] [Algebra k A]
    (τ : A →ₗ[k] k) {l : k} {y : A} (hy : ∀ m : ℕ, y ^ (m + 1) = l ^ m • y) (j : ℕ) :
    ∀ m : ℕ, eval (fun i : ℕ ↦ τ (y ^ i)) (newtonPoly (j + 1) (m + 1)) =
      l ^ m * ∏ i ∈ range (j + 1), (τ y - i * l) := by
  induction j with
  | zero => simp [newtonPoly_succ, newtonPoly_zero, hy]
  | succ j ih =>
    intro m
    -- unfold one step: `X (m + 1) * newtonPoly (j + 1) 1 - (j + 1) • newtonPoly (j + 1) (m + 2)`;
    -- `ih` at `0` and at `m + 1` turns both into products
    rw [newtonPoly_succ (j + 1), map_sub, map_mul, map_nsmul, eval_X, ih 0, ih (m + 1), hy,
      map_smul, prod_range_succ _ (j + 1), smul_eq_mul, nsmul_eq_mul]
    ring

/-- Let `τ` be a linear form on a `k`-algebra `A` and `y : A` with `y ^ (m + 1) = l ^ m • y` for all
`m`. If the Newton polynomial `newtonPoly (d + 1) 1` vanishes at the values `τ (y ^ i)`, then
`τ y = j * l` for some natural number `j`. -/
private lemma exists_eq_nat_mul_of_eval_newtonPoly_eq_zero {A : Type*} [Ring A] [Algebra k A]
    (τ : A →ₗ[k] k) {l : k} {y : A} (hy : ∀ m : ℕ, y ^ (m + 1) = l ^ m • y) {d : ℕ}
    (h_zero : eval (fun i : ℕ ↦ τ (y ^ i)) (newtonPoly (d + 1) 1) = 0) :
    ∃ j : ℕ, τ y = j * l := by
  -- at `m = 0` the Newton polynomial is the product of the `τ y - i * l`, `i ≤ d`, so one vanishes
  have h_prod : ∏ i ∈ range (d + 1), (τ y - i * l) = 0 := by
    simpa using (eval_newtonPoly_eq_pow_mul_prod_of_pow_succ_eq_smul τ hy d 0).symm.trans h_zero
  obtain ⟨i, -, hi⟩ := prod_eq_zero_iff.mp h_prod
  exact ⟨i, sub_eq_zero.mp hi⟩

/-- More than `card n ^ 2` linear forms `A ↦ trace (M i * A)` on the `n × n` matrices over a
field are linearly dependent. -/
private lemma _root_.Matrix.not_linearIndependent_trace_mul_of_card_lt {k n N : Type*} [Field k]
    [Fintype n] [DecidableEq n] [Fintype N] (M : N → Matrix n n k)
    (h_card : Fintype.card n * Fintype.card n < Fintype.card N) :
    ¬LinearIndependent k fun (i : N) (A : Matrix n n k) ↦ (M i * A).trace := by
  intro h_ind
  -- the `M i` would be independent in a space of dimension `card n * card n`
  have h_le : Fintype.card N ≤ Module.finrank k (Matrix n n k) :=
    (LinearIndependent.of_comp (v := M) (pi fun A ↦ traceLinearMap n k k ∘ₗ mulRight k A)
      h_ind).fintype_card_le_finrank
  simp only [finrank_matrix, Module.finrank_self, mul_one] at h_le
  lia

/-- The linear form on `k[G]` that extends `T : G → k`. -/
private noncomputable def linearExtension (T : G → k) : k[G] →ₗ[k] k :=
  (aeval T).toLinearMap ∘ₗ Finsupp.lift _ k G X ∘ₗ (coeffLinearEquiv k).toLinearMap

/-- If `T : G → k` obeys every polynomial identity among traces of homomorphisms `G →* GL n k`, then
its linear extension to `k[G]` obeys every polynomial identity among traces of algebra maps
`k[G] →ₐ[k] Matrix n n k`. -/
private lemma eval_linearExtension_eq_zero {T : G → k}
    (h_identities : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL n k, eval (fun g : G ↦ (x g).val.trace) B = 0) → eval T B = 0)
    (B : MvPolynomial k[G] k)
    (hB : ∀ ρ : k[G] →ₐ[k] Matrix n n k, eval (fun x : k[G] ↦ (ρ x).trace) B = 0) :
    eval (linearExtension T) B = 0 := by
  -- Apply `h_identities` to `B` with each variable `X (∑ c g • g)` replaced by `∑ c g • X g`.
  refine (B.aeval_bind₁ T _).symm.trans (h_identities _ fun ρ ↦ (aeval_bind₁ ..).trans ?_)
  simpa [Finsupp.sum, lift_apply] using
    hB (MonoidAlgebra.lift k (Matrix n n k) G ((Units.coeHom (Matrix n n k)).comp ρ))

/-- The kernel of the pairing `(x, y) ↦ t (x * y)` on `k[G]`, for a linear form `t` with
`t (x * y) = t (y * x)`; this symmetry makes the kernel a left ideal. -/
private def pairingKernel (t : k[G] →ₗ[k] k) (t_comm : ∀ x y : k[G], t (x * y) = t (y * x)) :
    Ideal k[G] :=
  { toAddSubmonoid := ((mul k k[G]).compr₂ t).ker.toAddSubmonoid
    smul_mem' := fun a x hx ↦ by simp_all [t_comm a, DFunLike.ext_iff, mul_assoc] }

/-- Let `t` be a linear form on `k[G]` that obeys every polynomial identity among traces of algebra
maps `k[G] → Matrix n n k`. Then the quotient of `k[G]` by the kernel of the pairing `t (x * y)` is
finite-dimensional: for `card n ^ 2 + 1` elements `s i`, independent modulo the kernel, the forms
`y ↦ t (s i * y)` would be independent, but their minors `det (t (s i * b j))` are polynomial
identities among traces, and these vanish since the `ρ (s i)` are dependent in every `ρ`. -/
private lemma finite_quotient_pairingKernel (t : k[G] →ₗ[k] k)
    (t_comm : ∀ x y : k[G], t (x * y) = t (y * x)) [hI : (pairingKernel t t_comm).IsTwoSided]
    (h_alg : ∀ B : MvPolynomial k[G] k,
      (∀ ρ : k[G] →ₐ[k] Matrix n n k, eval (fun x : k[G] ↦ (ρ x).trace) B = 0) → eval t B = 0) :
    Module.Finite k (k[G] ⧸ pairingKernel t t_comm) := by
  let N : ℕ := Fintype.card n * Fintype.card n + 1
  refine rank_lt_aleph0_iff.mp (not_le.mp fun h_inf ↦ ?_)
  obtain ⟨s, hs⟩ : ∃ s : Fin N → k[G], LinearIndependent k (mk (pairingKernel t t_comm) ∘ s) :=
    mk_surjective.comp_left.exists.mp (le_rank_iff.mp (Cardinal.aleph0_le.mp h_inf N))
  have h_ltoFun : LinearMap.ker (ltoFun k k[G] k k) = ⊥ := by aesop
  have h_indep : LinearIndependent k fun (i : Fin N) (y : k[G]) ↦ t (s i * y) :=
    (hs.map' _ (ker_liftQ_eq_bot' _ _ rfl)).map' (ltoFun k k[G] k k) h_ltoFun
  have h_dep (ρ : k[G] →ₐ[k] Matrix n n k) :
      ¬LinearIndependent k fun (i : Fin N) (A : Matrix n n k) ↦ (ρ (s i) * A).trace :=
    Matrix.not_linearIndependent_trace_mul_of_card_lt _ (by simp [N])
  refine det_eval_eq_zero_iff_not_linearIndependent.mp (fun b ↦ ?_) h_indep
  -- the minor `det (t (s i * b j))` is `t` at a polynomial that vanishes on traces
  have h_det_zero : eval t (of fun i j ↦ X (s i * b j) : Matrix (Fin N) (Fin N) _)ᵀ.det = 0 := by
    refine h_alg _ fun ρ ↦ ?_
    simpa [det_apply, Function.flip_def] using det_eval_eq_zero_iff_not_linearIndependent.mpr
      (h_dep ρ) (ρ ∘ b)
  simpa [det_apply, Function.flip_def] using h_det_zero

/-- A weak form of the Procesi–Taylor theorem: over an algebraically closed field `k` of
characteristic `0`, a function `T : G → k` that satisfies every polynomial identity holding among
the traces of homomorphisms `G →* GL n k` is the trace of such a homomorphism `r` with
non-degenerate trace form (`New.IsTraceNondeg`). -/
lemma exists_rep_of_trace_identities [IsAlgClosed k] [CharZero k] {T : G → k}
    (h_identities : ∀ B : MvPolynomial G k,
      (∀ x : G →* GL n k, eval (fun g : G ↦ (x g).val.trace) B = 0) → eval T B = 0) :
    ∃ r : G →* GL n k, IsTraceNondeg (n := n) r ∧ ∀ g : G, (r g).val.trace = T g := by
  -- Extend `T` to a linear form `t` on `k[G]` and divide by the kernel `I` of the pairing
  -- `t (x * y)`. Identities of traces show that the quotient is finite-dimensional, has no
  -- nonzero ideal of square zero, and that `t` takes natural values on idempotents;
  -- Wedderburn's theorem then gives the representation.
  let t : k[G] →ₗ[k] k := linearExtension T
  have h_alg : ∀ B : MvPolynomial k[G] k,
      (∀ ρ : k[G] →ₐ[k] Matrix n n k, eval (fun x : k[G] ↦ (ρ x).trace) B = 0) → eval t B = 0 :=
    eval_linearExtension_eq_zero h_identities
  have t_comm (x y : k[G]) : t (x * y) = t (y * x) := by
    simpa [trace_mul_comm (m := n) (n := n), sub_eq_zero] using h_alg (X (x * y - y * x))
  let I : Ideal k[G] := pairingKernel t t_comm
  have hI_twoSided : I.IsTwoSided := ⟨by simp_all [I, pairingKernel, mul_assoc, DFunLike.ext_iff]⟩
  let τ : k[G] ⧸ I →ₗ[k] k := liftQ _ t fun x hx ↦ by simpa using LinearMap.congr_fun hx 1
  -- If `x ^ (m + 1) = l ^ m • x`, then `τ x ∈ ℕ l`: the Newton polynomial for the elementary
  -- symmetric function of degree `card n + 1` vanishes on traces, and here it equals
  -- `∏ (τ x - i * l)` over `i ≤ card n`.
  have τ_nat (l : k) (x : k[G] ⧸ I) (hx : ∀ m : ℕ, x ^ (m + 1) = l ^ m • x) :
      ∃ j : ℕ, τ x = j * l := by
    obtain ⟨x, rfl⟩ := mk_surjective (I := I) x
    have h_zero : eval t (rename (fun i : ℕ ↦ x ^ i) (newtonPoly (Fintype.card n + 1) 1)) = 0 := by
      refine h_alg _ fun ρ ↦ ?_
      -- at the traces of the powers of `ρ x` the Newton polynomial is `(card n + 1)!` times the
      -- elementary symmetric function of degree `card n + 1` of the `card n` eigenvalues: `0`
      simp [eval_rename, eval_newtonPoly, trace_pow_eq_sum_roots, card_roots_eq_natDegree,
        Function.comp_def, Multiset.esymm]
    rw [eval_rename] at h_zero
    exact exists_eq_nat_mul_of_eval_newtonPoly_eq_zero τ hx h_zero
  have h_finite : Module.Finite k (k[G] ⧸ I) :=
    finite_quotient_pairingKernel t t_comm h_alg (hI := hI_twoSided)
  -- If `x g x = 0` for all `g`, each `x g` has square zero, so `t (x g) = 0` (`τ_nat` with `l = 0`)
  -- and `x ∈ I`.
  let π : G →* k[G] ⧸ I := (mk I).toMonoidHom.comp (of k G)
  have h_semisimple (x : k[G] ⧸ I) (_hx_span : x ∈ span k (Set.range π))
      (hx : ∀ g : G, x * π g * x = 0) : x = 0 := by
    obtain ⟨x, rfl⟩ := mk_surjective (I := I) x
    refine eq_zero_iff_mem.mpr ?_
    ext g
    have h_sq (m : ℕ) : (mk I x * π g) ^ (m + 1) = (0 : k) ^ m • (mk I x * π g) := by
      cases m <;> simp_all [pow_succ', ← mul_assoc]
    obtain ⟨j, hj⟩ := τ_nat 0 (mk I x * π g) h_sq
    simpa [show τ (mk I x * π g) = t (x * .single g 1) from rfl] using hj
  -- Wedderburn: `π = F ∘ s`, where `s G` spans a product of matrix algebras and `F` is an algebra
  -- map from it to the quotient.
  obtain ⟨b, d, hd, s, F, -, hs_span, hF⟩ :=
    exists_wedderburn (k := k) π (.id G) h_semisimple ⟨by simp⟩
  -- On the product of matrix algebras `τ ∘ₗ F` is a trace, natural on the idempotents
  -- `piMatrixUnit i` (`τ_nat` with `l = 1`) and `card n` at `1`; so `exists_rep_of_trace` applies.
  have hτF_comm (x y : PiMatrix k d) :
      (τ ∘ₗ F.toLinearMap) (x * y) = (τ ∘ₗ F.toLinearMap) (y * x) := by
    simpa using (F x).ind₂ t_comm (F y)
  have hτF_nat (i : Fin b) : ∃ m : ℕ, (τ ∘ₗ F.toLinearMap) (piMatrixUnit i) = m := by
    simpa using τ_nat 1 (F (piMatrixUnit i)) fun m ↦ by
      simp [(isIdempotentElem_map_piMatrixUnit F i).pow_succ_eq]
  have hτF_one : (τ ∘ₗ F.toLinearMap) 1 = Fintype.card n := by
    -- the identity `X 1 - card n` holds among traces, as the trace of `1` is `card n`
    have h_one : eval t (X 1 - ∑ _ : n, 1) = 0 := h_alg _ fun ρ ↦ by simp
    simpa [show τ 1 = t 1 from rfl, sub_eq_zero] using h_one
  obtain ⟨r, hr, hr_trace⟩ :=
    exists_rep_of_trace (n := n) hs_span (τ ∘ₗ F.toLinearMap) hτF_comm hτF_nat hτF_one
  refine ⟨r, hr, fun g ↦ ?_⟩
  calc (r g).val.trace = τ (F (s g)) := hr_trace g
    _ = τ (π g) := congrArg τ (hF g)
    _ = t (.single g 1) := rfl
    _ = T g := by simp [t, linearExtension]

/-- A limit of traces is a trace. Let `N` be a closed submonoid of pairs `(t, φ)` on which
`∑ i, c η i * φ (η, i)` tends to `t` uniformly as `η → 0` (`IsApproximatingMonoid s c N`). For each
`g` let `F g` be a nontrivial filter on `N` along which `t` eventually lies in the complete set `L`
and each `φ x` tends to the trace of `r x g`, with each `r x` continuous. Then some continuous `R`,
whose trace form is non-degenerate on the span of its matrices, has `(tr (R g), (tr (r x g))_x) ∈ N`
for all `g`. -/
lemma GaloisRep.exists_continuous_isTraceNondeg_of_tendsto_trace [TopologicalSpace G]
    [IsTopologicalGroup G] [IsAlgClosed K]
    [CharZero K] {s : Set.Ioi (0 : ℝ) → ℕ} {c : (η : Set.Ioi (0 : ℝ)) → Fin (s η) → K}
    {N : Submonoid (K × ((η : Set.Ioi (0 : ℝ)) × Fin (s η) → K))}
    (h_apx : IsApproximatingMonoid s c N) (F : G → Filter N) [∀ g : G, (F g).NeBot] {L : Set K}
    (hL : IsComplete L) (h_mem : ∀ g : G, ∀ᶠ p : N in F g, p.val.fst ∈ L)
    {r : (η : Set.Ioi (0 : ℝ)) × Fin (s η) → G →* GL n K}
    (hr_cont : ∀ x : (η : Set.Ioi (0 : ℝ)) × Fin (s η), Continuous (r x))
    (h_tendsto : ∀ (g : G) (x : (η : Set.Ioi (0 : ℝ)) × Fin (s η)),
      (F g).Tendsto (fun p : N ↦ p.val.snd x) (nhds (r x g).val.trace)) :
    ∃ R : G →* GL n K,
      Continuous R ∧ IsTraceNondeg R ∧
      ∀ g : G,
        ((R g).val.trace, fun x : (η : Set.Ioi (0 : ℝ)) × Fin (s η) ↦ (r x g).val.trace) ∈ N := by
  -- Along `F g` the first components have a limit `T g`. The approximation passes to the limit,
  -- so `T` is continuous and obeys the trace identities: it is a trace.
  have fst_cauchy (g : G) : Cauchy ((F g).map fun p : N ↦ p.val.fst) := by
    -- For each `η` the approximating sums converge along `F g`: their differences tend to `0`.
    -- A uniform limit of such families is again Cauchy.
    have sum_diff (η : Set.Ioi (0 : ℝ)) :
        Tendsto (fun q : N × N ↦
            ∑ i, c η i * q.fst.val.snd ⟨η, i⟩ - ∑ i, c η i * q.snd.val.snd ⟨η, i⟩)
          (F g ×ˢ F g) (nhds 0) :=
      ((cauchy_map_iff_tendsto (F g) _).mp
        (tendsto_finsetSum _ fun i _ ↦ (h_tendsto g _).const_mul _).cauchy_map).right
    refine (cauchy_map_iff_tendsto (F g) fun p : N ↦ p.val.fst).mpr ⟨map_neBot, ?_⟩
    exact ((h_apx.tendstoUniformly.comp Prod.fst).sub
      (h_apx.tendstoUniformly.comp Prod.snd)).tendsto_of_eventually_tendsto
        (.of_forall sum_diff) tendsto_const_nhds
  have h_lim (g : G) : ∃ t : K, (F g).Tendsto (fun p : N ↦ p.val.fst) (nhds t) :=
    (hL _ (fst_cauchy g) (tendsto_principal.mpr (h_mem g))).imp fun _ ht ↦ ht.2
  choose T hT using h_lim
  -- The limit system at `g`, as a point of the closed monoid `N`.
  let point (g : G) : N := ⟨(T g, fun x ↦ (r x g).val.trace), h_apx.isClosed_carrier.mem_of_tendsto
    (.prodMk_nhds (hT g) (tendsto_pi_nhds.2 (h_tendsto g))) (by simp)⟩
  have T_cont : Continuous T := by
    have sum_cont (η : Set.Ioi (0 : ℝ)) :
        Continuous fun g : G ↦ ∑ i : Fin (s η), c η i * (r ⟨η, i⟩ g).val.trace := by fun_prop
    exact (h_apx.tendstoUniformly.comp point).continuous (.of_forall sum_cont)
  -- A polynomial `D` that vanishes on all traces vanishes on their limit `T`.
  have T_identities (D : MvPolynomial G K)
      (hD : ∀ x : G →* GL n K, eval (fun g : G ↦ (x g).val.trace) D = 0) : eval T D = 0 := by
    have h_lim : Tendsto (fun η : Set.Ioi (0 : ℝ) ↦
        ∑ i : Fin (s η), c η i * D.eval fun g : G ↦ (r ⟨η, i⟩ g).val.trace) atBot
          (nhds (D.eval T)) :=
      (h_apx.tendstoUniformly_eval D ![point]).tendsto_at 0
    simpa [hD, eq_comm] using h_lim
  obtain ⟨R, hR, trace_R⟩ := exists_rep_of_trace_identities T_identities
  obtain rfl : (fun g ↦ (R g).val.trace) = T := funext trace_R
  exact ⟨R, hR.continuous_of_trace T_cont, hR, fun g ↦ (point g).prop⟩

end New

end Pseudorepresentation

end
