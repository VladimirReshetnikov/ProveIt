import Lib.ClassField.Places.DecompositionCyclotomic

/-!
# Coker/ker indices and Tate's index formula for cyclic actions of prime order

For a map `f` of abelian groups, `New.cokerKerIndex f` is the rational number `#coker f / #ker f`.
`(l : End ℤ A)` denotes multiplication by the natural number `l` on `A`. The file gives counting
tools for this index and for equivariant maps into finite projective `𝔽_l[Δ]`-modules.

## Main definitions and results

* `New.cokerKerIndex`: the rational number `#coker f / #ker f`; it is `0` if either group is
  infinite, so `cokerKerIndex f ≠ 0` says that both are finite.
* `New.cokerKerIndex_natCast_eq_of_ne_zero`: the index of `l` is unchanged under maps with finite
  kernel and cokernel.
* `New.card_hom_lattice_eq_card_equivariant`: `A / torsion` and a finite `Δ`-set `Z` have equally
  many equivariant maps to a finite projective `𝔽_l[Δ]`-module. This needs `A` finitely generated,
  of rank at most `#Z`, and with an equivariant map `A → ℝ^Z` whose image spans `ℝ^Z`.
* `New.Tate.index_formula`: computes the index of the norm group in the fixed points of an
  automorphism `σ` with `σ ^ l = 1`, `l` prime, from the indices of multiplication by `l`. It
  assumes that the kernel of the norm is the image of `σ - 1`, and it takes the place of the
  Herbrand quotient.
* `New.tate_index_formula_norm`: `New.Tate.index_formula` for a Galois-stable subgroup `U` of `Lˣ`
  with `H¹(Gal(L/K), U) = 0`, where `L / K` is Galois of prime degree. The hypothesis `hH1` gives
  this vanishing through Hilbert's Theorem 90.

## Relation to the literature

Known; see `Lib.ClassField.GreenbergWiles.CocycleCounts` and
`Lib.ClassField.GaloisCohomology.KummerCyclicClasses` for sources.
-/

/-! ## The coker/ker index and equivariant maps from lattices to projective modules -/

namespace New

variable {l : ℕ}
  {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  (f : A →ₗ[ℤ] B) (g : B →ₗ[ℤ] C)

open Nat Function LinearMap Submodule Module Matrix AddSubgroup Representation MonoidAlgebra

attribute [local instance low] Fintype.ofFinite

/-- For a linear map f : A → B, the rational number #coker f / #ker f; it is 0 if either group
is infinite. -/
noncomputable def cokerKerIndex : ℚ := Nat.card (B ⧸ f.range) / Nat.card f.ker

/-- (a) The index of `g ∘ f` is `#coker g * ([B : I ⊔ N] / #(I ⊓ N)) / #ker f`, where
`I = f.range` and `N = g.ker`. (b) If one of the indices of `f` and `g` is nonzero, the index
of `g ∘ f` is their product. -/
lemma cokerKerIndex_comp :
    -- (a)
    cokerKerIndex (g ∘ₗ f) =
      g.range.cardQuot * ((f.range ⊔ g.ker).cardQuot / Nat.card (f.range ⊓ g.ker :)) /
        Nat.card f.ker ∧
    -- (b)
    (cokerKerIndex f ≠ 0 ∨ cokerKerIndex g ≠ 0 →
     cokerKerIndex (g ∘ₗ f) = cokerKerIndex f * cokerKerIndex g) := by
  -- Write `I = f.range`, `N = g.ker` and `t = [N : I ⊓ N] = [I ⊔ N : I]`. All four groups are
  -- counted by index towers; `t` occurs in `coker f` and in `ker g` and cancels if nonzero.
  set t : ℕ := f.range.toAddSubgroup.relIndex g.ker.toAddSubgroup with ht
  have ker_g : Nat.card g.ker = Nat.card (f.range ⊓ g.ker :) * t := by
    simpa [bot_inf_eq] using (relIndex_inf_mul_relIndex ⊥ f.range.toAddSubgroup
      g.ker.toAddSubgroup).symm
  have ker_comp : Nat.card (g ∘ₗ f).ker = Nat.card f.ker * Nat.card (f.range ⊓ g.ker :) := by
    simpa [relIndex_ker, AddSubgroup.map_comap_eq] using
      (relIndex_mul_relIndex ⊥ _ _ bot_le (f.toAddMonoidHom.ker_le_comap g.ker.toAddSubgroup)).symm
  have coker_f : f.range.cardQuot = t * (f.range ⊔ g.ker).cardQuot := by
    simp [ht, cardQuot, sup_toAddSubgroup,
      ← relIndex_mul_index (toAddSubgroup_mono (le_sup_left (b := g.ker)))]
  have coker_comp : (g ∘ₗ f).range.cardQuot = (f.range ⊔ g.ker).cardQuot * g.range.cardQuot := by
    simp [cardQuot, range_comp, sup_toAddSubgroup, index_map, map_toAddSubgroup]
    -- `↑g` and `g.toAddMonoidHom` are the same additive map only by unfolding the coercion.
    rfl
  simp only [cokerKerIndex, ← cardQuot_apply, ker_g, ker_comp, coker_f, coker_comp, Nat.cast_mul]
  constructor
  · ring
  · intro h_ne
    -- If `t = 0`, the formulas for `coker f` and `ker g` make both indices vanish.
    have t_ne : (t : ℚ) ≠ 0 := fun ht0 ↦ by simp [ht0] at h_ne
    field_simp

/-- For a short exact sequence `0 → A → B → C → 0` of abelian groups given by `f` and `g`, let
q_X = #(X/lX) / #X[l] be the rational cokernel-over-kernel index of multiplication by `l` on X,
taken to be 0 if either group is infinite. If q_A ≠ 0, meaning A/lA and A[l] are both finite, then
q_B = q_A · q_C. -/
lemma cokerKerIndex_mul_of_exact (hf : Function.Injective f) (h_exact : Exact f g)
    (hg : Surjective g) (hA : cokerKerIndex (l : End ℤ A) ≠ 0) :
    cokerKerIndex (l : End ℤ B) = cokerKerIndex (l : End ℤ A) * cokerKerIndex (l : End ℤ C) := by
  -- Multiplication by `l` on `B` factors through the range `X` of `ψ (b, a) = (l b - f a, g b)` as
  -- `B → X → B`. The first map has the index of `l` on `A`, the second that of `l` on `C`; both
  -- are read off from the exact sequence `A → B × A → B × C → C` by the first part of
  -- `cokerKerIndex_comp`.
  let ψ : B × A →ₗ[ℤ] B × C := (coprod (l : End ℤ B) (-f)).prod (g ∘ₗ fst ℤ B A)
  have exact_left : Exact (f.prod (l : End ℤ A)) ψ := by
    suffices h_iff : ∀ (b : B) (a : A),
        (l • b + -f a = 0 ∧ ∃ y : A, f y = b) ↔ ∃ y : A, f y = b ∧ l • f y = f a by
      simpa [Exact, ψ, h_exact _, ← hf.eq_iff] using h_iff
    grind
  have exact_right : Exact ψ (coprod (-g) (l : End ℤ C)) := by
    -- If `g b = l • g x`, then `l • x - b` lies in the range of `f`; take `b' = x`.
    have h_iff (b x : B) :
        -g b + l • g x = 0 ↔ ∃ b' : B, (∃ a : A, l • b' + -f a = b) ∧ g b' = g x := by
      grind [Exact, h_exact (l • x - b)]
    simpa [Exact, ψ, hg.forall] using h_iff
  let α : B →ₗ[ℤ] ψ.range := ψ.rangeRestrict ∘ₗ inl ℤ B A
  let β : ψ.range →ₗ[ℤ] B := fst ℤ B C ∘ₗ ψ.range.subtype
  have h_factor : (l : End ℤ B) = β ∘ₗ α := by aesop
  -- Write `l = snd ∘ (f, l)` on `A`: both indices compare `B × 0` with `ker ψ` inside `B × A`.
  have idx_α : cokerKerIndex (l : End ℤ A) = cokerKerIndex α := by
    rw [← snd_prod f (l : End ℤ A), (cokerKerIndex_comp (f.prod (l : End ℤ A)) (snd ℤ B A)).left,
      (cokerKerIndex_comp (inl ℤ B A) ψ.rangeRestrict).left]
    simp_all [exact_iff, range_inl, ← ker_eq_bot, sup_comm, inf_comm, bot_inf_eq]
  -- Write `l = coprod (-g) l ∘ inr` on `C`: both compare `0 × C` with `range ψ` in `B × C`.
  have idx_β : cokerKerIndex (l : End ℤ C) = cokerKerIndex β := by
    rw [← coprod_inr (-g) (l : End ℤ C),
      (cokerKerIndex_comp (inr ℤ B C) (coprod (-g) (l : End ℤ C))).left,
      (cokerKerIndex_comp ψ.range.subtype (fst ℤ B C)).left]
    simp_all [exact_iff, range_inr, ← range_eq_top, range_coprod, sup_comm, inf_comm]
  -- The index is multiplicative in `l = β ∘ α`, since `α` has nonzero index.
  rw [idx_α, idx_β, h_factor]
  exact (cokerKerIndex_comp α β).right (.inl (by rwa [← idx_α]))

/-- If `f : A → B` has finite kernel and cokernel, then `#(A/lA) / #A[l] = #(B/lB) / #B[l]`, each
side read as `0` when one of its groups is infinite. -/
lemma cokerKerIndex_natCast_eq_of_ne_zero (h : cokerKerIndex f ≠ 0) :
    cokerKerIndex (l : End ℤ A) = cokerKerIndex (l : End ℤ B) := by
  -- Take indices in `f ∘ l = l ∘ f` and cancel the nonzero index of `f`.
  have h_comm : f ∘ₗ (l : End ℤ A) = (l : End ℤ B) ∘ₗ f := by aesop
  apply mul_right_cancel₀ h
  calc cokerKerIndex (l : End ℤ A) * cokerKerIndex f
    _ = cokerKerIndex (f ∘ₗ (l : End ℤ A)) :=
      ((cokerKerIndex_comp (l : End ℤ A) f).right (.inr h)).symm
    _ = cokerKerIndex (l : End ℤ B) * cokerKerIndex f := by
      rw [h_comm, (cokerKerIndex_comp f (l : End ℤ B)).right (.inl h), mul_comm]

variable [NeZero l] [Module.Finite ℤ A]

/-- On a finitely generated abelian group `A`, multiplication by `l ≠ 0` has index
`#(A / l A) / #A[l] = l ^ rank A`. -/
lemma cokerKerIndex_natCast_eq_pow_finrank : cokerKerIndex (l : End ℤ A) = l ^ finrank ℤ A := by
  -- The torsion subgroup is finite, so we may pass to the free quotient `A ⧸ torsion ℤ A`, where
  -- multiplication by `l` is injective with image of index `l ^ rank`.
  have h_finite_torsion : Finite (torsion ℤ A) := finite_of_fg_torsion _ torsion_isTorsion
  have idx_ne : cokerKerIndex (torsion ℤ A).mkQ ≠ 0 := by
    simpa [cokerKerIndex] using (card_pos (α := torsion ℤ A)).ne'
  have ker_eq : ker (l : End ℤ (A ⧸ torsion ℤ A)) = ⊥ := by
    simp [ker_eq_bot', NeZero.ne, ← natCast_zsmul]
  have coker_card :
      Nat.card ((A ⧸ torsion ℤ A) ⧸ range (l : End ℤ (A ⧸ torsion ℤ A))) = l ^ finrank ℤ A :=
    (index_range_nsmul (M := A ⧸ torsion ℤ A) l).trans
      (by simp [finrank_quotient_eq_of_le_torsion])
  rw [cokerKerIndex_natCast_eq_of_ne_zero _ idx_ne, cokerKerIndex, ker_eq, coker_card]
  simp

/-- On a finitely generated abelian group `A`, multiplication by `l ≠ 0` has finite kernel and
cokernel: its index is nonzero. -/
lemma cokerKerIndex_natCast_ne_zero : cokerKerIndex (l : End ℤ A) ≠ 0 := by
  simp [cokerKerIndex_natCast_eq_pow_finrank, NeZero.ne]

/-- On a finitely generated abelian group `A`, multiplication by `l ≠ 0` has nonzero index
`#(A / l A) / #A[l] = l ^ rank A`: the two clauses are `New.cokerKerIndex_natCast_ne_zero` and
`New.cokerKerIndex_natCast_eq_pow_finrank`. -/
lemma cokerKerIndex_eq_pow_finrank :
    cokerKerIndex (l : End ℤ A) ≠ 0 ∧ cokerKerIndex (l : End ℤ A) = l ^ finrank ℤ A :=
  ⟨cokerKerIndex_natCast_ne_zero, cokerKerIndex_natCast_eq_pow_finrank⟩

variable (l)
  {Δ V Z : Type} [Group Δ] [Fintype Δ] [AddCommGroup V] [MulAction Δ Z] [Fact l.Prime]
  {σ : Representation ℤ Δ V} {τ : V →+ V}

omit [NeZero l] in
/-- Let `L` be a free `ℤ`-module of finite rank with basis `b` and `Δ`-action `ρ`, and `V` an
`𝔽_l`-space (`l` prime) with basis `c` and `Δ`-action `σ`. If `τ` satisfies
`∑ g, σ g ∘ τ ∘ σ g⁻¹ = id` (`hτ`), the averaging operator `π f = ∑ g, σ g ∘ τ ∘ f ∘ ρ g⁻¹` projects
`Hom(L, V)` onto the equivariant maps. So their number is `l ^ m`, with `m` the multiplicity of `1`
as a root modulo `l` of the characteristic polynomial of an integral lift of `π`, built from the
transposed matrices of `ρ g⁻¹` and integral lifts `T g` of the matrices of `σ g ∘ τ`. -/
lemma card_invariants_linHom (hτ : ∀ a : V, ∑ g : Δ, σ g (τ (σ g⁻¹ a)) = a) [Module (ZMod l) V]
    {ι κ L : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [AddCommGroup L]
    (c : Basis κ (ZMod l) V) {T : Δ → Matrix κ κ ℤ}
    (hT : ∀ (g : Δ) (i j : κ), T g i j = c.repr (σ g (τ (c j))) i) (b : Basis ι ℤ L)
    (ρ : Representation ℤ Δ L) :
    Nat.card (linHom ρ σ).invariants =
      Nat.card (ZMod l) ^
        ((∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).charpoly.map
            (algebraMap ℤ (ZMod l))).rootMultiplicity 1 := by
  -- The matrix of `π` in the basis `e` built from `b` and `c` is the integral lift modulo `l`.
  let π : (L →ₗ[ℤ] V) →ₗ[ZMod l] L →ₗ[ℤ] V :=
    ((∑ g, ρ.linHom σ g) ∘ₗ .compRight ℤ τ.toIntLinearMap).toAddMonoidHom.toZModLinearMap l
  let e : Basis (ι × κ) (ZMod l) (L →ₗ[ℤ] V) :=
    ((Pi.basis fun _ ↦ c).reindex (.sigmaEquivProd ι κ)).map (b.constr (ZMod l))
  have matrix_eq : (∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ (ZMod l)) =
      toMatrix e e π := by
    aesop (add simp Pi.single_apply) (add simp [Matrix.sum_apply, toMatrix_apply])
  have h_finite_hom : Module.Finite (ZMod l) (L →ₗ[ℤ] V) := Module.Finite.of_basis e
  have h_π_fixed (x : L →ₗ[ℤ] V) (hx : x ∈ (linHom ρ σ).invariants) : π x = x := by
    ext y
    simp_all [π, isIntertwiningMap_iff]
  have π_mem (x : L →ₗ[ℤ] V) : π x ∈ (linHom ρ σ).invariants := fun g ↦ self_norm_apply _ g _
  -- If `(π - 1) ^ (k + 1)` kills `x`, then `π x - x` is invariant by induction, hence so is `x`.
  have mem_of_pow (k : ℕ) (x : L →ₗ[ℤ] V)
      (hx : ((π - (1 : ZMod l) • 1 : End (ZMod l) (L →ₗ[ℤ] V)) ^ k) x = 0) :
      x ∈ (linHom ρ σ).invariants := by
    induction k generalizing x with
    | zero => simp_all
    | succ k ih =>
      simpa using sub_mem (π_mem x) (ih (π x - x) (by simpa [pow_succ] using hx))
  -- So the invariants are the generalised eigenspace of `π` for the eigenvalue `1`.
  rw [← charpoly_map, matrix_eq, π.charpoly_toMatrix, ← finrank_maxGenEigenspace_eq,
    ← natCard_eq_pow_finrank]
  congr! 3 with x
  rw [End.mem_maxGenEigenspace]
  exact ⟨fun hx ↦ ⟨1, by simp [h_π_fixed x hx]⟩, fun ⟨k, hk⟩ ↦ mem_of_pow k x hk⟩

omit [AddCommGroup V] [Fact l.Prime] in
/-- Let `Δ` act on the lattice `L` by `ρ` and suppose that some real basis `γ` of `Hom(L, ℝ)` is
permuted as `Δ` permutes `Z`. For integral matrices `T g`, the sum of the Kronecker products of
the transposed matrices of `ρ g⁻¹` with `T g` then has the same characteristic polynomial as the
same sum for the permutation representation on `ℤ[Z]`. -/
private lemma charpoly_sum_kronecker_eq_of_perm {ι κ L : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype Z] [DecidableEq Z] [AddCommGroup L] (b : Basis ι ℤ L)
    (ρ : Representation ℤ Δ L) (γ : Basis Z ℝ (L →ₗ[ℤ] ℝ))
    (hγ : ∀ (g : Δ) (z : Z), (ρ g⁻¹).lcomp ℝ ℝ (γ z) = γ (g • z)) (T : Δ → Matrix κ κ ℤ) :
    (∑ g : Δ, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).charpoly =
      (∑ g : Δ, (toMatrix (MonoidAlgebra.basis Z ℤ) (MonoidAlgebra.basis Z ℤ)
        (ofMulAction ℤ Δ Z g⁻¹))ᵀ.kronecker (T g)).charpoly := by
  -- Both are matrices of one real operator `Φ`, taking on the first tensor factor the basis dual
  -- to `b` or the basis `γ`.
  let Φ : Module.End ℝ (TensorProduct ℝ (L →ₗ[ℤ] ℝ) (κ → ℝ)) :=
    ∑ g, TensorProduct.map (lcomp ℝ ℝ (ρ g⁻¹)) (toLin' ((T g).map (algebraMap ℤ ℝ)))
  simp_rw [← (Polynomial.map_injective _ (algebraMap ℤ ℝ).injective_int).eq_iff, ← charpoly_map]
  let e_b := ((Pi.basisFun ℝ ι).map (b.constr ℝ)).tensorProduct (Pi.basisFun ℝ κ)
  let e_γ := γ.tensorProduct (Pi.basisFun ℝ κ)
  have h_mat_b : (∑ g, (toMatrix b b (ρ g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ ℝ) =
      toMatrix e_b e_b Φ := by
    ext ⟨⟩ ⟨⟩
    simp [e_b, Φ, Pi.single_apply, mul_comm, Matrix.sum_apply, toMatrix_apply]
  have h_mat_γ : (∑ g, (toMatrix (MonoidAlgebra.basis Z ℤ) (MonoidAlgebra.basis Z ℤ)
      (ofMulAction ℤ Δ Z g⁻¹))ᵀ.kronecker (T g)).map (algebraMap ℤ ℝ) = toMatrix e_γ e_γ Φ := by
    ext ⟨⟩ ⟨⟩
    simp [e_γ, Φ, mul_comm, hγ, basis, Finsupp.single_apply, eq_inv_smul_iff, eq_comm,
      Matrix.sum_apply, toMatrix_apply]
  have : Module.Finite ℝ (L →ₗ[ℤ] ℝ) := Module.Finite.of_basis γ
  rw [h_mat_b, h_mat_γ, Φ.charpoly_toMatrix, Φ.charpoly_toMatrix]

/-- Let the finite `𝔽_l[Δ]`-module `V` be projective in Higman's sense: some additive `τ` has
`∑ g, g τ g⁻¹ = 1`. Let `A` be a finitely generated `ℤ[Δ]`-module of rank at most `#Z` with real
linear forms `Λ z` that are linearly independent over `ℝ` and permuted by `Δ` as `Z` is. Then there
are as many equivariant maps `A → V` that kill torsion as equivariant maps `Z → V`. The proof lifts
the averaging projector to an integral matrix and reads its characteristic polynomial over `ℝ`. -/
lemma card_hom_lattice_eq_card_equivariant [Finite V] (hτ : ∀ a : V, ∑ g : Δ, σ g (τ (σ g⁻¹ a)) = a)
    [Module (ZMod l) V] {ρ : Representation ℤ Δ A} {Λ : Z → A →ₗ[ℤ] ℝ}
    (hΛ : ∀ (g : Δ) (z : Z) (y : A), Λ z (ρ g⁻¹ y) = Λ (g • z) y) (h_indep : LinearIndependent ℝ Λ)
    (h_rank : finrank ℤ A ≤ Nat.card Z) :
    Nat.card {f : IntertwiningMap ρ σ // torsion ℤ A ≤ ker f.toLinearMap} =
      Nat.card {F : Z → V // ∀ (g : Δ) (z : Z), F (g • z) = σ g (F z)} := by
  classical
  -- Both sides count invariants of `Hom(L, V)`, for `L = A / torsion` and for `L = ℤ[Z]`. The two
  -- integral matrices of `card_invariants_linHom` become conjugate over `ℝ`.
  let c := finBasis (ZMod l) V
  let T (g : Δ) : Matrix (Fin (finrank (ZMod l) V)) (Fin (finrank (ZMod l) V)) ℤ :=
    of fun i j ↦ (c.repr (σ g (τ (c j))) i).val
  have hT (g : Δ) (i j : Fin (finrank (ZMod l) V)) : T g i j = c.repr (σ g (τ (c j))) i := by
    simp [T]
  -- `ρ` keeps torsion, and the forms `Λ z` kill it, as `ℝ` has no torsion.
  have h_smul_zero (g : Δ) (x : A) : ∀ a : nonZeroDivisors ℤ, a • x = 0 → a • ρ g x = 0 := by
    simp_all [← map_smul]
  have h_torsion_ker (z : Z) : torsion ℤ A ≤ (Λ z).ker := by
    rintro y ⟨a, h_smul⟩
    simpa [Submonoid.smul_def] using congrArg (Λ z) h_smul
  let ρ' : Representation ℤ Δ (A ⧸ torsion ℤ A) :=
    ρ.quotient (torsion ℤ A) fun g x ↦ Exists.imp (h_smul_zero g x)
  -- So the forms `Λ z` descend to independent forms on `A / torsion`.
  let Λ' (z : Z) : A ⧸ torsion ℤ A →ₗ[ℤ] ℝ := liftQ _ (Λ z) (h_torsion_ker z)
  have indep : LinearIndependent ℝ Λ' := h_indep.of_comp (lcomp ℝ ℝ (mkQ _))
  have h_finite_Z : Finite Z := indep.finite
  -- By `h_rank` they are a basis `γ` of `Hom(A / torsion, ℝ)`, and `Δ` permutes it as it does `Z`.
  let γ : Basis Z ℝ (A ⧸ torsion ℤ A →ₗ[ℤ] ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank' Λ' indep (indep.fintype_card_le_finrank.antisymm
      (by simp_all [finrank_linearMap, finrank_quotient_eq_of_le_torsion]))
  have γ_perm (g : Δ) (z : Z) : (ρ' g⁻¹).lcomp ℝ ℝ (γ z) = γ (g • z) := by
    -- On the class of `y : A` both sides are `Λ z (ρ g⁻¹ y) = Λ (g • z) y`.
    ext y
    have h_ρ'_mk : ρ' g⁻¹ (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρ g⁻¹ y) := rfl
    simpa [γ, Λ', h_ρ'_mk] using hΛ g z y
  let b := finBasis ℤ (A ⧸ torsion ℤ A)
  let b₀ := MonoidAlgebra.basis Z ℤ
  let ρ₀ : Representation ℤ Δ (MonoidAlgebra ℤ Z) := ofMulAction ℤ Δ Z
  -- An equivariant map on `A` that kills the torsion is an equivariant map on `A / torsion`.
  let descend :
      {f : IntertwiningMap ρ σ // torsion ℤ A ≤ ker f.toLinearMap} ≃ IntertwiningMap ρ' σ :=
    { toFun f := ⟨liftQ (torsion ℤ A) f.val.toLinearMap f.property,
        fun g ↦ linearMap_qext _ (f.val.isIntertwining' g)⟩
      invFun x := ⟨x.comp ⟨mkQ (torsion ℤ A), fun _ ↦ rfl⟩, le_comap_mkQ _ x.toLinearMap.ker⟩ }
  calc
    _ = Nat.card (linHom ρ' σ).invariants :=
      card_congr (descend.trans (invariantsEquivIntertwiningMap ρ' σ).symm.toEquiv)
    _ = Nat.card (linHom ρ₀ σ).invariants := by
      rw [card_invariants_linHom l hτ c hT b, card_invariants_linHom l hτ c hT b₀,
        charpoly_sum_kronecker_eq_of_perm b ρ' γ γ_perm T]
    -- An equivariant map on `ℤ[Z]` is given by its values on the basis `Z`.
    _ = Nat.card {F : Z → V // ∀ (g : Δ) (z : Z), F (g • z) = σ g (F z)} := by
      refine card_congr ((b₀.constr ℕ).symm.subtypeEquiv fun F ↦ ?_)
      -- Invariance under every `g⁻¹`, read on the basis, is equivariance of the values.
      refine inv_surjective.forall.trans ?_
      simp [b₀, ρ₀, MonoidAlgebra.lhom_ext'_iff, LinearMap.ext_ring_iff, inv_apply_eq_iff]

end New

/-! ## Tate's index formula for a cyclic action of prime order -/

section TateIndex

open LinearMap Module End Polynomial Function GeneralLinearGroup IsCyclotomicExtension

set_option synthInstance.maxHeartbeats 200000 in
/-- Tate's index formula. Let `l` be prime, let `σ ^ l = 1` on `B`, let the sequence
`C → B → B → C` with maps `j`, `σ - 1`, `s` be exact with `j` injective, and let `s ∘ j = l`. So
`C` is the group of fixed points of `σ`, and `s` plays the role of the norm. With
`q_A = #(A/lA) / #A[l]` (`cokerKerIndex` of `l`) and `q_C ≠ 0`, one has
`[C : s B] ^ (l - 1) * q_B = q_C ^ l`. -/
lemma New.Tate.index_formula {B C : Type} [AddCommGroup B] [AddCommGroup C] (s : B →ₗ[ℤ] C)
    (j : C →ₗ[ℤ] B) {l : ℕ} [Fact l.Prime] (σ : End ℤ B) (hC : cokerKerIndex (l : End ℤ C) ≠ 0)
    (hσ : σ ^ l = 1) (hj : Function.Injective j) (exact_j : Exact j ⇑(σ - 1))
    (exact_s : Exact ⇑(σ - 1) s) (hsj : s ∘ₗ j = l) :
    s.range.cardQuot ^ (l - 1) * cokerKerIndex (l : End ℤ B) = cokerKerIndex (l : End ℤ C) ^ l := by
  -- Let `t` be `σ - 1` acting on `N = (σ - 1) B = ker s`. Then `q_C = [C : s B] * cokerKerIndex t`,
  -- and `q_N = cokerKerIndex t ^ (l - 1)` since `l` is `t ^ (l - 1)` times a unit on `N`; finally
  -- `q_B = q_C * q_N` along `0 → C → B → N → 0`.
  let N : Submodule ℤ B := (σ - 1).range
  let σN : End ℤ N := σ.restrict (show ∀ x ∈ N, σ x ∈ N by simp [N])
  let t : End ℤ N := (σ - 1).rangeRestrict ∘ₗ N.subtype
  obtain ⟨ζ, hζ⟩ : ∃ ζ : cycloField l, IsPrimitiveRoot ζ l := ⟨_, zeta_spec l ℚ _⟩
  -- `1 + σ + ⋯ + σ ^ (l - 1)` kills `N`, as its product with `σ - 1` is `σ ^ l - 1 = 0`. This is
  -- the minimal polynomial of `ζ`, so `N` is a `ℤ[ζ]`-module with `ζ` acting as `σ`.
  have minpoly_eq : cyclotomic l ℤ = minpoly ℤ hζ.toInteger := by
    rw [cyclotomic_eq_minpoly hζ Fin.pos', ← hζ.toInteger.minpoly_coe]
    exact congrArg (minpoly ℤ) hζ.coe_toInteger.symm
  have minpoly_kills : aeval σN (minpoly ℤ hζ.integralPowerBasis.gen) = 0 := by
    ext ⟨_, x, hx⟩
    simpa [σN, ← minpoly_eq, cyclotomic_prime, hσ, ← hx, pow_restrict _ _] using
      LinearMap.congr_fun (geom_sum_mul σ l) x
  -- In `ℤ[ζ]`, `l` is associated to `(ζ - 1) ^ (l - 1)`; transport this to `End ℤ N`.
  obtain ⟨u, hu⟩ : ∃ u : (End ℤ N)ˣ, t ^ (l - 1) * u = l := by
    rw [show t = σN - 1 by ext; simp [σN, t]]
    simpa [Associated, ← IsPrimitiveRoot.integralPowerBasis_gen] using
      (Rat.associated_zeta_sub_one_pow_prime _ hζ).map
        (hζ.integralPowerBasis.lift σN minpoly_kills)
  -- Both `cokerKerIndex (s ∘ₗ j)` and `cokerKerIndex t` unfold, by `cokerKerIndex_comp`, to the
  -- index of `ker (σ - 1) + N` in `B` over the order of `ker (σ - 1) ∩ N`; the first has the extra
  -- factor `[C : s B]`.
  have index_C : cokerKerIndex (l : End ℤ C) = s.range.cardQuot * cokerKerIndex t := by
    rw [← hsj, (cokerKerIndex_comp j s).left,
      (cokerKerIndex_comp N.subtype (σ - 1).rangeRestrict).left]
    simp_all [N, ker_eq_bot.mpr hj, exact_iff, sup_comm, inf_comm]
  have ht : cokerKerIndex t ≠ 0 := right_ne_zero_of_mul (by rwa [← index_C])
  -- The index is multiplicative once one factor is nonzero, and a unit has index `1`.
  have index_pow_mul (m : ℕ) : cokerKerIndex (t ^ m * (u : End ℤ N)) = cokerKerIndex t ^ m := by
    induction m with
    | zero =>
      have hu_eq : (u : End ℤ N) = (toLinearEquiv u).toLinearMap := rfl
      simp [cokerKerIndex, hu_eq]
    | succ m ih =>
      rw [pow_succ', mul_assoc, Module.End.mul_eq_comp,
        (cokerKerIndex_comp (t ^ m * (u : End ℤ N)) t).right (.inr ht), ih, pow_succ]
  have index_N : cokerKerIndex (l : End ℤ N) = cokerKerIndex t ^ (l - 1) := by
    rw [← hu, index_pow_mul]
  have index_B :
      cokerKerIndex (l : End ℤ B) = cokerKerIndex (l : End ℤ C) * cokerKerIndex (l : End ℤ N) :=
    cokerKerIndex_mul_of_exact j _ hj (by simp_all [exact_iff]) (σ - 1).surjective_rangeRestrict hC
  rw [index_B, index_N, mul_left_comm, ← mul_pow, ← index_C, mul_pow_sub_one NeZero.out]

end TateIndex

/-! ## Tate's index formula for the norm in an extension of prime degree -/

section TateNormIndex

open Module Algebra MonoidHom Units Set IsGalois groupCohomology

/-- Tate's index formula for the norm `N` of a Galois extension `L / K` of prime degree `l`.
Let `U ≤ Lˣ` be Galois-stable, `V = U ∩ Kˣ`, and suppose that every Galois-fixed class of
`Lˣ / U` comes from `Kˣ` (by Hilbert 90 this says `H¹(Gal(L/K), U) = 0`). With
`q_A = #(A / A ^ l) / #A[l]` and `q_V ≠ 0`, one has `[V : N U] ^ (l - 1) * q_U = q_V ^ l`. -/
lemma New.tate_index_formula_norm {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (l : ℕ) (hL : finrank K L = l) [Fact l.Prime]
    (U : Subgroup Lˣ) (V : Subgroup Kˣ) (hV : V = U.comap (Units.map (algebraMap K L)))
    (hU : ∀ g : Gal(L/K), ∀ y ∈ U, g • y ∈ U)
    (hH1 : ∀ z : Lˣ, (∀ g : Gal(L/K), g • z / z ∈ U) → ∃ x : Kˣ, x.map (algebraMap K L) / z ∈ U)
    (hqV : cokerKerIndex (l : End ℤ (Additive V)) ≠ 0) :
    (U.map (Units.map (Algebra.norm K))).relIndex V ^ (l - 1) *
        cokerKerIndex (l : End ℤ (Additive U)) =
      cokerKerIndex (l : End ℤ (Additive V)) ^ l := by
  -- Apply `Tate.index_formula` to `B = U`, `C = V` (written additively), a generator `g` of the
  -- Galois group, the inclusion `j : V → U` and the norm `N : U → V`.
  subst hL hV
  have cyc : IsCyclic Gal(L/K) := isCyclic_of_prime_card (card_aut_eq_finrank K L)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let σ : Gal(L/K) →* End ℤ (Additive U) :=
    unitsRep.subrepresentation U.toAddSubgroup.toIntSubmodule hU
  set V : Subgroup Kˣ := U.comap (map (algebraMap K L : K →* L))
  let val (v : Additive U) : L := (((Additive.toMul v : U) : Lˣ) : L)
  -- The norm of `y ∈ U` is the product of its conjugates, so it lies in `U ∩ Kˣ = V`.
  have norm_mem : ((Units.map (norm K : L →* K)).domRestrict U).range ≤ V := by
    rintro _ ⟨y, rfl⟩
    refine Subgroup.mem_comap.mpr <|
      mem_of_eq_of_mem ?_ (U.prod_mem (t := .univ) fun g _ ↦ hU g _ y.property)
    simp [Units.ext_iff, norm_eq_prod_automorphisms]
  -- The relative index is the index in `V` of the range of the norm `N : U → V`.
  rw [Subgroup.relIndex, ← domRestrict_range, subgroupOf_range_eq_of_le _ norm_mem]
  let N : U →* V := codRestrict _ V fun y ↦ norm_mem ⟨y, rfl⟩
  let j : V →* U := subgroupComap _ U
  have pow_eq_one : σ g ^ finrank K L = 1 := by simp [← card_aut_eq_finrank, ← map_pow]
  have j_inj : Function.Injective j.toAdditive.toIntLinearMap :=
    .restrictPreimage _ (map_injective (algebraMap K L).injective)
  -- An element of `U` is fixed by `g`, hence by the whole group, iff it comes from `K`.
  have exact_j : Function.Exact j.toAdditive.toIntLinearMap ⇑(σ g - 1) := by
    refine fun y ↦ sub_eq_zero.trans ⟨fun hy ↦ ?_, ?_⟩
    · -- `y` is fixed by `g`, hence by the whole group, so it comes from `Kˣ`.
      have h_fixed_g : g • val y = val y := congrArg val hy
      obtain ⟨x, hx⟩ := (DiscreteUnits.ofBase_bijective (Γ := Gal(L/K)) (K := K)).surjective
        ⟨((Additive.toMul y : U) : Lˣ),
          fun g' ↦ ext (smul_eq_self_of_mem_zpowers (hg g') h_fixed_g)⟩
      exact (range_restrictPreimage ..).ge ⟨x, Subtype.ext_iff.mp hx⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (ext (g.commutes _))
  -- The kernel of the norm on `U` consists of the `g • w / w` with `w ∈ U`.
  have exact_N : Function.Exact ⇑(σ g - 1) N.toAdditive.toIntLinearMap := by
    refine .of_comp_of_mem_range ?_ fun y hy ↦ ?_
    · -- `g • w` and `w` have the same norm
      ext x
      have h_σ_apply : val (σ g x) = g (val x) := rfl
      simp only [val] at h_σ_apply
      simp [N, field, h_σ_apply, norm_eq_of_algEquiv]
    · -- By Hilbert 90, `y = z / g z` with `z ∈ Lˣ`. So the class of `z` in `Lˣ / U` is fixed by
      -- `g`, hence by the whole group, and `hH1` gives `x ∈ Kˣ` with `w = x / z ∈ U`; then
      -- `g • w / w = z / g z = y`.
      have h_norm_one : Algebra.norm K (val y) = 1 :=
        congrArg (fun v : Additive V ↦ (((Additive.toMul v : V) : Kˣ) : K)) hy
      obtain ⟨z, hz⟩ : ∃ z : Lˣ, (z : L) / g z = val y :=
        exists_div_of_norm_eq_one hg (x := ((Additive.toMul y : U) : Lˣ)) h_norm_one
      let ρq : Representation ℤ Gal(L/K) (DiscreteUnits L ⧸ U.toAddSubgroup.toIntSubmodule) :=
        (unitsRep (Γ := Gal(L/K))).quotient U.toAddSubgroup.toIntSubmodule hU
      have fixed_g : ρq g ⟦.ofMul z⟧ = ⟦.ofMul z⟧ := by
        refine ((Submodule.Quotient.eq _).mpr (mem_of_eq_of_mem ?_ y.property)).symm
        ext
        simpa
      obtain ⟨x, hx⟩ : ∃ x : Kˣ, x.map (algebraMap K L) / z ∈ U :=
        hH1 z fun g' ↦ (Submodule.Quotient.eq _).mp
          ((ρq.mem_invariants_iff_of_forall_mem_zpowers g hg _).mpr fixed_g g')
      refine ⟨.ofMul ⟨_, hx⟩, Subtype.ext (Units.ext ?_)⟩
      -- With `a` the image of `x`, `(σ g - 1) w` is `g • w / w` in `Lˣ` for `w = a / z`.
      let w : Lˣ := x.map (algebraMap K L) / z
      show ((g • w / w : Lˣ) : L) = val y
      rw [← hz]
      simp [w, field]
  have norm_incl : N.toAdditive.toIntLinearMap ∘ₗ j.toAdditive.toIntLinearMap = finrank K L :=
    LinearMap.ext fun _ ↦ Subtype.ext (Units.ext (Algebra.norm_algebraMap _))
  exact Tate.index_formula N.toAdditive.toIntLinearMap j.toAdditive.toIntLinearMap (σ g) hqV
    pow_eq_one j_inj exact_j exact_N norm_incl

end TateNormIndex
