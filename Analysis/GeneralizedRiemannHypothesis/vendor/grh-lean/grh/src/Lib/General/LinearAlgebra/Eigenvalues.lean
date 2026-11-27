import Lib.General.Groups.CongruenceSubgroups

/-!
# Eigenvalues: traces of powers, common eigenvectors, Amitsur's theorem, Sylvester's law

This file collects linear algebra on eigenvalues and characteristic polynomials. It expresses traces
of powers and determinants such as `det (1 - c N)` through the roots of the characteristic
polynomial.

## Main definitions and results

* `New.exists_eigenvector_of_commute`: common eigenvectors of endomorphisms that preserve a
  finite-dimensional subspace `S` and commute on it, over an algebraically closed field.
* `New.exists_eigenvector_of_trace_mul_eq`: if twisted traces of a commuting family `A'` are
  proportional to traces of a commuting family `A`, a generalised eigensystem of `A` on which one
  operator has non-zero trace extends to an eigensystem of `A'` that is invariant under the twist.
* `New.amitsur_charpoly_mem_of_span` (Amitsur): for an algebra map to matrices, it suffices to check
  on a spanning set that the coefficients of the characteristic polynomials lie in the base ring.
  The proof works with det (1 - t ρ(w)) modulo a power of t and factors 1 - t ρ(w) step by step.
* `New.isConj_diagonal_of_isRoot_charpoly`: a complex square matrix whose characteristic polynomial
  vanishes at pairwise distinct numbers x_i, one for each index i, is conjugate to the diagonal
  matrix with entries x_i.
* `New.sylvester_law_of_inertia`: Sylvester's law of inertia for sign matrices.

## Relation to the literature

Known result: Amitsur's theorem that integral characteristic polynomials on a spanning set give them
on the whole algebra. It is a consequence of Amitsur's formula for the characteristic polynomial of
a sum of matrices. Source: S. A. Amitsur, On the characteristic polynomial of a sum of matrices,
Linear and Multilinear Algebra 8 (1980), no. 3, 177-182; G. Chenevier, The p-adic analytic space of
pseudocharacters of a profinite group and pseudorepresentations over arbitrary rings, LMS Lecture
Note Ser. 414 (2014), (1.5).
-/

/-! ## Traces of powers as power sums of eigenvalues -/

section PowerSums

open Matrix Polynomial IsAlgClosed

namespace New

variable {k n : Type*} [Field k] [IsAlgClosed k] [Fintype n] [DecidableEq n] (A : Matrix n n k)

/-- For a square matrix A over an algebraically closed field and a polynomial q, det q(−A) is
the product of q(−x) over the roots x of the characteristic polynomial of A, counted with
multiplicity. -/
lemma det_aeval_neg_eq_prod_roots (q : k[X]) :
    (aeval (-A) q).det = (A.charpoly.roots.map fun a : k ↦ q.eval (-a)).prod := by
  -- `q` is a product of constants and of factors `X + C a`; both sides are multiplicative in `q`.
  have hq : q ∈ Submonoid.closure ({C a | a : k} ∪ {X + C a | a : k}) := splits q
  refine Submonoid.closure_induction_left ?_ ?_ hq
  · simp
  · rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩) r - hr
    · -- A constant `a` contributes `a ^ card n` to both sides.
      simp [hr, card_roots_eq_natDegree, algebraMap]
    · -- `X + C a` contributes `det (a - A)`, the value at `a` of the characteristic polynomial.
      simp [hr, ← (splits _).eval_eq_prod_roots_of_monic, charpoly_monic, neg_add_eq_sub,
        eval_charpoly, algebraMap]

/-- Over an algebraically closed field, the trace of A^m is the sum of the m-th powers of the
roots of the characteristic polynomial of A, counted with multiplicity. -/
lemma trace_pow_eq_sum_roots (m : ℕ) :
    (A ^ m).trace = (A.charpoly.roots.map fun a : k ↦ a ^ m).sum := by
  -- The roots of the characteristic polynomial of `A ^ m` are the `m`-th powers of those of `A`.
  have h_charpoly :
      (A ^ m).charpoly = ((A.charpoly.roots.map (· ^ m)).map fun a ↦ X - C a).prod := by
    refine Polynomial.funext fun x ↦ ?_
    -- At `-A` the polynomial `C x - (-X) ^ m` is `x - A ^ m`; at `-a` it is `x - a ^ m`.
    have h_det := det_aeval_neg_eq_prod_roots A (C x - (-X) ^ m)
    simpa [eval_charpoly, eval_multiset_prod, algebraMap_eq_diagonal, Pi.algebraMap_def] using h_det
  rw [trace_eq_sum_roots_charpoly, h_charpoly, roots_multiset_prod_X_sub_C]

/-- Over an algebraically closed field of characteristic 0, if tr A^m = tr B^m + ∑_{e∈S} α_e^m
for all m ≥ 0, with S finite, then the characteristic polynomial of A is that of B times
∏_{e∈S} (X − α_e). -/
lemma charpoly_eq_mul_of_trace_pow_add [CharZero k] {r ι : Type*} [Fintype r] [DecidableEq r]
    {B : Matrix r r k} (S : Finset ι) (α : ι → k)
    (h_trace : ∀ m : ℕ, (A ^ m).trace = (B ^ m).trace + ∑ e ∈ S, α e ^ m) :
    A.charpoly = B.charpoly * ∏ e ∈ S, (X - C (α e)) := by
  classical
  -- The characters `m ↦ a ^ m` of `ℕ` are linearly independent (Dedekind), also over `ℕ`.
  have h_indep : LinearIndependent ℕ fun a : k ↦ ⇑(powersHom k a) :=
    ((linearIndependent_monoidHom _ k).comp _ (powersHom k).injective).restrict_scalars' ℕ
  -- Hence a multiset is determined by its power sums: read the multiplicities as coefficients.
  have eq_of_sum_pow (s t : Multiset k)
      (hst : ∀ m : ℕ, (s.map fun a ↦ a ^ m).sum = (t.map fun a ↦ a ^ m).sum) : s = t :=
    Multiset.toFinsupp.injective (h_indep (funext fun m ↦ by
      simpa [Finsupp.linearCombination, Finsupp.sum, Finset.sum_multiset_map_count] using
        hst m.toAdd))
  have h_roots : A.charpoly.roots = B.charpoly.roots + S.val.map α := by
    refine eq_of_sum_pow _ _ fun m ↦ ?_
    simpa [← trace_pow_eq_sum_roots, Multiset.map_map] using h_trace m
  -- A characteristic polynomial is monic and splits, so its roots determine its values.
  refine Polynomial.funext fun x ↦ ?_
  simp [eval_prod, (splits _).eval_eq_prod_roots_of_monic, charpoly_monic, h_roots]

end New

end PowerSums

/-- For a square matrix N over an algebraically closed field and a scalar c, det (1 − c N) is the
product of 1 − c x over the roots x of the characteristic polynomial of N, counted with
multiplicity. -/
lemma New.det_one_sub_smul_eq_prod_roots_of_isAlgClosed {k ι : Type*} [Field k] [IsAlgClosed k]
    [Fintype ι] [DecidableEq ι] (N : Matrix ι ι k) (c : k) :
    (1 - c • N).det = (N.charpoly.roots.map fun x : k ↦ 1 - c * x).prod := by
  -- Evaluate the polynomial `1 + c X` at `-N` and at `-x`.
  simpa [sub_eq_add_neg] using (det_aeval_neg_eq_prod_roots N (1 + c • Polynomial.X) :)

/-- For a complex square matrix N and a complex number c, det (1 − c N) is the product of 1 − c x
over the roots x of the characteristic polynomial of N, counted with multiplicity. -/
lemma New.det_one_sub_smul_eq_prod_roots {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℂ)
    (c : ℂ) :
    (1 - c • N).det = (N.charpoly.roots.map fun x : ℂ ↦ 1 - c * x).prod :=
  det_one_sub_smul_eq_prod_roots_of_isAlgClosed N c

/-! ## The trace of an idempotent matrix -/

/-- The trace of an idempotent matrix over a field is its rank. -/
lemma New.trace_eq_rank_of_isIdempotentElem {k n : Type*} [Field k] [Fintype n] [DecidableEq n]
    {p : Matrix n n k} (hp : IsIdempotentElem p) : p.trace = p.rank := by
  -- `p` is a projection, so its trace is the dimension of its range.
  rw [← p.trace_toLin'_eq]
  exact (LinearMap.IsIdempotentElem.isProj_range _ (hp.map Matrix.toLinAlgEquiv')).trace

/-! ## Sorting by adjacent swaps and common eigenvectors -/

section CommonEigenvectors

/-- Sorting by adjacent swaps: let `P` hold for some permutation, and pass from `σ` to `σ * (i j)`
whenever `j = i + 1` and `f (σ i) < f (σ j)`. Then `P σ` holds for some `σ` with `f ∘ σ`
non-increasing. -/
lemma New.exists_antitone_of_swap {α : Type*} {N : ℕ} [LinearOrder α] (f : Fin N → α)
    (P : Equiv.Perm (Fin N) → Prop) (h_exists : ∃ σ : Equiv.Perm (Fin N), P σ)
    (h_swap : ∀ (σ : Equiv.Perm (Fin N)) (i j : Fin N), i ⋖ j → f (σ i) < f (σ j) → P σ →
      P (σ * Equiv.swap i j)) :
    ∃ σ : Equiv.Perm (Fin N), P σ ∧ Antitone (f ∘ σ) := by
  -- Among the permutations with `P` take one for which `f ∘ σ` is lexicographically largest.
  obtain ⟨τ, hτ, τ_max⟩ : ∃ τ, P τ ∧ ∀ σ, P σ → toLex (f ∘ σ) ≤ toLex (f ∘ τ) :=
    Set.exists_max_image P _ Subtype.finite h_exists
  refine ⟨τ, hτ, (antitone_iff_forall_covBy _).2 fun i j hij ↦ le_of_not_gt fun hlt ↦ ?_⟩
  -- Swapping an increasing pair of neighbours `i`, `j` would give a larger one: the two agree
  -- before `i`.
  have larger : toLex (f ∘ τ) < toLex (f ∘ ⇑(τ * Equiv.swap i j)) :=
    ⟨i, fun r hr ↦ by simp [Equiv.swap_apply_of_ne_of_ne hr.ne (hr.trans hij.lt).ne],
      by simpa using hlt⟩
  exact (τ_max _ (h_swap τ i j hij hlt hτ)).not_gt larger

open Finsupp LieModule LieSubalgebra Module Submodule LinearMap

variable {k W : Type*} {ι : Sort*} [Field k] [IsAlgClosed k] [AddCommGroup W] [Module k W]
  (φ : ι → End k W) {S : Submodule k W} [Module.Finite k S]

/-- Let the endomorphisms `φ m` preserve the finite-dimensional subspace `S` and commute on it,
over an algebraically closed field, and let `U : Submodule k S` be proper. Then there are scalars
`χ m` whose joint generalised eigenspace in `S` is not contained in `U` and which are the
eigenvalues of a common non-zero eigenvector in `S`. -/
lemma New.exists_eigenvector_of_commute (hS : ∀ m : ι, ∀ x ∈ S, φ m x ∈ S)
    (h_comm : ∀ m n : ι, ∀ x ∈ S, φ m (φ n x) = φ n (φ m x)) {U : Submodule k S} (hU_ne : U ≠ ⊤) :
    ∃ χ : ι → k,
      -- (a) the joint generalised eigenspace of `χ` in `S` is not contained in `U`
      ¬(⨅ m : ι, End.maxGenEigenspace (restrict (φ m) (hS m)) (χ m) ≤ U) ∧
      -- (b) there is a common eigenvector with eigenvalues `χ`
      ∃ x ∈ S, x ≠ 0 ∧ ∀ m : ι, φ m x = χ m • x := by
  -- The restrictions of the `φ m` to `S` span an abelian Lie algebra `L` of endomorphisms, and `S`
  -- is the sum of its generalised weight spaces. One of them is not in `U`; take its weight.
  let : LieRing (End k S) := LieRing.ofAssociativeRing
  let L : LieSubalgebra k (End k S) := lieSpan k _ (Set.range fun m ↦ (φ m).restrict (hS m))
  -- `L` is abelian because its generators commute.
  have : IsLieAbelian L := isLieAbelian_lieSpan_iff.2 <| by
    rintro - ⟨m, rfl⟩ - ⟨n, rfl⟩
    exact sub_eq_zero.2 (LinearMap.ext fun x ↦ Subtype.ext (h_comm m n x x.property))
  obtain ⟨χ, hχ⟩ :
      ∃ χ : Weight k L S, ¬⨅ a : L, (genWeightSpaceOf S (χ a) a : Submodule k S) ≤ U := by
    by_contra! h_le
    refine hU_ne (eq_top_iff.2 ?_)
    rw [← LieSubmodule.top_toSubmodule (R := k) (L := L) (M := S),
      ← iSup_genWeightSpace_eq_top' k L S, LieSubmodule.iSup_toSubmodule]
    exact iSup_le fun χ ↦ by simpa [genWeightSpace] using h_le χ
  -- A weight of `L` has a weight vector `x`; evaluate the weight on the generators `f m` of `L`.
  let f (m : ι) : L := ⟨(φ m).restrict (hS m), subset_lieSpan ⟨m, rfl⟩⟩
  obtain ⟨x, hx, h_eigen⟩ := exists_forall_lie_eq_smul k L S χ
  refine ⟨fun m ↦ χ (f m), ?_, x, x.2, by simpa using hx, fun m ↦ ?_⟩
  · -- The generalised eigenspace of `f m` for `χ (f m)` is its generalised weight space.
    exact fun h_le ↦ hχ ((le_iInf_comp _ f).trans h_le)
  · -- The bracket of `f m` with `x` is the value of `φ m` at `x`.
    exact congrArg Subtype.val (h_eigen (f m))

/-- Let the `φ m` preserve the finite-dimensional subspace `S` and commute on it, over an
algebraically closed field. If a linear form `l`, non-zero on `S`, satisfies `l ∘ φ m = η m • l`,
then `S` contains a non-zero common eigenvector with eigenvalues `η m`. -/
lemma New.exists_eigenvector_of_functional (hS : ∀ m : ι, ∀ x ∈ S, φ m x ∈ S)
    (h_comm : ∀ m n : ι, ∀ x ∈ S, φ m (φ n x) = φ n (φ m x)) {η : ι → k} (l : W →ₗ[k] k)
    (hl_ne : ¬S ≤ l.ker) (hl : ∀ (m : ι) (x : W), l (φ m x) = η m * l x) :
    ∃ x ∈ S, x ≠ 0 ∧ ∀ m : ι, φ m x = η m • x := by
  -- Take a joint generalised eigenspace, of a character `χ`, on which `l` does not vanish.
  have ker_ne : l.ker.comap S.subtype ≠ ⊤ := by simpa using hl_ne
  obtain ⟨χ, not_le, eigenvector⟩ :
      ∃ χ : ι → k,
        ¬⨅ m, End.maxGenEigenspace (restrict (φ m) (hS m)) (χ m) ≤ l.ker.comap S.subtype ∧
        ∃ x ∈ S, x ≠ 0 ∧ ∀ m, φ m x = χ m • x :=
    exists_eigenvector_of_commute φ hS h_comm ker_ne
  suffices η_eq : η = χ by rwa [η_eq]
  refine funext fun m ↦ by_contra fun h_ne ↦ ?_
  -- As `l (ψ x) = (η m - χ m) * l x` for `ψ = φ m - χ m`, the form `l` kills every `ker (ψ ^ n)`.
  let ψ : End k S := restrict (φ m) (hS m) - χ m • 1
  have kills (n : ℕ) : ∀ x : S, (ψ ^ n) x = 0 → l x = 0 := by
    induction n with
    | zero => simp +contextual
    | succ n ih =>
      intro x hx
      have h_zero : l (ψ x) = 0 := ih (ψ x) (by simpa [pow_succ] using hx)
      simpa [ψ, sub_eq_zero, hl, h_ne] using h_zero
  refine not_le (iInf_le_of_le m fun x hx ↦ ?_)
  obtain ⟨n, hn⟩ := (End.mem_maxGenEigenspace _ _ _).1 hx
  exact kills n x hn

/-- Let Φ map words (lists of letters s) to endomorphisms of a finite-dimensional space over an
algebraically closed field, with Φ[s]Φ(L) = Φ(Ls). Suppose that the Φ[s] commute and have no
non-zero joint eigenvector with eigenvalues η_s. Then some finitely supported family of scalars
(c_L) has ∑ c_L ∏_{s∈L} η_s = 1 and ∑ c_L Φ(L) = 0. -/
lemma New.Variety.exists_words_comb_eq_zero [Module.Finite k W] {α : Type*}
    (Φ : List α → End k W) (mul_word : ∀ (s : α) (L : List α), Φ [s] * Φ L = Φ (L ++ [s]))
    (h_comm : ∀ s t : α, Commute (Φ [s]) (Φ [t])) {η : α → k}
    (no_eigen : ∀ x : W, (∀ s : α, Φ [s] x = η s • x) → x = 0) :
    ∃ f : List α →₀ k,
      f.sum (fun (L : List α) (a : k) ↦ a * (L.map η).prod) = 1 ∧
      f.sum (fun (L : List α) (a : k) ↦ a • Φ L) = 0 := by
  -- In the algebra `k × End k W` the pairs `(η s, Φ [s])` act by commuting multiplications on the
  -- span `S` of the pairs `w L` of all words, and the first coordinate is an eigenform for `η`.
  let w (L : List α) : k × End k W := ((L.map η).prod, Φ L)
  let S : Submodule k (k × End k W) := span k (Set.range w)
  let φ (s : α) : End k (k × End k W) := mulLeft k (η s, Φ [s])
  have stable (s : α) : ∀ y ∈ S, φ s y ∈ S :=
    mapsTo_span (Set.forall_mem_range.2 fun L ↦ ⟨L ++ [s], by simp [w, φ, mul_word, mul_comm]⟩)
  have comm (s t : α) : ∀ y ∈ S, φ s (φ t y) = φ t (φ s y) := by
    simp [φ, (h_comm _ _).left_comm, mul_left_comm]
  have not_le : ¬S ≤ (LinearMap.fst k k (End k W)).ker :=
    fun h_le ↦ one_ne_zero (h_le (subset_span ⟨[], rfl⟩))
  obtain ⟨⟨z, x⟩, mem, ne, eigen⟩ : ∃ y ∈ S, y ≠ 0 ∧ ∀ s : α, φ s y = η s • y :=
    exists_eigenvector_of_functional φ stable comm _ not_le fun _ _ ↦ rfl
  -- The values of `x` are joint eigenvectors for `η`, so `x = 0`; then `z ≠ 0` and `(1, 0) ∈ S`.
  have x_eigen (v : W) (s : α) : Φ [s] (x v) = η s • x v :=
    LinearMap.congr_fun (congrArg Prod.snd (eigen s)) v
  obtain rfl : x = 0 := LinearMap.ext fun v ↦ no_eigen _ (x_eigen v)
  have z_ne : z ≠ 0 := by simpa using ne
  have one_mem : (1, 0) ∈ S := by simpa [z_ne] using smul_mem S z⁻¹ mem
  -- So some combination of the `w L` is `(1, 0)`; read it off in the two coordinates.
  simpa [S, w, mem_span_range_iff_exists_finsupp, sum, ← prod_mk_sum] using one_mem

/-- A representation `ρ` of a commutative monoid over an algebraically closed field has a common
eigenvector in every non-zero finite-dimensional invariant subspace `S`, and its eigenvalues form
a character. -/
lemma New.exists_eigencharacter_of_ne_bot {M : Type*} [CommMonoid M] (ρ : M →* End k W)
    (hS : ∀ m : M, ∀ x ∈ S, ρ m x ∈ S) (hS_ne : S ≠ ⊥) :
    ∃ χ : M →* k, ∃ x ∈ S, x ≠ 0 ∧ ∀ m : M, ρ m x = χ m • x := by
  have comm (m n : M) : ∀ x ∈ S, ρ m (ρ n x) = ρ n (ρ m x) := by
    simp [← End.mul_apply, ← map_mul, mul_comm]
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS_ne
  obtain ⟨χ, -, x, x_mem, x_ne, eigen⟩ := exists_eigenvector_of_commute ρ hS comm bot_ne_top
  -- The eigenvalues are multiplicative, since scalars are determined by their action on `x ≠ 0`.
  have χ_mul (m n : M) : χ (m * n) = χ m * χ n := by
    simpa [smul_left_inj, x_ne, eigen, smul_smul, mul_comm, eq_comm] using eigen (m * n)
  exact ⟨{ toFun := χ, map_one' := (smul_left_inj x_ne).1 (by simp [← eigen]), map_mul' := χ_mul },
    x, x_mem, x_ne, eigen⟩

/-- The form of `New.exists_eigencharacter_of_ne_bot` for a subspace `S` that is not contained in
the zero subspace. -/
lemma New.exists_eigencharacter {M : Type*} [CommMonoid M] (ρ : M →* End k W)
    (hS : ∀ m : M, ∀ x ∈ S, ρ m x ∈ S) (hS_ne : ¬S ≤ ⊥) :
    ∃ χ : M →* k, ∃ x ∈ S, x ≠ 0 ∧ ∀ m : M, ρ m x = χ m • x :=
  exists_eigencharacter_of_ne_bot ρ hS (mt le_of_eq hS_ne)

end CommonEigenvectors

/-! ## Eigensystems from a twisted trace identity -/

section EigensystemTransfer
open Module End LinearMap Submodule

namespace New

variable {V V' I I' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/-- If `p ≠ ⊥` is finite dimensional, stable under `b` and contained in the generalised eigenspace
of `b` for `c ≠ 0`, then `b` has non-zero trace on `p`. -/
lemma trace_restrict_ne_zero {p : Submodule ℂ V} [FiniteDimensional ℂ p] {b : End ℂ V} {c : ℂ}
    (hc : c ≠ 0) (hp_ne : p ≠ ⊥) (hp_le : p ≤ maxGenEigenspace b c)
    (h_stable : ∀ x ∈ p, b x ∈ p) :
    trace ℂ p (restrict b h_stable) ≠ 0 := by
  -- `b - c` is nilpotent on `p`, so it has trace zero: the trace of `b` is `c * finrank ℂ p`.
  have h_nil : IsNilpotent (restrict b h_stable - c • 1) :=
    isNilpotent_iff_of_finite.2 fun v ↦ mem_genEigenspace_top.1
      ((genEigenspace_restrict b p ⊤ c h_stable).ge (hp_le v.2))
  have h_trace : trace ℂ p (restrict b h_stable) = c * finrank ℂ p := by
    simpa [sub_eq_zero] using isNilpotent_trace_of_isNilpotent h_nil
  simp [h_trace, hc, hp_ne]

/-- Generalised eigenspaces for different eigenvalues meet trivially: in a complex vector space
`V`, a vector killed by a power of `f - μ` that lies in the generalised eigenspace of `f` for
`ν ≠ μ` is zero. -/
lemma eq_zero_of_pow_apply_eq_zero_of_mem_maxGenEigenspace {f : End ℂ V} {μ ν : ℂ} (hne : μ ≠ ν)
    {N : ℕ} {v : V} (hμ : ((f - μ • 1) ^ N) v = 0) (hν : v ∈ maxGenEigenspace f ν) : v = 0 :=
  disjoint_def.1 (disjoint_genEigenspace f hne ⊤ ⊤) v ((mem_maxGenEigenspace f μ v).2 ⟨N, hμ⟩) hν

/-- If `s` intertwines `f` and `g`, that is `s * f = g * s`, and `u` commutes with `g`, then
`f * (u * s)` and `g * (u * s)` have the same trace. -/
lemma trace_mul_mul_eq_of_mul_eq_mul {f g s u : End ℂ V} (hs : s * f = g * s) (hu : Commute u g) :
    trace ℂ V (f * (u * s)) = trace ℂ V (g * (u * s)) := by
  rw [trace_mul_comm, mul_assoc, hs, ← mul_assoc, hu.eq, mul_assoc]

/-- Let `G a` be commuting elements of a complex algebra `R`, and let `S` be a finite-dimensional
subspace of `R` that is stable under left multiplication by the `G a`. If `τ` is a non-zero linear
form on `S`, then `τ z ≠ 0` for some joint generalised eigenvector `z ∈ S` of these
multiplications. -/
lemma exists_pow_sub_smul_mul_eq_zero_of_commute {R : Type*} {κ : Sort*} [Ring R] [Algebra ℂ R]
    {S : Submodule ℂ R} [FiniteDimensional ℂ S] {G : κ → R}
    (hG_comm : ∀ a a' : κ, Commute (G a) (G a')) (hG_maps : ∀ a : κ, ∀ z ∈ S, G a * z ∈ S)
    {τ : S →ₗ[ℂ] ℂ} (hτ : τ.ker ≠ ⊤) :
    ∃ (χ : κ → ℂ) (z : S), τ z ≠ 0 ∧ ∀ a : κ, ∃ N : ℕ, (G a - χ a • 1) ^ N * (z : R) = 0 := by
  let L (a : κ) : End ℂ R := Algebra.lmul ℂ R (G a)
  have hL_comm (a a' : κ) : ∀ z ∈ S, L a (L a' z) = L a' (L a z) :=
    fun z _ ↦ (hG_comm a a').left_comm z
  -- Some joint generalised eigenspace of the left multiplications is not in the kernel of `τ`.
  obtain ⟨χ, h_not_le⟩ : ∃ χ : κ → ℂ,
      ¬⨅ a : κ, maxGenEigenspace ((L a).restrict (hG_maps a)) (χ a) ≤ τ.ker :=
    (exists_eigenvector_of_commute L hG_maps hL_comm hτ).imp fun _ hχ ↦ hχ.left
  obtain ⟨z, hz, hτ_ne⟩ :
      ∃ z ∈ ⨅ a : κ, maxGenEigenspace ((L a).restrict (hG_maps a)) (χ a), τ z ≠ 0 :=
    IsConcreteLE.not_le_iff_exists.1 h_not_le
  refine ⟨χ, z, hτ_ne, fun a ↦ ?_⟩
  have h_mem : (z : R) ∈ maxGenEigenspace (L a) (χ a) :=
    (genEigenspace_restrict (L a) S ⊤ (χ a) (hG_maps a)).le ((mem_iInf _).1 hz a)
  obtain ⟨N, hN⟩ := (mem_maxGenEigenspace (L a) (χ a) z).1 h_mem
  refine ⟨N, ?_⟩
  -- The power of `L a - χ a` is multiplication by the power of `G a - χ a`.
  rwa [show L a = Algebra.lmul ℂ R (G a) from rfl, ← map_one (Algebra.lmul ℂ R), ← map_smul,
    ← map_sub, ← map_pow] at hN

/-- A commuting family `A'`, indexed by `I'`, of operators on a finite-dimensional complex space
`V'` has a common eigenvector in the range of any non-zero operator `f` that commutes with it. -/
lemma exists_eigenvector_mem_range_of_commute [FiniteDimensional ℂ V'] {A' : I' → End ℂ V'}
    (hA' : ∀ a b : I', Commute (A' a) (A' b)) {f : End ℂ V'} (hf : ∀ a : I', Commute f (A' a))
    (hf_ne : f ≠ 0) :
    ∃ (Θ : I' → ℂ) (v : V'), f v ≠ 0 ∧ ∀ a : I', A' a (f v) = Θ a • f v := by
  have : Nontrivial f.range := nontrivial_iff_ne_bot.2 (mt range_eq_bot.1 hf_ne)
  have h_stable (a : I') : ∀ u ∈ f.range, A' a u ∈ f.range :=
    Set.forall_mem_range.2 fun v ↦ ⟨A' a v, LinearMap.congr_fun (hf a).eq v⟩
  -- The `A' a` commute on the range of `f`, so they have a common eigenvector in it.
  obtain ⟨Θ, -, _, ⟨v, rfl⟩, hv, hΘ⟩ := exists_eigenvector_of_commute A' h_stable
    (fun a b u _ ↦ LinearMap.congr_fun (hA' a b).eq u) (U := ⊥) bot_ne_top
  exact ⟨Θ, v, hv, hΘ⟩

/-- An operator `g` that commutes with every `f a` preserves the joint generalised eigenspace of
the `f a` for any system of eigenvalues `θ`. -/
lemma apply_mem_iInf_maxGenEigenspace_of_commute {f : I → End ℂ V} {g : End ℂ V}
    (hg : ∀ a : I, Commute g (f a)) (θ : I → ℂ) (v : V)
    (hv : v ∈ ⨅ a : I, maxGenEigenspace (f a) (θ a)) :
    g v ∈ ⨅ a : I, maxGenEigenspace (f a) (θ a) :=
  (mem_iInf _).2 fun a ↦ mapsTo_maxGenEigenspace_of_comm (hg a).symm (θ a) ((mem_iInf _).1 hv a)

/-- Let the operators `f a` and `g` on `V` preserve a subspace `p`. If the restriction of `g` to `p`
commutes with those of the `f a`, then `g` preserves the part in `p` of the joint generalised
eigenspace of the `f a` for any system of eigenvalues `θ`. -/
lemma apply_mem_inf_iInf_maxGenEigenspace_of_commute_restrict {p : Submodule ℂ V}
    {f : I → End ℂ V} {g : End ℂ V} (hf_maps : ∀ a : I, ∀ v ∈ p, f a v ∈ p)
    (hg_maps : ∀ v ∈ p, g v ∈ p)
    (h_comm : ∀ a : I, Commute (g.restrict hg_maps) ((f a).restrict (hf_maps a))) (θ : I → ℂ)
    (v : V) (hv : v ∈ p ⊓ ⨅ a : I, maxGenEigenspace (f a) (θ a)) :
    g v ∈ p ⊓ ⨅ a : I, maxGenEigenspace (f a) (θ a) := by
  -- The space is the image in `V` of the joint generalised eigenspace of the restrictions.
  rw [inf_iInf_maxGenEigenspace_of_forall_mapsTo f p hf_maps] at hv ⊢
  obtain ⟨u, hu, rfl⟩ := hv
  exact ⟨g.restrict hg_maps u, apply_mem_iInf_maxGenEigenspace_of_commute h_comm θ u hu, rfl⟩

/-- Let the operators `f a` and `g` on `V` preserve a subspace `p`. Suppose that `g` preserves the
part in `p` of the joint generalised `θ`-eigenspace of the `f a` and has non-zero trace on it. Then
the restriction of `g` to `p` has non-zero trace on the joint generalised `θ`-eigenspace of the
restrictions of the `f a`. The hypothesis `h_stable_restrict` serves to state the conclusion; it is
equivalent to `h_stable`. -/
lemma trace_restrict_iInf_maxGenEigenspace_ne_zero {p : Submodule ℂ V} {f : I → End ℂ V}
    {g : End ℂ V} (hf_maps : ∀ a : I, ∀ v ∈ p, f a v ∈ p) (hg_maps : ∀ v ∈ p, g v ∈ p) (θ : I → ℂ)
    (h_stable : ∀ v ∈ p ⊓ ⨅ a : I, maxGenEigenspace (f a) (θ a),
      g v ∈ p ⊓ ⨅ a : I, maxGenEigenspace (f a) (θ a))
    (h_trace_ne :
      trace ℂ ↥(p ⊓ ⨅ a : I, maxGenEigenspace (f a) (θ a)) (g.restrict h_stable) ≠ 0)
    (h_stable_restrict : ∀ v ∈ ⨅ a : I, maxGenEigenspace ((f a).restrict (hf_maps a)) (θ a),
      g.restrict hg_maps v ∈ ⨅ a : I, maxGenEigenspace ((f a).restrict (hf_maps a)) (θ a)) :
    trace ℂ ↥(⨅ a : I, maxGenEigenspace ((f a).restrict (hf_maps a)) (θ a))
      ((g.restrict hg_maps).restrict h_stable_restrict) ≠ 0 := by
  -- The eigenspace in `V` is the image of `U`, on which `g` is conjugate to its restriction.
  let U : Submodule ℂ p := ⨅ a : I, maxGenEigenspace ((f a).restrict (hf_maps a)) (θ a)
  have h_image : p ⊓ ⨅ a : I, maxGenEigenspace (f a) (θ a) = U.map p.subtype :=
    inf_iInf_maxGenEigenspace_of_forall_mapsTo f p hf_maps
  let e : ↥(p ⊓ ⨅ a : I, maxGenEigenspace (f a) (θ a)) ≃ₗ[ℂ] U :=
    (LinearEquiv.ofEq _ _ h_image).trans (p.equivSubtypeMap U).symm
  have h_conj : e.conj (g.restrict h_stable) = (g.restrict hg_maps).restrict h_stable_restrict :=
    rfl
  rwa [← h_conj, trace_conj']

/-- For families `A` and `A'` of operators on spaces `W` and `W'`, the pairs `(x, y)` such that
`x` commutes with `A`, `y` with `A'`, and `tr (y * t.2 * s) = c * tr (x * t.1)` for all `t` in `Q`
whose second component commutes with `A'`. -/
def traceIdentityMultipliers {W W' : Type*} {J J' : Sort*} [AddCommGroup W] [Module ℂ W]
    [AddCommGroup W'] [Module ℂ W'] (A : J → End ℂ W) (A' : J' → End ℂ W') (s : End ℂ W') (c : ℂ)
    (Q : Set (End ℂ W × End ℂ W')) : Submodule ℂ (End ℂ W × End ℂ W') where
  carrier := {z : End ℂ W × End ℂ W' |
    (∀ a : J, Commute z.1 (A a)) ∧ (∀ a : J', Commute z.2 (A' a)) ∧
    ∀ t ∈ Q, (∀ a : J', Commute t.2 (A' a)) →
      trace ℂ W' (z.2 * t.2 * s) = c * trace ℂ W (z.1 * t.1)}
  zero_mem' := by simp
  add_mem' := fun ⟨hx, hy, htr⟩ ⟨hx', hy', htr'⟩ ↦
    ⟨fun a ↦ (hx a).add_left (hx' a), fun a ↦ (hy a).add_left (hy' a), fun t ht ht_comm ↦ by
      simp [add_mul, mul_add, htr t ht ht_comm, htr' t ht ht_comm]⟩
  smul_mem' := fun r _ ⟨hx, hy, htr⟩ ↦
    ⟨fun a ↦ (hx a).smul_left r, fun a ↦ (hy a).smul_left r, fun t ht ht_comm ↦ by
      simp [htr t ht ht_comm, mul_left_comm]⟩

section Multipliers

variable {W W' : Type*} {J J' : Sort*} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {A : J → End ℂ W} {A' : J' → End ℂ W'} {s : End ℂ W'} {c : ℂ} {Q : Set (End ℂ W × End ℂ W')}

/-- The multipliers of a trace identity are stable under left multiplication by a pair
`(A a, A' a')` that maps `Q` into itself, if each of the families `A`, `A'` commutes. -/
lemma mk_mul_mem_traceIdentityMultipliers (hA : ∀ a b : J, Commute (A a) (A b))
    (hA' : ∀ a b : J', Commute (A' a) (A' b)) {a : J} {a' : J'}
    (hQ : ∀ t ∈ Q, (A a, A' a') * t ∈ Q) {z : End ℂ W × End ℂ W'}
    (hz : z ∈ traceIdentityMultipliers A A' s c Q) :
    (A a, A' a') * z ∈ traceIdentityMultipliers A A' s c Q := by
  obtain ⟨hx, hy, htr⟩ := hz
  refine ⟨fun b ↦ (hA a b).mul_left (hx b), fun b ↦ (hA' a' b).mul_left (hy b),
    fun t ht ht_comm ↦ ?_⟩
  have h_shift : trace ℂ W' (z.2 * (A' a' * t.2) * s) = c * trace ℂ W (z.1 * (A a * t.1)) :=
    htr _ (hQ t ht) fun b ↦ (hA' a' b).mul_left (ht_comm b)
  change trace ℂ W' (A' a' * z.2 * t.2 * s) = c * trace ℂ W (A a * z.1 * t.1)
  rwa [← mul_assoc z.2, ← mul_assoc z.1, (hx a).eq, (hy a').eq] at h_shift

/-- If `s * A' a = A' a' * s` in a commuting family `A'`, the multipliers of a trace identity are
stable under left multiplication by `(0, A' a - A' a')`. -/
lemma zero_sub_mul_mem_traceIdentityMultipliers (hA' : ∀ a b : J', Commute (A' a) (A' b))
    {a a' : J'} (h_twist : s * A' a = A' a' * s) {z : End ℂ W × End ℂ W'}
    (hz : z ∈ traceIdentityMultipliers A A' s c Q) :
    ((0 : End ℂ W), A' a - A' a') * z ∈ traceIdentityMultipliers A A' s c Q := by
  obtain ⟨-, hy, -⟩ := hz
  refine ⟨by simp, fun b ↦ ((hA' a b).sub_left (hA' a' b)).mul_left (hy b),
    fun t _ ht_comm ↦ ?_⟩
  have h_cycle : trace ℂ W' (A' a * (z.2 * t.2 * s)) = trace ℂ W' (A' a' * (z.2 * t.2 * s)) :=
    trace_mul_mul_eq_of_mul_eq_mul h_twist ((hy a').mul_left (ht_comm a'))
  change trace ℂ W' ((A' a - A' a') * z.2 * t.2 * s) = c * trace ℂ W (0 * z.1 * t.1)
  simpa [sub_mul, mul_assoc, sub_eq_zero] using h_cycle

end Multipliers

/-- Let `G a` be operators on a finite-dimensional complex space `V'`. Suppose that the image of a
non-zero operator `f`, commuting with a commuting family `A'` indexed by a type `I'`, lies in the
generalised `χ a`-eigenspace of each `G a`. Then `A'` has a common eigenvector in that image, and
the only eigenvalue that `G a` can have at it is `χ a`. -/
lemma exists_eigenvector_and_forall_eigenvalue_eq [FiniteDimensional ℂ V'] {κ : Sort*}
    {A' : I' → End ℂ V'} (hA' : ∀ a a' : I', Commute (A' a) (A' a')) {f : End ℂ V'}
    (hf : ∀ a : I', Commute f (A' a)) (hf_ne : f ≠ 0) {G : κ → End ℂ V'} {χ : κ → ℂ}
    (h_range : ∀ (a : κ) (v : V'), f v ∈ maxGenEigenspace (G a) (χ a)) :
    ∃ (Θ : I' → ℂ) (v : V'), f v ≠ 0 ∧ (∀ a : I', A' a (f v) = Θ a • f v) ∧
      ∀ (a : κ) (z : ℂ), G a (f v) = z • f v → χ a = z := by
  obtain ⟨Θ, v, hv, hΘ⟩ := exists_eigenvector_mem_range_of_commute hA' hf hf_ne
  refine ⟨Θ, v, hv, hΘ, fun a z hz ↦ by_contra fun h_ne ↦ ?_⟩
  exact hv (disjoint_def.1 (disjoint_genEigenspace (G a) h_ne ⊤ ⊤) _ (h_range a v)
    (eigenspace_le_maxGenEigenspace (mem_eigenspace_iff.2 hz)))

/-- Let `A` and `A'` be commuting families of operators on finite-dimensional complex spaces `V`
and `V'`, and let `s` be an operator on `V'`. Suppose that `A b` has non-zero trace on the joint
generalised `θ`-eigenspace of the `A (k a)`. Let `Q` be a set of pairs of operators that contains
`(A b, A' i)` and is stable under left multiplication by the `(A (k a), A' (j a))`. Suppose that
`tr (t.2 * s) = c * tr t.1` for all `t` in `Q`, where `c ≠ 0`. Then `A'` has a common eigenvector in
the image of `A' i` whose system of eigenvalues `Θ` satisfies `Θ ∘ j = θ`, and `Θ a = Θ a'` whenever
`s * A' a = A' a' * s`. The hypothesis `h_stable` serves to state the trace hypothesis; it follows
from `hA` by `New.apply_mem_iInf_maxGenEigenspace_of_commute`. -/
lemma exists_eigenvector_of_trace_mul_eq [FiniteDimensional ℂ V] [FiniteDimensional ℂ V']
    {J : Sort*} {A : J → End ℂ V} {A' : I' → End ℂ V'} (hA : ∀ a a' : J, Commute (A a) (A a'))
    (hA' : ∀ a a' : I', Commute (A' a) (A' a')) (k : I → J) (j : I → I') (b : J) (i : I')
    (θ : I → ℂ)
    (h_stable : ∀ v ∈ ⨅ a : I, maxGenEigenspace (A (k a)) (θ a),
      A b v ∈ ⨅ a : I, maxGenEigenspace (A (k a)) (θ a))
    (h_trace_ne :
      trace ℂ ↥(⨅ a : I, maxGenEigenspace (A (k a)) (θ a)) ((A b).restrict h_stable) ≠ 0)
    {s : End ℂ V'} {c : ℂ} (hc : c ≠ 0) {Q : Set (End ℂ V × End ℂ V')} (hQ_mem : (A b, A' i) ∈ Q)
    (hQ_trace : ∀ t ∈ Q, trace ℂ V' (t.2 * s) = c * trace ℂ V t.1)
    (hQ_stable : ∀ t ∈ Q, ∀ a : I, (A (k a), A' (j a)) * t ∈ Q) :
    ∃ (Θ : I' → ℂ) (v w : V'), (∀ a a' : I', s * A' a = A' a' * s → Θ a = Θ a') ∧
      Θ ∘ j = θ ∧
      v = A' i w ∧ v ≠ 0 ∧ ∀ a : I', A' a v = Θ a • v := by
  -- The multipliers `(x, y)` of the trace identity form a space `S` on which commuting pairs `G a`
  -- act. A joint generalised eigenvector `(x, y)` with `tr (x * A b | U) ≠ 0` has `y * A' i ≠ 0`,
  -- and a common eigenvector of `A'` in the range of `y * A' i` has the required eigenvalues.
  -- `U` is the generalised `θ`-eigenspace of `A ∘ k`.
  let U : Submodule ℂ V := ⨅ a : I, maxGenEigenspace (A (k a)) (θ a)
  have hU {g : End ℂ V} (hg : ∀ a : J, Commute g (A a)) (v : V) (hv : v ∈ U) : (g * A b) v ∈ U :=
    apply_mem_iInf_maxGenEigenspace_of_commute (fun a ↦ (hg (k a)).mul_left (hA b (k a))) θ v hv
  let S : Submodule ℂ (End ℂ V × End ℂ V') := traceIdentityMultipliers A A' s c Q
  -- The commuting pairs: `(A (k a), A' (j a))`, and `(0, A' a - A' a')` if `s` intertwines the two.
  let κ : Type _ := I ⊕ {e : I' × I' // s * A' e.1 = A' e.2 * s}
  let G : κ → End ℂ V × End ℂ V' :=
    Sum.elim (fun a ↦ (A (k a), A' (j a))) fun ⟨(a, a'), _⟩ ↦ (0, A' a - A' a')
  have hG_comm : ∀ a a' : κ, Commute (G a) (G a') := by simp [κ, G, hA, hA', Prod.commute_iff]
  have hGS : ∀ a : κ, ∀ z ∈ S, G a * z ∈ S := by
    rintro (a | ⟨⟨a, a'⟩, h_twist⟩) z hz
    · exact mk_mul_mem_traceIdentityMultipliers hA hA' (fun t ht ↦ hQ_stable t ht a) hz
    · exact zero_sub_mul_mem_traceIdentityMultipliers hA' h_twist hz
  -- The form `τ (x, y) = tr (x * A b | U)` on `S` is not zero at `1`, by `h_trace_ne`.
  let ρ : S →ₗ[ℂ] End ℂ U :=
    { toFun := fun z ↦ ((z : End ℂ V × End ℂ V').1 * A b).restrict (hU z.property.left)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let τ : S →ₗ[ℂ] ℂ := trace ℂ U ∘ₗ ρ
  have one_mem : (1 : End ℂ V × End ℂ V') ∈ S :=
    ⟨fun _ ↦ .one_left _, fun _ ↦ .one_left _, fun t ht _ ↦ by simpa using hQ_trace t ht⟩
  have h_one : τ ⟨1, one_mem⟩ = trace ℂ U ((A b).restrict h_stable) := rfl
  have hτ : τ.ker ≠ ⊤ := fun h_top ↦
    h_trace_ne (h_one.symm.trans (LinearMap.congr_fun (ker_eq_top.1 h_top) ⟨1, one_mem⟩))
  -- A generalised eigenvector `(x, y) ∈ S` of multiplication by the `G a` with `τ (x, y) ≠ 0`.
  obtain ⟨χ, ⟨⟨x, y⟩, hx, hy, htr⟩, hτ_ne, h_nil⟩ : ∃ (χ : κ → ℂ) (z : S), τ z ≠ 0 ∧
      ∀ a : κ, ∃ N : ℕ, (G a - χ a • 1) ^ N * (z : End ℂ V × End ℂ V') = 0 :=
    exists_pow_sub_smul_mul_eq_zero_of_commute hG_comm hGS hτ
  choose N hN using h_nil
  have hN_fst (a : κ) (v : V) : (((G a).1 - χ a • 1) ^ N a) (x v) = 0 :=
    LinearMap.congr_fun (congrArg Prod.fst (hN a)) v
  have hN_snd (a : κ) (v : V') : (((G a).2 - χ a • 1) ^ N a) (y v) = 0 :=
    LinearMap.congr_fun (congrArg Prod.snd (hN a)) v
  -- The range of `x` is in the generalised `χ a`-eigenspace of `(G a).1`, and `x * A b` is a
  -- non-zero map of `U` to itself: so `χ` is `θ` on the first pairs and `0` on the others.
  have h_eig (v : U) (a : κ) : (x * A b) v ∈ maxGenEigenspace (G a).1 (Sum.elim θ 0 a) := by
    rcases a with a | e
    · exact (mem_iInf _).1 (hU hx v v.2) a
    · exact eigenspace_le_maxGenEigenspace (mem_eigenspace_iff.2 (by simp [G]))
  have hχ (a : κ) : χ a = Sum.elim θ 0 a := by
    by_contra h_ne
    have hzero (v : U) : (x * A b) v = 0 :=
      eq_zero_of_pow_apply_eq_zero_of_mem_maxGenEigenspace h_ne (hN_fst a (A b v)) (h_eig v a)
    have hρ : ρ ⟨(x, y), hx, hy, htr⟩ = 0 := ext fun v ↦ Subtype.ext (hzero v)
    exact hτ_ne (by simp [τ, hρ])
  obtain rfl : χ = Sum.elim θ 0 := funext hχ
  -- If `y * A' i = 0`, the identity at `(A b, A' i)` gives `tr (x * A b) = 0`; but `x * A b` has
  -- range in `U`, so this trace is `τ (x, y)`.
  have h_ne : y * A' i ≠ 0 := by
    intro hzero
    have h_identity : trace ℂ V' (y * A' i * s) = c * trace ℂ V (x * A b) := htr _ hQ_mem (hA' i)
    have htrace : trace ℂ V (x * A b) = 0 := by simpa [hzero, hc] using h_identity
    have h_range (v : V) : (x * A b) v ∈ U :=
      (mem_iInf _).2 fun a ↦
        (mem_maxGenEigenspace (A (k a)) (θ a) _).2 ⟨N (.inl a), hN_fst (.inl a) (A b v)⟩
    exact hτ_ne ((trace_restrict_eq_of_forall_mem U (x * A b) h_range).trans htrace)
  -- A common eigenvector of the `A' a` in the range of `y * A' i`. It lies in the range of `y`, so
  -- an eigenvalue of `(G a).2` on it is `Sum.elim θ 0 a`.
  obtain ⟨Θ, v, hv, hΘ, eigval_eq⟩ : ∃ (Θ : I' → ℂ) (v : V'),
      (y * A' i) v ≠ 0 ∧ (∀ a : I', A' a ((y * A' i) v) = Θ a • (y * A' i) v) ∧
      ∀ (a : κ) (z : ℂ), (G a).2 ((y * A' i) v) = z • (y * A' i) v → Sum.elim θ 0 a = z :=
    exists_eigenvector_and_forall_eigenvalue_eq hA' (fun a ↦ (hy a).mul_left (hA' i a)) h_ne
      fun a v ↦ (mem_maxGenEigenspace _ _ _).2 ⟨N a, hN_snd a (A' i v)⟩
  have h_invariant (a a' : I') (h_twist : s * A' a = A' a' * s) : Θ a = Θ a' := by
    have h_sub : (A' a - A' a') ((y * A' i) v) = (Θ a - Θ a') • (y * A' i) v := by
      rw [LinearMap.sub_apply, hΘ, hΘ, sub_smul]
    exact sub_eq_zero.1 (eigval_eq (.inr ⟨(a, a'), h_twist⟩) _ h_sub).symm
  have h_extends : Θ ∘ j = θ := funext fun a ↦ (eigval_eq (.inl a) (Θ (j a)) (hΘ (j a))).symm
  exact ⟨Θ, (y * A' i) v, y v, h_invariant, h_extends, LinearMap.congr_fun (hy i).eq v, hv, hΘ⟩

/-- The form of `New.exists_eigenvector_of_trace_mul_eq` for operators `B a` on a complex vector
space `V` that preserve a finite-dimensional subspace `p` and commute on it. Let `A'` be a commuting
family on a finite-dimensional space `V'` and `s` an operator on `V'`. Suppose that `B b` has
non-zero trace on the part in `p` of the joint generalised `θ`-eigenspace of the `B (k a)`. Let `Q`
be a set of pairs of operators on `p` and `V'` that contains `(B b | p, A' i)` and is stable under
left multiplication by the `(B (k a) | p, A' (j a))`. Suppose that `tr (t.2 * s) = c * tr t.1` for
all `t` in `Q`, where `c ≠ 0`. Then `A'` has a common eigenvector in the image of `A' i` whose
system of eigenvalues `Θ` satisfies `Θ ∘ j = θ`, and `Θ a = Θ a'` whenever `s * A' a = A' a' * s`.
The hypothesis `h_stable` serves to state the trace hypothesis; it follows from `hB_comm` by
`New.apply_mem_inf_iInf_maxGenEigenspace_of_commute_restrict`. -/
lemma exists_eigenvector_of_trace_identity {p : Submodule ℂ V} [FiniteDimensional ℂ p]
    [FiniteDimensional ℂ V'] {J : Sort*} {B : J → End ℂ V} {A' : I' → End ℂ V'}
    (hB_maps : ∀ a : J, ∀ v ∈ p, B a v ∈ p)
    (hB_comm : ∀ a a' : J, Commute ((B a).restrict (hB_maps a)) ((B a').restrict (hB_maps a')))
    (hA' : ∀ a a' : I', Commute (A' a) (A' a')) (k : I → J) (j : I → I') (b : J) (i : I')
    (θ : I → ℂ)
    (h_stable : ∀ v ∈ p ⊓ ⨅ a : I, maxGenEigenspace (B (k a)) (θ a),
      B b v ∈ p ⊓ ⨅ a : I, maxGenEigenspace (B (k a)) (θ a))
    (h_trace_ne :
      trace ℂ ↥(p ⊓ ⨅ a : I, maxGenEigenspace (B (k a)) (θ a)) ((B b).restrict h_stable) ≠ 0)
    {s : End ℂ V'} {c : ℂ} (hc : c ≠ 0) {Q : Set (End ℂ p × End ℂ V')}
    (hQ_mem : ((B b).restrict (hB_maps b), A' i) ∈ Q)
    (hQ_trace : ∀ t ∈ Q, trace ℂ V' (t.2 * s) = c * trace ℂ p t.1)
    (hQ_stable : ∀ t ∈ Q, ∀ a : I, ((B (k a)).restrict (hB_maps (k a)), A' (j a)) * t ∈ Q) :
    ∃ (Θ : I' → ℂ) (v w : V'), (∀ a a' : I', s * A' a = A' a' * s → Θ a = Θ a') ∧
      Θ ∘ j = θ ∧
      v = A' i w ∧ v ≠ 0 ∧ ∀ a : I', A' a v = Θ a • v := by
  -- Pass to the restrictions `A a` to `p` and their joint generalised `θ`-eigenspace `U`.
  let A (a : J) : End ℂ p := (B a).restrict (hB_maps a)
  let U : Submodule ℂ p := ⨅ a : I, maxGenEigenspace (A (k a)) (θ a)
  have hU_stable : ∀ v ∈ U, A b v ∈ U :=
    apply_mem_iInf_maxGenEigenspace_of_commute (fun a ↦ hB_comm b (k a)) θ
  exact exists_eigenvector_of_trace_mul_eq (A := A) hB_comm hA' k j b i θ hU_stable
    (trace_restrict_iInf_maxGenEigenspace_ne_zero (fun a ↦ hB_maps (k a)) (hB_maps b) θ h_stable
      h_trace_ne hU_stable) hc hQ_mem hQ_trace hQ_stable

end New

end EigensystemTransfer

/-!
## Amitsur's theorem on integral characteristic polynomials

Let ρ be a B-algebra map from a ring Λ to n × n matrices over a commutative B-algebra A. The
question is when the characteristic polynomials of the ρ(w) have coefficients in the image of B, the
range of `algebraMap B A`.
-/

namespace New

variable {B A n Λ : Type*} [CommRing B] [CommRing A] [Fintype n] [DecidableEq n] [Algebra B A]
  [Ring Λ] [Algebra B Λ] (ρ : Λ →ₐ[B] Matrix n n A)

open Polynomial Submodule AdjoinRoot Matrix Finset Fintype Algebra Function

/-- Let ρ be a B-algebra map from Λ to square matrices over a commutative B-algebra A. If all
characteristic polynomials of the ρ(w) have coefficients in the image of B, then for each w there
are F in B with det ρ(w) = F and v in Λ with ρ(v) ρ(w) = ρ(w) ρ(v) = F • 1.

This is a consequence of the Cayley–Hamilton theorem for ρ(w): when the characteristic polynomial
has coefficients from B, the determinant of ρ(w) is ρ(v) ρ(w) with v in Λ. -/
lemma exists_adjugate_of_charpoly_mem
    (h_coeff : ∀ (w : Λ) (k : ℕ), (ρ w).charpoly.coeff k ∈ (algebraMap B A).range) (w : Λ) :
    ∃ (v : Λ) (F : B), (ρ w).det = algebraMap B A F ∧ ρ v * ρ w = F • 1 ∧ ρ w * ρ v = F • 1 := by
  -- Let `Q` over `B` lift the characteristic polynomial of `ρ (-w)`, and write
  -- `Q = divX Q * X + C (Q.coeff 0)`. Then `Q.coeff 0` maps to `det (ρ w)`, and by Cayley–Hamilton
  -- `divX Q` at `-w` is the required adjugate.
  obtain ⟨Q, hQ⟩ : ∃ Q : B[X], Q.map (algebraMap B A) = (ρ (-w)).charpoly :=
    (lifts_iff_coeff_lifts _).2 (h_coeff (-w))
  let v : Λ := Q.divX.aeval (-w)
  have det_eq : (ρ w).det = algebraMap B A (Q.coeff 0) := by
    simpa [eval_charpoly, eval_map] using congrArg (Polynomial.eval 0) hQ.symm
  have cayley_hamilton : ρ v * ρ w = Q.coeff 0 • 1 := by
    have vanish : aeval (ρ (-w)) ((Q.divX * X + C (Q.coeff 0)).map (algebraMap B A)) = 0 := by
      rw [Q.divX_mul_X_add, hQ, aeval_self_charpoly]
    simpa [v, ← aeval_algHom_apply, neg_add_eq_zero, algebraMap_eq_smul_one] using vanish
  have comm : ρ w * ρ v = ρ v * ρ w := by
    simpa [v, ← aeval_algHom_apply] using congrArg (aeval (-ρ w)) (X_mul (p := Q.divX))
  exact ⟨v, Q.coeff 0, det_eq, cayley_hamilton, comm.trans cayley_hamilton⟩

/-- Amitsur's theorem. Let ρ be a B-algebra map from Λ to square matrices over a commutative
B-algebra A. If Λ is spanned over B by the elements s for which the characteristic polynomial of
ρ(s) has all coefficients in the image of B in A, then every w in Λ has this property. -/
lemma amitsur_charpoly_mem_of_span
    (hρ : span B {s : Λ | ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap B A).range} = ⊤) (w : Λ)
    (k : ℕ) : (ρ w).charpoly.coeff k ∈ (algebraMap B A).range := by
  -- Work modulo `t ^ e = 0` over `R = B[t]`, the image of `B[X]` in `A[X] / X ^ e`. By descending
  -- induction on `j`, adding `t ^ j • γ` to `β` keeps `det (1 - t • f β)` in `R`. So
  -- `det (1 - t • ρ w)`, the reversed characteristic polynomial at `t`, lies in `R`.
  -- The `k`-th coefficient sits in degree `e - 1` of the reversed polynomial.
  let e : ℕ := revAt (ρ w).charpoly.natDegree k + 1
  let R : Subalgebra B (AdjoinRoot (X ^ e : A[X])) := (aeval (root (X ^ e : A[X]))).range
  let t : R := ⟨aeval (root (X ^ e : A[X])) (X : B[X]), X, rfl⟩
  -- `f` is the extension of `ρ` to `R ⊗ Λ`.
  let f : TensorProduct B R Λ →ₐ[R] Matrix n n (AdjoinRoot (X ^ e : A[X])) :=
    ((ofAlgHom B (X ^ e : A[X])).mapMatrix.comp ρ).liftEquiv B R _ _
  have det_eq (s : Λ) (c : R) :
      det (1 - c • f (1 ⊗ₜ s)) = (ρ s).charpoly.reverse.aeval (c : AdjoinRoot (X ^ e : A[X])) := by
    simp [f, reverse_charpoly, charpolyRev, AlgHom.map_det, R.smul_def, map_sub, Matrix.map_smul',
      comp_def]
  let S : Set Λ := {s | ∀ k : ℕ, (ρ s).charpoly.coeff k ∈ (algebraMap B A).range}
  have det_mem (s : Λ) (hs : s ∈ S) (c : R) : det (1 - c • f (1 ⊗ₜ s)) ∈ R := by
    obtain ⟨y, hy⟩ : ∃ y : B[X], y.map (algebraMap B A) = (ρ s).charpoly :=
      (lifts_iff_coeff_lifts _).2 hs
    simp [det_eq, reverse, ← hy, reflect_map]
  -- The tensors `1 ⊗ₜ s`, `s ∈ S`, span `R ⊗ Λ` over `R`.
  have mem_span (γ : TensorProduct B R Λ) : γ ∈ span R (TensorProduct.mk B R Λ 1 '' S) := by
    simp [← baseChange_span, show span B S = ⊤ from hρ]
  have stable (j : ℕ) (hj : j ≤ e) (γ β : TensorProduct B R Λ) :
      det (1 - t • f β) ∈ R → det (1 - t • f (β + t ^ j • γ)) ∈ R := by
    induction hj using Nat.decreasingInduction generalizing γ β with
    | self =>
      have t_pow : t ^ e = 0 := Subtype.ext (by simp [t, ← mk_X, ← map_pow])
      simp [t_pow]
    | of_succ j _ ih =>
      induction mem_span γ using closure_induction generalizing β with
      | zero => simp
      | add γ γ' _ _ ih_γ ih_γ' =>
        intro hβ
        simpa [smul_add, ← add_assoc] using ih_γ' _ (ih_γ β hβ)
      | smul_mem c x hx =>
        obtain ⟨s, hs, rfl⟩ := hx
        intro hβ
        -- Multiplying by `1 - t ^ (j + 1) • c • s` adds `t ^ j • c • s` to `β`, up to the error
        -- `t ^ (j + 1) • δ`, which the induction hypothesis removes.
        let δ : TensorProduct B R Λ := c • β * 1 ⊗ₜ s
        let β' : TensorProduct B R Λ := β + t ^ j • c • (1 : R) ⊗ₜ[B] s - t ^ (j + 1) • δ
        have factor : 1 - t • f β' = (1 - t • f β) * (1 - (t ^ (j + 1) * c) • f (1 ⊗ₜ s)) := by
          simp only [β', δ, map_sub, map_add, map_smul, map_mul, sub_mul, mul_sub, mul_one, one_mul,
            smul_mul_assoc, mul_smul_comm]
          module
        have h_mem : det (1 - t • f β') ∈ R := by
          rw [factor, det_mul]
          exact mul_mem hβ (det_mem s hs _)
        simpa [β'] using ih δ β' h_mem
  -- The case `j = 0`, `β = 0`: `det (1 - t • ρ w)` is the value at `t` of some `q : B[X]`.
  obtain ⟨q, hq⟩ : det (1 - t • f (0 + t ^ 0 • (1 : R) ⊗ₜ[B] w)) ∈ R :=
    stable 0 e.zero_le (1 ⊗ₜ w) 0 (by simp)
  -- `q` agrees with the reversed characteristic polynomial in all degrees below `e`.
  have h_agree : ∀ d < e,
      algebraMap B A (q.coeff d) = (ρ w).charpoly.coeff (revAt (ρ w).charpoly.natDegree d) := by
    simpa [aeval_eq_of_algebra, det_eq, t, X_pow_dvd_iff, sub_eq_zero, coeff_reverse] using hq
  exact ⟨q.coeff (e - 1), by simpa [e] using h_agree (e - 1) (Nat.lt_succ_self _)⟩

/-- Scaling a square matrix of size `card n` by `a` multiplies the `k`-th coefficient of its
characteristic polynomial by `a ^ (card n - k)`. -/
lemma charpoly_smul_coeff (a : A) (M : Matrix n n A) (k : ℕ) :
    (a • M).charpoly.coeff k = a ^ (Fintype.card n - k) * M.charpoly.coeff k := by
  nontriviality A
  by_cases! h : card n < k
  · simp [coeff_eq_zero_of_natDegree_lt, h]
  -- The coefficient is a signed sum of principal minors of size `card n - k`.
  obtain ⟨m, hm, rfl⟩ : ∃ m ≤ card n, k = card n - m := ⟨card n - k, by omega, by omega⟩
  have h_minor (s : Finset n) (hs : s ∈ univ.powersetCard m) :
      ((a • M).submatrix (Subtype.val : s → n) Subtype.val).det =
        a ^ m * (M.submatrix (Subtype.val : s → n) Subtype.val).det := by
    simp [submatrix_smul, (mem_powersetCard.1 hs).2]
  rw [charpoly_coeff_eq_sum_minors _ _ hm, charpoly_coeff_eq_sum_minors _ _ hm,
    sum_congr rfl h_minor, ← mul_sum, Nat.sub_sub_self hm, mul_left_comm]

end New

/-!
## Diagonalisation and Sylvester's law of inertia

Linear algebra over ℂ for square matrices indexed by a finite type n.
-/

section SylvesterInertia

open Matrix Equiv Int Finset ComplexOrder Module.End

namespace New

variable {n : Type*} [Fintype n] [DecidableEq n] {g h : Matrix n n ℂ}

/-- If the characteristic polynomial of a complex square matrix g vanishes at pairwise distinct
numbers x_i, one for each row index i, then g is conjugate by an invertible matrix to the
diagonal matrix with entries x_i. -/
lemma isConj_diagonal_of_isRoot_charpoly {x : n ↪ ℂ} (hg : ∀ i : n, g.charpoly.IsRoot (x i)) :
    IsConj (diagonal x) g := by
  -- Each root is an eigenvalue. Eigenvectors for the distinct roots are independent; they are the
  -- columns of the conjugating matrix.
  have h_eig (i : n) : HasEigenvalue (toLin' g) (x i) := by
    simpa [hasEigenvalue_iff_isRoot_charpoly] using hg i
  choose v hv using fun i : n ↦ (h_eig i).exists_hasEigenvector
  have h_unit : IsUnit (of v)ᵀ :=
    linearIndependent_col_iff_isUnit.1 (eigenvectors_linearIndependent' _ x x.injective v hv)
  have h_conj : (of v)ᵀ * diagonal x = g * (of v)ᵀ := by
    ext i j
    have h_col : (g *ᵥ v j) i = (x j • v j) i := congrFun (hv j).apply_eq_smul i
    simpa [Matrix.mul_apply, mulVec, dotProduct, mul_comm, diagonal_apply] using h_col.symm
  exact ⟨h_unit.unit, by rwa [SemiconjBy, h_unit.unit_spec]⟩

/-- Sylvester's law of inertia: if hᴴ diag(s) h = diag(t) for families of signs s, t and a complex
square matrix h, then some permutation τ has s_{τ(j)} = t_j for all j. Here `signMatrix s` is the
diagonal matrix diag(s). -/
lemma sylvester_law_of_inertia {s t : n → ℤˣ} (h_form : hᴴ * signMatrix s * h = signMatrix t) :
    ∃ τ : Perm n, ∀ j : n, s (τ j) = t j := by
  -- With `S`, `T` the sign matrices, `hᴴ h + 1 = hᴴ (h + S h T)` is positive definite. The entry
  -- `(i, j)` of `h + S h T` vanishes if `s i ≠ t j`, so without such a `τ` every term of its
  -- determinant is zero.
  by_contra! h_none
  have h_factor : hᴴ * h + 1 = hᴴ * (h + signMatrix s * h * signMatrix t) := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, h_form, signMatrix_mul_self]
  have h_entry {i j : n} (hij : s i ≠ t j) :
      (h + signMatrix s * h * signMatrix t : Matrix n n ℂ) i j = 0 := by
    simp [signMatrix, units_ne_iff_eq_neg.1 hij, field, sq, ← cast_mul]
  have h_det : (h + signMatrix s * h * signMatrix t).det = 0 := by
    rw [det_apply']
    refine sum_eq_zero fun τ _ ↦ ?_
    obtain ⟨j, hj⟩ := h_none τ
    exact mul_eq_zero_of_right _ (prod_eq_zero (mem_univ j) (h_entry hj))
  apply (PosDef.one.posSemidef_add h.posSemidef_conjTranspose_mul_self).det_pos.ne'
  rw [h_factor, det_mul, h_det, mul_zero]

end New

end SylvesterInertia
