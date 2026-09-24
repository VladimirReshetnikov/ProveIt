import Surreal.Algebra.PronyHankel
import Surreal.Algebra.PolynomialDiscriminant
import Surreal.Algebra.PolynomialNormResultant
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Valuation.Basic

/-!
# Hankel subdiscriminants and the Hermite trace form

This file formalizes `spec:hank:prop:hermite`, with the subdiscriminant identity
`spec:hank:eq:subdisc`, and the affine clause of `spec:hank:prop:invariance` in
`docs/surcomplex/spectral-theory/article.tex`. Everything is proved over an arbitrary field
`K`, ordered where positivity is involved; nothing uses the Hahn structure of `F_Γ`.

For a monic `p`, the Newton sums are defined intrinsically as traces
`s_j = Tr_{K[X]/(p) / K}(X ^ j)` (`newtonSum`), with `H_p = (s_{i+j})_{i,j<n}`
(`traceHankel`) and `h_k = det (s_{i+j})_{i,j<k}` (`subdisc`, so `h_0 = 1`).

* `traceMatrix_eq_traceHankel`: `H_p` is the matrix of the trace form `(u, w) ↦ Tr(u w)` in
  the monomial basis.
* `newtonSum_nodePoly`, `map_newtonSum_of_map_eq`: when `p` factors as `∏ (X - zᵢ)` over some
  extension field, for instance an algebraic closure (`exists_map_eq_nodePoly`), the trace
  Newton sums are the root power sums, with multiplicity. The trace is computed in the
  Newton basis `∏_{i<k} (X - zᵢ)`, where multiplication by `X` is lower bidiagonal.
* `det_mul_eq_sum_subsets`: the Cauchy–Binet formula, which Mathlib lacks.
* `hankelDet_powerSum_eq_sum_prod`, `map_subdisc_eq_sum_prod`, `subdisc_nodePoly`:
  `spec:hank:eq:subdisc`, from `H_p = Vᵀ V` and Cauchy–Binet.
* `subdisc_natDegree`: `h_n = Disc(p)` for every monic `p`, split or not, from the existing
  identity `det (trace matrix) = Disc(p)`.
* `hermite_tfae`: the equivalence of (i) `p` squarefree, (ii) `H_p` positive definite over `K`,
  and (iii) `h_k(p) > 0` for `1 ≤ k ≤ n`, for every monic `p` whose roots lie in an ordered
  field `L` containing `K` as an ordered subfield, such as the real closed Hahn field
  `F_{Γ_ℚ}` ⊇ `F_Γ`. `squarefree_of_posDef` and `squarefree_of_subdisc_pos` give the
  squarefree half of (ii) ⇒ (i) and (iii) ⇒ (i) for every monic `p`, with no assumption on
  the roots.
* `subdisc_affineTransform`: `h_k(p_{a,c}) = a ^ (k (k - 1)) h_k(p)` for every monic `p`,
  `a ≠ 0` and `c`. `valuation_subdisc_affineTransform` (any additive valuation) and
  `pivotClass_affineTransform` (values in an ordered group `Γ`) show that each pivot class
  `v(h_{k+1}) - v(h_k) + 2Γ` is unchanged, index by index. The profile `m_p` and the span
  `D_p` are functions of these classes and are not defined separately here.

Pending: the implication from (ii) or (iii) to real-rootedness when the roots are not
already known to lie in an ordered extension. The source derives it over the real closed
field `F_{Γ_ℚ}`: conjugate-pair factors of the quotient algebra have indefinite trace form,
and the no-pivot `LDLᵀ` (Sylvester) criterion transfers positivity from `F_Γ` to `F_{Γ_ℚ}`.
Neither Sylvester's criterion over ordered fields nor the structure of finite extensions of a
real closed field is available in Mathlib. The additivity clause `m_{p p̃} = m_p + m_{p̃}` of
`spec:hank:prop:invariance`, which needs `spec:hank:lem:graded`, is also pending.
-/

namespace Surreal.HankelHermite

open Matrix Polynomial Finset

noncomputable section

section CauchyBinet

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- The Cauchy–Binet formula for a `k × m` times `m × k` product: the determinant is the
sum, over the `k`-element sets of middle indices, of the products of the corresponding
maximal minors. -/
theorem det_mul_eq_sum_subsets (A : Matrix (Fin k) ι R) (B : Matrix ι (Fin k) R) :
    (A * B).det = ∑ S : {S : Finset ι // S.card = k},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  -- Expand every column of `A * B` as a combination of columns of `A`.
  have h1 : (A * B).det = ∑ f : Fin k → ι, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
      submatrix_apply, id_eq]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun f _ => sum_congr rfl fun σ _ => ?_
    rw [prod_mul_distrib]
    ring
  -- Column patterns with a repeated index contribute nothing.
  have h2 : ∑ f ∈ univ.filter Function.Injective, (∏ i, B (f i) i) * (A.submatrix id f).det =
      ∑ f : Fin k → ι, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    refine sum_filter_of_ne fun f _ hf => ?_
    by_contra hinj
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hinj
    exact hf (by rw [det_zero_of_column_eq hne fun r => by simp [hij], mul_zero])
  -- An injective pattern is an increasing enumeration of its image after a permutation.
  have h3 : ∑ x : {S : Finset ι // S.card = k} × Equiv.Perm (Fin k),
      (∏ i, B (x.1.1.orderEmbOfFin x.1.2 (x.2 i)) i) *
        (A.submatrix id (x.1.1.orderEmbOfFin x.1.2 ∘ x.2)).det =
      ∑ f ∈ univ.filter Function.Injective, (∏ i, B (f i) i) * (A.submatrix id f).det := by
    refine sum_bij (fun x _ => x.1.1.orderEmbOfFin x.1.2 ∘ x.2) (fun x _ => ?_) ?_ ?_
      (fun _ _ => rfl)
    · simp only [mem_filter, mem_univ, true_and]
      exact (x.1.1.orderEmbOfFin x.1.2).injective.comp x.2.injective
    · rintro ⟨⟨S, hS⟩, σ⟩ _ ⟨⟨T, hT⟩, τ⟩ _ h
      dsimp only at h
      have hST : S = T := by
        have hr := congrArg Set.range h
        simp only [Set.range_comp, Equiv.range_eq_univ, Set.image_univ,
          range_orderEmbOfFin] at hr
        exact_mod_cast hr
      subst hST
      exact Prod.ext rfl (Equiv.ext fun i => (S.orderEmbOfFin hS).injective (congrFun h i))
    · intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf
      have hS : (univ.image f).card = k := by
        rw [card_image_of_injective _ hf, card_univ, Fintype.card_fin]
      have hmem : ∀ i, ∃ j, (univ.image f).orderEmbOfFin hS j = f i := fun i => by
        have : f i ∈ Set.range ((univ.image f).orderEmbOfFin hS) := by
          rw [range_orderEmbOfFin]
          simp
        exact this
      choose g hg using hmem
      have hginj : Function.Injective g := fun a b hab => hf (by rw [← hg a, ← hg b, hab])
      exact ⟨(⟨univ.image f, hS⟩, Equiv.ofBijective g (Finite.injective_iff_bijective.mp hginj)),
        mem_univ _, funext fun i => hg i⟩
  rw [h1, ← h2, ← h3, Fintype.sum_prod_type]
  refine sum_congr rfl fun S _ => ?_
  have hA (σ : Equiv.Perm (Fin k)) : (A.submatrix id (S.1.orderEmbOfFin S.2 ∘ σ)).det =
      Equiv.Perm.sign σ * (A.submatrix id (S.1.orderEmbOfFin S.2)).det := by
    rw [← det_permute', submatrix_submatrix]
    rfl
  simp only [hA]
  rw [det_apply' (B.submatrix _ id), mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id_eq]
  ring

/-- Powers of a lower triangular matrix are lower triangular, with the powers of the
diagonal entries on the diagonal. -/
theorem lowerTriangular_pow {m : ℕ} (L : Matrix (Fin m) (Fin m) R)
    (hL : ∀ i k, i < k → L i k = 0) (j : ℕ) :
    (∀ i k, i < k → (L ^ j) i k = 0) ∧ ∀ i, (L ^ j) i i = L i i ^ j := by
  induction j with
  | zero =>
    refine ⟨fun i k hik => ?_, fun i => ?_⟩
    · rw [pow_zero, one_apply_ne hik.ne]
    · rw [pow_zero, pow_zero, one_apply_eq]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨fun i k hik => ?_, fun i => ?_⟩
    · rw [pow_succ, mul_apply]
      refine sum_eq_zero fun l _ => ?_
      rcases lt_or_ge i l with h | h
      · rw [h1 i l h, zero_mul]
      · rw [hL l k (h.trans_lt hik), mul_zero]
    · rw [pow_succ, mul_apply, sum_eq_single i, h2, pow_succ]
      · intro l _ hli
        rcases lt_or_gt_of_ne hli with h | h
        · rw [hL l i h, mul_zero]
        · rw [h1 i l h, zero_mul]
      · simp

end CauchyBinet

section Hankel

variable {K : Type*} [Field K] {n : ℕ}

/-- The power sums `s_j = ∑ᵢ zᵢ ^ j` of a finite list of roots, with multiplicity. -/
def powerSum (z : Fin n → K) (j : ℕ) : K :=
  ∑ i, z i ^ j

/-- The leading Hankel minor `det (s_{i+j})_{0 ≤ i,j < k}` of a sequence. -/
def hankelDet (s : ℕ → K) (k : ℕ) : K :=
  (Prony.hankel k s).det

theorem hankelDet_zero (s : ℕ → K) : hankelDet s 0 = 1 :=
  det_isEmpty

theorem hankelDet_map {L : Type*} [Field L] (f : K →+* L) (s : ℕ → K) (k : ℕ) :
    f (hankelDet s k) = hankelDet (fun j => f (s j)) k := by
  rw [hankelDet, hankelDet, RingHom.map_det]
  rfl

/-- The Hankel matrix of the root power sums factors as `Vᵀ V`, with `V = (zᵢ ^ r)` the
rectangular Vandermonde matrix. This is the source's `H_p = Vᵀ V` once combined with
`newtonSum_nodePoly`, which identifies the trace Newton sums with the root power sums. -/
theorem hankel_powerSum (z : Fin n → K) (k : ℕ) :
    Prony.hankel k (powerSum z) = (Prony.powerMatrix k z)ᵀ * Prony.powerMatrix k z := by
  ext r s
  simp only [Prony.hankel, powerSum, Prony.powerMatrix, mul_apply, transpose_apply, of_apply,
    pow_add]

/-- The quadratic form of the power-sum Hankel matrix is `∑ᵢ u(zᵢ)²`, written as `|V x|²`. -/
theorem dotProduct_hankel_powerSum (z x : Fin n → K) :
    x ⬝ᵥ (Prony.hankel n (powerSum z) *ᵥ x) = (vandermonde z *ᵥ x) ⬝ᵥ (vandermonde z *ᵥ x) := by
  rw [hankel_powerSum, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rfl

/-- `spec:hank:eq:subdisc`, Cauchy–Binet form: `h_k` is the sum of the squared Vandermonde
determinants of the `k`-element subsets of the roots, enumerated increasingly. -/
theorem hankelDet_powerSum_eq_sum_vandermonde (z : Fin n → K) (k : ℕ) :
    hankelDet (powerSum z) k = ∑ S : {S : Finset (Fin n) // S.card = k},
      (vandermonde fun i => z (S.1.orderEmbOfFin S.2 i)).det ^ 2 := by
  rw [hankelDet, hankel_powerSum, det_mul_eq_sum_subsets]
  refine sum_congr rfl fun S _ => ?_
  rw [← transpose_submatrix, det_transpose, sq]
  rfl

/-- The squared Vandermonde determinant of an increasingly enumerated subset is the product of
its squared root differences. -/
theorem det_vandermonde_orderEmbOfFin_sq (z : Fin n → K) (S : Finset (Fin n)) {k : ℕ}
    (hS : S.card = k) :
    (vandermonde fun i => z (S.orderEmbOfFin hS i)).det ^ 2 =
      ∏ i ∈ S, ∏ j ∈ S.filter (i < ·), (z j - z i) ^ 2 := by
  set e := S.orderEmbOfFin hS
  have hrange : ∀ x, x ∈ S ↔ ∃ a, e a = x := fun x => by
    have h := congrArg (x ∈ ·) (range_orderEmbOfFin S hS)
    simp only [Set.mem_range, mem_coe, eq_iff_iff] at h
    exact h.symm
  have himg : univ.map e.toEmbedding = S := by
    ext x
    simp only [mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding, hrange]
  have hfil : ∀ r, (Ioi r).map e.toEmbedding = S.filter (e r < ·) := by
    intro r
    ext x
    simp only [mem_map, mem_Ioi, mem_filter, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(hrange _).mpr ⟨a, rfl⟩, e.strictMono ha⟩
    · rintro ⟨hx, hlt⟩
      obtain ⟨a, rfl⟩ := (hrange x).mp hx
      exact ⟨a, e.lt_iff_lt.mp hlt, rfl⟩
  calc (vandermonde fun i => z (e i)).det ^ 2
      = ∏ r : Fin k, ∏ j ∈ Ioi r, (z (e j) - z (e r)) ^ 2 := by
        rw [det_vandermonde]
        simp only [← prod_pow]
    _ = ∏ r : Fin k, ∏ j ∈ S.filter (e r < ·), (z j - z (e r)) ^ 2 := by
        refine prod_congr rfl fun r _ => ?_
        rw [← hfil, prod_map]
        rfl
    _ = ∏ i ∈ S, ∏ j ∈ S.filter (i < ·), (z j - z i) ^ 2 := by
        have h := prod_map (univ : Finset (Fin k)) e.toEmbedding
          (fun i => ∏ j ∈ S.filter (i < ·), (z j - z i) ^ 2)
        rw [himg] at h
        rw [h]
        rfl

/-- `spec:hank:eq:subdisc`: `h_k = ∑_{|I| = k} ∏_{i < j ∈ I} (z_j - z_i)²`. -/
theorem hankelDet_powerSum_eq_sum_prod (z : Fin n → K) (k : ℕ) :
    hankelDet (powerSum z) k = ∑ I : {I : Finset (Fin n) // I.card = k},
      ∏ i ∈ I.1, ∏ j ∈ I.1.filter (i < ·), (z j - z i) ^ 2 := by
  rw [hankelDet_powerSum_eq_sum_vandermonde]
  exact sum_congr rfl fun I _ => det_vandermonde_orderEmbOfFin_sq z I.1 I.2

/-- The full Hankel determinant of the power sums is the squared Vandermonde determinant. -/
theorem hankelDet_powerSum_self (z : Fin n → K) :
    hankelDet (powerSum z) n = (vandermonde z).det ^ 2 := by
  rw [hankelDet, hankel_powerSum, det_mul, det_transpose, sq]
  rfl

/-- The full Hankel determinant of the power sums vanishes exactly at a repeated root. -/
theorem hankelDet_powerSum_self_ne_zero_iff (z : Fin n → K) :
    hankelDet (powerSum z) n ≠ 0 ↔ Function.Injective z := by
  rw [hankelDet_powerSum_self, pow_ne_zero_iff two_ne_zero, det_vandermonde_ne_zero_iff]

/-- Scaling and translating the roots multiplies a squared Vandermonde determinant by
`a ^ (k (k - 1))`. -/
theorem det_vandermonde_affine_sq {k : ℕ} (w : Fin k → K) (a c : K) :
    (vandermonde fun i => a * w i + c).det ^ 2 = a ^ (k * (k - 1)) * (vandermonde w).det ^ 2 := by
  rw [det_vandermonde_add (fun i => a * w i) c]
  have hscale : vandermonde (fun i => a * w i) =
      vandermonde w * diagonal fun j : Fin k => a ^ (j : ℕ) := by
    ext i j
    simp only [vandermonde_apply, mul_diagonal, mul_pow, mul_comm]
  rw [hscale, det_mul, det_diagonal, prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun j => j) k, mul_pow, ← pow_mul, sum_range_id_mul_two]
  ring

/-- `spec:hank:prop:invariance`, affine clause at the level of roots:
`h_k` of the roots `a zᵢ + c` is `a ^ (k (k - 1)) h_k`. -/
theorem hankelDet_powerSum_affine (z : Fin n → K) (a c : K) (k : ℕ) :
    hankelDet (powerSum fun i => a * z i + c) k =
      a ^ (k * (k - 1)) * hankelDet (powerSum z) k := by
  rw [hankelDet_powerSum_eq_sum_vandermonde, hankelDet_powerSum_eq_sum_vandermonde, mul_sum]
  exact sum_congr rfl fun S _ => det_vandermonde_affine_sq _ a c

end Hankel

section Trace

variable {K : Type*} [Field K] {n : ℕ}

/-- The Newton sums of `p`, defined intrinsically as `s_j = Tr_{K[X]/(p) / K}(X ^ j)`. -/
def newtonSum (p : K[X]) (j : ℕ) : K :=
  Algebra.trace K (AdjoinRoot p) (AdjoinRoot.root p ^ j)

/-- The Newton-sum Hankel matrix `H_p = (s_{i+j})_{0 ≤ i,j < n}`. -/
def traceHankel (p : K[X]) : Matrix (Fin p.natDegree) (Fin p.natDegree) K :=
  Prony.hankel p.natDegree (newtonSum p)

/-- The Hankel subdiscriminant `h_k(p) = det (s_{i+j})_{0 ≤ i,j < k}`, with `h_0 = 1`. -/
def subdisc (p : K[X]) (k : ℕ) : K :=
  hankelDet (newtonSum p) k

theorem powerBasisAux'_apply {p : K[X]} (hp : p.Monic) (i : Fin p.natDegree) :
    AdjoinRoot.powerBasisAux' hp i = AdjoinRoot.root p ^ (i : ℕ) :=
  (AdjoinRoot.powerBasis' hp).basis_eq_pow i

/-- `spec:hank:prop:hermite`: `H_p` is the matrix of the trace form
`(u, w) ↦ Tr_{K[X]/(p) / K}(u w)` in the monomial basis `1, X, …, X ^ (n - 1)`. -/
theorem traceMatrix_eq_traceHankel {p : K[X]} (hp : p.Monic) :
    Algebra.traceMatrix K (AdjoinRoot.powerBasisAux' hp) = traceHankel p := by
  ext i j
  rw [Algebra.traceMatrix_apply, Algebra.traceForm_apply, powerBasisAux'_apply,
    powerBasisAux'_apply, ← pow_add]
  rfl

/-- `spec:hank:prop:hermite`: `h_n = Disc(p)` for every monic `p`, split or not. -/
theorem subdisc_natDegree {p : K[X]} (hp : p.Monic) : subdisc p p.natDegree = p.discr := by
  rw [← FinitePolynomial.quotient_det_traceMatrix_eq_discr p hp, traceMatrix_eq_traceHankel hp]
  rfl

/-- The Newton sums are finite monic-division calculations. -/
theorem newtonSum_eq_sum {p : K[X]} (hp : p.Monic) (j : ℕ) :
    newtonSum p j = ∑ i ∈ range p.natDegree, ((X ^ j * X ^ i) %ₘ p).coeff i := by
  rw [newtonSum, ← AdjoinRoot.mk_X, ← map_pow, FinitePolynomial.quotient_trace_eq_sum p hp,
    Fin.sum_univ_eq_sum_range (fun i => ((X ^ j * X ^ i) %ₘ p).coeff i)]

/-- The Newton sums commute with every extension of scalars. -/
theorem newtonSum_map {L : Type*} [Field L] (f : K →+* L) {p : K[X]} (hp : p.Monic) (j : ℕ) :
    newtonSum (p.map f) j = f (newtonSum p j) := by
  rw [newtonSum_eq_sum (hp.map f), newtonSum_eq_sum hp, natDegree_map, map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [FinitePolynomial.map_monic_remainder_coeff p hp f, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_pow, map_X]

theorem subdisc_map {L : Type*} [Field L] (f : K →+* L) {p : K[X]} (hp : p.Monic) (k : ℕ) :
    f (subdisc p k) = subdisc (p.map f) k := by
  rw [subdisc, subdisc, hankelDet_map]
  congr 1
  funext j
  rw [newtonSum_map f hp]

/-- The Newton polynomials `e_k = ∏_{i < k} (X - zᵢ)`, whose classes form a basis of
`K[X]/(∏ (X - zᵢ))` in which multiplication by `X` is lower bidiagonal. -/
def newtonPoly (z : Fin n → K) (k : ℕ) : K[X] :=
  ∏ i ∈ univ.filter (fun i : Fin n => (i : ℕ) < k), (X - C (z i))

theorem newtonPoly_monic (z : Fin n → K) (k : ℕ) : (newtonPoly z k).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)

theorem natDegree_newtonPoly (z : Fin n → K) {k : ℕ} (hk : k ≤ n) :
    (newtonPoly z k).natDegree = k := by
  rw [newtonPoly, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (z i)]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one, Fin.card_filter_val_lt]
  omega

theorem newtonPoly_succ (z : Fin n → K) (k : Fin n) :
    newtonPoly z (k + 1) = newtonPoly z k * (X - C (z k)) := by
  have hs : univ.filter (fun i : Fin n => (i : ℕ) < k + 1) =
      insert k (univ.filter fun i : Fin n => (i : ℕ) < k) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
    omega
  rw [newtonPoly, hs, prod_insert (by simp), mul_comm]
  rfl

theorem newtonPoly_self (z : Fin n → K) : newtonPoly z n = Prony.nodePoly z := by
  rw [newtonPoly, filter_true_of_mem fun i _ => i.2]
  rfl

/-- `spec:hank:prop:hermite`, Newton-sum clause: for `p = ∏ (X - zᵢ)` the trace Newton sums are
the power sums of the roots, counted with multiplicity. -/
theorem newtonSum_nodePoly (z : Fin n → K) (j : ℕ) :
    newtonSum (Prony.nodePoly z) j = powerSum z j := by
  classical
  obtain ⟨p, hpdef⟩ : ∃ p, p = Prony.nodePoly z := ⟨_, rfl⟩
  rw [← hpdef]
  have hp : p.Monic := hpdef ▸ Prony.nodePoly_monic z
  have hdeg : p.natDegree = n := hpdef ▸ Prony.natDegree_nodePoly z
  -- Coordinates in the reindexed power basis are coefficients.
  obtain ⟨b0, hrepr⟩ : ∃ b0 : Module.Basis (Fin n) K (AdjoinRoot p), ∀ q : K[X],
      q.natDegree < n → ∀ i, b0.repr (AdjoinRoot.mk p q) i = q.coeff i := by
    refine ⟨(AdjoinRoot.powerBasisAux' hp).reindex (finCongr hdeg), fun q hq i => ?_⟩
    rw [Module.Basis.repr_reindex_apply, AdjoinRoot.powerBasisAux'_repr_apply_to_fun,
      AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff hp).mpr]
    · rfl
    · rw [degree_eq_natDegree hp.ne_zero, hdeg]
      exact degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hq)
  have hlt (k : Fin n) : (newtonPoly z k).natDegree < n := by
    rw [natDegree_newtonPoly z k.2.le]
    exact k.2
  -- The Newton classes form a basis: their power-basis matrix is unitriangular.
  obtain ⟨nb, hnb⟩ : ∃ nb : Module.Basis (Fin n) K (AdjoinRoot p),
      ∀ k : Fin n, nb k = AdjoinRoot.mk p (newtonPoly z k) := by
    have hdet : IsUnit (b0.det fun k : Fin n => AdjoinRoot.mk p (newtonPoly z k)) := by
      rw [Module.Basis.det_apply, det_of_upperTriangular]
      · have hd : ∀ i : Fin n,
            b0.toMatrix (fun k : Fin n => AdjoinRoot.mk p (newtonPoly z k)) i i = 1 := fun i => by
          rw [Module.Basis.toMatrix_apply, hrepr _ (hlt i)]
          have h := (newtonPoly_monic z i).coeff_natDegree
          rwa [natDegree_newtonPoly z i.2.le] at h
        have hprod : ∏ i : Fin n,
            b0.toMatrix (fun k : Fin n => AdjoinRoot.mk p (newtonPoly z k)) i i = 1 :=
          prod_eq_one fun i _ => hd i
        rw [hprod]
        exact isUnit_one
      · intro i k hki
        rw [Module.Basis.toMatrix_apply, hrepr _ (hlt k)]
        exact coeff_eq_zero_of_natDegree_lt (by rw [natDegree_newtonPoly z k.2.le]; exact hki)
    obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det b0).mpr hdet
    exact ⟨Module.Basis.mk hli hsp.ge, Module.Basis.mk_apply hli hsp.ge⟩
  have hmul (k : Fin n) : AdjoinRoot.root p * nb k =
      AdjoinRoot.mk p (newtonPoly z (k + 1)) + z k • nb k := by
    have he : X * newtonPoly z k = newtonPoly z (k + 1) + C (z k) * newtonPoly z k := by
      rw [newtonPoly_succ z k]
      ring
    rw [hnb, ← AdjoinRoot.mk_X, ← map_mul, he, map_add, map_mul, AdjoinRoot.mk_C,
      Algebra.smul_def]
    rfl
  -- Multiplication by the root is lower triangular with the roots on the diagonal.
  have hL (i k : Fin n) (hik : i ≤ k) :
      Algebra.leftMulMatrix nb (AdjoinRoot.root p) i k = if i = k then z k else 0 := by
    rw [Algebra.leftMulMatrix_eq_repr_mul, hmul, map_add, map_smul, Finsupp.add_apply,
      Finsupp.smul_apply, Module.Basis.repr_self, smul_eq_mul]
    have h0 : nb.repr (AdjoinRoot.mk p (newtonPoly z (k + 1))) i = 0 := by
      have := k.2
      rcases (by omega : (k : ℕ) + 1 < n ∨ (k : ℕ) + 1 = n) with h | h
      · have hk1 : nb ⟨k + 1, h⟩ = AdjoinRoot.mk p (newtonPoly z (k + 1)) := hnb ⟨k + 1, h⟩
        rw [← hk1, Module.Basis.repr_self, Finsupp.single_apply, if_neg]
        intro h'
        have h'' : (k : ℕ) + 1 = i := congrArg Fin.val h'
        have : (i : ℕ) ≤ k := hik
        omega
      · rw [h, newtonPoly_self, ← hpdef, AdjoinRoot.mk_self, map_zero, Finsupp.coe_zero,
          Pi.zero_apply]
    rw [h0, zero_add, Finsupp.single_apply]
    by_cases h : i = k
    · rw [if_pos h.symm, if_pos h, mul_one]
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
  rw [newtonSum, Algebra.trace_eq_matrix_trace nb, map_pow]
  have htri := lowerTriangular_pow (Algebra.leftMulMatrix nb (AdjoinRoot.root p))
    (fun i k hik => by rw [hL i k hik.le, if_neg hik.ne]) j
  simp only [Matrix.trace, diag_apply, htri.2, hL _ _ le_rfl]
  rfl

/-- `spec:hank:prop:hermite` over any field containing the roots: if `p` maps to
`∏ (X - zᵢ)`, then the Newton sums are the root power sums. -/
theorem map_newtonSum_of_map_eq {L : Type*} [Field L] (f : K →+* L) {p : K[X]} (hp : p.Monic)
    {z : Fin n → L} (hz : p.map f = Prony.nodePoly z) (j : ℕ) :
    f (newtonSum p j) = powerSum z j := by
  rw [← newtonSum_map f hp, hz, newtonSum_nodePoly]

theorem map_subdisc_of_map_eq {L : Type*} [Field L] (f : K →+* L) {p : K[X]} (hp : p.Monic)
    {z : Fin n → L} (hz : p.map f = Prony.nodePoly z) (k : ℕ) :
    f (subdisc p k) = hankelDet (powerSum z) k := by
  rw [subdisc, hankelDet_map]
  congr 1
  funext j
  exact map_newtonSum_of_map_eq f hp hz j

/-- A multiset of cardinality `m` can be listed by `Fin m`. -/
theorem exists_fin_prod_eq {α M : Type*} [CommMonoid M] (g : α → M) :
    ∀ (m : ℕ) (s : Multiset α), Multiset.card s = m →
      ∃ z : Fin m → α, (s.map g).prod = ∏ i, g (z i)
  | 0, s, hs => ⟨Fin.elim0, by rw [Multiset.card_eq_zero.mp hs]; simp⟩
  | m + 1, s, hs => by
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < Multiset.card s)
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    rw [Multiset.card_cons, Nat.add_right_cancel_iff] at hs
    obtain ⟨z, hz⟩ := exists_fin_prod_eq g m t hs
    refine ⟨Fin.cons a z, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, hz, Fin.prod_univ_succ]
    simp

/-- Every monic polynomial has a root list, with multiplicity, in an algebraic closure. -/
theorem exists_map_eq_nodePoly {p : K[X]} (hp : p.Monic) :
    ∃ z : Fin p.natDegree → AlgebraicClosure K,
      p.map (algebraMap K (AlgebraicClosure K)) = Prony.nodePoly z := by
  have hs : (p.map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hcard := splits_iff_card_roots.mp hs
  rw [natDegree_map] at hcard
  obtain ⟨z, hz⟩ := exists_fin_prod_eq (fun a => X - C a) _ _ hcard
  exact ⟨z, (hs.eq_prod_roots_of_monic (hp.map _)).trans hz⟩

/-- `spec:hank:prop:hermite`, `spec:hank:eq:subdisc`: for a monic `p` whose image in a field `L`
is `∏ (X - zᵢ)`, the Hankel subdiscriminant is `∑_{|I| = k} ∏_{i < j ∈ I} (z_j - z_i)²`. -/
theorem map_subdisc_eq_sum_prod {L : Type*} [Field L] (f : K →+* L) {p : K[X]} (hp : p.Monic)
    {z : Fin n → L} (hz : p.map f = Prony.nodePoly z) (k : ℕ) :
    f (subdisc p k) = ∑ I : {I : Finset (Fin n) // I.card = k},
      ∏ i ∈ I.1, ∏ j ∈ I.1.filter (i < ·), (z j - z i) ^ 2 := by
  rw [map_subdisc_of_map_eq f hp hz, hankelDet_powerSum_eq_sum_prod]

/-- `spec:hank:eq:subdisc` for a split polynomial over the coefficient field itself. -/
theorem subdisc_nodePoly (z : Fin n → K) (k : ℕ) :
    subdisc (Prony.nodePoly z) k = ∑ I : {I : Finset (Fin n) // I.card = k},
      ∏ i ∈ I.1, ∏ j ∈ I.1.filter (i < ·), (z j - z i) ^ 2 := by
  simpa using map_subdisc_eq_sum_prod (RingHom.id K) (Prony.nodePoly_monic z)
    (Polynomial.map_id) k

end Trace

section Affine

variable {K : Type*} [Field K] {n : ℕ}

/-- The affine substitution `p_{a,c}(X) = a ^ n p((X - c) / a)` with `n = deg p`. -/
def affineTransform (p : K[X]) (a c : K) : K[X] :=
  C (a ^ p.natDegree) * p.comp (C a⁻¹ * (X - C c))

/-- The affine substitution moves the roots from `zᵢ` to `a zᵢ + c`. -/
theorem affineTransform_nodePoly (z : Fin n → K) {a : K} (ha : a ≠ 0) (c : K) :
    affineTransform (Prony.nodePoly z) a c = Prony.nodePoly fun i => a * z i + c := by
  have hC : C (a ^ n) = ∏ _i : Fin n, C a := by rw [Fin.prod_const, map_pow]
  rw [affineTransform, Prony.natDegree_nodePoly, hC, Prony.nodePoly, Polynomial.prod_comp,
    ← prod_mul_distrib, Prony.nodePoly]
  refine prod_congr rfl fun i _ => ?_
  rw [sub_comp, X_comp, C_comp, mul_sub, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1,
    one_mul, C_add, C_mul]
  ring

/-- `spec:hank:prop:invariance`, affine clause: `h_k(p_{a,c}) = a ^ (k (k - 1)) h_k(p)` for every
monic `p`, every `a ≠ 0` and every `c`. -/
theorem subdisc_affineTransform {p : K[X]} (hp : p.Monic) {a : K} (ha : a ≠ 0) (c : K)
    (k : ℕ) : subdisc (affineTransform p a c) k = a ^ (k * (k - 1)) * subdisc p k := by
  obtain ⟨z, hz⟩ := exists_map_eq_nodePoly hp
  generalize algebraMap K (AlgebraicClosure K) = f at hz
  have hfa : f a ≠ 0 := (map_ne_zero f).mpr ha
  have hmap : (affineTransform p a c).map f = Prony.nodePoly fun i => f a * z i + f c := by
    rw [← affineTransform_nodePoly z hfa, affineTransform, affineTransform, Polynomial.map_mul,
      map_C, Polynomial.map_comp, hz, Polynomial.map_mul, map_C, Polynomial.map_sub, map_X,
      map_C, Prony.natDegree_nodePoly, map_pow, map_inv₀]
  have hmono : (affineTransform p a c).Monic :=
    Polynomial.monic_map_iff.mp (hmap ▸ Prony.nodePoly_monic _)
  apply f.injective
  rw [map_subdisc_of_map_eq f hmono hmap, map_mul, map_pow, map_subdisc_of_map_eq f hp hz,
    hankelDet_powerSum_affine]

/-- `spec:hank:prop:invariance`: under the affine substitution the consecutive valuations
`v(h_{k+1}) - v(h_k)` change by `2 k v(a)`, stated without subtraction for any additive
valuation. -/
theorem valuation_subdisc_affineTransform {Γ₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ₀]
    (v : AddValuation K Γ₀) {p : K[X]} (hp : p.Monic) {a : K} (ha : a ≠ 0) (c : K) (k : ℕ) :
    v (subdisc (affineTransform p a c) (k + 1)) + v (subdisc p k) =
      v (subdisc (affineTransform p a c) k) + v (subdisc p (k + 1)) + (2 * k) • v a := by
  rw [subdisc_affineTransform hp ha, subdisc_affineTransform hp ha, AddValuation.map_mul,
    AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow]
  have hk : (k + 1) * (k + 1 - 1) = k * (k - 1) + 2 * k := by
    cases k with
    | zero => rfl
    | succ m =>
      simp only [Nat.add_sub_cancel]
      ring
  rw [hk, add_nsmul]
  abel

/-- `spec:hank:prop:invariance`: every pivot class `v(h_{k+1}) - v(h_k) + 2Γ` is unchanged by
the affine substitution; the two consecutive differences differ by `2 • (k • v(a))`. The
statement applies when the relevant `h_k` and `h_{k+1}` are nonzero, so that their valuations
lie in `Γ` (as when `H_p` is positive definite, the source's convention for pivot classes). -/
theorem pivotClass_affineTransform {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : AddValuation K (WithTop Γ)) {p : K[X]} (hp : p.Monic) {a : K}
    (ha : a ≠ 0) (c : K) (k : ℕ) {α γ γ' δ δ' : Γ} (hα : v a = α) (hγ : v (subdisc p k) = γ)
    (hγ' : v (subdisc p (k + 1)) = γ') (hδ : v (subdisc (affineTransform p a c) k) = δ)
    (hδ' : v (subdisc (affineTransform p a c) (k + 1)) = δ') :
    δ' - δ = γ' - γ + 2 • (k • α) := by
  have h := valuation_subdisc_affineTransform v hp ha c k
  rw [hα, hγ, hγ', hδ, hδ'] at h
  have h' : δ' + γ = δ + γ' + (2 * k) • α := by exact_mod_cast h
  rw [← mul_nsmul']
  calc δ' - δ = (δ' + γ) - δ - γ := by abel
    _ = (δ + γ' + (2 * k) • α) - δ - γ := by rw [h']
    _ = γ' - γ + (2 * k) • α := by abel

end Affine

section Ordered

variable {K L : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Field L] [LinearOrder L] [IsStrictOrderedRing L] {n : ℕ}

/-- Distinct real roots give a positive definite power-sum Hankel matrix. -/
theorem hankel_powerSum_posDef {z : Fin n → L} (hz : Function.Injective z) {x : Fin n → L}
    (hx : x ≠ 0) : 0 < x ⬝ᵥ (Prony.hankel n (powerSum z) *ᵥ x) := by
  rw [dotProduct_hankel_powerSum]
  have hv : vandermonde z *ᵥ x ≠ 0 := fun h =>
    hx (eq_zero_of_mulVec_eq_zero (det_vandermonde_ne_zero_iff.mpr hz) h)
  refine lt_of_le_of_ne ?_ (Ne.symm (mt dotProduct_self_eq_zero.mp hv))
  exact sum_nonneg fun i _ => mul_self_nonneg _

/-- Distinct real roots give positive leading Hankel minors `h_k`, `0 ≤ k ≤ n`: each is a
nonempty sum of positive products in `spec:hank:eq:subdisc`. -/
theorem hankelDet_powerSum_pos {z : Fin n → L} (hz : Function.Injective z) {k : ℕ}
    (hk : k ≤ n) : 0 < hankelDet (powerSum z) k := by
  rw [hankelDet_powerSum_eq_sum_vandermonde]
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin n))) (by simpa using hk)
  refine sum_pos (fun S _ => sq_pos_of_ne_zero ?_) ⟨⟨S, hS⟩, mem_univ _⟩
  exact det_vandermonde_ne_zero_iff.mpr (hz.comp (S.1.orderEmbOfFin S.2).injective)

omit [IsStrictOrderedRing K] in
/-- A positive definite `H_p` is nonsingular: `h_n(p) ≠ 0`. -/
theorem subdisc_natDegree_ne_zero_of_posDef {p : K[X]}
    (h : ∀ x : Fin p.natDegree → K, x ≠ 0 → 0 < x ⬝ᵥ (traceHankel p *ᵥ x)) :
    subdisc p p.natDegree ≠ 0 := by
  intro h0
  obtain ⟨x, hx, hHx⟩ := exists_mulVec_eq_zero_iff.mpr (show (traceHankel p).det = 0 from h0)
  have := h x hx
  rw [hHx, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- `spec:hank:prop:hermite`, squarefree half of (ii) ⇒ (i), for every monic `p` over an
ordered field, with no assumption on its roots: a positive definite `H_p` forces
`Disc(p) = h_n ≠ 0`. -/
theorem squarefree_of_posDef {p : K[X]} (hp : p.Monic)
    (h : ∀ x : Fin p.natDegree → K, x ≠ 0 → 0 < x ⬝ᵥ (traceHankel p *ᵥ x)) :
    Squarefree p := by
  rw [← FinitePolynomial.discr_ne_zero_iff_squarefree p hp.ne_zero, ← subdisc_natDegree hp]
  exact subdisc_natDegree_ne_zero_of_posDef h

/-- `spec:hank:prop:hermite`, squarefree half of (iii) ⇒ (i), for every monic `p` over an
ordered field, with no assumption on its roots. -/
theorem squarefree_of_subdisc_pos {p : K[X]} (hp : p.Monic)
    (h : ∀ k, 1 ≤ k → k ≤ p.natDegree → 0 < subdisc p k) : Squarefree p := by
  rw [← FinitePolynomial.discr_ne_zero_iff_squarefree p hp.ne_zero, ← subdisc_natDegree hp]
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
  · rw [h0, subdisc, hankelDet_zero]
    exact one_ne_zero
  · exact (h _ h0 le_rfl).ne'

/-- `spec:hank:prop:hermite`, positivity equivalence for a real-rooted `p`: when the roots of `p`
lie in an ordered field `L` containing `K` as an ordered subfield, the following are equivalent:
`p` is squarefree; `H_p` is positive definite over `K`; `h_k(p) > 0` for `1 ≤ k ≤ n`. -/
theorem hermite_tfae (f : K →+* L) (hf : StrictMono f) {p : K[X]} (hp : p.Monic)
    {z : Fin p.natDegree → L} (hz : p.map f = Prony.nodePoly z) :
    List.TFAE [Squarefree p,
      ∀ x : Fin p.natDegree → K, x ≠ 0 → 0 < x ⬝ᵥ (traceHankel p *ᵥ x),
      ∀ k, 1 ≤ k → k ≤ p.natDegree → 0 < subdisc p k] := by
  have hpos (y : K) : 0 < f y ↔ 0 < y := by
    rw [← map_zero f]
    exact hf.lt_iff_lt
  have hS (j : ℕ) : f (newtonSum p j) = powerSum z j := map_newtonSum_of_map_eq f hp hz j
  have hinj : Squarefree p ↔ Function.Injective z := by
    rw [← FinitePolynomial.discr_ne_zero_iff_squarefree p hp.ne_zero, ← subdisc_natDegree hp,
      ← hankelDet_powerSum_self_ne_zero_iff, ← map_subdisc_of_map_eq f hp hz, _root_.map_ne_zero]
  tfae_have 1 → 2 := by
    intro h x hx
    rw [← hpos]
    have hform : f (x ⬝ᵥ (traceHankel p *ᵥ x)) =
        (fun i => f (x i)) ⬝ᵥ (Prony.hankel p.natDegree (powerSum z) *ᵥ fun i => f (x i)) := by
      simp only [dotProduct, mulVec, traceHankel, Prony.hankel, of_apply, map_sum, map_mul, hS]
    rw [hform]
    refine hankel_powerSum_posDef (hinj.mp h) fun h0 => hx (funext fun i => ?_)
    simpa using congrFun h0 i
  tfae_have 2 → 1 := squarefree_of_posDef hp
  tfae_have 1 → 3 := by
    intro h k _ hk
    rw [← hpos, map_subdisc_of_map_eq f hp hz]
    exact hankelDet_powerSum_pos (hinj.mp h) hk
  tfae_have 3 → 1 := squarefree_of_subdisc_pos hp
  tfae_finish

/-- `spec:hank:prop:hermite` for a polynomial that splits over the ordered field `K` itself. -/
theorem hermite_tfae_of_eq_nodePoly {p : K[X]} {z : Fin p.natDegree → K}
    (hz : p = Prony.nodePoly z) :
    List.TFAE [Squarefree p,
      ∀ x : Fin p.natDegree → K, x ≠ 0 → 0 < x ⬝ᵥ (traceHankel p *ᵥ x),
      ∀ k, 1 ≤ k → k ≤ p.natDegree → 0 < subdisc p k] :=
  hermite_tfae (RingHom.id K) strictMono_id (hz ▸ Prony.nodePoly_monic z)
    (by rw [Polynomial.map_id]; exact hz)

end Ordered

end

end Surreal.HankelHermite
