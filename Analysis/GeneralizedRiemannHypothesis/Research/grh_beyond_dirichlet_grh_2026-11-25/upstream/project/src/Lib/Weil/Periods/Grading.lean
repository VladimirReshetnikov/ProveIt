import Lib.Adelic.Unitary.RationalPoints
import Lib.DiscreteSeries.Rigidity.KernelFixes

/-!
# Graded hermitian spaces X ⊕ J_s, Bessel subgroups, the map T, and c_λ in a frame

A hermitian space `V = X ⊕ J_s` is presented (`New.Grading`) as a space `X` with an orthonormal
basis plus a string of `s` vectors with antidiagonal Gram matrix, whose entries are 1 except `-N`
for the middle vector (`N = N̄ ≠ 0`). The weight, also called grade, is `0` on `X` and `s - 1 - 2i`
on the `i`-th string vector. The grading defines three objects in `U(V)(𝔸)`: the unipotent subgroup
`New.Grading.unipotent`, which raises weights; the embedding `New.Grading.inclX` of `U(X)`; and the
Bessel subgroup `New.Grading.besselGroup`. These are described by matrix entries in rational
coordinates. For a second graded space `V' = X' ⊕ J_(s-1)` the map `T : V → V'`
(`New.Grading.stringMap`) is studied, and separately the matrix coefficient c_λ of a discrete series
is transported to `U(J)` through a frame.

## Main definitions and results

* `New.Grading`: a presentation of `V` in this form, with a constant `genericConst` for the generic
  character.
* `New.Grading.stringMap`: the map between two graded spaces that kills `X` and sends each string
  vector to a multiple of the string vector with the same number (to `0` if there is none). It has
  degree at least `-1` when `s' = s - 1`. `New.Grading.AgreesWithStringMap` is partial agreement
  with it.
* `New.Grading.besselProj`, `New.Grading.exists_besselGroup_proj`,
  `New.Grading.exists_unipotent_mul_inclX`: taking the X-block is a homomorphism from
  `New.Grading.besselGroup` onto U(X) with kernel `New.Grading.unipotent`, split by
  `New.Grading.inclX`.
* `New.isIdempotentKernel_dsCoeffInFrame`: for λ with a large gap, the formal degree times
  `New.HCParam.dsCoeffInFrame l` is an idempotent kernel on `U J` (Schur orthogonality).
* `New.Grading.hasDegreeGe_zero_mul_stringMap_mul_sub`: the Bessel subgroups
  `New.Grading.besselGroup` of both spaces fix `T` modulo degree at least `0`.
* `New.Grading.formAdjoint_stringMap_mul_stringMap_eq_shift`,
  `New.Grading.stringMap_mul_formAdjoint_stringMap_eq_shift`: `T† T` is the shift
  `New.Grading.shift` of `V`, and `T T†` is that of `V'` when the two constants agree;
  `New.Grading.formAdjoint_stringMap_mul_stringMap` states both.

Notions from other files:
* `New.Space`: a hermitian space with a point: a matrix J over E and an x in GL_n(𝔸) such that xᴴJx
  is diag(ε) at the infinite places and 1 at the finite places. `V.Γ` is the group of g whose matrix
  in rational coordinates has entries in E; `New.stdSpace E X` is the definite space on X with point
  1.
* `New.𝔸`: the adele ring of the CM field E, as the product of ℂ^f (one copy of ℂ for each infinite
  place) and the finite adeles.
* `New.G`: the adelic unitary group G = G_∞ × G_f of the form diag(ε) at the infinite places and 1
  at the finite places; `g.adeleMatrix` is the adelic matrix of g.
* `New.IsHermitianInvolution J`: the complex matrix J satisfies J* = J and J² = 1.
* `New.HCParam.HasLargeGap`, `New.HCParam.formalDegree`: for l = 2λ and signs ε on n indices, the
  condition that λ has gap 500n³+A for a natural number A, and the reciprocal of the integral of
  |c_λ|² over U(diag ε) for the compact dual measure.

## Relation to the literature

Known; see `Lib.Weil.Periods.Unfolding` and `Lib.DiscreteSeries.CuspKernel` for sources.

Part of a known construction: adelic points of unitary groups in rational coordinates. See
`Lib.Adelic.Unitary.WeakApproximation`.
-/

noncomputable section

/-!
## Gradings X ⊕ J_s of a hermitian space and their subgroups

All matrix conditions are in rational coordinates (`New.Space.ratCoordMatrix`).
-/

section Grading

open Matrix

namespace New

variable {R X X' ι ι' : Type*} {s s' : ℕ} [CommRing R]
  {E : Type*} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
  (e' : X' ⊕ Fin s' ≃ ι') (e : X ⊕ Fin s ≃ ι) {ε : ι → ℤˣ} {N : E} (V : Space E ι ε)

/-- The block diagonal matrix with block A from X to X' and block B from string to string,
reindexed along e and e'. -/
abbrev gradedBlocks (A : Matrix X' X R) (B : Matrix (Fin s') (Fin s) R) : Matrix ι' ι R :=
  (fromBlocks (α := R) A 0 0 B).submatrix e'.symm e.symm

/-- The Gram matrix of X plus a string of length s: identity on X; string vectors a, b with
a + b = s − 1 pair to 1, or to −N if a = b. -/
def gradedGram (N : R) : Matrix ι ι R :=
  gradedBlocks e e 1 (of fun a b : Fin s ↦ if a = b.rev then (if a = b then -N else 1) else 0)

/-- For a space (J, x) and g in G, the adelic matrix x g x⁻¹ of g in rational coordinates. This is
the matrix of an element of U(J)(𝔸), and it is multiplicative in g. -/
def Space.ratCoordMatrix : G E ε →* Matrix ι ι (𝔸 E) where
  toFun g := V.toRatCoords g
  map_one' := by simp
  map_mul' := by simp

/-- A presentation of `V` as `X ⊕ J_s`: an indexing of the basis by `X` and a string of `s` vectors
for which the Gram matrix is `New.gradedGram`, with `N = N̄ ≠ 0`. It also carries a constant
`c = genericConst`, with `c = c̄ ≠ 0` in `E`, for the generic character. Certain multiples of the
string vectors, defined in `Lib.Weil.Periods.StringPowers`, are the vectors `𝔢 ^ i`, which pair to
`-N` for opposite grades. -/
structure Grading (N : E) (X : Type _) [DecidableEq X] (s : ℕ) where
  /-- The splitting of the basis of `V` into `X`, of grade 0, and a string of `s` vectors. -/
  indexEquiv : X ⊕ Fin s ≃ ι
  /-- The Gram matrix is 1 on `X`; vector i of the string pairs only with vector s - 1 - i, to 1,
  but to -N if it is the middle vector. -/
  gram_eq : V.J = gradedGram indexEquiv N
  /-- `N` is nonzero and fixed by complex conjugation. -/
  N_ne_zero_and_star_eq : N ≠ 0 ∧ star N = N
  /-- The constant of the generic character, nonzero and fixed by complex conjugation. -/
  genericConst : {genericConst : E // genericConst ≠ 0 ∧ star genericConst = genericConst}

namespace Grading

variable {V} (Y : Grading V N X s)

/-- The grade of a basis index of X plus a string of length s: 0 on X, and s − 1 − 2i on the
i-th string vector. -/
@[local simp]
def gradeOf (i : ι) : ℤ :=
  (Y.indexEquiv.symm i).elim (0 : X → ℤ) fun a : Fin s ↦ s - 1 - 2 * (a : ℕ)

omit [Fintype X] in
@[simp]
lemma gradeOf_inl (a : X) : Y.gradeOf (Y.indexEquiv (Sum.inl a)) = 0 := by simp

omit [Fintype X] in
/-- For a grading `Y` of `V`, which indexes the basis of `V` by `X` together with a string of `s`
vectors, the `a`-th string vector (the basis index `Y.indexEquiv (Sum.inr a)`) has grade
`s - 1 - 2 * a`. -/
@[simp]
lemma gradeOf_inr (a : Fin s) : Y.gradeOf (Y.indexEquiv (Sum.inr a)) = s - 1 - 2 * a := by simp

/-- The unipotent subgroup of the g in G whose matrix in rational coordinates, minus 1, strictly
raises grades. -/
def unipotent : Subgroup (G E ε) :=
  (unitriangular (fun i ↦ -Y.gradeOf i) (𝔸 E)).comap V.ratCoordMatrix.toHomUnits

/-- The homomorphism from the adelic unitary group of the standard definite space on X to that
of V, acting on X and fixing the string vectors. -/
def inclX : G E (1 : X → ℤˣ) →* G E ε :=
  ((U.reindex Y.indexEquiv (by
        -- The Gram matrix in the adeles is block diagonal with the standard form on X; the block of
        -- the string is found by unification. The rewrite has to unfold `gradedGram`, hence `erw`.
        erw [Y.gram_eq, ← submatrix_map]
        aesop (add simp fromBlocks_map))).trans V.toRatCoords.symm).toMonoidHom.comp
    ((U.sum rfl).comp ((G.toUnitary (s := 1)).toMonoidHom.prod 1))

/-- In rational coordinates, `Y.inclX h` is block diagonal: the matrix of `h` on `X` and the
identity on the string. -/
lemma ratCoordMatrix_inclX (h : G E 1) :
    V.ratCoordMatrix (Y.inclX h) = gradedBlocks Y.indexEquiv Y.indexEquiv h.adeleMatrix 1 := by
  simp [Space.ratCoordMatrix, inclX, U.reindex, U.sum, blockGL, G.toUnitary, G.adeleMatrix]

/-- The Bessel (Fourier–Jacobi) subgroup: the `g` whose matrix in rational coordinates sends each
string vector of weight `≥ 0` to itself plus a combination of string vectors of higher weight.
In the column `k` of such a vector, the entries in the rows `i` of weight at most that of `k` are
those of the identity matrix. -/
def besselGroup : Subgroup (G E ε) :=
  Subgroup.comap V.ratCoordMatrix.toHomUnits <| agreeWithOneOn
    (fun i k : ι ↦ (Y.indexEquiv.symm k).isRight ∧ 0 ≤ Y.gradeOf k ∧ Y.gradeOf i ≤ Y.gradeOf k)
    (𝔸 E) <| by
      -- Given a prescribed entry `(i, j)` and any `k`, one of `(i, k)` and `(k, j)` is prescribed:
      -- `(k, j)` if the weight of `k` is at most that of `j`, and `(i, k)` otherwise.
      intro i k j ⟨hj_string, hj_nonneg, hij⟩
      obtain hkj | hjk := le_or_gt (Y.gradeOf k) (Y.gradeOf j)
      · exact .inr ⟨hj_string, hj_nonneg, hkj⟩
      · refine .inl ⟨?_, hj_nonneg.trans hjk.le, hij.trans hjk.le⟩
        -- The weight of `k` is positive, while the vectors of `X` have weight `0`.
        have hk_pos : 0 < Y.gradeOf k := hj_nonneg.trans_lt hjk
        cases hk : Y.indexEquiv.symm k <;> simp_all

omit [Fintype X] in
/-- An element `g` lies in the Bessel subgroup if and only if its matrix in rational coordinates
agrees with the identity at every entry (i, k) with k a string index of grade ≥ 0 and grade(i) at
most grade(k). -/
lemma mem_besselGroup {g : G E ε} :
    g ∈ Y.besselGroup ↔
      ∀ i k : ι, (Y.indexEquiv.symm k).isRight → 0 ≤ Y.gradeOf k → Y.gradeOf i ≤ Y.gradeOf k →
        V.ratCoordMatrix g i k = (1 : Matrix ι ι (𝔸 E)) i k := by
  -- `gradeOf` is a local simp lemma, which would unfold the grades on one side only.
  simp [besselGroup, -gradeOf]

/-- The rational points of U(V) that lie in the Bessel (Fourier–Jacobi) subgroup of the grading
Y. -/
abbrev ratBessel : Subgroup (G E ε) := V.Γ ⊓ Y.besselGroup

end Grading

end New

end Grading

/-!
## Degrees of matrices and entrywise membership in the subgroups

* `New.HasDegreeGe`: a matrix raises weights by at least `d`; degrees add (`New.HasDegreeGe.mul`).
-/

namespace New

open Matrix Space

variable {E : Type*} [Field E] [CMType E] {ι X : Type _} [Fintype ι] [DecidableEq ι] [Fintype X]
  [DecidableEq X] {s : ℕ} {ε : ι → ℤˣ} {N : E} {V : Space E ι ε} (Y : Grading V N X s)
  {ι' : Type*} [Fintype ι']

/-! ### Degrees and rational coordinates -/

/-- The matrix x raises weights by at least d: x_{ba} = 0 whenever w'(b) < w(a) + d. -/
def HasDegreeGe {R ι ι' : Type*} [Zero R] (w' : ι' → ℤ) (w : ι → ℤ) (d : ℤ)
    (x : Matrix ι' ι R) : Prop :=
  ∀ (b : ι') (a : ι), w' b < w a + d → x b a = 0

/-- Degree bounds add: if `x` has degree at least `d` and `y` has degree at least `d'`, then
`x * y` has degree at least `e` for every `e ≤ d + d'`. -/
lemma HasDegreeGe.mul {R ι κ : Type*} [CommRing R] {w'' : κ → ℤ} {w' : ι' → ℤ} {w : ι → ℤ}
    {d d' : ℤ} {y : Matrix ι' ι R} {x : Matrix κ ι' R} (hx : HasDegreeGe w'' w' d x)
    (hy : HasDegreeGe w' w d' y) {e : ℤ} (he : e ≤ d + d') :
    HasDegreeGe w'' w e (x * y) := by
  refine fun c a hca ↦ Finset.sum_eq_zero fun b _ ↦ ?_
  -- In each term `x c b * y b a` of the entry, one of the two factors vanishes.
  obtain hcb | hcb := lt_or_ge (w'' c) (w' b + d)
  · simp [hx c b hcb]
  · simp [hy b a (by lia)]

@[fun_prop]
lemma Space.isEmbedding_ratCoordMatrix : Topology.IsEmbedding V.ratCoordMatrix := by
  -- The map is `G.adeleMatrix` followed by conjugation with the point `V.x`.
  change Topology.IsEmbedding ((ConjAct.toConjAct V.x • ·) ∘ fun g : G E ε ↦ g.adeleMatrix)
  exact (isHomeomorph_smul _).isEmbedding.comp G.isClosedEmbedding_adeleMatrix.toIsEmbedding

/-- An adelic point lies in the group `V.Γ` of rational points if and only if all entries of its
matrix in rational coordinates come from `E` under the diagonal embedding `New.toAdele`. -/
lemma Space.mem_Gamma_iff_ratCoordMatrix {g : G E ε} :
    g ∈ V.Γ ↔ ∀ i k : ι, V.ratCoordMatrix g i k ∈ toAdele.range :=
  mem_Gamma_iff_range _

@[simp]
lemma ratCoordMatrix_stdSpace (g : G E (1 : X → ℤˣ)) :
    (stdSpace E X).ratCoordMatrix g = g.adeleMatrix := by
  -- The point of the standard space is the identity.
  show (1 : Matrix X X (𝔸 E)) * g.adeleMatrix * 1 = g.adeleMatrix
  rw [one_mul, mul_one]

namespace Grading

/-! ### The unipotent and Bessel subgroups -/

omit [Fintype X] in
/-- For a grading `Y` presenting the hermitian space `V` over the CM field `E` as `X ⊕ J_s`, an
element `g` of the adelic unitary group of `V` lies in `Y.unipotent` iff its matrix in rational
coordinates minus 1 raises grades by at least 1. That is, its (b, a) entry vanishes whenever
`Y.gradeOf b < Y.gradeOf a + 1`, where the grade is 0 on `X` and s − 1 − 2i on the i-th string
vector. -/
@[simp]
lemma mem_unipotent {g : G E ε} :
    g ∈ Y.unipotent ↔ HasDegreeGe Y.gradeOf Y.gradeOf 1 (V.ratCoordMatrix g - 1) := by
  simp [unipotent, HasDegreeGe, sub_eq_zero]

omit [Fintype X] in
/-- For a string of odd length all grades are even, so an element of the unipotent group, whose
matrix minus 1 raises grades, raises them by at least 2. -/
lemma hasDegreeGe_two_of_odd {g : G E ε} (hs : Odd s) (hg : g ∈ Y.unipotent) :
    HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix g - 1) := by
  have h_even (i : ι) : Even (Y.gradeOf i) := by
    obtain ⟨x | a, rfl⟩ := Y.indexEquiv.surjective i <;> simp [hs, parity_simps]
  exact fun i k hik ↦ Y.mem_unipotent.1 hg i k (by grind [h_even i, h_even k])

omit [Fintype X] in
/-- Membership in the Bessel subgroup, by the vanishing of entries of `g - 1`. The vectors of `X`
have weight `0`, so the first condition selects the string vectors of weight `≥ 0`. -/
@[local simp] lemma mem_besselGroup_iff_sub_one {g : G E ε} :
    g ∈ Y.besselGroup ↔
      ∀ i k : ι, (if (Y.indexEquiv.symm k).isRight then 0 else 1) ≤ Y.gradeOf k →
        Y.gradeOf i ≤ Y.gradeOf k → (V.ratCoordMatrix g - 1) i k = 0 := by
  simp [Y.mem_besselGroup, reindex_equiv Y.indexEquiv, sub_eq_zero]

/-- Let `Y` present the hermitian space `V` over the CM field `E` as `X ⊕ J_s`. For every element
`a` of the adelic unitary group of the standard definite space on `X`, its image under `Y.inclX`
(acting on `X` and fixing the string vectors) lies in the Bessel (Fourier–Jacobi) subgroup
`Y.besselGroup` of the adelic unitary group of `V`. -/
lemma inclX_mem_besselGroup (a : G E 1) : Y.inclX a ∈ Y.besselGroup := by
  simp [reindex_equiv Y.indexEquiv, ratCoordMatrix_inclX, Matrix.one_apply]

omit [Fintype X] in
/-- For a grading `Y` presenting the hermitian space `V` over the CM field `E` as `X ⊕ J_s`, the
unipotent subgroup `Y.unipotent` is contained in the Bessel (Fourier–Jacobi) subgroup
`Y.besselGroup`. Here `Y.unipotent` consists of the `g` whose matrix in rational coordinates minus 1
strictly raises grades. -/
lemma unipotent_le_besselGroup : Y.unipotent ≤ Y.besselGroup := fun _ hg ↦
  Y.mem_besselGroup_iff_sub_one.2 fun i k _ h_le ↦ Y.mem_unipotent.1 hg i k (by lia)

/-- The Bessel group `Y.besselGroup` is closed. -/
instance isClosed_besselGroup : IsClosed (Y.besselGroup : Set (G E ε)) := by
  -- Membership prescribes certain entries of `V.ratCoordMatrix g`; an entry is continuous in `g`,
  -- so it keeps its value on the closure.
  refine isClosed_of_closure_subset fun g hg i k hik ↦ closure_singleton.le ?_
  exact map_mem_closure (f := (V.ratCoordMatrix · i k)) (by fun_prop) hg fun γ hγ ↦ hγ i k hik

@[fun_prop]
lemma continuous_inclX : Continuous Y.inclX := by
  refine V.isEmbedding_ratCoordMatrix.continuous_iff.2 ?_
  simp only [Function.comp_def, ratCoordMatrix_inclX]
  fun_prop

/-- The embedding `Y.inclX` sends the rational points of the standard definite space on `X` to
rational points in the Bessel subgroup. -/
lemma inclX_mem_ratBessel {a : G E (1 : X → ℤˣ)} (ha : a ∈ (stdSpace E X).Γ) :
    Y.inclX a ∈ Y.ratBessel := by
  refine ⟨mem_Gamma_iff_ratCoordMatrix.2 fun i k ↦ ?_, Y.inclX_mem_besselGroup a⟩
  -- The entries are those of `a` on the `X`-block, and `0` or `1` elsewhere.
  rw [ratCoordMatrix_inclX]
  obtain ⟨x | b, rfl⟩ := Y.indexEquiv.surjective i <;>
    obtain ⟨y | c, rfl⟩ := Y.indexEquiv.surjective k
  · simpa using mem_Gamma_iff_ratCoordMatrix.1 ha x y
  all_goals simp [Matrix.one_apply, apply_ite]

end Grading

end New

/-!
## The map T, the shift and the string reversal

* `New.Grading.stringReversal`: the involution of the indices that fixes `X` and reverses the
  string.
-/

namespace New.Grading

variable {E ι ι' X X' : Type} [DecidableEq X] [DecidableEq X'] [Field E] [CMType E] [Fintype ι]
  [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] {s s' : ℕ} {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {N : E}
  {V : Space E ι ε} {V' : Space E ι' ε'} (Y : Grading V N X s) (Y' : Grading V' N X' s')
  (d : ι' → ℤ)

/-- The involution of the basis indices of V that fixes the indices of X and exchanges the
string vectors i and s − 1 − i. -/
def stringReversal (i : ι) : ι := Y.indexEquiv ((Y.indexEquiv.symm i).map id Fin.rev)

/-- The rational map `V → V'` that kills `X` and sends the string vector `a` to `t a` times the
string vector of `V'` with the same number (to `0` if there is none). For `s` odd, `t a` is
`1`, `-N c`, `c` when the weight of `a` is positive, zero, negative. For `s` even, `t a` is
`c`, `1` when the weight is positive, negative. It has degree at least `-1` when `s' = s - 1`.
For `s' = s - 1` and equal constants `c` it sends each `𝔢 ^ i` (`New.Grading.stringPower`) to
`𝔢 ^ i`, which is `0` in `V'` for `i = s - 1` (`New.Grading.stringMap_mulVec_stringPower`). -/
def stringMap : Matrix ι' ι (𝔸 E) :=
  -- The weight of `a` is positive iff `2 * a + 1 < s`, and zero iff `2 * a + 1 = s`.
  (gradedBlocks Y'.indexEquiv Y.indexEquiv 0 <| Matrix.of fun (b : Fin s') (a : Fin s) ↦
    if (b : ℕ) = a then
      (if Odd s ↔ 2 * a + 1 < s then 1 else ↑Y.genericConst) * (if 2 * a + 1 = s then -N else 1)
    else 0).map toAdele

/-- The condition that the matrix w agrees with T (`New.Grading.stringMap`) at all entries (b, a)
where a has positive grade and b has grade below that of a. -/
abbrev AgreesWithStringMap (w : Matrix ι' ι (𝔸 E)) : Prop :=
  ∀ (b : ι') (a : ι), 0 < Y.gradeOf a → Y'.gradeOf b < Y.gradeOf a → w b a = Y.stringMap Y' b a

/-- For weights d on the target basis and an index pair (b, a), the integer d(b) minus the grade
of a in Y: the amount by which the entry (b, a) of a map raises grades. -/
abbrev mapDegree (r : ι' × ι) : ℤ := d r.1 - Y.gradeOf r.2

/-- For weights d on the target indices, the additive group of rational matrices
(`ratMatrices E ι' ι`, adelic matrices with entries from E) whose entry (b, a) vanishes whenever
d(b) is less than the grade of a. -/
def nonnegMaps : AddSubgroup (ratMatrices E ι' ι) where
  carrier := {w : ratMatrices E ι' ι | HasDegreeGe d Y.gradeOf 0 (w : Matrix ι' ι (𝔸 E))}
  add_mem' := by simp_all [HasDegreeGe]
  zero_mem' := by simp [HasDegreeGe]
  neg_mem' := by simp_all [HasDegreeGe]

/-- Multiplication by `𝔢`: the rational map `V → V` that kills `X` and the last string vector and
sends the string vector `b` to a multiple of the vector `b + 1`. The factor is `-N c` if `b` has
weight `0`, `-N c²` if `b` has weight `1`, and `c` otherwise. It sends `𝔢 ^ i` to `𝔢 ^ (i + 1)`
(`New.Grading.shift_mulVec_stringPower`). -/
def shift : Matrix ι ι (𝔸 E) :=
  -- For `a = b + 1`: `b` has weight zero iff `2 * b + 1 = s`, and weight one iff `2 * a = s`.
  (gradedBlocks Y.indexEquiv Y.indexEquiv 0 <| Matrix.of fun a b : Fin s ↦
    if (a : ℕ) = b + 1 then
      Y.genericConst * (if 2 * b + 1 = s then -N else if 2 * a = s then -N * Y.genericConst else 1)
    else 0).map toAdele

end New.Grading

/-!
## Adjoints in graded coordinates and the projection to U(X)

Matrix computations in a space presented as X plus a string (`New.Grading`).

* `New.Grading.formAdjoint_apply`: the entries of the adjoint `New.Space.formAdjoint` of an adelic
  matrix.
-/

namespace New

open Matrix Fintype Space

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] {s s' : ℕ} {ε : ι → ℤˣ}
  {ε' : ι' → ℤˣ} {N : E} (V : Space E ι ε) (V' : Space E ι' ε')

/-- The adjoint J⁻¹yᴴJ' of an adelic map y from the space with Gram matrix J to the space with
Gram matrix J'. -/
noncomputable def Space.formAdjoint (y : Matrix ι' ι (𝔸 E)) : Matrix ι ι' (𝔸 E) :=
  V.J⁻¹.map toAdele * yᴴ * V'.J.map toAdele

lemma Space.formAdjoint_formAdjoint (x : Matrix ι' ι (𝔸 E)) :
    V'.formAdjoint V (V.formAdjoint V' x) = x := by
  simp [conjTranspose_nonsing_inv, conjTranspose_J, ← Matrix.mul_assoc, x.mul_assoc, formAdjoint,
    map_J_inv_mul_map_J]

/-- The adjoint of `g y` is the adjoint of `y` times `g⁻¹`, because `g` preserves the form. -/
lemma Space.formAdjoint_ratCoordMatrix_mul (g : G E ε) (y : Matrix ι ι' (𝔸 E)) :
    V'.formAdjoint V (V.ratCoordMatrix g * y) = V'.formAdjoint V y * V.ratCoordMatrix g⁻¹ := by
  simp [ratCoordMatrix, ← U.form_mul_inv_eq, formAdjoint, Matrix.mul_assoc]

variable {V : Space E ι ε} {V' : Space E ι' ε'} (Y : Grading V N X s) (Y' : Grading V' N X' s')

namespace Grading

omit [Fintype X] in
@[simp]
lemma gradeOf_stringReversal : ∀ i : ι, Y.gradeOf (Y.stringReversal i) = -Y.gradeOf i := by
  simp +arith [reindex_equiv Y.indexEquiv, stringReversal]

/-- For the graded Gram matrix `Gr` over `E` with any constant `M`, a ring homomorphism
`f : E →+* R` and a matrix `A` over `R`, the entry (i, p) of f(Gr) times `A` is
f(Gr(i, σi)) · A(σi, p), where σ is the dual index `New.Grading.stringReversal`. -/
lemma map_gradedGram_mul_apply {R κ : Type} {M : E} [CommRing R] (f : E →+* R) (A : Matrix ι κ R) :
    ∀ (i : ι) (p : κ), ((gradedGram Y.indexEquiv M).map f * A) i p =
      f (gradedGram Y.indexEquiv M i (Y.stringReversal i)) * A (Y.stringReversal i) p := by
  simp [gradedGram, mul_apply, reindex_equiv Y.indexEquiv, apply_ite f, ← Fin.rev_eq_iff,
    stringReversal, Matrix.one_apply]

/-- The entry a of the row vector y J is y(σa) J(σa, a), with σ the dual index
`New.Grading.stringReversal`. -/
lemma vecMul_J_apply (y : ι → 𝔸 E) :
    ∀ a : ι, (y ᵥ* V.J.map toAdele) a =
      y (Y.stringReversal a) * gradedGram Y.indexEquiv N (Y.stringReversal a) a := by
  -- Column `a` of the Gram matrix has its only nonzero entry at the dual index.
  simp [Y.gram_eq, gradedGram, vecMul_apply_eq_sum, reindex_equiv Y.indexEquiv, apply_ite toAdele,
    stringReversal, Matrix.one_apply]

@[simp]
lemma J_inv_eq_gradedGram : V.J⁻¹ = gradedGram Y.indexEquiv N⁻¹ := by
  rw [Y.gram_eq]
  refine inv_eq_left_inv ?_
  -- Blockwise: on the string both matrices are antidiagonal, with middle product (-N⁻¹) * (-N).
  simp [gradedGram, ← ext_iff, Matrix.mul_apply, reindex_equiv Y.indexEquiv, Matrix.one_apply]
  grind [Y.N_ne_zero_and_star_eq]

/-- The entry (a, b) of the adjoint J⁻¹ yᴴ J' is the conjugate of the entry of y at the dual indices
(σ'b, σa), times the entries J⁻¹(a, σa) and J'(σ'b, b). Here σ and σ' are the dual indices
`New.Grading.stringReversal` of `Y` and `Y'`. Both presentations have the same N. -/
lemma formAdjoint_apply (y : Matrix ι' ι (𝔸 E)) (a : ι) (b : ι') :
    V.formAdjoint V' y a b =
      gradedGram Y.indexEquiv N⁻¹ a (Y.stringReversal a) *
        star (y (Y'.stringReversal b) (Y.stringReversal a)) *
        gradedGram Y'.indexEquiv N (Y'.stringReversal b) b := by
  -- The entry is that of the row `a` of `J⁻¹ yᴴ` times `J'`.
  change ((V.J⁻¹.map toAdele * yᴴ) a ᵥ* V'.J.map toAdele) b = _
  simp [Y'.vecMul_J_apply, Y.J_inv_eq_gradedGram, map_gradedGram_mul_apply]

/-! ### The Bessel subgroup and its projection to U(X) -/

/-- g lies in `New.Grading.besselGroup` if and only if its matrix agrees with the identity at every
entry (i, k) such that weight(i) ≤ weight(k) and i or k is an index of the string. -/
lemma mem_besselGroup_iff {g : G E ε} :
    g ∈ Y.besselGroup ↔
      ∀ i k : ι, Y.gradeOf i ≤ Y.gradeOf k →
        (Y.indexEquiv.symm i).isRight ∨ (Y.indexEquiv.symm k).isRight →
        V.ratCoordMatrix g i k = (1 : Matrix ι ι (𝔸 E)) i k := by
  refine ⟨fun hg i k hle h_string ↦ ?_,
    fun h_one ↦ by simp_all [mem_besselGroup_iff_sub_one, reindex_equiv Y.indexEquiv]⟩
  -- `mem_besselGroup_iff_sub_one` gives the entries `(i, k)` with `k` on the string and of weight
  -- `≥ 0`. For the others `i` is on the string and of weight `≤ 0`; they come from `g⁻¹`, since the
  -- adjoint of `g⁻¹ - 1` is `g - 1` and duality negates the weights.
  have adj : V.formAdjoint V (V.ratCoordMatrix g⁻¹ - 1) = V.ratCoordMatrix g - 1 := by
    -- apply `(g⁻¹ y)† = y† g` to y = 1, and subtract 1† = 1
    simpa [formAdjoint, mul_sub, sub_mul, map_J_inv_mul_map_J] using
      V.formAdjoint_ratCoordMatrix_mul V g⁻¹ 1
  have of_dual :
      (V.ratCoordMatrix g⁻¹ - 1) (Y.stringReversal k) (Y.stringReversal i) = 0 →
      (V.ratCoordMatrix g - 1) i k = 0 :=
    fun h_dual ↦ by rw [← adj, Y.formAdjoint_apply Y, h_dual, star_zero, mul_zero, zero_mul]
  have direct : (if (Y.indexEquiv.symm k).isRight then 0 else 1) ≤ Y.gradeOf k →
      Y.gradeOf i ≤ Y.gradeOf k → (V.ratCoordMatrix g - 1) i k = 0 :=
    Y.mem_besselGroup_iff_sub_one.1 hg i k
  have dual : (if (Y.indexEquiv.symm (Y.stringReversal i)).isRight then 0 else 1) ≤
        Y.gradeOf (Y.stringReversal i) →
      Y.gradeOf (Y.stringReversal k) ≤ Y.gradeOf (Y.stringReversal i) →
      (V.ratCoordMatrix g⁻¹ - 1) (Y.stringReversal k) (Y.stringReversal i) = 0 :=
    Y.mem_besselGroup_iff_sub_one.1 (inv_mem hg) (Y.stringReversal k) (Y.stringReversal i)
  suffices (V.ratCoordMatrix g - 1) i k = 0 by simpa [sub_eq_zero]
  grind [stringReversal, gradeOf_stringReversal]

/-- The matrix of an element of `New.Grading.besselGroup` in rational coordinates does not lower
weights: its entry (i, k) is zero when weight(i) < weight(k). -/
lemma hasDegreeGe_zero_of_mem_besselGroup {g : G E ε} (hg : g ∈ Y.besselGroup) :
    HasDegreeGe Y.gradeOf Y.gradeOf 0 (V.ratCoordMatrix g) := by
  intro i k hlt
  -- Indices of `X` have weight `0`, so they cannot both occur.
  have h_string : (Y.indexEquiv.symm i).isRight ∨ (Y.indexEquiv.symm k).isRight := by
    cases hi : Y.indexEquiv.symm i <;> cases hk : Y.indexEquiv.symm k <;> simp_all [gradeOf]
  rw [Y.mem_besselGroup_iff.1 hg i k (by omega) h_string, Matrix.one_apply_ne (by grind)]

omit [Fintype X] in
/-- The X-block of the Gram matrix of `V` over the adeles is the standard form of the definite
space on X. -/
lemma submatrix_inl_map_J :
    (V.J.map toAdele).submatrix (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl) =
      stdForm E (1 : X → ℤˣ) := by
  simp [← ext_iff, Y.gram_eq, gradedGram, Matrix.one_apply]

/-- For g in `New.Grading.besselGroup`, the X-block B of its matrix in rational coordinates
satisfies Bᴴ S B = S, where S is the standard form of the definite space on X. -/
lemma submatrix_inl_ratCoordMatrix_unitary {g : G E ε} (hg : g ∈ Y.besselGroup) :
    ((V.ratCoordMatrix g).submatrix (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl))ᴴ *
        stdForm E (1 : X → ℤˣ) *
        (V.ratCoordMatrix g).submatrix (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl) =
      stdForm E (1 : X → ℤˣ) := by
  have h_zero (a : Fin s) (x : X) (ha : s ≤ 2 * a.val + 1) :
      V.ratCoordMatrix g (Y.indexEquiv (Sum.inr a)) (Y.indexEquiv (Sum.inl x)) = 0 := by
    rw [Y.mem_besselGroup_iff.1 hg _ _ (by simp; omega) (by simp), Matrix.one_apply_ne (by simp)]
  calc
    _ = ((V.ratCoordMatrix g)ᴴ * V.J.map toAdele * V.ratCoordMatrix g).submatrix
          (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl) := by
      -- The string contributes nothing, since dual string indices have opposite weights and g has
      -- no entry from X to a string index of weight ≤ 0.
      simp [← ext_iff, Matrix.mul_apply, reindex_equiv Y.indexEquiv, Y.gram_eq, gradedGram,
        Matrix.mul_assoc, Matrix.one_apply]
      grind -funext [star_zero, sum_eq_zero]
    _ = _ := by
      rw [show (V.ratCoordMatrix g)ᴴ * V.J.map toAdele * V.ratCoordMatrix g = V.J.map toAdele from
        (V.toRatCoords g).2, Y.submatrix_inl_map_J]

/-- On `New.Grading.besselGroup`, the X-block of the matrix in rational coordinates is
multiplicative. -/
lemma submatrix_inl_ratCoordMatrix_mul {g h : G E ε} (hg : g ∈ Y.besselGroup)
    (hh : h ∈ Y.besselGroup) :
    (V.ratCoordMatrix (g * h)).submatrix (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl) =
      (V.ratCoordMatrix g).submatrix (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl) *
        (V.ratCoordMatrix h).submatrix (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl) := by
  -- The string contributes nothing: an entry of `h` from `X` to a string vector needs its weight
  -- `> 0`, and an entry of `g` from it back to `X` needs its weight `< 0`.
  have h_string (x y : X) (a : Fin s) :
      V.ratCoordMatrix g (Y.indexEquiv (Sum.inl x)) (Y.indexEquiv (Sum.inr a)) *
        V.ratCoordMatrix h (Y.indexEquiv (Sum.inr a)) (Y.indexEquiv (Sum.inl y)) = 0 := by
    obtain h_nonneg | h_nonpos := le_total 0 (Y.gradeOf (Y.indexEquiv (Sum.inr a)))
    · rw [Y.mem_besselGroup_iff.1 hg _ _ (by rwa [gradeOf_inl]) (by simp),
        Matrix.one_apply_ne (by simp), zero_mul]
    · rw [Y.mem_besselGroup_iff.1 hh _ _ (by rwa [gradeOf_inl]) (by simp),
        Matrix.one_apply_ne (by simp), mul_zero]
  exact Matrix.ext fun x y ↦ by simp [Matrix.mul_apply, reindex_equiv Y.indexEquiv, h_string]

/-- The projection from `New.Grading.besselGroup` to the adelic unitary group of the standard
definite space on X: it takes an element to the X-block of its matrix in rational coordinates. -/
def besselProj : Y.besselGroup →* G E (1 : X → ℤˣ) :=
  .mk'
    (fun r : Y.besselGroup ↦ G.toUnitary.symm <| U.of (by simp)
      ((V.ratCoordMatrix r).submatrix (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl))
      (Y.submatrix_inl_ratCoordMatrix_unitary r.property))
    fun a b ↦ (stdSpace E X).isEmbedding_ratCoordMatrix.injective <| by
      simpa [G.adeleMatrix] using Y.submatrix_inl_ratCoordMatrix_mul a.property b.property

/-- The matrix of `Y.besselProj r` is the X-block of the matrix of `r` in rational coordinates. -/
lemma adeleMatrix_besselProj (r : Y.besselGroup) :
    (Y.besselProj r).adeleMatrix =
      (V.ratCoordMatrix r).submatrix (Y.indexEquiv ∘ Sum.inl) (Y.indexEquiv ∘ Sum.inl) := by
  simp [besselProj, G.adeleMatrix]

@[fun_prop]
lemma continuous_besselProj : Continuous Y.besselProj := by
  simp only [G.continuous_iff, Function.comp_def, adeleMatrix_besselProj]
  fun_prop

lemma besselProj_inclX (a : G E (1 : X → ℤˣ)) :
    Y.besselProj ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩ = a :=
  (stdSpace E X).isEmbedding_ratCoordMatrix.injective <| by
    simp [adeleMatrix_besselProj, ← ext_iff, ratCoordMatrix_inclX]

/-- An element of the Bessel group lies in the unipotent group if and only if its projection to U(X)
is trivial. -/
lemma mem_unipotent_iff_besselProj_eq_one (r : Y.besselGroup) :
    (r : G E ε) ∈ Y.unipotent ↔ Y.besselProj r = 1 := by
  -- Off the `X`-block, the conditions for the unipotent and the Bessel group are the same.
  have hr := Y.mem_besselGroup_iff.1 r.2
  rw [← (stdSpace E X).isEmbedding_ratCoordMatrix.injective.eq_iff]
  simp_all [adeleMatrix_besselProj, ← ext_iff, reindex_equiv Y.indexEquiv, HasDegreeGe,
    Matrix.one_apply,
    sub_eq_zero]

/-- An element `r` of the Bessel group agrees with the embedding of its projection to U(X) up to a
unipotent factor on the left. -/
lemma mul_inv_inclX_besselProj_mem_unipotent (r : Y.besselGroup) :
    (r : G E ε) * (Y.inclX (Y.besselProj r))⁻¹ ∈ Y.unipotent := by
  let a : Y.besselGroup := ⟨Y.inclX (Y.besselProj r), Y.inclX_mem_besselGroup _⟩
  exact (Y.mem_unipotent_iff_besselProj_eq_one (r * a⁻¹)).2 <| by simp [a, besselProj_inclX]

lemma besselProj_mem_Gamma {r : Y.besselGroup} (hr : (r : G E ε) ∈ V.Γ) :
    Y.besselProj r ∈ (stdSpace E X).Γ := by
  rw [mem_Gamma_iff_ratCoordMatrix] at hr ⊢
  exact fun x y ↦ by
    simpa [adeleMatrix_besselProj] using hr (Y.indexEquiv (Sum.inl x)) (Y.indexEquiv (Sum.inl y))

/-- There is a continuous homomorphism p from `New.Grading.besselGroup` to the adelic unitary group
of the standard definite space on X such that (a) r · `New.Grading.inclX`(p r)⁻¹ lies in
`New.Grading.unipotent`, (b) p ∘ `New.Grading.inclX` is the identity, (c) the kernel of p is
`New.Grading.unipotent`, (d) p maps rational points to rational points. The projection
`New.Grading.besselProj` is such a p. -/
lemma exists_besselGroup_proj :
    ∃ p : Y.besselGroup →* G E (1 : X → ℤˣ), Continuous p ∧
      (∀ r : Y.besselGroup, (r : G E ε) * (Y.inclX (p r))⁻¹ ∈ Y.unipotent) ∧
      (∀ a : G E (1 : X → ℤˣ), p ⟨Y.inclX a, Y.inclX_mem_besselGroup a⟩ = a) ∧
      (∀ r : Y.besselGroup, (r : G E ε) ∈ Y.unipotent ↔ p r = 1) ∧
      ∀ r : Y.besselGroup, (r : G E ε) ∈ Y.ratBessel → p r ∈ (stdSpace E X).Γ :=
  ⟨Y.besselProj, Y.continuous_besselProj, Y.mul_inv_inclX_besselProj_mem_unipotent,
    Y.besselProj_inclX, Y.mem_unipotent_iff_besselProj_eq_one,
    fun _ hr ↦ Y.besselProj_mem_Gamma (Subgroup.mem_inf.1 hr).1⟩

/-- Every element of the Bessel group `New.Grading.besselGroup` is a product na with n in the
unipotent group and a in U(X). -/
lemma exists_unipotent_mul_inclX {g : G E ε} (hg : g ∈ Y.besselGroup) :
    ∃ n ∈ Y.unipotent, ∃ a : G E (1 : X → ℤˣ), g = n * Y.inclX a :=
  ⟨_, Y.mul_inv_inclX_besselProj_mem_unipotent ⟨g, hg⟩, Y.besselProj ⟨g, hg⟩,
    (inv_mul_cancel_right g _).symm⟩

end Grading

end New

/-!
## Rational coordinates of finite adelic points; finite Bessel subgroups

Points of the adelic group of a space `V = (J, x)` are matrices preserving
the standard form of signs `ε`;
`V.ratCoordMatrix g = x g x⁻¹` is the matrix in rational coordinates, and `New.Space.xFin` the
finite part of `x`.

* `New.Grading.besselFin`, `New.Grading.inclXFin`: for `V` presented as `X` plus a string
  (`New.Grading`), the finite parts of the Bessel subgroup `New.Grading.besselGroup` and of the
  embedding `New.Grading.inclX` of `U(X)`.
-/

section FiniteBesselGroup

open Matrix RingHom New Space

variable {E X ι : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
  {ε : ι → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} (Y : Grading V N X s)

namespace New.Space

/-- For g in G_f, the matrix x_f g x_f⁻¹ of g in rational coordinates. -/
def ratCoordMatrixFin (g : Gf E ι) : Matrix ι ι (𝔸f E) := V.xFin.val * g * V.xFin⁻¹

lemma ratCoordMatrix_eq (g : G E ε) : V.ratCoordMatrix g = V.x * g.adeleMatrix * V.x⁻¹ := rfl

/-- The finite part of the matrix of g in rational coordinates is the matrix of the finite component
of g in rational coordinates. -/
lemma ratCoordMatrixFin_snd (g : G E ε) :
    V.ratCoordMatrixFin g.2 =
      (V.ratCoordMatrix g).map (snd (NumberField.InfinitePlace E → ℂ) (𝔸f E)) := by
  simp_rw [ratCoordMatrix_eq, Matrix.map_mul]
  rfl

/-- For g in G_f, the matrix of (1, g) in rational coordinates is the identity at the infinite
places and `V.ratCoordMatrixFin g` at the finite places. -/
lemma ratCoordMatrix_inr (g : Gf E ι) (a b : ι) :
    V.ratCoordMatrix (1, g) a b =
      ((1 : Matrix ι ι (NumberField.InfinitePlace E → ℂ)) a b, V.ratCoordMatrixFin g a b) := by
  -- The finite part is `ratCoordMatrixFin_snd`; the infinite part is that of `V.x * V.x⁻¹ = 1`.
  have h_inf : ((V.x.1 * V.x⁻¹.1) a b).1 = ((1 : Matrix ι ι (𝔸 E)) a b).1 := by rw [V.x.mul_inv]
  refine Prod.ext ?_ (by simp [ratCoordMatrixFin_snd (1, g)])
  simpa [ratCoordMatrix_eq, mul_apply, Prod.fst_sum, funext_iff, apply_ite,
    Matrix.one_apply] using h_inf

/-- The finite part x_f of the point of a space (J, x) satisfies x_fᴴ J x_f = 1 over the finite
adeles, to which J is mapped entrywise. This is the finite part of `V.gram_point`. -/
lemma gram_xFin : V.xFin.valᴴ * V.J.map ((↑) : E → 𝔸f E) * V.xFin.val = 1 := by
  -- `using!` identifies the map E → 𝔸_f with the finite component of `toAdele`.
  simpa [stdForm, -coe_snd] using!
    congr_arg (Matrix.map · (snd (NumberField.InfinitePlace E → ℂ) (𝔸f E))) V.gram_point

end Space

namespace Grading

/-- The finite points `g` such that `(1, g)` lies in the Bessel subgroup `Y.besselGroup`. -/
def besselFin : Subgroup (Gf E ι) := Y.besselGroup.comap (MonoidHom.inr (GInf E ε) (Gf E ι))

/-- The embedding of the finite points of `U(X)` in those of `U(V)`: the finite component of
`Y.inclX (1, h)`. -/
def inclXFin : Gf E X →* Gf E ι :=
  (MonoidHom.snd (GInf E ε) (Gf E ι)).comp (Y.inclX.comp (MonoidHom.inr (GInf E 1) (Gf E X)))

/-- In rational coordinates the matrix of `inclXFin h` is `h` on `X` and the identity on the
string. -/
lemma ratCoordMatrixFin_inclXFin (h : Gf E X) :
    V.ratCoordMatrixFin (Y.inclXFin h) = gradedBlocks Y.indexEquiv Y.indexEquiv h 1 :=
  ext (by simp [reindex_equiv Y.indexEquiv, apply_ite, inclXFin, ratCoordMatrixFin_snd,
    ratCoordMatrix_inclX, Matrix.one_apply])

lemma inclX_inr (h : Gf E X) : Y.inclX (1, h) = (1, Y.inclXFin h) := by
  -- Compare the matrices in rational coordinates, block by block along `Y.indexEquiv`.
  refine V.isEmbedding_ratCoordMatrix.injective (ext ?_)
  simp [reindex_equiv Y.indexEquiv, ratCoordMatrix_inclX, inclXFin, ratCoordMatrix_inr,
    Matrix.one_apply, ratCoordMatrixFin_snd]
  aesop

omit [Fintype X] in
lemma snd_mem_besselFin {g : G E ε} (hg : g ∈ Y.besselGroup) : g.2 ∈ Y.besselFin := by
  -- The matrix of `(1, g.2)` is the identity at infinity and the finite part of that of `g`.
  refine Y.mem_besselGroup.2 fun i k h_string h_nonneg hik ↦ ?_
  rw [MonoidHom.inr_apply, ratCoordMatrix_inr, ratCoordMatrixFin_snd, map_apply,
    Y.mem_besselGroup.1 hg i k h_string h_nonneg hik]
  obtain rfl | h_eq := eq_or_ne i k <;> simp [*]

/-- The finite Bessel subgroup is closed. -/
instance : IsClosed (Y.besselFin : Set (Gf E ι)) :=
  Y.isClosed_besselGroup.preimage_of_continuous (f := fun g ↦ (1, g))

end Grading

end New

end FiniteBesselGroup

/-!
## c_λ on U(J) through a frame

The matrix coefficient c_λ = `New.HCParam.dsCoeff` (`l = 2λ`) of a discrete series is defined on
the unitary group `New.USign ε` of the diagonal form with signs `ε`. Let `J` be a hermitian
involution and `p` a frame (`New.DiscreteSeries.SignFrame J ε`), that is, an invertible matrix with
`pᴴ J p = diag ε`.
-/

namespace New

open DiscreteSeries Matrix MeasureTheory

variable {n : Type _} [Fintype n] [DecidableEq n]

/-- A frame for the complex matrix J with signs ε: an invertible matrix p (the field `matrix`) with
pᴴJp = diag(ε). -/
class DiscreteSeries.SignFrame (J : outParam (Matrix n n ℂ)) (ε : outParam (n → ℤˣ)) where
  /-- The invertible matrix p of the frame. -/
  matrix : GL n ℂ
  /-- The matrix p satisfies pᴴJp = diag(ε). -/
  gram_eq : matrix.1ᴴ * J * matrix.1 = signMatrix ε

variable {ε : n → ℤˣ} {A : ℕ} {J : Matrix n n ℂ}
  {l : HCParam (n := n) ε} [p : SignFrame J ε] [IsHermitianInvolution J]

/-- The isomorphism of topological groups U(J) → U(diag ε), g ↦ p⁻¹gp, for the frame p of
`New.DiscreteSeries.SignFrame J ε`, so that pᴴJp = diag(ε). -/
def DiscreteSeries.frameEquiv : U J ≃ₜ* USign ε :=
  ContinuousMulEquiv.mk (U.conj p.matrix p.gram_eq).symm

/-- The function g ↦ c_λ(p⁻¹gp) on U(J), for l = 2λ and the frame p of
`New.DiscreteSeries.SignFrame J ε`, so that pᴴJp = diag(ε). -/
def HCParam.dsCoeffInFrame (l : HCParam ε) (g : U J) : ℂ := l.dsCoeff (frameEquiv g)

omit [IsHermitianInvolution J] in
@[fun_prop]
theorem continuous_dsCoeffInFrame : Continuous l.dsCoeffInFrame := by
  fun_prop [HCParam.dsCoeffInFrame]

/-- The isomorphism g ↦ P⁻¹gP from U(J) to U(diag ε), for the matrix P of a frame, carries the
measure `New.haarU` of U(J), which is the `volume` there, to that of U(diag ε). -/
lemma DiscreteSeries.measurePreserving_frameEquiv : MeasurePreserving (frameEquiv (p := p)) :=
  -- the bijection is g ↦ p⁻¹ g p by definition, and it scales the form by 1
  measurePreserving_haarU p.matrix⁻¹ p.matrix 1 _ (by simp [p.gram_eq]) (fun _ ↦ rfl)

/-- The integral over U(J) of f(p⁻¹gp), for the frame p, is the integral of f over U(diag ε). -/
theorem DiscreteSeries.integral_comp_frameEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : USign ε → E) : ∫ g : U J, f (frameEquiv g) = ∫ g : USign ε, f g :=
  measurePreserving_frameEquiv.integral_comp frameEquiv.measurableEmbedding _

/-- If l = 2λ is a parameter with gap 500n³+A, J is a hermitian involution and pᴴJp = diag(ε), the
function deg_λ c_λ (formal degree times coefficient), carried to U(J) by the frame p, is an
idempotent kernel on U(J): continuous, integrable, self-adjoint, nonzero at 1 and reproducing
under convolution. -/
theorem isIdempotentKernel_dsCoeffInFrame [Nonempty n] (hl_gap : l.HasLargeGap A) :
    IsIdempotentKernel fun g : U J ↦ l.formalDegree * l.dsCoeffInFrame g := by
  -- The kernel of `-l` is `l.formalDegree * l.dsCoeff`, the complex conjugate of that of `l`; carry
  -- it over to `U J` along the measure preserving isomorphism `frameEquiv`.
  have h_kernel : IsIdempotentKernel (-l).dsKernel :=
    HCParam.HasLargeGap.isIdempotentKernel_dsKernel hl_gap.neg
  have h_pullback : IsIdempotentKernel fun g : U J ↦ (-l).dsKernel (frameEquiv g) :=
    { continuous := by fun_prop
      integrable := measurePreserving_frameEquiv.integrable_comp_of_integrable h_kernel.integrable
      apply_inv g := by simp [← h_kernel.apply_inv]
      apply_one_ne_zero := by simp [h_kernel.apply_one_ne_zero]
      convolution_eq x y := by simp [← h_kernel.convolution_eq, ← integral_comp_frameEquiv] }
  simpa [dsKernel, HCParam.formalDegree, HCParam.dsCoeffInFrame] using h_pullback

end New

/-! ## Degree of T, invariance under the Bessel subgroups, and T†T -/

namespace New.Grading

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι'] [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
  {s : ℕ} {ε : ι → ℤˣ} {ε' : ι' → ℤˣ} {N : E} {V : Space E ι ε} {V' : Space E ι' ε'}
  (Y : Grading V N X s) {Y' : Grading V' N X' (s - 1)}

omit [Fintype X] [Fintype X'] in
/-- For s' = s − 1, the map T = `New.Grading.stringMap` lowers weights by at most 1. -/
lemma hasDegreeGe_neg_one_stringMap : HasDegreeGe Y'.gradeOf Y.gradeOf (-1) (Y.stringMap Y') := by
  -- The only entries of T are between string vectors with the same number a, of weights
  -- s - 1 - 2 a and s - 2 - 2 a.
  simp [reindex_equiv Y.indexEquiv, reindex_equiv Y'.indexEquiv, HasDegreeGe, stringMap]
  lia

/-- Let s' = s − 1. For g in `New.Grading.besselGroup` of Y and δ in that of Y', the map δTg − T has
degree at least 0, where T = `New.Grading.stringMap` and δ, g are read in rational coordinates. -/
lemma hasDegreeGe_zero_mul_stringMap_mul_sub {g : G E ε} {δ : G E ε'}
    (hg : g ∈ Y.besselGroup) (hδ : δ ∈ Y'.besselGroup) :
    HasDegreeGe Y'.gradeOf Y.gradeOf 0
      (V'.ratCoordMatrix δ * (Y.stringMap Y' * V.ratCoordMatrix g) - Y.stringMap Y') := by
  -- δTg - T = (δ - 1)Tg + T(g - 1). Here T lowers weights by at most 1 and links only the strings,
  -- and a string entry of δ - 1 or g - 1 raises weights by at least 1.
  set T : Matrix ι' ι (𝔸 E) := Y.stringMap Y'
  have hT : HasDegreeGe Y'.gradeOf Y.gradeOf (-1) T := Y.hasDegreeGe_neg_one_stringMap
  have hT_string (b : ι') (a : ι) (h_ne : T b a ≠ 0) :
      (Y'.indexEquiv.symm b).isRight ∧ (Y.indexEquiv.symm a).isRight := by
    obtain ⟨x | b, rfl⟩ := Y'.indexEquiv.surjective b <;>
      obtain ⟨y | a, rfl⟩ := Y.indexEquiv.surjective a <;> simp_all [T, stringMap]
  have h_left : HasDegreeGe Y'.gradeOf Y.gradeOf 0 ((V'.ratCoordMatrix δ - 1) * T) := by
    refine fun b a hlt ↦ Finset.sum_eq_zero fun y _ ↦ by_contra fun h_ne ↦ ?_
    have hy : Y'.gradeOf b ≤ Y'.gradeOf y := by grind [HasDegreeGe]
    simp_all [Y'.mem_besselGroup_iff.1 hδ b y hy
      (.inr (hT_string y a (right_ne_zero_of_mul h_ne)).1)]
  have h_right : HasDegreeGe Y'.gradeOf Y.gradeOf 0 (T * (V.ratCoordMatrix g - 1)) := by
    refine fun b a hlt ↦ Finset.sum_eq_zero fun z _ ↦ by_contra fun h_ne ↦ ?_
    have hz : Y.gradeOf z ≤ Y.gradeOf a := by grind [HasDegreeGe]
    simp_all [Y.mem_besselGroup_iff.1 hg z a hz (.inl (hT_string b z (left_ne_zero_of_mul h_ne)).2)]
  have h_split : V'.ratCoordMatrix δ * (T * V.ratCoordMatrix g) - T =
      (V'.ratCoordMatrix δ - 1) * T * V.ratCoordMatrix g + T * (V.ratCoordMatrix g - 1) := by
    simp [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  intro b a hlt
  rw [h_split, Matrix.add_apply, h_right b a hlt,
    h_left.mul (Y.hasDegreeGe_zero_of_mem_besselGroup hg) (zero_add 0).ge b a hlt, add_zero]

/-- Let `s' = s - 1` and `T = Y.stringMap Y'`. The adjoint `T†` of `T` for the two forms kills `X'`
and sends the string vector `b` of `Y'` to a multiple of the string vector `a = b + 1` of `Y`. For
`s` odd the factor is `c` or `1` when the weight of `a` is nonnegative or negative. For `s` even
it is `1`, `-N c`, `c` when the weight of `a` is positive, `-1`, less than `-1`. -/
lemma formAdjoint_stringMap :
    V.formAdjoint V' (Y.stringMap Y') =
      (gradedBlocks Y.indexEquiv Y'.indexEquiv 0
        (Matrix.of fun (a : Fin s) (b : Fin (s - 1)) ↦
          if a.val = b + 1 then
            (if Odd s ↔ s < 2 * a + 1 then 1 else (Y.genericConst : E)) *
              (if 2 * a = s then -N else 1)
          else 0)).map toAdele := by
  -- The entry `(a, b)` is the entry of `T` at the dual indices `s - 2 - b` and `s - 1 - a`, times
  -- an entry of `J⁻¹` and one of `J'`; conjugation fixes `N` and `c`.
  obtain ⟨hN_ne, hN_star⟩ := Y.N_ne_zero_and_star_eq
  have hc_star : star (Y.genericConst : E) = Y.genericConst := Y.genericConst.2.2
  ext i k : 1
  simp only [Y.formAdjoint_apply Y', stringMap, Matrix.map_apply, star_toAdele, ← map_mul]
  -- It remains to compare the rational entries; only those between two string vectors are nonzero.
  refine congrArg toAdele ?_
  obtain ⟨x | a, rfl⟩ := Y.indexEquiv.surjective i <;>
    obtain ⟨y | b, rfl⟩ := Y'.indexEquiv.surjective k <;>
    simp [stringReversal, gradedGram, apply_ite star, hN_star, hc_star]
  grind

/-- Let `T = Y.stringMap Y'`, where `Y'` has a string of length `s - 1`. `T` is the rational map
`V → V'` that kills `X` and sends each string vector of `Y` to a multiple of the one of `Y'` with
the same number (`0` if none). Let `T†` be its adjoint for the two forms. Then `T† T` is `Y.shift`,
the map that kills `X` and the last string vector and moves each other string vector of `Y` to a
multiple of the next one. -/
lemma formAdjoint_stringMap_mul_stringMap_eq_shift :
    V.formAdjoint V' (Y.stringMap Y') * Y.stringMap Y' = Y.shift := by
  -- `T` keeps the number of a string vector and `T†` raises it by one; the factors multiply.
  have h_factor (a b : ℕ) (hab : a = b + 1) :
      (if Odd s ↔ s < 2 * a + 1 then 1 else (Y.genericConst : E)) * (if 2 * a = s then -N else 1) *
          ((if Odd s ↔ 2 * b + 1 < s then 1 else (Y.genericConst : E)) *
            (if 2 * b + 1 = s then -N else 1)) =
        Y.genericConst * (if 2 * b + 1 = s then -N else if 2 * a = s then -N * Y.genericConst else
          1) := by
    grind
  rw [formAdjoint_stringMap, stringMap, shift, ← Matrix.map_mul, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 3
  ext a b
  by_cases hb : b.val < s - 1
  · rw [Matrix.mul_apply, Fintype.sum_eq_single ⟨b, hb⟩ (by simp +contextual [Fin.ext_iff])]
    by_cases hab : a.val = b + 1
    · simpa [hab] using h_factor a b hab
    · simp [hab]
  · -- the last string vector is killed by both sides
    have h_ne (k : Fin (s - 1)) : k.val ≠ b := by omega
    simp [Matrix.mul_apply, h_ne, show a.val ≠ b + 1 by omega]

/-- Let `s' = s - 1`, `T = Y.stringMap Y'` and let `T†` be its adjoint for the two forms. If `Y` and
`Y'` have the same constant of the generic character, `Y'.genericConst = Y.genericConst`, then
`T T†` is the shift `Y'.shift` of `Y'`. -/
lemma stringMap_mul_formAdjoint_stringMap_eq_shift (hc : Y'.genericConst = Y.genericConst) :
    Y.stringMap Y' * V.formAdjoint V' (Y.stringMap Y') = Y'.shift := by
  -- `T†` raises the number of a string vector by one and `T` keeps it; the factors multiply.
  have h_factor (a b : ℕ) (hab : a = b + 1) (ha : a < s) :
      (if Odd s ↔ 2 * a + 1 < s then 1 else (Y.genericConst : E)) *
        (if 2 * a + 1 = s then -N else 1) *
          ((if Odd s ↔ s < 2 * a + 1 then 1 else (Y.genericConst : E)) *
            (if 2 * a = s then -N else 1)) =
        Y.genericConst * (if 2 * b + 1 = s - 1 then -N else if 2 * a = s - 1 then -N *
          Y.genericConst else 1) := by
    grind
  rw [formAdjoint_stringMap, stringMap, shift, hc, ← Matrix.map_mul, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 3
  ext a b
  rw [Matrix.mul_apply,
    Fintype.sum_eq_single ⟨b + 1, by omega⟩ (by simp +contextual [Fin.ext_iff])]
  by_cases hab : a.val = b + 1
  · simpa [hab] using h_factor a b hab (by omega)
  · simp [hab]

/-- Let `Y` present `V` as `X ⊕ J_s` and `Y'` present `V'` as `X' ⊕ J_{s-1}` with the same `N`, each
carrying a constant `c = c̄ ≠ 0`. Let `T = Y.stringMap Y'` be the map `V → V'` that kills `X` and
sends the string vector `a` to `t a` times the string vector of `Y'` with the same number (to `0` if
there is none), where `t a` depends on the parity of `s`, the weight of `a`, `c` and `N`, and let
`T†` be its adjoint for the two hermitian forms. (a) `T† T` is `Y.shift`, the map that kills `X` and
the last string vector and sends each string vector `b` to `-N c`, `-N c²` or `c` times the vector
`b + 1`, according as `b` has weight `0`, `1` or another weight; (b) if
`Y'.genericConst = Y.genericConst`, then `T T†` is the shift `Y'.shift` of `Y'`. -/
lemma formAdjoint_stringMap_mul_stringMap :
    V.formAdjoint V' (Y.stringMap Y') * Y.stringMap Y' = Y.shift ∧
    (Y'.genericConst = Y.genericConst → Y.stringMap Y' * V.formAdjoint V' (Y.stringMap Y') =
      Y'.shift) :=
  ⟨Y.formAdjoint_stringMap_mul_stringMap_eq_shift, Y.stringMap_mul_formAdjoint_stringMap_eq_shift⟩

end New.Grading

end
