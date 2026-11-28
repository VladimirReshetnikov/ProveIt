import Lib.Adelic.Adeles.LocalFactors
import Lib.General.LinearAlgebra.IdempotentRadical
import Lib.Weil.Unramified.HeckeGL

/-!
# Test functions and the two local conditions of the comparison of traces

Test functions on a topological group, their translates, and the function `a ⋆ 1_K` of an element
`a` of the group algebra. On the finite adelic group the comparison of traces asks for two
conditions: the test function is cuspidal at a split place (`IsCuspidalAt`), and at a second place
the components of the elements of its support are integral with a simple eigenvalue zero modulo the
place. `HasSimpleZero` is this last property of one matrix over the completion at the place.

Notions from other files:
* `Gf E n`: the group of finite adelic points of the unitary group of the `n × n` identity matrix;
* `LocField w`, `LocInt w`, `ResField w`, `localIntGL n w`: the completion at a finite place `w`,
  its ring of integers, its residue field, and `GL_n` of that ring inside `GL_n` of the completion;
* `ofSplitPlace hw`: at a split place `w`, the map from `GL_n` of the completion at `w` to `Gf E n`;
* `radicalHom`: for an idempotent `ε`, the homomorphism `Y ↦ 1 + ε Y (1 - ε)` onto the unipotent
  radical of the parabolic subgroup that keeps the image of `ε`.

## Relation to the literature

Known; see `Lib.Adelic.TraceFormula.TraceComparison` for sources.
-/

open NumberField Polynomial Matrix Finset IsLocalRing Multiplicative

namespace New

section Group

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

/-- The space of test functions on `G`: the locally constant complex functions of compact
support. -/
abbrev TestFunction (G : Type) [TopologicalSpace G] : Submodule ℂ (G → ℂ) :=
  schwartzBruhat (Set.univ : Set G)

/-- The composite of a test function with `x ↦ a⁻¹ * x * b` is again a test function. -/
lemma TestFunction.comp_mul_mem {f : G → ℂ} (hf : f ∈ TestFunction G) (a b : G) :
    (f ∘ fun x : G ↦ a⁻¹ * x * b) ∈ TestFunction G :=
  schwartzBruhat.comp hf (fun x : G ↦ a * (x * b⁻¹)) (fun x ↦ by group) (Set.mapsTo_univ _ _)

/-- Left and right translation of test functions: `(a, b)` takes `f` to `x ↦ f (a⁻¹ * x * b)`. -/
def TestFunction.translate : Representation ℂ (G × G) (TestFunction G) where
  toFun g := (LinearMap.funLeft ℂ ℂ fun x : G ↦ g.1⁻¹ * x * g.2).restrict
    fun _ hf ↦ TestFunction.comp_mul_mem hf g.1 g.2
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_assoc]

/-- The translate of `f` by the pair `g = (a, b)` takes `x` to `f (a⁻¹ * x * b)`. -/
@[simp] lemma TestFunction.translate_apply (g : G × G) (f : TestFunction G) (x : G) :
    (translate g f : G → ℂ) x = (f : G → ℂ) (g.1⁻¹ * x * g.2) := rfl

/-- The characteristic function of a compact open subgroup. -/
noncomputable def TestFunction.indicator {K : Subgroup G} (hK_open : IsOpen (K : Set G))
    (hK_compact : IsCompact (K : Set G)) : TestFunction G :=
  ⟨Set.indicator K 1,
    (LocallyConstant.indicator 1 ⟨K.isClosed_of_isOpen hK_open, hK_open⟩).isLocallyConstant,
    HasCompactSupport.intro hK_compact fun _ hx ↦ Set.indicator_of_notMem hx _, Set.subset_univ _⟩

/-- The linear map `a ↦ a ⋆ 1_K` from the group algebra to the test functions, for a compact open
subgroup `K`: the group element `b` goes to the characteristic function of the coset `b K`. -/
noncomputable def convIndicator {K : Subgroup G} (hK_open : IsOpen (K : Set G))
    (hK_compact : IsCompact (K : Set G)) : MonoidAlgebra ℂ G →ₗ[ℂ] TestFunction G :=
  (Representation.asAlgebraHom (TestFunction.translate.comp (.inl G G))).toLinearMap.flip
    (TestFunction.indicator hK_open hK_compact)

open scoped Classical in
/-- For a compact open subgroup `K`, a group element `b` and a scalar `c`, the test function
`(c b) ⋆ 1_K` given by `convIndicator` is `c` on the coset `b K` and zero elsewhere. -/
lemma convIndicator_single {K : Subgroup G} (hK_open : IsOpen (K : Set G))
    (hK_compact : IsCompact (K : Set G)) (b : G) (c : ℂ) (x : G) :
    (convIndicator hK_open hK_compact (.single b c) : G → ℂ) x =
      if b⁻¹ * x ∈ K then c else 0 := by
  simp [convIndicator, TestFunction.indicator, Set.indicator_apply]

/-- For a compact open subgroup `K` and an element `a` of the group algebra, write `a ⋆ 1_K` for
the test function given by `convIndicator`. Then `(c b * a) ⋆ 1_K` is `c` times the left translate
of `a ⋆ 1_K` by the group element `b`. -/
lemma convIndicator_single_mul {K : Subgroup G} (hK_open : IsOpen (K : Set G))
    (hK_compact : IsCompact (K : Set G)) (b : G) (c : ℂ) (a : MonoidAlgebra ℂ G) (x : G) :
    (convIndicator hK_open hK_compact (.single b c * a) : G → ℂ) x =
      c * (convIndicator hK_open hK_compact a : G → ℂ) (b⁻¹ * x) := by
  simp [convIndicator]

/-- The representation of `G × G` on test functions by translation is smooth: each test function is
fixed by all translations near the identity. -/
instance [WeaklyLocallyCompactSpace G] : IsSmoothRep (TestFunction.translate (G := G)) := by
  refine ⟨fun f : TestFunction G ↦ ?_⟩
  have h_const : IsLocallyConstant fun (g : G × G) (x : G) ↦ f.1 (g.1⁻¹ * x * g.2) :=
    schwartzBruhat.isLocallyConstant_curry f.2 (fun (g : G × G) (x : G) ↦ g.1⁻¹ * x * g.2)
      (fun (g : G × G) (x : G) ↦ g.1 * (x * g.2⁻¹)) (fun g x ↦ by group)
  filter_upwards [h_const.eventually_eq 1] with g hg
  ext x
  simpa using congrFun hg x

end Group

section Radical

variable {n k : Type} [Fintype n] [DecidableEq n] [CommRing k] (T : Finset n)

/-- The diagonal projector on the coordinates in `T`. -/
noncomputable def coordProjector : Matrix n n k := diagonal fun i : n ↦ if i ∈ T then 1 else 0

lemma isIdempotentElem_coordProjector : IsIdempotentElem (coordProjector (k := k) T) := by
  simp [IsIdempotentElem, coordProjector, ← ite_and]

/-- A ring homomorphism `f`, applied entrywise, takes the element `1 + ε Z (1 - ε)` of the unipotent
radical (`radicalHom`), with `ε` the diagonal projector on the coordinates in `T`, to the element
attached in the same way to `T` and `f(Z)`. -/
lemma map_radicalHom_coordProjector {k' : Type} [CommRing k'] (f : k →+* k') (Z : Matrix n n k) :
    GeneralLinearGroup.map f (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z)) =
      radicalHom (isIdempotentElem_coordProjector T) (ofAdd (Z.map f)) := by
  ext1
  simp [radicalHom, coordProjector, Matrix.map_add, Matrix.map_sub, apply_ite f]

end Radical

variable {E n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  {w : FinPlace E}

/-- The test function `φ` is cuspidal at the split place `w`. Let `U` be the unipotent radical of a
proper parabolic subgroup of `GL_n(F_w)`, with `F_w` the residue field at `w`, that is cut out by a
set `T` of coordinates. Then every left translate of `φ` has sum zero over each coset `U t`, lifted
to `GL_n(O_w)` and put into the adelic group at `w` by `ofSplitPlace`. In detail, the sum runs over
all matrices `Z` over `F_w`, each with a lift of the element `radicalHom Z * t` of the coset; every
element is met equally often, and every choice of these lifts is allowed. -/
def IsCuspidalAt (hw : w.IsSplit) (φ : TestFunction (Gf E n)) : Prop :=
  ∀ T : Finset n, T ≠ ∅ → T ≠ univ → ∀ (t : GL n (ResField w))
    (lift : Matrix n n (ResField w) → localIntGL n w),
    (∀ Z : Matrix n n (ResField w),
      reduceGL (lift Z) = radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z) * t) →
    ∀ g : Gf E n, ∑ᶠ Z : Matrix n n (ResField w), φ.1 (g * ofSplitPlace hw (lift Z)) = 0

omit [IsCMField E] in
/-- Let `T` be a set of coordinates. Every element `1 + ε Z (1 - ε)` (`radicalHom`, with `ε` the
projector on `T`) over the residue field at `w` is the reduction (`reduceGL`) of an element
`1 + ε Y (1 - ε)` over `E_w` that lies in `localIntGL n w`, the group `GL_n(O_w)`. -/
lemma exists_radicalHom_reduceGL_eq (T : Finset n) (Z : Matrix n n (ResField w)) :
    ∃ (Y : Matrix n n (LocField w)) (hY :
      radicalHom (isIdempotentElem_coordProjector T) (ofAdd Y) ∈ localIntGL n w),
      reduceGL ⟨radicalHom (isIdempotentElem_coordProjector T) (ofAdd Y), hY⟩ =
        radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z) := by
  obtain ⟨Y, rfl⟩ : ∃ Y : Matrix n n (LocInt w), Y.map (residue (LocInt w)) = Z :=
    residue_surjective.comp_left.comp_left Z
  refine ⟨Y.map (LocInt w).subtype, ?_⟩
  rw [← map_radicalHom_coordProjector T (LocInt w).subtype Y]
  refine ⟨⟨radicalHom (isIdempotentElem_coordProjector T) (ofAdd Y), rfl⟩, ?_⟩
  -- the reduction of the image of an integral matrix is computed entrywise
  change GeneralLinearGroup.map (residue (LocInt w))
    (radicalHom (isIdempotentElem_coordProjector T) (ofAdd Y)) = _
  exact map_radicalHom_coordProjector T (residue (LocInt w)) Y

/-- Let the test function `φ` on the finite adelic group `Gf E n` be cuspidal at the split place
`w` and let `T` be a set of coordinates, neither empty nor everything. Then there is a finite
nonempty family `κ` of matrices over `E_w`, written multiplicatively, with the following property:
for every `k` in `GL_n(O_w)`, the right translates of `φ` by the images in `Gf E n` of the products
`(1 + ε (κ i) (1 - ε)) * k` sum to zero over `i`. Here `1 + ε (κ i) (1 - ε)` is `radicalHom` of
`κ i` for the projector `ε` on `T`, and the images are taken under the embedding `ofSplitPlace` at
`w`. -/
lemma IsCuspidalAt.exists_sum_translate_eq_zero {hw : w.IsSplit} {φ : TestFunction (Gf E n)}
    (hφ : IsCuspidalAt hw φ) {T : Finset n} (hT_empty : T ≠ ∅) (hT_univ : T ≠ univ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι)
      (κ : ι → Multiplicative (Matrix n n (LocField w))), ∀ k ∈ localIntGL n w,
      ∑ i : ι, TestFunction.translate
        (1, ofSplitPlace hw (radicalHom (isIdempotentElem_coordProjector T) (κ i) * k)) φ = 0 := by
  -- Take for `κ` one lift of each matrix over the residue field.
  choose Y hY_mem hY using exists_radicalHom_reduceGL_eq (w := w) T
  let _ : Fintype (Matrix n n (ResField w)) := .ofFinite _
  refine ⟨Matrix n n (ResField w), inferInstance, inferInstance, ofAdd ∘ Y,
    fun (k : GL n (LocField w)) (hk : k ∈ localIntGL n w) ↦ ?_⟩
  ext g
  let lift (Z : Matrix n n (ResField w)) : localIntGL n w :=
    ⟨radicalHom (isIdempotentElem_coordProjector T) (ofAdd (Y Z)), hY_mem Z⟩ * ⟨k, hk⟩
  have h_lift (Z : Matrix n n (ResField w)) :
      reduceGL (lift Z) = radicalHom (isIdempotentElem_coordProjector T) (ofAdd Z) * reduceGL
        ⟨k, hk⟩ := by
    rw [← hY Z]
    exact reduceGL.map_mul _ _
  have h_sum : ∑ᶠ Z : Matrix n n (ResField w), φ.1 (g * ofSplitPlace hw (lift Z)) = 0 :=
    hφ T hT_empty hT_univ _ lift h_lift g
  simpa [lift, finsum_eq_sum_of_fintype] using h_sum

/-- Let `K` be a compact open subgroup of the finite adelic group `Gf E n` and `a`, `b` elements of
its group algebra. If the test function `a ⋆ 1_K` (`convIndicator`) is cuspidal at the split place
`w` (`IsCuspidalAt`: zero sums over the cosets of unipotent radicals modulo `w`), then so is
`(b * a) ⋆ 1_K`. -/
lemma IsCuspidalAt.convIndicator_mul {hw : w.IsSplit} {K : Subgroup (Gf E n)}
    {hK_open : IsOpen (K : Set (Gf E n))} {hK_compact : IsCompact (K : Set (Gf E n))}
    {a : MonoidAlgebra ℂ (Gf E n)} (ha : IsCuspidalAt hw (convIndicator hK_open hK_compact a))
    (b : MonoidAlgebra ℂ (Gf E n)) :
    IsCuspidalAt hw (convIndicator hK_open hK_compact (b * a)) := by
  intro T hT_empty hT_univ t lift h_lift g
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b b' hb hb' =>
    simp [add_mul, finsum_add_distrib (Set.toFinite _) (Set.toFinite _), hb, hb']
  | single x c =>
    simp [convIndicator_single_mul, ← mul_assoc, ← mul_finsum,
      ha T hT_empty hT_univ t lift h_lift (x⁻¹ * g)]

/-- The matrix `g` has entries in `O_w`, and `0` is a simple root of its characteristic polynomial
modulo `w`. -/
def HasSimpleZero (g : GL n (LocField w)) : Prop :=
  (∀ i j : n, Valued.v (g i j) ≤ 1) ∧ (g.1.map residueOrZero).charpoly.rootMultiplicity 0 = 1

/-- If a monic polynomial over an integrally closed domain is a `j`-th power over the fraction
field, with `j ≠ 0`, then it is the `j`-th power of a polynomial over the domain. -/
lemma exists_eq_pow_of_monic_of_map_eq_pow {R K : Type} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {p : R[X]}
    (hp : p.Monic) {Q : K[X]} {j : ℕ} (hj : j ≠ 0) (h_map : p.map (algebraMap R K) = Q ^ j) :
    ∃ P : R[X], p = P ^ j := by
  -- Up to its leading coefficient `Q` is integral, as it divides a monic integral polynomial.
  obtain ⟨P, hP⟩ : ∃ P : R[X], P.map (algebraMap R K) * C Q.leadingCoeff = Q :=
    IsIntegrallyClosed.eq_map_mul_C_of_dvd K hp (by simp [h_map, dvd_pow_self Q hj])
  have h_lead : Q.leadingCoeff ^ j = 1 := by
    rw [← leadingCoeff_pow, ← h_map, (hp.map _).leadingCoeff]
  refine ⟨P, Polynomial.map_injective _ (IsFractionRing.injective R K) ?_⟩
  rw [h_map, ← hP, mul_pow, ← C_pow, h_lead, C_1, mul_one, Polynomial.map_pow]

omit [IsCMField E] in
/-- If the matrix `g` has entries in `O_w` and `0` is a simple root of its characteristic polynomial
modulo `w` (`HasSimpleZero g`), then the characteristic polynomial of `g` over `E_w` itself is no
`j`-th power for `j > 1`. -/
lemma HasSimpleZero.charpoly_ne_pow {g : GL n (LocField w)} (hg : HasSimpleZero g)
    (Q : (LocField w)[X]) {j : ℕ} (hj : 1 < j) : g.1.charpoly ≠ Q ^ j := by
  classical
  intro h_pow
  obtain ⟨h_int, h_simple⟩ : (∀ a b : n, Valued.v (g a b) ≤ 1) ∧
      (g.1.map residueOrZero).charpoly.rootMultiplicity 0 = 1 := hg
  let M : Matrix n n (LocInt w) := of fun a b : n ↦ ⟨g a b, h_int a b⟩
  have h_red : g.1.map residueOrZero = M.map (residue (LocInt w)) :=
    Matrix.ext fun a b : n ↦ residueOrZero_coe (M a b)
  have h_map : M.charpoly.map (algebraMap (LocInt w) (LocField w)) = Q ^ j := by
    rw [← charpoly_map, show M.map (algebraMap (LocInt w) (LocField w)) = g.1 from rfl, h_pow]
  obtain ⟨P, h_pow_int⟩ : ∃ P : (LocInt w)[X], M.charpoly = P ^ j :=
    exists_eq_pow_of_monic_of_map_eq_pow M.charpoly_monic (by omega) h_map
  -- Modulo `w` every root of `P ^ j` has multiplicity divisible by `j`.
  have h_count : j * (P.map (residue (LocInt w))).roots.count 0 = 1 := by
    rw [← Multiset.count_nsmul, ← roots_pow, ← Polynomial.map_pow, ← h_pow_int, count_roots,
      ← charpoly_map, ← h_red, h_simple]
  exact hj.ne' (Nat.eq_one_of_mul_eq_one_right h_count)

end New
