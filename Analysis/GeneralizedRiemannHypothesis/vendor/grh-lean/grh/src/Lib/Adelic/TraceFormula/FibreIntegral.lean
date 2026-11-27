import Lib.Adelic.TraceFormula.TestFunction
import Lib.DiscreteSeries.Haar.CayleyChart

/-!
# Integration over the fibres of a conjugation map

A group `Γ` acts on a group `G` by conjugation through `j : Γ → G`. Let `X` be a slice of a closed
set `C ⊆ G` (`IsSlice`): the map `(g, y) ↦ g y g⁻¹` from `Γ × X` onto `C` is open in the sense of
`IsSlice.eventually_exists_conj_mem`, and its fibres are the orbits of a closed subgroup `H` of `Γ`.
The file proves two steps of the descent of invariant distributions from `C` to `X`.

* Step 1, images. Integration over the fibres takes a test function `Ψ` on `Γ × G` to a test
  function on `C`. A test function on `G` that extends it is an image of `Ψ` (`IsImage`), and one
  exists (`IsSlice.exists_isImage`).
* Step 2, Haar measure. An invariant distribution on `C` kills the image of `Ψ` as soon as the
  integrals of `Ψ (·, y)` over `Γ` vanish for all `y ∈ X`
  (`IsInvariantDistribution.eq_zero_of_isImage`).

Functions on `Γ × X` and on `C` are handled as restrictions of test functions on `Γ × G` and on `G`.

Notions from other files:
* `TestFunction G`: the locally constant functions of compact support from `G` to `ℂ`.
* `TestFunction.translate (a, b) f`: the test function `x ↦ f (a⁻¹ * x * b)`.
* `compactMean ρ L x`: the mean of the orbit of the vector `x` under a compact subgroup `L`.

## Relation to the literature

Known result: descent of invariant distributions to a slice, after Harish-Chandra.
-/

open Set Topology Filter MeasureTheory Pointwise

namespace New
/-! ### Conjugation of test functions -/

variable {G Γ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [Group Γ] [TopologicalSpace Γ]

/-- The action of `Γ` on the test functions on `G` by conjugation through `j : Γ → G`. -/
def TestFunction.conjugate (j : Γ →ₜ* G) : Representation ℂ Γ (TestFunction G) :=
  TestFunction.translate.comp (j.toMonoidHom.prod j.toMonoidHom)

/-- The conjugate of the test function `f` by `g ∈ Γ` through `j : Γ → G` takes the value
`f ((j g)⁻¹ * x * j g)` at `x`. -/
lemma TestFunction.conjugate_apply (j : Γ →ₜ* G) (g : Γ) (f : TestFunction G) (x : G) :
    (conjugate j g f).1 x = f.1 ((j g)⁻¹ * x * j g) := rfl

/-- The action of `Γ` on the test functions on `G` by conjugation through `j` is smooth: every test
function is fixed by the elements of a neighbourhood of `1`. -/
instance TestFunction.isSmoothRep_conjugate [WeaklyLocallyCompactSpace G] (j : Γ →ₜ* G) :
    IsSmoothRep (conjugate j) where
  eventually_fixed f :=
    ((j.continuous.prodMk j.continuous).tendsto' 1 1 (Prod.ext (map_one j) (map_one j))).eventually
      (IsSmoothRep.eventually_fixed (ρ := TestFunction.translate) f)

/-! ### Test functions on products and on closed subsets -/

section Space

variable {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]

/-- The value of a test function at a point, as a linear form. -/
def TestFunction.eval (x : Y) : TestFunction Y →ₗ[ℂ] ℂ :=
  (LinearMap.proj x).comp (TestFunction Y).subtype

lemma TestFunction.eval_apply (x : Y) (f : TestFunction Y) : eval x f = f.1 x := rfl
lemma TestFunction.isLocallyConstant (f : TestFunction Y) : IsLocallyConstant f.1 :=
  f.2.1

lemma TestFunction.hasCompactSupport (f : TestFunction Y) : HasCompactSupport f.1 :=
  f.2.2.1

/-- A test function is integrable for every measure that is finite on compact sets. -/
lemma TestFunction.integrable [MeasurableSpace Y] [OpensMeasurableSpace Y] (f : TestFunction Y)
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] : Integrable f.1 μ :=
  (isLocallyConstant f).continuous.integrable_of_hasCompactSupport (hasCompactSupport f)

variable [T2Space Y] [T2Space Z]

/-- The product `(y, z) ↦ a y * b z` of two test functions. -/
def TestFunction.tensor (a : TestFunction Y) (b : TestFunction Z) : TestFunction (Y × Z) :=
  ⟨fun p : Y × Z ↦ a.1 p.1 * b.1 p.2,
    ((isLocallyConstant a).comp_continuous continuous_fst).mul
      ((isLocallyConstant b).comp_continuous continuous_snd),
    HasCompactSupport.intro ((hasCompactSupport a).isCompact.prod (hasCompactSupport b).isCompact)
      fun p hp ↦ by
      rcases not_and_or.1 hp with ha | hb
      · rw [image_eq_zero_of_notMem_tsupport ha, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hb, mul_zero],
    subset_univ _⟩

/-- The product of the test functions `a` and `b` takes the value `a y * b z` at `(y, z)`. -/
lemma TestFunction.tensor_apply (a : TestFunction Y) (b : TestFunction Z) (y : Y) (z : Z) :
    (tensor a b).1 (y, z) = a.1 y * b.1 z := rfl

/-- The test function `z ↦ Ψ (y, z)`. -/
def TestFunction.partialApply (Ψ : TestFunction (Y × Z)) (y : Y) : TestFunction Z :=
  ⟨fun z : Z ↦ Ψ.1 (y, z),
    schwartzBruhat.comp Ψ.2 Prod.snd (fun _ ↦ rfl) (mapsTo_univ _ _) (by fun_prop) continuous_snd⟩

/-- For a test function `Ψ` on `Y × Z`, the function `y ↦ Ψ (y, z)` is integrable for every measure
that is finite on compact sets. -/
lemma TestFunction.integrable_prodMk_left [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (Ψ : TestFunction (Y × Z)) (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] (z : Z) :
    Integrable (fun y : Y ↦ Ψ.1 (y, z)) μ :=
  TestFunction.integrable ⟨fun y : Y ↦ Ψ.1 (y, z),
    schwartzBruhat.comp Ψ.2 Prod.fst (fun _ ↦ rfl) (mapsTo_univ _ _) (by fun_prop) continuous_fst⟩ μ

/-- The characteristic function of a compact open set. -/
noncomputable def TestFunction.setIndicator {V : Set Y} (hV_open : IsOpen V)
    (hV_compact : IsCompact V) : TestFunction Y :=
  ⟨V.indicator 1,
    (LocallyConstant.indicator 1 ⟨hV_compact.isClosed, hV_open⟩).isLocallyConstant,
    HasCompactSupport.intro hV_compact fun _ hy ↦ indicator_of_notMem hy _, subset_univ _⟩

/-- The characteristic function of `V`, as a test function, is `V.indicator 1`. -/
lemma TestFunction.setIndicator_apply {V : Set Y} (hV_open : IsOpen V) (hV_compact : IsCompact V)
    (y : Y) : (setIndicator hV_open hV_compact).1 y = V.indicator 1 y := rfl

end Space

section Extension

/-- In a locally compact non-archimedean group, a compact open set lies between any compact set and
any open set containing it. -/
lemma exists_isCompact_isOpen_superset_subset {G : Type} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G] {S U : Set G} (hS : IsCompact S)
    (hU : IsOpen U) (hSU : S ⊆ U) : ∃ V : Set G, IsOpen V ∧ IsCompact V ∧ S ⊆ V ∧ V ⊆ U := by
  -- Take `V = S M` for a small compact open subgroup `M`.
  obtain ⟨N, hN, hSN⟩ := compact_open_separated_mul_right hS hU hSU
  obtain ⟨N', hN'_compact, hN'⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨M, hM⟩ : ∃ M : OpenSubgroup G, (M : Set G) ⊆ N ∩ N' :=
    NonarchimedeanGroup.is_nonarchimedean (N ∩ N') (inter_mem hN hN')
  have hM_compact : IsCompact (M : Set G) :=
    hN'_compact.of_isClosed_subset M.isClosed (hM.trans inter_subset_right)
  exact ⟨S * (M : Set G), M.isOpen.mul_left, hS.mul hM_compact, subset_mul_left S M.one_mem,
    (mul_subset_mul_left (hM.trans inter_subset_left)).trans hSN⟩

/-- A compact open subset of a closed subset `C` of a locally compact Hausdorff non-archimedean
group is cut out by a compact open subset of the group. -/
lemma exists_isCompact_isOpen_preimage_eq {G : Type} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [T2Space G] [WeaklyLocallyCompactSpace G] {C : Set G} (hC : IsClosed C)
    {A : Set C} (hA_open : IsOpen A) (hA_compact : IsCompact A) :
    ∃ V : Set G, IsOpen V ∧ IsCompact V ∧ ∀ x : C, (x : G) ∈ V ↔ x ∈ A := by
  have h_rest : IsClosed (Subtype.val '' Aᶜ) := hC.isClosedMap_subtype_val _ hA_open.isClosed_compl
  have h_disjoint : Disjoint (Subtype.val '' A) (Subtype.val '' Aᶜ) :=
    disjoint_image_of_injective Subtype.val_injective disjoint_compl_right
  obtain ⟨V, hV_open, hV_compact, h_subset_V, hV_subset⟩ :=
    exists_isCompact_isOpen_superset_subset (hA_compact.image continuous_subtype_val)
      h_rest.isOpen_compl h_disjoint.subset_compl_right
  exact ⟨V, hV_open, hV_compact, fun x ↦
    ⟨fun hx ↦ by_contra fun h_notMem ↦ hV_subset hx ⟨x, h_notMem, rfl⟩,
      fun hx ↦ h_subset_V ⟨x, hx, rfl⟩⟩⟩

/-- A test function on a closed subset `C` of a locally compact Hausdorff non-archimedean group is
the restriction of a test function on the group. -/
theorem TestFunction.exists_extension {G : Type} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] [T2Space G] [WeaklyLocallyCompactSpace G] {C : Set G} (hC : IsClosed C)
    (F : TestFunction C) : ∃ f : TestFunction G, ∀ x : C, f.1 x = F.1 x := by
  classical
  -- `F` takes finitely many values; extend its part on each level set and add up.
  obtain ⟨hF_const, hF_compact, -⟩ := F.2
  have h_part (c : ℂ) : ∃ a : TestFunction G, ∀ x : C, a.1 x = if F.1 x = c then c else 0 := by
    rcases eq_or_ne c 0 with rfl | hc
    · exact ⟨0, fun x ↦ (ite_self 0).symm⟩
    have h_level : IsCompact {x : C | F.1 x = c} :=
      hF_compact.isCompact.of_isClosed_subset (hF_const.isClosed_fiber c) fun x hx ↦
        subset_tsupport _ (ne_of_eq_of_ne hx hc)
    obtain ⟨V, hV_open, hV_compact, hV⟩ :=
      exists_isCompact_isOpen_preimage_eq hC (hF_const.isOpen_fiber c) h_level
    exact ⟨c • setIndicator hV_open hV_compact, fun x ↦ by
      simp [setIndicator_apply, indicator_apply, hV x]⟩
  choose a ha using h_part
  obtain ⟨values, h_values⟩ := hF_compact.isCompact.elim_finite_subcover _ hF_const.isOpen_fiber
    fun x _ ↦ mem_iUnion.2 ⟨F.1 x, rfl⟩
  refine ⟨∑ c ∈ values, a c, fun x ↦ ?_⟩
  suffices F.1 x ∉ values → F.1 x = 0 by simpa [ha, ite_eq_left_iff, eq_comm]
  exact fun h_notMem ↦ image_eq_zero_of_notMem_tsupport fun hx ↦
    h_notMem (by simpa using h_values hx)

end Extension

/-! ### Invariant distributions -/
open New.TestFunction

/-- `I` is an invariant distribution on `C`: a linear form on the test functions on `G` that is
invariant under conjugation by `Γ` and depends only on the restriction to `C`. -/
structure IsInvariantDistribution (j : Γ →ₜ* G) (C : Set G) (I : TestFunction G →ₗ[ℂ] ℂ) :
    Prop where
  /-- `I` is invariant under conjugation by `Γ`. -/
  map_conjugate : ∀ (g : Γ) (f : TestFunction G), I (conjugate j g f) = I f
  /-- `I` kills the test functions that vanish on `C`. -/
  eq_zero : ∀ f : TestFunction G, (∀ y ∈ C, f.1 y = 0) → I f = 0

section Mean

variable {j : Γ →ₜ* G} {C : Set G} {I : TestFunction G →ₗ[ℂ] ℂ} [WeaklyLocallyCompactSpace G]
  {K L : Subgroup Γ} [CompactSpace K] [CompactSpace L]

/-- An invariant distribution `I` on `C`, for conjugation by `Γ` through `j`, takes the same value
at a test function and at the mean of its conjugates over a compact subgroup `L` of `Γ`. -/
lemma IsInvariantDistribution.map_compactMean [IsTopologicalGroup Γ]
    (hI : IsInvariantDistribution j C I)
    (f : TestFunction G) : I (compactMean (conjugate j) L f) = I f :=
  map_compactMean_of_const I fun l _ ↦ hI.map_conjugate l f

/-- Let `κ` be a finite family in `Γ` and `φ` a test function on `G`. Suppose that, for each `k` in
the compact subgroup `K`, the right translates of `φ` by the elements `j (κ i * k)` sum to zero.
Then the mean `ψ` of the conjugates of `φ` over `K` satisfies `∑ i, ψ (x * j (κ i)) = 0`. -/
lemma TestFunction.sum_compactMean_conjugate_eq_zero [IsTopologicalGroup Γ]
    {ι : Type} [Fintype ι] {κ : ι → Γ}
    {φ : TestFunction G} (h_sum : ∀ k ∈ K, ∑ i : ι, translate (1, j (κ i * k)) φ = 0) (x : G) :
    ∑ i : ι, (compactMean (conjugate j) K φ).1 (x * j (κ i)) = 0 := by
  -- The sum of the values at the points `x * j (κ i)` kills every conjugate of `φ` under `K`.
  have h_mean : (∑ i : ι, eval (x * j (κ i))) (compactMean (conjugate j) K φ) = 0 := by
    refine map_compactMean_of_const _ fun k hk ↦ ?_
    have h_eval : ∑ i : ι, eval ((j k)⁻¹ * x) (translate (1, j (κ i * k)) φ) = 0 := by
      rw [← map_sum, h_sum k hk, map_zero]
    rw [LinearMap.sum_apply, ← h_eval]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [eval_apply, conjugate_apply, translate_apply, inv_one, one_mul, map_mul, mul_assoc]
  simpa only [LinearMap.sum_apply, eval_apply] using h_mean

end Mean

/-! ### Uniqueness of Haar measure, with a parameter (for Step 2) -/

section Haar

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
  {Y : Type} [TopologicalSpace Y] [T2Space Y]

omit [T2Space Γ] [T2Space Y] in
/-- There is an open subgroup of `Γ` whose elements fix a given test function `Ψ` on `Γ × Y` under
right translation in the first variable. -/
lemma TestFunction.exists_isOpen_subgroup_forall_mul_right_eq (Ψ : TestFunction (Γ × Y)) :
    ∃ S : Subgroup Γ, IsOpen (S : Set Γ) ∧
      ∀ o ∈ S, ∀ (g : Γ) (y : Y), Ψ.1 (g * o, y) = Ψ.1 (g, y) := by
  let S : Subgroup Γ :=
    { carrier := {o : Γ | ∀ (g : Γ) (y : Y), Ψ.1 (g * o, y) = Ψ.1 (g, y)}
      one_mem' := fun g y ↦ by rw [mul_one]
      mul_mem' := fun ha hb g y ↦ by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha g y ↦ by rw [← ha, inv_mul_cancel_right] }
  have h_const : IsLocallyConstant fun (o : Γ) (p : Γ × Y) ↦ Ψ.1 (p.1 * o, p.2) :=
    schwartzBruhat.isLocallyConstant_curry Ψ.2 (fun (o : Γ) (p : Γ × Y) ↦ (p.1 * o, p.2))
      (fun (o : Γ) (p : Γ × Y) ↦ (p.1 * o⁻¹, p.2)) (fun o p ↦ by rw [mul_inv_cancel_right])
  refine ⟨S, S.isOpen_of_mem_nhds (g := 1) ?_, fun o ho ↦ ho⟩
  filter_upwards [h_const.eventually_eq 1] with o ho g y using by simpa using congrFun ho (g, y)

/-- If `Γ` has a compact open subgroup `K`, every test function on `Γ × Y` is a finite sum of
products `(g, y) ↦ 1_{a O} g * ψ y`, for one compact open subgroup `O`, cosets `a O` and test
functions `ψ` on `Y`; here `tensor` is the product, `indicator _ _` is the characteristic function
of the compact open subgroup `O`, and `translate (a, 1) (indicator _ _)` is the characteristic
function of `a O`. -/
lemma TestFunction.exists_eq_sum_tensor {K : Subgroup Γ} (hK_open : IsOpen (K : Set Γ))
    (hK_compact : IsCompact (K : Set Γ)) (Ψ : TestFunction (Γ × Y)) :
    ∃ (O : Subgroup Γ) (hO_open : IsOpen (O : Set Γ)) (hO_compact : IsCompact (O : Set Γ))
      (cosets : Finset (Γ ⧸ O)) (ψ : Γ ⧸ O → TestFunction Y),
      Ψ = ∑ q ∈ cosets, tensor (translate (q.out, 1) (indicator hO_open hO_compact)) (ψ q) := by
  classical
  -- Let `O` be an open subgroup of `K` whose right translations fix `Ψ`. The support of `Ψ`
  -- meets finitely many cosets of `O`.
  obtain ⟨S, hS_open, hS_fixes⟩ := exists_isOpen_subgroup_forall_mul_right_eq Ψ
  let O : Subgroup Γ := K ⊓ S
  have hO_open : IsOpen (O : Set Γ) := hK_open.inter hS_open
  have hO_compact : IsCompact (O : Set Γ) :=
    hK_compact.inter_right (S.isClosed_of_isOpen hS_open)
  have : DiscreteTopology (Γ ⧸ O) := QuotientGroup.discreteTopology hO_open
  have h_finite : ((fun p : Γ × Y ↦ (p.1 : Γ ⧸ O)) '' tsupport Ψ.1).Finite :=
    ((hasCompactSupport Ψ).isCompact.image (by fun_prop)).finite_of_discrete
  let cosets : Finset (Γ ⧸ O) := h_finite.toFinset
  refine ⟨O, hO_open, hO_compact, cosets, fun q : Γ ⧸ O ↦ partialApply Ψ q.out, ?_⟩
  ext ⟨g, y⟩
  have h_out : Ψ.1 ((g : Γ ⧸ O).out, y) = Ψ.1 (g, y) := by
    obtain ⟨o, ho⟩ := QuotientGroup.mk_out_eq_mul O g
    rw [ho, hS_fixes o (Subgroup.mem_inf.1 o.2).2]
  have h_term (q : Γ ⧸ O) :
      (tensor (translate (q.out, 1) (indicator hO_open hO_compact)) (partialApply Ψ q.out)).1
        (g, y) = if (g : Γ ⧸ O) = q then Ψ.1 (q.out, y) else 0 := by
    rw [tensor_apply, translate_apply, mul_one]
    change (O : Set Γ).indicator 1 (q.out⁻¹ * g) * Ψ.1 (q.out, y) = _
    simp [indicator_apply, ← QuotientGroup.eq, eq_comm]
  suffices Ψ.1 (g, y) = if (g : Γ ⧸ O) ∈ cosets then Ψ.1 (g, y) else 0 by simpa [h_term, h_out]
  rw [eq_comm, ite_eq_left_iff]
  exact fun h_notMem ↦ (image_eq_zero_of_notMem_tsupport fun hp ↦
    h_notMem (h_finite.mem_toFinset.2 ⟨(g, y), hp, rfl⟩)).symm

/-- **Uniqueness of Haar measure, with a parameter.** Let the group `Γ` have a compact open subgroup
`K`, and let `Λ` be a linear form on the test functions (locally constant, of compact support) on
`Γ × Y` that is invariant under left translations in the first variable and kills the functions
that vanish on `Γ × X`. Then `Λ Ψ = 0` if the integral of `Ψ (·, y)` for a left Haar measure `μ`
vanishes for each `y ∈ X`. -/
theorem TestFunction.map_eq_zero_of_integral_eq_zero [MeasurableSpace Γ] [BorelSpace Γ]
    {K : Subgroup Γ} (hK_open : IsOpen (K : Set Γ)) (hK_compact : IsCompact (K : Set Γ))
    (μ : Measure Γ) [μ.IsHaarMeasure] {X : Set Y} {Λ : TestFunction (Γ × Y) →ₗ[ℂ] ℂ}
    (h_left : ∀ (a : Γ) (Ψ Ψ' : TestFunction (Γ × Y)),
      (∀ (g : Γ) (y : Y), Ψ'.1 (g, y) = Ψ.1 (a⁻¹ * g, y)) → Λ Ψ' = Λ Ψ)
    (h_zero : ∀ Ψ : TestFunction (Γ × Y), (∀ g : Γ, ∀ y ∈ X, Ψ.1 (g, y) = 0) → Λ Ψ = 0)
    {Ψ : TestFunction (Γ × Y)} (hΨ : ∀ y ∈ X, ∫ g : Γ, Ψ.1 (g, y) ∂μ = 0) : Λ Ψ = 0 := by
  -- Write `Ψ = ∑ 1_{a O} ⊗ ψ_a`. Then `Λ Ψ = Λ (∑ 1_O ⊗ ψ_a)`, and `vol O * ∑ ψ_a` is the
  -- integral of `Ψ` over `Γ`.
  obtain ⟨O, hO_open, hO_compact, cosets, ψ, rfl⟩ := exists_eq_sum_tensor hK_open hK_compact Ψ
  set e : TestFunction Γ := indicator hO_open hO_compact
  have h_integral (a : Γ) : ∫ g : Γ, (translate (a, 1) e).1 g ∂μ = μ.real O := by
    simp only [translate_apply, mul_one, integral_mul_left_eq_self e.1 a⁻¹]
    exact (integral_indicator_const (1 : ℂ) hO_open.measurableSet).trans (by simp)
  have h_vol : (μ.real O : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 <| ENNReal.toReal_ne_zero.2
    ⟨hO_open.measure_ne_zero μ ⟨1, O.one_mem⟩, hO_compact.measure_ne_top⟩
  have h_sum (y : Y) (hy : y ∈ X) : ∑ q ∈ cosets, (ψ q).1 y = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left h_vol
    calc (μ.real O : ℂ) * ∑ q ∈ cosets, (ψ q).1 y
        = ∑ q ∈ cosets, ∫ g : Γ, (translate (q.out, 1) e).1 g * (ψ q).1 y ∂μ := by
          simp only [integral_mul_const, h_integral, Finset.mul_sum]
      _ = ∫ g : Γ, ∑ q ∈ cosets, (translate (q.out, 1) e).1 g * (ψ q).1 y ∂μ :=
          (integral_finsetSum _ fun q _ ↦ (TestFunction.integrable _ μ).mul_const _).symm
      _ = 0 := by simpa [tensor_apply] using hΨ y hy
  calc Λ (∑ q ∈ cosets, tensor (translate (q.out, 1) e) (ψ q))
      = Λ (∑ q ∈ cosets, tensor e (ψ q)) := by
        simp only [map_sum]
        exact Finset.sum_congr rfl fun q _ ↦ h_left q.out _ _ fun g y ↦ by
          simp [tensor_apply, translate_apply]
    _ = 0 := h_zero _ fun g y hy ↦ by simp [tensor_apply, ← Finset.mul_sum, h_sum y hy]

end Haar

/-! ### Step 1: slices and images -/

/-- `X` is a slice of the closed set `C ⊆ G` for conjugation by `Γ` through `j`: the map
`(g, y) ↦ g y g⁻¹` takes `Γ × X` onto `C`, its fibres are the orbits `{(g h, h⁻¹ y h) | h ∈ H}` of
the closed subgroup `H`, and it is open in the sense of `eventually_exists_conj_mem`. -/
structure IsSlice (j : Γ →ₜ* G) (H : Subgroup Γ) (C X : Set G) : Prop where
  /-- `H` is closed. -/
  isClosed_subgroup : IsClosed (H : Set Γ)
  /-- `C` is closed. -/
  isClosed : IsClosed C
  /-- `C` is the set of the conjugates of the elements of `X`. -/
  mem_iff : ∀ x : G, x ∈ C ↔ ∃ g : Γ, (j g)⁻¹ * x * j g ∈ X
  /-- A conjugate of an element of `X` lies in `X` exactly if the conjugating element is in `H`. -/
  conj_mem_iff : ∀ y ∈ X, ∀ g : Γ, (j g)⁻¹ * y * j g ∈ X ↔ g ∈ H
  /-- For every neighbourhood `O` of `1` in `Γ`, the points of `C` near a point of `X` are conjugate
  into `X` by elements of `O`. -/
  eventually_exists_conj_mem :
    ∀ O ∈ 𝓝 (1 : Γ), ∀ y ∈ X, ∀ᶠ x : G in 𝓝[C] y, ∃ o ∈ O, (j o)⁻¹ * x * j o ∈ X

omit [IsTopologicalGroup G] [T2Space G] in
/-- The set `C` of the conjugates of the elements of a slice `X` is stable under conjugation by
`Γ`. -/
lemma IsSlice.conj_mem {j : Γ →ₜ* G} {H : Subgroup Γ} {C X : Set G} (hX : IsSlice j H C X) {x : G}
    (hx : x ∈ C) (a : Γ) : (j a)⁻¹ * x * j a ∈ C := by
  obtain ⟨g, hg⟩ := (hX.mem_iff x).1 hx
  exact (hX.mem_iff _).2 ⟨a⁻¹ * g, by simpa [mul_assoc] using hg⟩

variable {G Γ : Type} [Group G] [TopologicalSpace G]
  [Group Γ] [TopologicalSpace Γ] [MeasurableSpace Γ]

/-- The integral of `Ψ` over the orbit `{(g h, h⁻¹ y h) | h ∈ H}` of `(g, y)`, for a measure `ν` on
`H`; here `h` acts on `y` through `j`. -/
noncomputable def fibreIntegral (j : Γ →ₜ* G) {H : Subgroup Γ} (ν : Measure H)
    (Ψ : TestFunction (Γ × G)) (g : Γ) (y : G) : ℂ :=
  ∫ h : H, Ψ.1 (g * h, (j h)⁻¹ * y * j h) ∂ν

/-- `f` is an image of `Ψ`: its value at `g y g⁻¹`, for `g ∈ Γ` and `y ∈ X`, is the integral of `Ψ`
over the `H`-orbit of `(g, y)`. -/
def IsImage (j : Γ →ₜ* G) {H : Subgroup Γ} (ν : Measure H) (X : Set G) (Ψ : TestFunction (Γ × G))
    (f : TestFunction G) : Prop :=
  ∀ g : Γ, ∀ y ∈ X, f.1 (j g * y * (j g)⁻¹) = fibreIntegral j ν Ψ g y

variable {j : Γ →ₜ* G} {H : Subgroup Γ} {ν : Measure H} {C X : Set G}
  {Ψ Ψ' : TestFunction (Γ × G)} {f f' : TestFunction G} {I : TestFunction G →ₗ[ℂ] ℂ}

/-- The integral `fibreIntegral j ν Ψ g y` of a test function `Ψ` over the orbit
`{(g h, h⁻¹ y h) | h ∈ H}` is locally constant in `(g, y)`. -/
lemma isLocallyConstant_fibreIntegral [IsTopologicalGroup G] [IsTopologicalGroup Γ]
    (Ψ : TestFunction (Γ × G)) :
    IsLocallyConstant fun p : Γ × G ↦ fibreIntegral j ν Ψ p.1 p.2 := by
  -- The integrand, as a function of `h`, is itself locally constant in `(g, y)`.
  let orbit : Γ × G → Γ → Γ × G := fun p h ↦ (p.1 * h, (j h)⁻¹ * p.2 * j h)
  have h_const : IsLocallyConstant fun (p : Γ × G) (h : Γ) ↦ Ψ.1 (orbit p h) :=
    schwartzBruhat.isLocallyConstant_curry Ψ.2 (f := orbit) (g := fun (p q : Γ × G) ↦ p.1⁻¹ * q.1)
      (fun p h ↦ inv_mul_cancel_left p.1 h) (by fun_prop) (by fun_prop)
  exact h_const.comp fun u : Γ → ℂ ↦ ∫ h : H, u h ∂ν

/-- If the integral of `Ψ` over the orbit `{(g h, h⁻¹ y h) | h ∈ H}` is not zero, then `g y g⁻¹` is
`g' y' g'⁻¹` for a point `(g', y')` in the support of `Ψ`. -/
lemma mem_image_tsupport_of_fibreIntegral_ne_zero {g : Γ} {y : G}
    (h_ne : fibreIntegral j ν Ψ g y ≠ 0) :
    j g * y * (j g)⁻¹ ∈ (fun p : Γ × G ↦ j p.1 * p.2 * (j p.1)⁻¹) '' tsupport Ψ.1 := by
  obtain ⟨h, hΨ⟩ : ∃ h : H, Ψ.1 (g * h, (j h)⁻¹ * y * j h) ≠ 0 := by
    by_contra! h_all
    exact h_ne (by simp only [fibreIntegral, h_all, integral_zero])
  exact ⟨(g * h, (j h)⁻¹ * y * j h), subset_tsupport _ hΨ, by simp [mul_assoc]⟩

lemma IsImage.smul (hf : IsImage j ν X Ψ f) (c : ℂ) : IsImage j ν X (c • Ψ) (c • f) :=
  fun g y hy ↦ by simp [hf g y hy, fibreIntegral, integral_const_mul]

/-- Let `f` be an image of `Ψ` (its value at `g y g⁻¹`, for `y ∈ X`, is the integral of `Ψ` over the
`H`-orbit of `(g, y)`), and let `Ψ'` be the left translate of `Ψ` by `a` in the first variable. Then
the conjugate `x ↦ f (a⁻¹ x a)` is an image of `Ψ'`. -/
lemma IsImage.conjugate [IsTopologicalGroup G] [T2Space G] (hf : IsImage j ν X Ψ f) {a : Γ}
    (h_left : ∀ (g : Γ) (y : G), Ψ'.1 (g, y) = Ψ.1 (a⁻¹ * g, y)) :
    IsImage j ν X Ψ' (conjugate j a f) := by
  intro g y hy
  have h_conj : (j a)⁻¹ * (j g * y * (j g)⁻¹) * j a = j (a⁻¹ * g) * y * (j (a⁻¹ * g))⁻¹ := by
    simp [mul_assoc]
  calc (TestFunction.conjugate j a f).1 (j g * y * (j g)⁻¹)
      = f.1 (j (a⁻¹ * g) * y * (j (a⁻¹ * g))⁻¹) := by rw [conjugate_apply, h_conj]
    _ = fibreIntegral j ν Ψ (a⁻¹ * g) y := hf (a⁻¹ * g) y hy
    _ = fibreIntegral j ν Ψ' g y := by simp only [fibreIntegral, h_left, mul_assoc]

/-- Let `X` be a slice, so that `H` conjugates `X` into itself. If `Ψ` vanishes on `Γ × X`, then its
integrals over the `H`-orbits in `Γ × X` vanish, that is, `0` is an image of `Ψ`. -/
lemma IsSlice.isImage_zero (hX : IsSlice j H C X) (h_zero : ∀ g : Γ, ∀ y ∈ X, Ψ.1 (g, y) = 0) :
    IsImage j ν X Ψ 0 := by
  intro g y hy
  simp [fibreIntegral, fun h : H ↦ h_zero (g * h) _ ((hX.conj_mem_iff y hy h).2 h.2)]

/-- Let `X` be a slice of `C`, so that `C` consists of the conjugates of the elements of `X`. Two
images `f` and `f'` of `Ψ` agree on `C`, since both are given there by the integrals of `Ψ` over
`H`-orbits. Hence an invariant distribution `I` on `C`, a linear form that is invariant under
conjugation and depends only on the restriction to `C`, has the same value on them. -/
lemma IsInvariantDistribution.eq_of_isImage [IsTopologicalGroup G] [T2Space G]
    (hI : IsInvariantDistribution j C I)
    (hX : IsSlice j H C X) (hf : IsImage j ν X Ψ f) (hf' : IsImage j ν X Ψ f') : I f = I f' := by
  rw [← sub_eq_zero, ← map_sub]
  refine hI.eq_zero _ fun x hx ↦ ?_
  obtain ⟨g, hg⟩ := (hX.mem_iff x).1 hx
  have hx_conj : x = j g * ((j g)⁻¹ * x * j g) * (j g)⁻¹ := by group
  rw [Submodule.coe_sub, Pi.sub_apply, hx_conj, hf g _ hg, hf' g _ hg, sub_self]

variable [IsTopologicalGroup Γ] [BorelSpace Γ] [ν.IsHaarMeasure]

/-- For a left Haar measure `ν` on `H`, the integral of `Ψ` over the orbit
`{(g h, h⁻¹ y h) | h ∈ H}` does not change when `(g, y)` is replaced by another point
`(g a, a⁻¹ y a)` of the orbit. -/
lemma fibreIntegral_mul_conj (Ψ : TestFunction (Γ × G)) (g : Γ) (y : G) (a : H) :
    fibreIntegral j ν Ψ (g * a) ((j a)⁻¹ * y * j a) = fibreIntegral j ν Ψ g y := by
  simpa [fibreIntegral, mul_assoc] using
    integral_mul_left_eq_self (μ := ν) (fun h : H ↦ Ψ.1 (g * h, (j h)⁻¹ * y * j h)) a

/-- For a closed subgroup `H` and a Haar measure `ν` on it, a test function on `Γ × G` is integrable
along the orbit `h ↦ (g h, h⁻¹ y h)`. -/
lemma TestFunction.integrable_mul_conj [IsTopologicalGroup G] [T2Space G]
    [T2Space Γ] (hH : IsClosed (H : Set Γ)) (Ψ : TestFunction (Γ × G)) (g : Γ) (y : G) :
    Integrable (fun h : H ↦ Ψ.1 (g * h, (j h)⁻¹ * y * j h)) ν := by
  obtain ⟨h_const, h_compact, -⟩ :
      (fun h : Γ ↦ Ψ.1 (g * h, (j h)⁻¹ * y * j h)) ∈ TestFunction Γ :=
    schwartzBruhat.comp Ψ.2 (fun p : Γ × G ↦ g⁻¹ * p.1) (fun h ↦ inv_mul_cancel_left g h)
      (mapsTo_univ _ _) (by fun_prop) (by fun_prop)
  exact (h_const.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (h_compact.comp_isClosedEmbedding hH.isClosedEmbedding_subtypeVal)

/-- Let `H` be closed, and let `f` and `f'` be images of `Ψ` and `Ψ'` (their values at `g y g⁻¹`,
for `y ∈ X`, are the integrals over the `H`-orbit of `(g, y)`). Then `f + f'` is an image of
`Ψ + Ψ'`. -/
lemma IsImage.add [IsTopologicalGroup G] [T2Space G]
    [T2Space Γ] (hH : IsClosed (H : Set Γ)) (hf : IsImage j ν X Ψ f)
    (hf' : IsImage j ν X Ψ' f') : IsImage j ν X (Ψ + Ψ') (f + f') := by
  intro g y hy
  simp only [Submodule.coe_add, Pi.add_apply, hf g y hy, hf' g y hy, fibreIntegral]
  exact (integral_add (integrable_mul_conj hH Ψ g y) (integrable_mul_conj hH Ψ' g y)).symm

/-- Let `X` be a slice. The integral of `Ψ` over the `H`-orbit of `(g, g⁻¹ x g)` is the same for all
`g` that conjugate `x` into `X`, since two such `g` differ by an element of `H`. -/
lemma IsSlice.fibreIntegral_conj_eq (hX : IsSlice j H C X) (Ψ : TestFunction (Γ × G)) {x : G}
    {g g' : Γ} (hg : (j g)⁻¹ * x * j g ∈ X) (hg' : (j g')⁻¹ * x * j g' ∈ X) :
    fibreIntegral j ν Ψ g' ((j g')⁻¹ * x * j g') = fibreIntegral j ν Ψ g ((j g)⁻¹ * x * j g) := by
  have h_conj : (j (g⁻¹ * g'))⁻¹ * ((j g)⁻¹ * x * j g) * j (g⁻¹ * g') = (j g')⁻¹ * x * j g' := by
    simp [mul_assoc]
  have h_mem : g⁻¹ * g' ∈ H := (hX.conj_mem_iff _ hg (g⁻¹ * g')).1 (by rwa [h_conj])
  rw [← fibreIntegral_mul_conj Ψ g ((j g)⁻¹ * x * j g) ⟨g⁻¹ * g', h_mem⟩, h_conj,
    mul_inv_cancel_left]

/-- Let `X` be a slice of `C` (the conjugates of `X` make up `C`, and nearby points of `C` are
conjugated into `X` by elements near `1`), and for each `x ∈ C` let `g x` conjugate `x` into `X` (no
continuity of `g` is assumed). The integral of `Ψ` over the `H`-orbit of `(g x, (g x)⁻¹ x (g x))` is
a locally constant function of `x`. -/
lemma IsSlice.isLocallyConstant_fibreIntegral_conj [IsTopologicalGroup G] (hX : IsSlice j H C X)
    (Ψ : TestFunction (Γ × G)) {g : C → Γ} (hg : ∀ x : C, (j (g x))⁻¹ * x * j (g x) ∈ X) :
    IsLocallyConstant fun x : C ↦ fibreIntegral j ν Ψ (g x) ((j (g x))⁻¹ * x * j (g x)) := by
  -- A point `x` near `x₀` is conjugated into `X` by some `g x₀ * o` with `o` near `1`, and the
  -- integral over the orbit is locally constant in `(o, x)`.
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ ↦ ?_
  let Φ : Γ × C → ℂ := fun p ↦
    fibreIntegral j ν Ψ (g x₀ * p.1) ((j (g x₀ * p.1))⁻¹ * p.2 * j (g x₀ * p.1))
  have hΦ : IsLocallyConstant Φ :=
    (isLocallyConstant_fibreIntegral Ψ).comp_continuous
      (f := fun p : Γ × C ↦ (g x₀ * p.1, (j (g x₀ * p.1))⁻¹ * p.2 * j (g x₀ * p.1))) (by fun_prop)
  obtain ⟨O, hO, V, hV, hΦ_near⟩ :
      ∃ O ∈ 𝓝 (1 : Γ), ∃ V ∈ 𝓝 x₀, O ×ˢ V ⊆ {p : Γ × C | Φ p = Φ (1, x₀)} :=
    mem_nhds_prod_iff.1 (hΦ.eventually_eq (1, x₀))
  have h_tendsto : Tendsto (fun x : C ↦ (j (g x₀))⁻¹ * x * j (g x₀)) (𝓝 x₀)
      (𝓝[C] ((j (g x₀))⁻¹ * x₀ * j (g x₀))) :=
    tendsto_nhdsWithin_iff.2 ⟨Continuous.tendsto (by fun_prop) x₀,
      .of_forall fun x ↦ hX.conj_mem x.2 (g x₀)⟩
  have h_section : ∀ᶠ x : C in 𝓝 x₀, ∃ o ∈ O, (j o)⁻¹ * ((j (g x₀))⁻¹ * x * j (g x₀)) * j o ∈ X :=
    h_tendsto.eventually (hX.eventually_exists_conj_mem O hO _ (hg x₀))
  filter_upwards [hV, h_section] with x hx ⟨o, ho, hox⟩
  have h_mem : (j (g x₀ * o))⁻¹ * x * j (g x₀ * o) ∈ X := by simpa [mul_assoc] using hox
  calc fibreIntegral j ν Ψ (g x) ((j (g x))⁻¹ * x * j (g x))
      = Φ (o, x) := hX.fibreIntegral_conj_eq Ψ h_mem (hg x)
    _ = Φ (1, x₀) := hΦ_near (mk_mem_prod ho hx)
    _ = _ := by simp only [Φ, mul_one]

section Main

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ]
  {H : Subgroup Γ} [BorelSpace Γ]
  {G : Type} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G] [T2Space G]
  [WeaklyLocallyCompactSpace G] {j : Γ →ₜ* G} {C X : Set G}

/-- **Images.** Let `X` be a slice of `C` for conjugation by `Γ`: the map `(g, y) ↦ g y g⁻¹` from
`Γ × X` onto `C` is open, and its fibres are the orbits of the closed subgroup `H` of `Γ`. For a
Haar measure `ν` on `H`, every test function `Ψ` on `Γ × G` has an image: a test function `f` on `G`
whose value at `g y g⁻¹`, for `y ∈ X`, is the integral of `Ψ` over the orbit of `(g, y)`. -/
theorem IsSlice.exists_isImage (hX : IsSlice j H C X) (ν : Measure H) [ν.IsHaarMeasure]
    (Ψ : TestFunction (Γ × G)) : ∃ f : TestFunction G, IsImage j ν X Ψ f := by
  -- Choose `g x` conjugating `x ∈ C` into `X`, and integrate over the orbit of
  -- `(g x, (g x)⁻¹ x (g x))`.
  choose g hg using fun x : C ↦ (hX.mem_iff x).1 x.2
  let F : C → ℂ := fun x ↦ fibreIntegral j ν Ψ (g x) ((j (g x))⁻¹ * x * j (g x))
  have hF_compact : HasCompactSupport F := by
    let S : Set G := (fun p : Γ × G ↦ j p.1 * p.2 * (j p.1)⁻¹) '' tsupport Ψ.1
    have hS_compact : IsCompact S := (hasCompactSupport Ψ).isCompact.image (by fun_prop)
    have h_support (x : C) (h_ne : F x ≠ 0) : (x : G) ∈ S := by
      simpa [S, mul_assoc] using mem_image_tsupport_of_fibreIntegral_ne_zero h_ne
    exact HasCompactSupport.of_support_subset_isCompact
      (hX.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage hS_compact) h_support
  let F' : TestFunction C :=
    ⟨F, hX.isLocallyConstant_fibreIntegral_conj Ψ hg, hF_compact, subset_univ _⟩
  obtain ⟨f, hf⟩ : ∃ f : TestFunction G, ∀ x : C, f.1 x = F x := exists_extension hX.isClosed F'
  refine ⟨f, fun a y hy ↦ ?_⟩
  have h_conj : (j a)⁻¹ * (j a * y * (j a)⁻¹) * j a = y := by group
  have h_mem : (j a)⁻¹ * (j a * y * (j a)⁻¹) * j a ∈ X := by rwa [h_conj]
  let x : C := ⟨j a * y * (j a)⁻¹, (hX.mem_iff _).2 ⟨a, h_mem⟩⟩
  calc f.1 x = F x := hf x
    _ = fibreIntegral j ν Ψ a ((j a)⁻¹ * x * j a) := hX.fibreIntegral_conj_eq Ψ h_mem (hg x)
    _ = fibreIntegral j ν Ψ a y := by rw [h_conj]

/-! ### Step 2: invariant distributions on images -/

/-- Let `X` be a slice of `C` and `I` an invariant distribution on `C` (a linear form on the test
functions on `G`, invariant under conjugation by `Γ` and depending only on the restriction to `C`).
There is a linear form `Λ` on the test functions on `Γ × G` such that `Λ Ψ = I f` for every image
`f` of `Ψ` under integration over the fibres of `Γ × X → C`. -/
lemma IsInvariantDistribution.exists_linearMap_eq_of_isImage [T2Space Γ]
    {I : TestFunction G →ₗ[ℂ] ℂ} (hI : IsInvariantDistribution j C I) (hX : IsSlice j H C X)
    (ν : Measure H) [ν.IsHaarMeasure] :
    ∃ Λ : TestFunction (Γ × G) →ₗ[ℂ] ℂ,
      ∀ (Ψ : TestFunction (Γ × G)) (f : TestFunction G), IsImage j ν X Ψ f → Λ Ψ = I f := by
  choose image h_image using hX.exists_isImage ν
  have h_eq {Ψ : TestFunction (Γ × G)} {f : TestFunction G} (hf : IsImage j ν X Ψ f) :
      I (image Ψ) = I f := hI.eq_of_isImage hX (h_image Ψ) hf
  have h_add (Ψ Ψ' : TestFunction (Γ × G)) : I (image (Ψ + Ψ')) = I (image Ψ) + I (image Ψ') := by
    rw [h_eq ((h_image Ψ).add hX.isClosed_subgroup (h_image Ψ')), map_add]
  have h_smul (c : ℂ) (Ψ : TestFunction (Γ × G)) : I (image (c • Ψ)) = c • I (image Ψ) := by
    rw [h_eq ((h_image Ψ).smul c), map_smul]
  exact ⟨{ toFun := fun Ψ ↦ I (image Ψ), map_add' := h_add, map_smul' := h_smul },
    fun Ψ f hf ↦ h_eq hf⟩

/-- **Descent to a slice.** Let `Γ` have a compact open subgroup `K` and let `μ` and `ν` be Haar
measures on `Γ` and on `H`. Let `X` be a slice of `C` with the fibres of `Γ × X → C` the orbits of
`H`, and let `I` be an invariant distribution on `C`: a linear form on the test functions on `G`
that is invariant under conjugation by `Γ` and depends only on the restriction to `C`. If the
integral of `Ψ (·, y)` over `Γ` vanishes for each `y ∈ X`, then `I f = 0` for every image `f` of
`Ψ`: a test function whose value at `g y g⁻¹`, for `g ∈ Γ` and `y ∈ X`, is the integral of `Ψ` over
the orbit of `(g, y)`. -/
theorem IsInvariantDistribution.eq_zero_of_isImage [T2Space Γ] {K : Subgroup Γ}
    {I : TestFunction G →ₗ[ℂ] ℂ} (hI : IsInvariantDistribution j C I) (hX : IsSlice j H C X)
    (hK_open : IsOpen (K : Set Γ)) (hK_compact : IsCompact (K : Set Γ))
    (μ : Measure Γ) [μ.IsHaarMeasure] {ν : Measure H} [ν.IsHaarMeasure]
    {Ψ : TestFunction (Γ × G)} (hΨ : ∀ y ∈ X, ∫ g : Γ, Ψ.1 (g, y) ∂μ = 0)
    {f : TestFunction G} (hf : IsImage j ν X Ψ f) : I f = 0 := by
  -- The value of `I` on the image is a linear form in `Ψ` that left translations do not change.
  obtain ⟨Λ, hΛ⟩ := hI.exists_linearMap_eq_of_isImage hX ν
  have h_left (a : Γ) (Φ Φ' : TestFunction (Γ × G))
      (h_translate : ∀ (g : Γ) (y : G), Φ'.1 (g, y) = Φ.1 (a⁻¹ * g, y)) : Λ Φ' = Λ Φ := by
    obtain ⟨φ, hφ⟩ := hX.exists_isImage ν Φ
    rw [hΛ Φ' (conjugate j a φ) (hφ.conjugate h_translate), hI.map_conjugate, hΛ Φ φ hφ]
  have h_zero (Φ : TestFunction (Γ × G)) (hΦ : ∀ g : Γ, ∀ y ∈ X, Φ.1 (g, y) = 0) : Λ Φ = 0 := by
    rw [hΛ Φ 0 (hX.isImage_zero hΦ), map_zero]
  rw [← hΛ Ψ f hf]
  exact map_eq_zero_of_integral_eq_zero hK_open hK_compact μ h_left h_zero hΨ

end Main

end New
