import Lib.GLn.SchurModule.SchurNorm

/-!
# Algebraic modular forms: delta forms, unitary translation and spanning by Hecke eigenforms

This file concerns algebraic modular forms. These are functions on a group that transform on the
left by a representation of a group `Γ` embedded in it, and on the right by a character of a level.
`New.levelSpace π K χ` is the space of vectors on which `K` acts through `χ`.

## Main definitions and results

* `New.deltaForm`: the form supported on one double coset, made from a vector. Its values are sums
  over the finite sets `New.transporter` (`New.deltaForm_apply`); `New.classSum_deltaForm` gives the
  class sum of its values under an invariant family of additive maps `W →+ ℂ`.
* `New.freeLevelEquiv`, `New.finrank_levelSpace_smoothFormRep`: at a sufficiently small level, also
  called free (all `New.classAut` trivial), forms are arbitrary families of values, so the dimension
  is the class number times `finrank ℂ W`.
* `New.Space.exists_isUnitary_formTranslation`: right translation `New.Space.formTranslation` on the
  forms `New.Space.forms` of weight `κ` has an invariant positive definite scalar product.
* `New.Space.finite_formTranslation_levelSpace`: the eigenforms of an open level for
  `New.Space.formTranslation` form a finite-dimensional space.
* `New.hasHeckePolyAt_iff`: a form has a Hecke polynomial at a split place exactly when it is
  spherical there and an eigenvector of the Hecke operators there, the polynomial being formed from
  the eigenvalues.
* `New.le_span_isSphericalOff`: a finite-dimensional Hecke-stable space of forms fixed by the
  integral points trivial at `S` is spanned by simultaneous eigenforms.

Notions from other files:
* `New.Space E n ε`: a hermitian space with a point, given by a matrix J over a field E with a CM
  structure (`CMType E`) and x in GL_n(𝔸) with xᴴJx equal to diag(ε) at the infinite places and 1 at
  the finite places; the signs `ε = 1` give the definite spaces.
* `New.Space.forms`: Algebraic modular forms of weight κ on a definite space V: functions f on G_f
  with open right stabiliser and f(γg) = ρ_κ(γ)f(g) for rational γ, ρ_κ = `New.Space.weightRep` for
  a weight κ : `New.Weight E`; values lie in `WeylIndex n κ.1 → ℂ`.
* `New.HasFiniteType Γ K`: `K` is compact and open, `Γ \ G / K` is finite and every group
  `New.classAut Γ K g`, which is `Γ ∩ g K g⁻¹`, is finite.
* `New.classSum Γ K f`: the sum over the classes `c`, with representative `g_c`, of
  `f g_c / #(Γ ∩ g_c K g_c⁻¹)`.

## Relation to the literature

Known result: Finite dimension of spaces of algebraic modular forms and the Hecke eigenforms
spanning them. Related files: `Lib.Adelic.AutomorphicForms.SmoothAlgebraicForms` and, for congruence
subgroups and level structures, `Lib.Adelic.Unitary.CongruenceLevels`.
-/

/-!
## Algebraic forms of a level: delta forms, values on classes, dimension

Algebraic forms on a group `G` are defined for a homomorphism `e : Γ →* G` (assumed injective from
the delta forms on), a representation `ρ` of `Γ` on a complex vector space `W`, a level `K ≤ G` and
a character `χ` of `K`. They are the vectors of `New.levelSpace` for the representation
`New.smoothFormRep` of `G` by right translation. Each form is a smooth function `φ : G → W`. For an
element `φ` of the subtype `levelSpace (smoothFormRep e ρ) K χ`, `φ.val.val` is the function.
-/

namespace New

open DoubleCoset Finset Function LinearMap HasFiniteType Module

variable {G Γ W : Type*} [Group G] [Group Γ] {K : Subgroup G} [AddCommGroup W] [Module ℂ W]
  {e : Γ →* G} {ρ : Representation ℂ Γ W} {χ : K →* ℂ} [TopologicalSpace G]

/-- Let `φ : G → W` be a smooth form (left equivariant for `e` and `ρ`, with open right stabiliser)
on which `K` acts by right translation through `χ`. Then `φ (e γ * g * k) = χ k • ρ γ (φ g)`. -/
lemma levelSpace_smoothFormRep_apply [IsTopologicalGroup G] {φ : SmoothForm e ρ}
    (hφ : φ ∈ levelSpace (smoothFormRep e ρ) K χ) (γ : Γ) (g : G) (k : K) :
    φ.val (e γ * g * k) = χ k • ρ γ (φ.val g) := by
  rw [← φ.property.right γ g]
  exact congrFun (congrArg Subtype.val (hφ k)) (e γ * g)

/-- Let `e : Γ →* G` be a homomorphism, `ρ` a representation of `Γ` on `W` and `χ` a character of
the subgroup `K`, and let `r` be a system of representatives of the double cosets `e(Γ) \ G / K`.
Two forms of level `(K, χ)`, that is, smooth `φ : G → W` with `φ (e γ * g * k) = χ k • ρ γ (φ g)`,
are equal if they agree at every representative `r c`. -/
lemma levelSpace_ext_doubleCosets [IsTopologicalGroup G] {r : DoubleCosets e.range K → G}
    (hr : ∀ c : DoubleCosets e.range K, DoubleCoset.mk e.range K (r c) = c)
    {φ ψ : levelSpace (smoothFormRep e ρ) K χ}
    (h_rep : ∀ c : DoubleCosets e.range K, φ.val.val (r c) = ψ.val.val (r c)) : φ = ψ := by
  -- Every `y` is some `e γ * r c * k`, and `levelSpace_smoothFormRep_apply` gives the value there
  -- from that at `r c`.
  ext y
  obtain ⟨c, γ, k, rfl⟩ := exists_eq_map_mul_rep_mul e K hr y
  simp [levelSpace_smoothFormRep_apply φ.property, levelSpace_smoothFormRep_apply ψ.property, h_rep]

variable (e ρ χ) in
/-- For points `r c` of `G` indexed by the double cosets `c` in `e(Γ) \ G / K`, the linear map
sending a form `φ` of level `(K, χ)` to the family of its values `c ↦ φ (r c)`. -/
def evalClassReps [IsTopologicalGroup G] (r : DoubleCosets e.range K → G) :
    levelSpace (smoothFormRep e ρ) K χ →ₗ[ℂ] DoubleCosets e.range K → W :=
  ((funLeft ℂ W r).domRestrict (SmoothForm e ρ)).domRestrict (levelSpace (smoothFormRep e ρ) K χ)

lemma evalClassReps_apply [IsTopologicalGroup G] (r : DoubleCosets e.range K → G)
    (φ : levelSpace (smoothFormRep e ρ) K χ) (c : DoubleCosets e.range K) :
    evalClassReps e ρ χ r φ c = φ.val.val (r c) :=
  rfl

/-- Evaluation of forms of level `(K, χ)` at representatives `r c` of the double cosets `c` in
`e(Γ) \ G / K` is injective. -/
lemma evalClassReps_injective [IsTopologicalGroup G] {r : DoubleCosets e.range K → G}
    (hr : ∀ c : DoubleCosets e.range K, DoubleCoset.mk e.range K (r c) = c) :
    Function.Injective (evalClassReps e ρ χ r) :=
  fun _ _ h_eval ↦ levelSpace_ext_doubleCosets hr (congrFun h_eval)

/-- The trivial character is trivial near `1`. -/
instance : Fact ((1 : K →* ℂ) =ᶠ[nhds 1] 1) := ⟨.rfl⟩

variable (e ρ χ)
  [o : Fact (χ =ᶠ[nhds 1] 1)] -- `χ` is trivial near `1`
  [H : HasFiniteType e.range K] -- `K` is compact open, with finitely many classes and finite
                                -- stabilisers
  [i : Fact (Injective e)] -- `e` is injective

omit H i in
/-- Let `K` be an open subgroup of `G` and `χ` a character of `K` that is trivial near `1` (given as
a `Fact`). A function `f : G → W` on which each `k ∈ K` acts by right translation (`rightRegular`)
as multiplication by `χ k` is smooth, that is, has an open right stabiliser. -/
lemma mem_smoothFunctions_of_eigen [IsTopologicalGroup G] (hK : IsOpen (K : Set G)) {f : G → W}
    (hf : ∀ k : K, rightRegular ℂ G W k f = χ k • f) :
    f ∈ (smoothFunctions ℂ).toSubmodule := by
  -- The elements of `K` near `1` have `χ k = 1`, so they fix `f`; and `K` is open in `G`.
  have h_fix : ∀ᶠ k : K in nhds 1, (k : G) ∈ rightStabilizer f := by
    filter_upwards [o.out] with k (hk : χ k = 1) g
    simpa [hk] using congrFun (hf k) g
  exact (rightStabilizer f).isOpen_of_mem_nhds (hK.isOpenMap_subtype_val.nhds_le 1 h_fix)

/-! ### Forms supported on one class -/

variable (K) in
/-- For injective `e` and `K` of finite type for `e(Γ)`, the finite set of the `γ : Γ` with
`x⁻¹ * e γ * y ∈ K`. -/
noncomputable def transporter (x y : G) : Finset Γ :=
  (exists_transporter e.range i.out .rfl K x y).choose

open scoped Classical in
variable {e} in
/-- The two properties of `transporter K e x y` given by `exists_transporter`: its elements and
their number. -/
lemma mem_transporter_iff_and_card (x y : G) :
    (∀ γ : Γ, γ ∈ transporter K e x y ↔ e γ ∈ e.range ∧ x⁻¹ * e γ * y ∈ K) ∧
      #(transporter K e x y) = if DoubleCoset.mk e.range K x = DoubleCoset.mk e.range K y then
        Nat.card (classAut e.range K x) else 0 :=
  (exists_transporter e.range i.out e.coe_range.subset K x y).choose_spec

variable {e} in
lemma mem_transporter {x y : G} {γ : Γ} : γ ∈ transporter K e x y ↔ x⁻¹ * e γ * y ∈ K := by
  rw [(mem_transporter_iff_and_card x y).left γ, and_iff_right ⟨γ, rfl⟩]

open scoped Classical in
/-- Let `e` be injective and `(e(Γ), K)` of finite type. Then the set `transporter K e x y` of the
`γ : Γ` with `x⁻¹ * e γ * y ∈ K` has as many elements as the stabiliser
`classAut e.range K x = e(Γ) ∩ x K x⁻¹` if `x` and `y` lie in the same double coset. It is empty
otherwise. -/
lemma card_transporter (x y : G) :
    #(transporter K e x y) = if DoubleCoset.mk e.range K x = DoubleCoset.mk e.range K y then
      Nat.card (classAut e.range K x) else 0 :=
  (mem_transporter_iff_and_card x y).right

open scoped Classical in
/-- The function `y ↦ ∑ χ (x⁻¹ * e γ * y) • ρ γ⁻¹ v`, summed over the `γ` with
`x⁻¹ * e γ * y ∈ K`, as a linear map in `v`. -/
noncomputable def deltaFun (x : G) : W →ₗ[ℂ] G → W :=
  .pi fun y : G ↦ ∑ γ ∈ transporter K e x y,
    if h : x⁻¹ * e γ * y ∈ K then χ ⟨x⁻¹ * e γ * y, h⟩ • ρ γ⁻¹ else 0

open scoped Classical in
omit o in
/-- The value of `deltaFun e ρ χ x v` at `y`, as a sum over the `γ` with `x⁻¹ * e γ * y ∈ K`. -/
lemma deltaFun_apply (x : G) (v : W) (y : G) :
    deltaFun e ρ χ x v y = ∑ γ ∈ transporter K e x y,
      if h : x⁻¹ * e γ * y ∈ K then χ ⟨x⁻¹ * e γ * y, h⟩ • ρ γ⁻¹ v else 0 := by
  simp [deltaFun, DFunLike.dite_apply]

omit o in
/-- Right translation by `k ∈ K` multiplies `deltaFun e ρ χ x v` by `χ k`. -/
lemma rightRegular_deltaFun (x : G) (v : W) (k : K) :
    rightRegular ℂ G W k (deltaFun e ρ χ x v) = χ k • deltaFun e ρ χ x v := by
  ext y
  have h_mem (γ : Γ) : x⁻¹ * e γ * (y * k) ∈ K ↔ x⁻¹ * e γ * y ∈ K := by
    rw [← mul_assoc, K.mul_mem_cancel_right k.2]
  have h_set : transporter K e x (y * k) = transporter K e x y := by
    simp [Finset.ext_iff, mem_transporter, h_mem]
  rw [rightRegular_apply_apply, Pi.smul_apply, deltaFun_apply, deltaFun_apply, h_set, smul_sum]
  refine sum_congr rfl fun γ hγ ↦ ?_
  have h_char : χ ⟨x⁻¹ * e γ * (y * k), (h_mem γ).2 (mem_transporter.1 hγ)⟩ =
      χ k * χ ⟨x⁻¹ * e γ * y, mem_transporter.1 hγ⟩ := by
    rw [mul_comm, ← map_mul]
    exact congrArg χ (Subtype.ext (mul_assoc _ y k.val).symm)
  simp [mem_transporter.1 hγ, (h_mem γ).2 (mem_transporter.1 hγ), h_char, mul_smul]

omit o in
/-- The function `deltaFun e ρ χ x v` is left equivariant under `Γ`. -/
lemma deltaFun_map_mul (x : G) (v : W) (γ : Γ) (y : G) :
    deltaFun e ρ χ x v (e γ * y) = ρ γ (deltaFun e ρ χ x v y) := by
  -- Right multiplication by `γ` matches the terms at `e γ * y` with those at `y`.
  rw [deltaFun_apply, deltaFun_apply, _root_.map_sum]
  refine sum_equiv (.mulRight γ) (fun δ ↦ by simp [mem_transporter, mul_assoc]) fun δ hδ ↦ ?_
  simp_all [mem_transporter, mul_assoc]

variable [IsTopologicalGroup G]

/-- The linear map sending `v` to the form of level `(K, χ)` supported on the double coset
`e(Γ) x K` whose value at `y` is the sum of `χ (x⁻¹ * e γ * y) • ρ γ⁻¹ v` over the `γ` with
`x⁻¹ * e γ * y ∈ K`. With `γ⁻¹` in place of `γ`, this is the sum of `χ (x⁻¹ * e γ⁻¹ * y) • ρ γ v`
over the `γ` with `x⁻¹ * e γ⁻¹ * y ∈ K`. -/
noncomputable def deltaForm (x : G) : W →ₗ[ℂ] levelSpace (smoothFormRep e ρ) K χ :=
  .codRestrict (levelSpace (smoothFormRep e ρ) K χ)
    (.codRestrict (SmoothForm e ρ) (deltaFun e ρ χ x) fun v ↦
      ⟨mem_smoothFunctions_of_eigen χ H.isOpen (rightRegular_deltaFun e ρ χ x v),
        deltaFun_map_mul e ρ χ x v⟩)
    fun v k ↦ Subtype.ext (rightRegular_deltaFun e ρ χ x v k)

open scoped Classical in
/-- The value at `y` of `deltaForm e ρ χ x v`, the form of level `(K, χ)` supported on `e(Γ) x K`,
is a sum over the `γ` in `transporter K e x y`, the finite set of `γ : Γ` with `x⁻¹ * e γ * y ∈ K`.
The summand is `χ (x⁻¹ * e γ * y) • ρ γ⁻¹ v`. -/
lemma deltaForm_apply (x : G) (v : W) (y : G) :
    (deltaForm e ρ χ x v).val.val y = ∑ γ ∈ transporter K e x y,
      if h : x⁻¹ * e γ * y ∈ K then χ ⟨x⁻¹ * e γ * y, h⟩ • ρ γ⁻¹ v else 0 :=
  deltaFun_apply e ρ χ x v y

/-- If every stabiliser `classAut e.range K g = e(Γ) ∩ g K g⁻¹` is trivial (a free level) and `r` is
a system of representatives of `e(Γ) \ G / K`, the sum over the classes `c` of the forms
`deltaForm e ρ χ (r c) (f c)` supported on `c` takes the value `f d` at `r d`. -/
lemma sum_deltaForm_apply_rep (h_free : ∀ g : G, classAut e.range K g = ⊥)
    {r : DoubleCosets e.range K → G}
    (hr : ∀ c : DoubleCosets e.range K, DoubleCoset.mk e.range K (r c) = c)
    (f : DoubleCosets e.range K → W) (d : DoubleCosets e.range K) :
    (∑ c : DoubleCosets e.range K, deltaForm e ρ χ (r c) (f c)).val.val (r d) = f d := by
  -- The value is a sum over the classes `c` and the `γ` with `(r c)⁻¹ * e γ * r d ∈ K`. Only the
  -- term `c = d`, `γ = 1` is there.
  have h_off (c : DoubleCosets e.range K) (hc : c ≠ d) : transporter K e (r c) (r d) = ∅ := by
    rw [← card_eq_zero, card_transporter, ite_eq_right (by rwa [hr, hr])]
  have h_diag : transporter K e (r d) (r d) = {1} := (eq_of_subset_of_card_le
    (by simp [mem_transporter]) (by rw [card_transporter, ite_eq_left rfl]; simp [h_free])).symm
  simp only [Submodule.coe_sum, Finset.sum_apply, deltaForm_apply]
  rw [Fintype.sum_eq_single d fun c hc ↦ by rw [h_off c hc, sum_empty], h_diag]
  simp [← K.one_def]

/-- If every stabiliser `classAut e.range K g` is trivial, evaluation at representatives `r c` of
the double cosets `c` in `e(Γ) \ G / K` is a linear isomorphism from the forms of level `(K, χ)` to
the `W`-valued functions on the double cosets. The inverse sends `f` to the sum of the forms
`deltaForm e ρ χ (r c) (f c)`. -/
noncomputable def freeLevelEquiv (h_free : ∀ g : G, classAut e.range K g = ⊥)
    {r : DoubleCosets e.range K → G}
    (hr : ∀ c : DoubleCosets e.range K, DoubleCoset.mk e.range K (r c) = c) :
    levelSpace (smoothFormRep e ρ) K χ ≃ₗ[ℂ] DoubleCosets e.range K → W where
  toLinearMap := evalClassReps e ρ χ r
  invFun f := ∑ c : DoubleCosets e.range K, deltaForm e ρ χ (r c) (f c)
  left_inv φ :=
    levelSpace_ext_doubleCosets hr (sum_deltaForm_apply_rep e ρ χ h_free hr
      (evalClassReps e ρ χ r φ))
  right_inv f := funext (sum_deltaForm_apply_rep e ρ χ h_free hr f)

/-- `freeLevelEquiv` sends a form to its values at the representatives `r c`. -/
lemma freeLevelEquiv_apply (h_free : ∀ g : G, classAut e.range K g = ⊥)
    {r : DoubleCosets e.range K → G}
    (hr : ∀ c : DoubleCosets e.range K, DoubleCoset.mk e.range K (r c) = c)
    (φ : levelSpace (smoothFormRep e ρ) K χ) (c : DoubleCosets e.range K) :
    freeLevelEquiv e ρ χ h_free hr φ c = φ.val.val (r c) :=
  rfl

/-- The inverse of `freeLevelEquiv` sends `f` to the sum over the classes `c` of the forms
`deltaForm e ρ χ (r c) (f c)`. -/
lemma freeLevelEquiv_symm_apply (h_free : ∀ g : G, classAut e.range K g = ⊥)
    {r : DoubleCosets e.range K → G}
    (hr : ∀ c : DoubleCosets e.range K, DoubleCoset.mk e.range K (r c) = c)
    (f : DoubleCosets e.range K → W) :
    (freeLevelEquiv e ρ χ h_free hr).symm f =
      ∑ c : DoubleCosets e.range K, deltaForm e ρ χ (r c) (f c) :=
  rfl

variable {e ρ χ}

/-- Let `e` be injective, `χ` trivial near `1` and `K` of finite type for `e(Γ)`
(`New.HasFiniteType`). If additive maps `L g : W →+ ℂ` satisfy
`L (e γ * x * k) (χ k • ρ γ v) = L x v` for all `γ` and `k`, then the class sum (`New.classSum`,
over `e(Γ) \ G / K`, weighted by the inverse orders of the stabilisers) of `g ↦ L g (δ g)` is
`L x v`, where `δ = deltaForm e ρ χ x v` is the form supported on `e(Γ) x K` made from `v`. -/
lemma classSum_deltaForm (L : G → W →+ ℂ) {x : G} {v : W}
    (hL : ∀ (γ : Γ) (k : K), L (e γ * x * k) (χ k • ρ γ v) = L x v) :
    classSum e.range K (fun g : G ↦ L g ((deltaForm e ρ χ x v).val.val g)) = L x v := by
  -- The value of the form at `y` is a sum over `transporter K e x y`, and `L y` sends each term
  -- to `L x v`.
  have h_term (y : G) (γ : Γ) (h : x⁻¹ * e γ * y ∈ K) :
      L y (χ ⟨x⁻¹ * e γ * y, h⟩ • ρ γ⁻¹ v) = L x v := by
    simpa [mul_assoc] using hL γ⁻¹ ⟨x⁻¹ * e γ * y, h⟩
  have h_value (y : G) :
      L y ((deltaForm e ρ χ x v).val.val y) = #(transporter K e x y) • L x v := by
    rw [deltaForm_apply, map_sum]
    exact sum_eq_card_nsmul fun γ hγ ↦ by rw [dite_eq_left (mem_transporter.1 hγ), h_term]
  -- Only the class of `x` counts, and `classSum` divides by the order of its `classAut`.
  have h_class (c : DoubleCosets e.range K) : mk e.range K c.out = c := DoubleCoset.out_eq' ..
  rw [classSum, finsum_eq_single _ (mk e.range K x)]
  · rw [h_value, card_transporter, ite_eq_left (h_class _).symm, ← card_classAut_out x,
      ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ (Nat.cast_ne_zero.2 Nat.card_pos.ne')]
  · exact fun c hc ↦ by
      rw [h_value, card_transporter, ite_eq_right (by rwa [h_class, eq_comm]), zero_smul, smul_zero]

/-! ### Dimension -/

/-- Forms embed in the `W`-valued functions on the finite set of classes, by their values at
representatives, so they span a finite-dimensional space. -/
instance finite_levelSpace_smoothFormRep [Module.Finite ℂ W] :
    Module.Finite ℂ (levelSpace (smoothFormRep e ρ) K χ) :=
  .of_injective (evalClassReps e ρ χ Quot.out) (evalClassReps_injective Quot.out_eq)

/-- Let `e : Γ →* G` be injective, `K` a level of finite type for `e(Γ)` (`New.HasFiniteType`), `χ`
a character of `K` trivial near `1` and `ρ` a finite-dimensional representation of `Γ` on `W`. If
all stabilisers `classAut e.range K g = e(Γ) ∩ g K g⁻¹` are trivial, the space of smooth
`φ : G → W` with `φ (e γ * g * k) = χ k • ρ γ (φ g)` has dimension the number of double cosets
`e(Γ) \ G / K` times the dimension of `W`. -/
lemma finrank_levelSpace_smoothFormRep [Module.Finite ℂ W]
    (h_free : ∀ g : G, classAut e.range K g = ⊥) :
    finrank ℂ (levelSpace (smoothFormRep e ρ) K χ) =
      Nat.card (DoubleCosets e.range K) * finrank ℂ W := by
  simp [(freeLevelEquiv e ρ χ h_free Quot.out_eq).finrank_eq, finrank_pi_fintype]

end New

/-! ## Unitarity of right translation and finiteness at open level -/

section FormRepresentation

open Submodule Subgroup ComplexOrder

namespace New.Space

variable {E n : Type} [Field E] [Fintype n] [DecidableEq n] [CMType E] (V : Space E n 1)
  (κ : Weight E)

/-- For a definite hermitian space `V` and a weight `κ`, the forms of weight `κ` on `V` carry a
sesquilinear form `B` that is positive definite and invariant under right translation by the finite
adelic unitary group (`New.IsUnitary`). -/
lemma exists_isUnitary_formTranslation :
    ∃ B : V.forms κ →ₗ⋆[ℂ] V.forms κ →ₗ[ℂ] ℂ, IsUnitary (V.formTranslation κ) B := by
  -- The inner product is the mean over `Γ \ G_f` of the Gram pairing of the values.
  refine ⟨smoothPairing _ fun _ ↦ gramForm_conjWeylRep _, fun φ hφ ↦ ?_,
    smoothPairing_formTranslation _⟩
  -- Positivity: `f g = ⟨φ g, φ g⟩` is nonnegative and positive at some `g`.
  let f : Gf E n → ℂ := fun g ↦ gramForm (φ.1 g) (φ.1 g)
  obtain ⟨hf_left, hf_open⟩ : f ∈ smoothInvariants V.Γf :=
    pairing_mem_smoothInvariants (fun _ ↦ gramForm_conjWeylRep _) φ φ
  obtain ⟨g, hg⟩ : ∃ g : Gf E n, φ.1 g ≠ 0 := Function.ne_iff.1 fun h ↦ hφ (Subtype.ext h)
  have hf_nonneg : ∀ g : Gf E n, 0 ≤ f g := by simp [f, gramForm, weylGramOver_posDef.posSemidef]
  have hf_pos : 0 < f g := by simp [f, gramForm, weylGramOver_posDef.dotProduct_mulVec_pos hg]
  -- The mean is a positive multiple of the class sum at the level `rightStabilizer f ⊓ stdLevel`
  -- fixing `f`.
  have : HasFiniteType V.Γf (rightStabilizer f ⊓ stdLevel E n) :=
    .of_le inf_le_right (hf_open.and isOpen_stdLevel)
  have h_sum : 0 < classSum V.Γf (rightStabilizer f ⊓ stdLevel E n) f :=
    classSum_pos hf_nonneg ((apply_doubleCoset_out hf_left inf_le_left g).trans_gt hf_pos)
  change 0 < classIntegral V.Γf (stdLevel E n) f
  exact smul_pos (by positivity [isCompact_stdLevel.relIndex_ne_zero hf_open]) h_sum

/-- For an open subgroup K of the finite adelic points and a character χ of K, the forms of
weight κ on a positive definite V on which K acts through χ form a finite-dimensional
complex vector space. -/
lemma finite_formTranslation_levelSpace {K : Subgroup (Gf E n)} (hK : K.IsOpen) (χ : K →* ℂ := 1) :
    Module.Finite ℂ (levelSpace (V.formTranslation κ) K χ) := by
  -- The level `K ⊓ stdLevel` is open in `stdLevel`, so it inherits `HasFiniteType` and has a
  -- finite-dimensional eigenspace, which contains the eigenforms of level `K`.
  have h_fin : HasFiniteType V.embFin.range (K ⊓ stdLevel E n) :=
    .of_le inf_le_right (hK.and isOpen_stdLevel)
  let χ' : (K ⊓ stdLevel E n : Subgroup (Gf E n)) →* ℂ := χ.comp (Subgroup.inclusion inf_le_left)
  have : Module.Finite ℂ (levelSpace (V.formTranslation κ) (K ⊓ stdLevel E n) χ') :=
    finite_levelSpace_smoothFormRep (H := h_fin)
  have h_le : levelSpace (V.formTranslation κ) K χ ≤
      levelSpace (V.formTranslation κ) (K ⊓ stdLevel E n) χ' :=
    fun _ h k ↦ h ⟨k, k.property.left⟩
  exact finiteDimensional_of_le h_le

end New.Space

end FormRepresentation

/-!
## Hecke polynomials and spanning by eigenforms for forms spherical off a finite set

The forms here live on a definite unitary space and have maximal level off a finite set `S`.

`New.Gf` is the finite adelic unitary group, `New.stdLevel` its integral points,
`New.maxCompactAt n w` those supported at `w, w̄`, `New.Gf.trivialOn n S` the elements trivial at
`S`.

* `New.exists_inf_trivialOn_le`: an open subgroup contains the integral points trivial at some
  finite set `S`, which avoids each `w, w̄` for which the subgroup contains `maxCompactAt n w`.
-/

namespace New

open Submodule Gf

variable {E n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]

/-- For an open subgroup `H` of the finite adelic unitary group there is a finite set `S` of
places such that (a) neither `w` nor its conjugate is in `S` when `H` contains `maxCompactAt n w`,
the integral points supported at `w, w̄`, and (b) `H` contains all integral points (`stdLevel E n`)
that are trivial at `S`. -/
lemma exists_inf_trivialOn_le {H : Subgroup (Gf E n)} (hH : H.IsOpen) :
    ∃ S : Finset (FinPlace E), (∀ w : FinPlace E, maxCompactAt n w ≤ H → w ∉ S ∧ star w ∉ S) ∧
      stdLevel E n ⊓ trivialOn n S ≤ H := by
  classical
  -- The compact set `stdLevel \ H` is covered by the open sets `{g | g.atPlace w ≠ 1}`; a finite
  -- subcover is a finite `S` with `stdLevel ⊓ trivialOn S ≤ H`. Take a minimal such `S`.
  have hex : ∃ S : Finset (FinPlace E), stdLevel E n ⊓ trivialOn n S ≤ H := by
    have h_cover : (stdLevel E n : Set (Gf E n)) \ H ⊆ ⋃ w : FinPlace E, {g | g.atPlace w ≠ 1} := by
      intro g hg
      have hg_ne : g ≠ 1 := (H.one_mem.ne_of_notMem hg.right).symm
      simpa using mt Gf.ext hg_ne
    obtain ⟨S, hS⟩ := (isCompact_stdLevel.diff hH).elim_finite_subcover _
      (fun w ↦ isOpen_ne_fun (continuous_atPlace w) continuous_const) h_cover
    refine ⟨S, fun g ⟨hg, hoff⟩ ↦ by_contra fun hgH ↦ ?_⟩
    simpa +contextual [mem_trivialOn.1 hoff] using hS ⟨hg, hgH⟩
  obtain ⟨S, hS, hmin⟩ := exists_minimal_of_wellFoundedLT _ hex
  refine ⟨S, fun w hw ↦ ?_, hS⟩
  -- If `maxCompactAt n w ≤ H`, the places `w, w̄` can be dropped from `S`: write `g = a * b` with
  -- `a` supported at `w, w̄` and `b` trivial there; `a ∈ maxCompactAt n w`, and `b` is trivial on
  -- all of `S`.
  have hdrop : stdLevel E n ⊓ trivialOn n (S \ {w, star w} : Finset _) ≤ H := by
    rintro g ⟨hg, hoff⟩
    obtain ⟨a, ha, b, hb, rfl, hab⟩ := exists_supportedOn_mul_trivialOn {w} g
    obtain ⟨ha_int, hb_int⟩ : a ∈ stdLevel E n ∧ b ∈ stdLevel E n := hab hg
    refine mul_mem (hw ⟨ha_int, ha⟩) (hS ⟨hb_int, mem_trivialOn.2 fun u hu ↦ ?_⟩)
    have hoff_u : u ∈ (↑(S \ {w, star w}) : Set (FinPlace E)) → (a * b).atPlace u = 1 :=
      mem_trivialOn.1 hoff u
    grind [mem_trivialOn, mem_supportedOn, atPlace_star_eq_one_iff, star_star]
  have hsub : S ⊆ S \ {w, star w} := hmin hdrop Finset.sdiff_subset
  grind

/-- An open subgroup `K` of the finite adelic group contains `maxCompactAt n v`, the integral
elements supported at `v` and its conjugate, for almost all places `v`. -/
lemma eventually_maxCompactAt_le {K : Subgroup (Gf E n)} (hK : K.IsOpen) :
    ∀ᶠ v : FinPlace E in Filter.cofinite, maxCompactAt n v ≤ K := by
  obtain ⟨S, -, hS⟩ := exists_inf_trivialOn_le hK
  filter_upwards [S.finite_toSet.conjClosure.eventually_cofinite_notMem] with v hv
  -- Elements supported at `v` and its conjugate are trivial at every place of `S`.
  have h_trivial : supportedOn n {v} ≤ trivialOn n (S : Set (FinPlace E)) := by
    rw [← supportedOn_compl]
    exact supportedOn_mono (Set.singleton_subset_iff.2 hv)
  exact le_trans (inf_le_inf_left (stdLevel E n) h_trivial) hS

variable {V : Space E n 1} {κ : Weight E} {S : Finset (FinPlace E)} {f : V.forms κ} {w : FinPlace E}

/-- A form f has Hecke polynomial P at a split place w (`New.HasHeckePolyAt`) if and only if f is in
`sphericalAt` at w (is fixed by the integral points K_w supported at w, w̄) and there are scalars
t_j with T_{w,j} f = t_j f for the Hecke operators T_{w,j} = `heckeSplit (V.formTranslation κ) hw j`
at w acting on forms (they commute with the inclusion of forms in functions) and P = Σ_{j ≤ N}
(−1)^j q_w^{j(j−1)/2} t_j X^{N−j} with N = `Fintype.card n`, which is `heckePoly w.q N t`. -/
lemma hasHeckePolyAt_iff (hw : star w ≠ w) {P : Polynomial ℂ} :
    HasHeckePolyAt f.val w hw P ↔
      f ∈ sphericalAt (V.formTranslation κ) w ∧
        ∃ t : ℕ → ℂ, P = heckePoly w.q (Fintype.card n) t ∧
          ∀ j : ℕ, heckeSplit (V.formTranslation κ) hw j f = t j • f := by
  -- The inclusion of forms in functions commutes with the Hecke operators.
  have h_map (j : ℕ) : heckeSplit (rightRegular ℂ (Gf E n) (WeylIndex n κ.1 → ℂ)) hw j f.val =
      (heckeSplit (V.formTranslation κ) hw j f).val :=
    (map_heckeSplit hw j (V.forms κ).subtype fun _ _ ↦ rfl).symm
  simp [HasHeckePolyAt, h_map, Subtype.ext_iff]

/-- For a split place `w` and an open subgroup `H`, the preimage of `H` under the endomorphism of
the finite adelic unitary group that replaces the components at `w` and `w̄` by `1`. -/
noncomputable def offPartComap (hw : star w ≠ w) (H : OpenSubgroup (Gf E n)) :
    OpenSubgroup (Gf E n) :=
  H.comap
    (MonoidHom.mk' (fun g ↦ g * (ofSplitPlace hw (g.atPlace w))⁻¹) (by
      simp [(commute_supportedOn_trivialOn (ofSplitPlace_mem_supportedOn _ _) _).inv_left.eq,
        mul_assoc]))
    (by simp; fun_prop)

/-- Let `V` be a definite hermitian space, `κ` a weight, `S` a finite set of finite places and `M` a
finite-dimensional space of forms of weight `κ` on `V`. Suppose that the integral points trivial at
`S` (`stdLevel E n ⊓ trivialOn n S`) fix `M` pointwise, and that `M` is stable under the Hecke
operators `T_{w,j} = heckeSplit _ hw j` at all split `w` with `w, w̄ ∉ S`. Then `M` is spanned by
its elements f with `IsSphericalOff S f P` for some `P`: f is nonzero, fixed by
`stdLevel E n ⊓ trivialOn n S`, and has a Hecke polynomial `P w` at each such `w`. -/
lemma le_span_isSphericalOff (M : Submodule ℂ (V.forms κ))
    (h_level : M ≤ levelSpace (V.formTranslation κ) (stdLevel E n ⊓ trivialOn n S) 1)
    [Module.Finite ℂ M]
    (h_hecke : ∀ (w : FinPlace E) (hw : w.IsSplit), w ∉ S → star w ∉ S →
      ∀ j : ℕ, ∀ f ∈ M, heckeSplit (V.formTranslation κ) hw j f ∈ M) :
    M ≤ span ℂ {f ∈ M | ∃ P : FinPlace E → Polynomial ℂ, IsSphericalOff S f.val P} := by
  -- Right translation is unitary for an inner product `B`, so the spectral theorem applies at the
  -- set `T` of split places `w` with `w, w̄ ∉ S`: `M` is spanned by joint eigenvectors.
  obtain ⟨B, hB⟩ := V.exists_isUnitary_formTranslation κ
  let T : Set (FinPlace E) := {w | w.IsSplit ∧ w ∉ S ∧ star w ∉ S}
  have h_star : ∀ w ∈ T, star w ∈ T :=
    fun w ⟨hw, hS, hS_star⟩ ↦ ⟨hw.star, hS_star, by rwa [star_star]⟩
  have h_span : M ≤ span ℂ {f ∈ M | ∃ t : FinPlace E → ℕ → ℂ, ∀ w ∈ T, ∀ (hw : w.IsSplit) (j : ℕ),
      heckeSplit (V.formTranslation κ) hw j f = t w j • f} :=
    hB.le_span_joint_eigenvectors (fun w hw ↦ hw.left) h_star
      (fun w ⟨_, hS, hS_star⟩ ↦ h_level.trans (levelSpace_le_sphericalAt hS hS_star))
      fun w ⟨_, hS, hS_star⟩ hw ↦ h_hecke w hw hS hS_star
  refine h_span.trans (span_le.2 ?_)
  -- A nonzero joint eigenvector has at `w` the Hecke polynomial formed from its eigenvalues.
  rintro f ⟨hf, t, h_eigen⟩
  obtain rfl | hf_ne := eq_or_ne f 0
  · exact zero_mem _
  have h_fixed : ∀ k ∈ stdLevel E n ⊓ trivialOn n S, rightRegular ℂ (Gf E n) _ k f.val = f.val :=
    fun k hk ↦ by simpa using congrArg Subtype.val (h_level hf ⟨k, hk⟩)
  have h_poly (w : FinPlace E) (hw : star w ≠ w) (hS : w ∉ S) (hS_star : star w ∉ S) :
      HasHeckePolyAt f.val w hw (heckePoly w.q (Fintype.card n) (t w)) :=
    (hasHeckePolyAt_iff hw).2 ⟨levelSpace_le_sphericalAt hS hS_star (h_level hf), t w, rfl,
      h_eigen w ⟨hw, hS, hS_star⟩ hw⟩
  exact subset_span ⟨hf, _, by simpa using hf_ne, h_fixed, h_poly⟩

end New
