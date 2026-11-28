import Lib.General.LinearAlgebra.Eigenvalues
import Lib.Weil.Unramified.HeckeGL

/-!
# Hecke operators and Hecke polynomials at split places; spherical eigenvectors

Let `w` be a split finite place (`star w ≠ w`) with residue field of order `q`. Through
`New.ofSplitPlace`, the spherical Hecke operators of `GL_n(E_w)` act on representations of the
finite adelic unitary group `New.Gf`. A vector is spherical at `w` when it lies in
`New.sphericalAt`, that is, when it is fixed by the integral elements `New.maxCompactAt` supported
at `w` and `w̄`.

## Main definitions and results

* `New.heckeSplit`: the operator `T_{w,j}` of the double coset `New.basicDoubleCoset` of
  `diag (ϖ 1_j, 1)`.
* `New.heckeSplit_star`: on vectors spherical at `w`, `T_{w̄,j}` is the action at `w` of the inverse
  double coset. Hence `New.heckeSplit_dual` (`ϖ T_{w̄,i} = T_{w,n-i}` on such vectors) and
  `New.heckeSplit_adjoint` (`T_{w̄,j}` is adjoint to `T_{w,j}` on spherical vectors, for a
  `G_f`-invariant pairing).
* `New.heckeSplit_comm`: the operators at two split places commute on vectors spherical at both.
* `New.IsUnitary.le_span_joint_eigenvectors`: in a representation unitary for a form `B`
  (`B y y > 0` for `y ≠ 0`, `B (π g x) (π g y) = B x y`), a finite-dimensional stable space of
  spherical vectors is spanned by joint eigenvectors. `New.IsUnitary.le_span_hecke_eigenvectors` is
  the form for places given by a predicate.
* `New.heckePolyEval`, `New.heckePolyOp`: the Hecke polynomial `∑ (-X)^i q^(i choose 2) T_{w,i}`,
  where `i` runs from `0` to `n`, `q` is the order of the residue field at `w`, and
  `New.heckePolyOp` takes the `T_{w,i}` to be the operators `New.heckeSplit`, while
  `New.heckePolyEval` allows any coefficients `t i`.
* `New.HasHeckePolynomial`: vectors spherical at `w` (`New.sphericalAt`) on which this polynomial
  acts by given scalars.

Notions from other files:
* `New.levelSpace`: For a representation π of G, a subgroup K and a character χ of K, the submodule
  of vectors v with π(k)v = χ(k)v for all k in K.
* `New.heckeFun`: For a function f on G, the operator ∑ f(g)π(g), summed over representatives g of
  G/K.
* `New.stdLevel`: The subgroup K₀ = G_f ∩ GL_n(Ô) of the finite adelic unitary group.
* `New.Gf.supportedOn`: The subgroup of G_f of elements supported on S ∪ S̄, that is, with component
  1 at every place outside S ∪ S̄; `New.Gf.trivialOn`: those with component 1 at every place in S.
* `New.localIntGL`: For a finite place w of E, the subgroup GL_n(O_w) of GL_n(E_w) of matrices that,
  with their inverses, have entries in the local integers.

## Relation to the literature

Known; see `Lib.General.LinearAlgebra.IntegralLattices` for sources.
-/

namespace New

section SplitHecke

open Matrix NumberField Gf Set RingHom

variable {n A W W' E : Type*} [Fintype n] [DecidableEq n] [Field E] [NumberField E] [IsCMField E]
  [CommRing A] [AddCommGroup W] [Module A W] [AddCommGroup W'] [Module A W']
  {w u : FinPlace E} (π : Representation A (Gf E n) W) {π' : Representation A (Gf E n) W'} {v : W}

variable (n w) in
/-- The subgroup of K₀ of elements whose components away from w and w̄ are 1. -/
noncomputable abbrev maxCompactAt : Subgroup (Gf E n) := stdLevel E n ⊓ supportedOn n {w}

/-- The Hecke operator `T_{w,j}` at a split place `w`: the operator of the double coset of
`diag (ϖ 1_j, 1)` in `GL_n(E_w)`, acting through the embedding `ofSplitPlace hw` of `GL_n(E_w)` in
the finite adelic unitary group. -/
noncomputable def heckeSplit (hw : w.IsSplit) (j : ℕ) : Module.End A W :=
  heckeGL (π.comp (ofSplitPlace hw)) j

/-- `T_{w,j}` is the operator `New.heckeFun` of the indicator function of the double coset. -/
lemma heckeSplit_eq_heckeFun (hw : w.IsSplit) (j : ℕ) :
    heckeSplit π hw j =
      heckeFun (π.comp (ofSplitPlace hw)) (localIntGL n w) ((basicDoubleCoset n w j).indicator 1) :=
        rfl

/-- For a representation π of G_f, the vectors spherical at w: those fixed by all elements of K₀
whose components away from w and w̄ are 1. -/
noncomputable abbrev sphericalAt (w : FinPlace E) : Submodule A W := levelSpace π (maxCompactAt n w)

variable {π} {σ : A →+* A}

/-- The conjugate of a split place is split. -/
lemma FinPlace.IsSplit.star (hw : w.IsSplit) : (Star.star w).IsSplit := star_injective.ne hw

/-- The elements supported at `w, w̄` do not depend on which of the two places is named. -/
lemma Gf.supportedOn_star : supportedOn n {star w} = supportedOn n {w} := by aesop

/-- For a finite set S of places containing neither w nor w̄, every vector of π fixed by the
elements of K₀ with component 1 at all places of S is spherical at w. -/
lemma levelSpace_le_sphericalAt {S : Finset (FinPlace E)} (hw : w ∉ S) (hw' : star w ∉ S) :
    levelSpace π (stdLevel E n ⊓ trivialOn n S) ≤ sphericalAt π w := by
  -- An element supported at `w, w̄` has component 1 at the places of `S`.
  have h_supp : supportedOn n {w} ≤ trivialOn n S := by
    intro g hg
    have h_one : ∀ u : FinPlace E, u ≠ w → star u ≠ w → g.atPlace u = 1 := by simpa using hg
    suffices h_S : ∀ u ∈ S, g.atPlace u = 1 by simpa [trivialOn] using h_S
    exact fun u hu ↦ h_one u (ne_of_mem_of_not_mem hu hw)
      (by simpa using star_injective.ne (ne_of_mem_of_not_mem hu hw'))
  exact levelSpace_anti (inf_le_inf_left (stdLevel E n) h_supp)

/-- At a split place, spherical means fixed by `GL_n(O_w)` acting through `New.ofSplitPlace`. -/
lemma mem_sphericalAt_iff (hw : w.IsSplit) :
    v ∈ sphericalAt π w ↔ v ∈ levelSpace (π.comp (ofSplitPlace hw)) (localIntGL n w) := by
  simp [inf_comm (stdLevel E n), ← range_ofSplitPlace hw]

/-- A semilinear map `L` that intertwines, on `v`, the actions of the elements supported at
`w, w̄` intertwines the Hecke operators `T_{w,j}` on `v`. -/
lemma map_heckeSplit (hw : w.IsSplit) (j : ℕ) (L : W →ₛₗ[σ] W')
    (hL : ∀ g ∈ supportedOn n {w}, L (π g v) = π' g (L v) := by tauto) :
    L (heckeSplit π hw j v) = heckeSplit π' hw j (L v) := by
  -- The operator is a finite sum, with coefficients `0` or `1`, of elements supported at `w, w̄`.
  simp [heckeSplit, heckeGL, heckeFun_eq_sum_toFinset, map_indicator, hL]

/-- An element with component 1 at `w` (hence at `w̄`) commutes with `T_{w,j}` on every vector. -/
lemma heckeSplit_comm_of_trivialOn (hw : w.IsSplit) (j : ℕ) {g : Gf E n}
    (hg : g ∈ trivialOn n {w}) :
    π g (heckeSplit π hw j v) = heckeSplit π hw j (π g v) := by
  -- An element trivial at `w, w̄` commutes with every element supported there.
  refine map_heckeSplit hw j (π g) fun k hk ↦ ?_
  have h_comm : Commute k g := commute_supportedOn_trivialOn hk hg
  calc π g (π k v) = π (g * k) v := by rw [map_mul, Module.End.mul_apply]
    _ = π (k * g) v := by rw [h_comm.eq]
    _ = π k (π g v) := by rw [map_mul, Module.End.mul_apply]

/-! ### The operators on spherical vectors -/

/-- For `w` split and `v` spherical at `w`, the vector `T_{w̄,j} v` is the action on `v`, through
`GL_n(E_w)`, of the indicator function of the inverse of the double coset of `diag (ϖ 1_j, 1)`. -/
lemma heckeSplit_star (hw : w.IsSplit) (j : ℕ) (hv : v ∈ sphericalAt π w) :
    heckeSplit π hw.star j v =
      heckeFun (π.comp (ofSplitPlace hw)) (localIntGL n w)
        (fun g : GL n (LocField w) ↦ (basicDoubleCoset n w j).indicator 1 g⁻¹) v := by
  -- Transport the operator along `φ : GL_n(E_w̄) → G_f → GL_n(E_w)`, which by `atPlace_star` is
  -- the conjugate transpose inverse; `heckeFun_comp` asks for the facts below.
  let φ : GL n (LocField (star w)) →* GL n (LocField w) :=
    (atPlace w).comp (ofSplitPlace (n := n) hw.star)
  have h_right_inv : ∀ (g : GL n (LocField w)) (k : localIntGL n w),
      (basicDoubleCoset n w j).indicator (1 : GL n (LocField w) → A) (g * k)⁻¹ =
        (basicDoubleCoset n w j).indicator 1 g⁻¹ := by simp
  have h_finite : HasFiniteCosets (localIntGL n (star w))
    ((basicDoubleCoset n (star w) j).indicator (1 : GL n (LocField (star w)) → A)) := by simp
  -- `φ` is onto: the groups embedded at `w` and at `w̄` have the same image.
  have h_surj : Function.Surjective φ := by
    intro g
    obtain ⟨a, ha⟩ := (range_ofSplitPlace hw.star).ge
      (supportedOn_star.ge (ofSplitPlace_mem_supportedOn (n := n) hw g))
    exact ⟨a, by simp [φ, ha]⟩
  -- `φ` matches the maximal compact subgroups.
  have h_level (g : GL n (LocField (star w))) :
    φ g ∈ localIntGL n w ↔ g ∈ localIntGL n (star w) := by
    simp [φ, ← atPlace_star_mem_iff]
  -- The two actions agree: both elements are supported at `w, w̄` with the same `w`-component.
  have h_act (g : GL n (LocField (star w))) :
      π (ofSplitPlace hw.star g) v = π (ofSplitPlace hw (φ g)) v := by
    have h_eq : ofSplitPlace hw.star g = ofSplitPlace hw (φ g) :=
      eq_of_supportedOn (supportedOn_star.le (ofSplitPlace_mem_supportedOn hw.star g))
        (ofSplitPlace_mem_supportedOn hw (φ g)) (by simp [φ])
    rw [h_eq]
  -- The conditions defining `basicDoubleCoset` are stable under the conjugate transpose.
  have h_fun (g : GL n (LocField (star w))) :
      (basicDoubleCoset n (star w) j).indicator (1 : GL n (LocField (star w)) → A) g =
        (basicDoubleCoset n w j).indicator 1 (φ g)⁻¹ := by
    -- `(φ g)⁻¹` is the conjugate transpose of `g`, which keeps the three conditions.
    -- (`-coe_units_inv`: the inverse must stay on the unit for `map_inv` to move it inside.)
    have h_mem : (φ g)⁻¹ ∈ basicDoubleCoset n w j ↔ g ∈ basicDoubleCoset n (star w) j := by
      simp [φ, basicDoubleCoset, ← map_inv, atPlace_star (star_star _), -coe_units_inv,
        ← mapMatrix_apply, ← map_det]
      aesop
    exact Set.indicator_eq_indicator h_mem.symm rfl
  rw [heckeSplit_eq_heckeFun]
  exact heckeFun_comp φ h_right_inv ((mem_sphericalAt_iff hw).mp hv) h_finite h_surj h_level h_act
    h_fun

/-- For a uniformiser `ϖ` of `E_w`, `n = i + j` and `v` spherical at the split place `w`: applying
`T_{w̄,i}` and then the scalar matrix `ϖ` embedded at `w` gives `T_{w,j} v`. -/
lemma heckeSplit_dual (hw : w.IsSplit) (i j : ℕ) (hv : v ∈ sphericalAt π w) {ϖ : (LocField w)ˣ}
    (hϖ : Valued.v ϖ.val = WithZero.exp (-1)) (hn : Fintype.card n = i + j) :
    π (ofSplitPlace hw (GeneralLinearGroup.scalar n ϖ)) (heckeSplit π hw.star i v) =
      heckeSplit π hw j v := by
  rw [heckeSplit_star hw i hv]
  exact heckeGL_dual ((mem_sphericalAt_iff hw).mp hv) hϖ hn

/-- On a spherical vector, `T_{w,j}` commutes with every element that is integral at `w`. -/
lemma heckeSplit_comm_of_atPlace_mem (hw : w.IsSplit) (j : ℕ) (hv : v ∈ sphericalAt π w)
    {g : Gf E n} (hg : g.atPlace w ∈ localIntGL n w) :
    heckeSplit π hw j (π g v) = π g (heckeSplit π hw j v) := by
  -- Write `g = g / k * k` with `k = ofSplitPlace hw (g.atPlace w)`, so that `g / k` is trivial at
  -- `w`. Then `k` fixes both `v` and `heckeSplit π hw j v`, and `g / k` commutes with the operator.
  set k : Gf E n := ofSplitPlace hw (g.atPlace w) with hk
  have h_sph : v ∈ levelSpace (π.comp (ofSplitPlace hw)) (localIntGL n w) :=
    (mem_sphericalAt_iff hw).mp hv
  have h_off : g / k ∈ trivialOn n {w} := by simp [trivialOn, hk]
  have h_fix : π k v = v := by simpa using mem_levelSpace.mp h_sph ⟨_, hg⟩
  have h_T_sph : heckeSplit π hw j v ∈ levelSpace (π.comp (ofSplitPlace hw)) (localIntGL n w) := by
    rw [heckeSplit_eq_heckeFun]
    exact (isHeckeFunction_basicDoubleCoset j).heckeFun_mem h_sph
  have h_fix_T : π k (heckeSplit π hw j v) = heckeSplit π hw j v := by
    simpa using mem_levelSpace.mp h_T_sph ⟨g.atPlace w, hg⟩
  have h_g (x : W) : π g x = π (g / k) (π k x) := by
    rw [← Module.End.mul_apply (π (g / k)) (π k), ← map_mul, div_mul_cancel]
  calc heckeSplit π hw j (π g v) = heckeSplit π hw j (π (g / k) v) := by rw [h_g, h_fix]
    _ = π (g / k) (heckeSplit π hw j v) := (heckeSplit_comm_of_trivialOn hw j h_off).symm
    _ = π g (heckeSplit π hw j v) := by rw [h_g, h_fix_T]

/-- The adjoint of `T_{w,j}` is `T_{w̄,j}`. Let `w` be split, let `v` and `v'` be spherical at `w`
for `π` and `π'`, and let `B` be an invariant pairing of `π` with `π'`, `σ`-semilinear in the first
variable. Then `B (T_{w,j} v) v' = B v (T_{w̄,j} v')`. -/
lemma heckeSplit_adjoint (hw : w.IsSplit) (j : ℕ) {Z : Type*} [AddCommMonoid Z] [Module A Z]
    (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v' : W'} (hv : v ∈ sphericalAt π w) (hv' : v' ∈ sphericalAt π' w)
    (hB : ∀ (g : Gf E n) (x : W) (y : W'), B (π g x) (π' g y) = B x y) :
    B (heckeSplit π hw j v) v' = B v (heckeSplit π' hw.star j v') := by
  -- The adjoint is the action at `w` of the inverse double coset, which is `T_{w̄,j}` by
  -- `heckeSplit_star`.
  have h_adj : B (heckeSplit π hw j v) v' = B v (heckeFun (π'.comp (ofSplitPlace hw))
    (localIntGL n w) (fun g ↦ σ ((basicDoubleCoset n w j).indicator 1 g⁻¹)) v') :=
    ((isHeckeFunction_basicDoubleCoset j).heckeFun_adjoint B ((mem_sphericalAt_iff hw).mp hv)
      (fun g ↦ hB (ofSplitPlace hw g)) ((mem_sphericalAt_iff hw).mp hv')).right
  -- `σ` fixes the values `0` and `1` of the indicator function.
  have h_sigma : (fun g : GL n (LocField w) ↦ σ ((basicDoubleCoset n w j).indicator 1 g⁻¹)) =
      fun g ↦ (basicDoubleCoset n w j).indicator 1 g⁻¹ := funext fun g ↦ by simp [indicator]
  rw [h_adj, h_sigma, heckeSplit_star hw j hv']

/-- Let w be split, K a subgroup of K₀ and χ a character of K. If v is spherical at w and of
level (K, χ), then T_{w,j} v is of level (K, χ). -/
lemma heckeSplit_mem_levelSpace (hw : w.IsSplit) (j : ℕ) (hv : v ∈ sphericalAt π w)
    {K : Subgroup (Gf E n)} {χ : K →* A} (hK : K ≤ stdLevel E n) (hv_eigen : v ∈ levelSpace π K χ) :
    heckeSplit π hw j v ∈ levelSpace π K χ := by
  -- Elements of `K` are integral at `w`, so on `v` they commute with the operator.
  refine mem_levelSpace.mpr fun k ↦ ?_
  have hk_int : (k : Gf E n).atPlace w ∈ localIntGL n w := mem_stdLevel_iff.mp (hK k.prop) w
  calc π k (heckeSplit π hw j v) = heckeSplit π hw j (π k v) :=
        (heckeSplit_comm_of_atPlace_mem hw j hv hk_int).symm
    _ = χ k • heckeSplit π hw j v := by rw [mem_levelSpace.mp hv_eigen k, map_smul]

omit [IsCMField E] in
/-- The function `g ↦ 1_D(g⁻¹)`, for `D` the double coset `New.basicDoubleCoset n w j`, is
bi-invariant under `GL_n(O_w)` and lives on finitely many cosets. -/
private lemma isHeckeFunction_basicDoubleCoset_inv (w : FinPlace E) (j : ℕ) :
    IsHeckeFunction (A := A) (localIntGL n w)
      (fun g : GL n (LocField w) ↦ (basicDoubleCoset n w j).indicator 1 g⁻¹) := by
  -- Part (a) of `IsHeckeFunction.heckeFun_adjoint` holds for any pairing: take the zero pairing
  -- on the trivial representation and the vector `0`.
  have h_zero : (0 : A) ∈ levelSpace (Representation.trivial A (GL n (LocField w)) A)
    (localIntGL n w) := zero_mem _
  exact ((isHeckeFunction_basicDoubleCoset j).heckeFun_adjoint (σ := RingHom.id A) (Z := A) 0
    h_zero (by simp) h_zero).left

/-- Hecke operators at split places `w` and `u` commute on a vector `v` spherical at both:
`T_{w,i} T_{u,j} v = T_{u,j} T_{w,i} v`. A case of the commutativity of the spherical Hecke
algebra. -/
lemma heckeSplit_comm (hw : w.IsSplit) (hu : u.IsSplit) (i j : ℕ) (hv : v ∈ sphericalAt π w)
    (hv' : v ∈ sphericalAt π u) :
    heckeSplit π hw i (heckeSplit π hu j v) = heckeSplit π hu j (heckeSplit π hw i v) := by
  have h_sph : v ∈ levelSpace (π.comp (ofSplitPlace hw)) (localIntGL n w) :=
    (mem_sphericalAt_iff hw).mp hv
  rcases em (w = u ∨ star w = u) with (rfl | rfl) | h_ne
  · -- same place: Gelfand's trick (`IsHeckeFunction.heckeFun_comm`: bi-invariant functions commute)
    rw [heckeSplit_eq_heckeFun π hw i, heckeSplit_eq_heckeFun π hu j]
    exact (isHeckeFunction_basicDoubleCoset i).heckeFun_comm (isHeckeFunction_basicDoubleCoset j)
      h_sph
  · -- conjugate places: on vectors spherical at `w`, `T_{w̄,j}` is the action at `w` of the inverse
    -- double coset (`heckeSplit_star`), which is again bi-invariant, so Gelfand's trick applies
    have h_Tv_sph : heckeSplit π hw i v ∈ sphericalAt π w :=
      heckeSplit_mem_levelSpace hw i hv inf_le_left hv
    rw [heckeSplit_star hw j h_Tv_sph, heckeSplit_star hw j hv, heckeSplit_eq_heckeFun π hw i]
    exact (isHeckeFunction_basicDoubleCoset i).heckeFun_comm
      (isHeckeFunction_basicDoubleCoset_inv w j)
      h_sph
  · -- different pairs of places: elements supported at `u, ū` are trivial at `w`, so commute with
    -- `T_{w,i}` (`heckeSplit_comm_of_trivialOn`)
    refine map_heckeSplit hu j (heckeSplit π hw i) fun g hg ↦ ?_
    have h_triv : g ∈ trivialOn n {w} := by simp_all [trivialOn, supportedOn]
    exact (heckeSplit_comm_of_trivialOn hw i h_triv).symm

/-! ### Joint eigenvectors in a unitary representation -/

/-- Let `B` be a sesquilinear form with `B y y ≠ 0` for `y ≠ 0`, and let `T'` be adjoint to `T`
and commute with it. If a power of `T' - c` kills `x`, then `T x = star c • x`. -/
lemma eigenvector_of_pow_adjoint {V : Type*} [AddCommGroup V] [Module ℂ V] {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}
    {T T' : Module.End ℂ V} {c : ℂ} (hB : ∀ y : V, B y y = 0 → y = 0)
    (h_adj : ∀ y z : V, B (T y) z = B y (T' z)) (h_comm : ∀ y : V, T (T' y) = T' (T y)) (k : ℕ)
    (x : V) (hx : ((T' - c • 1) ^ k) x = 0) :
    T x = star c • x := by
  induction k generalizing x with
  | zero => simp_all
  | succ k ih =>
    -- `y = (T - c̄) x` is killed by `T' - c`, as `T - c̄` kills `(T' - c) x` by induction.
    -- Moving `T - c̄` across `B` turns it into `T' - c`, so `B y y = 0`.
    set y : V := T x - star c • x with hy
    have h_ih : T (T' x - c • x) = star c • (T' x - c • x) := ih _ (by simpa [pow_succ] using hx)
    have h_kill : T' y - c • y = 0 := by
      simpa [hy, h_comm, smul_sub, smul_comm c, sub_sub_sub_comm] using sub_eq_zero.mpr h_ih
    refine sub_eq_zero.mp (hB y ?_)
    calc B y y = B (T x) y - c * B x y := by simp [hy]
      _ = B x (T' y - c • y) := by simp [h_adj]
      _ = 0 := by simp [h_kill]

open ComplexOrder in
/-- Spectral theorem for spherical Hecke operators. Let `π` be a unitary representation of the
finite adelic unitary group and `S` a set of split places stable under conjugation. Let `U` be a
finite-dimensional subspace, spherical at every `w ∈ S` and stable under every `T_{w,j}` with
`w ∈ S`. Then `U` lies in the span of its vectors `x` that are eigenvectors of all these `T_{w,j}`
at once; `c w j` is the eigenvalue. -/
lemma IsUnitary.le_span_joint_eigenvectors [Module ℂ W] {π : Representation ℂ (Gf E n) W}
    {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hB : IsUnitary π B) {S : Set (FinPlace E)}
    (h_split : ∀ w ∈ S, w.IsSplit) (h_star : ∀ w ∈ S, star w ∈ S)
    {U : Submodule ℂ W} [Module.Finite ℂ U] (hU : ∀ w ∈ S, U ≤ sphericalAt π w)
    (h_stable : ∀ w ∈ S, ∀ (hw : w.IsSplit) (j : ℕ), ∀ x ∈ U, heckeSplit π hw j x ∈ U) :
    U ≤ Submodule.span ℂ {x ∈ U | ∃ c : FinPlace E → ℕ → ℂ,
      ∀ w ∈ S, ∀ (hw : w.IsSplit) (j : ℕ), heckeSplit π hw j x = c w j • x} := by
  -- If the span were proper, the commuting operators `T_{w̄,i}` on `U` would have a joint
  -- generalised eigenspace not contained in it. But `T_{w̄,i}` is adjoint to `T_{w,i}` and commutes
  -- with it, so each vector of that space is a joint eigenvector of the `T_{w,i}`.
  classical
  let T' (w : S) (i : ℕ) : Module.End ℂ W := heckeSplit π (h_split w w.property).star i
  have h_stable' (w : S) (i : ℕ) : ∀ x ∈ U, T' w i x ∈ U := h_stable _ (h_star w w.property) _ i
  have h_comm' (w u : S) (i j : ℕ) : ∀ x ∈ U, T' w i (T' u j x) = T' u j (T' w i x) := fun x hx ↦
    heckeSplit_comm _ _ i j (hU _ (h_star w w.property) hx) (hU _ (h_star u u.property) hx)
  rw [← U.comap_subtype_eq_top]
  by_contra h_ne
  obtain ⟨c, h_not_le, -⟩ := exists_eigenvector_of_commute (fun a : S × ℕ ↦ T' a.1 a.2)
    (fun a ↦ h_stable' a.1 a.2) (fun a b ↦ h_comm' a.1 b.1 a.2 b.2) h_ne
  refine h_not_le fun x hx ↦ Submodule.subset_span ⟨x.property,
    fun w i ↦ if hwS : w ∈ S then star (c (⟨w, hwS⟩, i)) else 0, fun w hwS hw i ↦ ?_⟩
  -- A power of `T_{w̄,i} - c (w, i)` kills `x`: apply `eigenvector_of_pow_adjoint` on `U`.
  let T_U : Module.End ℂ U := (heckeSplit π hw i).restrict (h_stable w hwS hw i)
  let T'_U : Module.End ℂ U := (T' ⟨w, hwS⟩ i).restrict (h_stable' ⟨w, hwS⟩ i)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((T'_U - c (⟨w, hwS⟩, i) • 1) ^ k) x = 0 :=
    (Module.End.mem_maxGenEigenspace ..).1 ((Submodule.mem_iInf _).1 hx (⟨w, hwS⟩, i))
  have h_def : ∀ y : U, B.domRestrict₁₂ U U y y = 0 → y = 0 := fun y hy ↦
    by_contra fun hy_ne ↦ (hB.pos y (by simpa using hy_ne)).ne' hy
  -- `T_{w̄,i}` is adjoint to `T_{w,i}`
  have h_adj : ∀ y z : U, B.domRestrict₁₂ U U (T_U y) z = B.domRestrict₁₂ U U y (T'_U z) :=
    fun y z ↦ heckeSplit_adjoint hw i B (hU w hwS y.property) (hU w hwS z.property) hB.map_map_eq
  -- the two operators commute
  have h_comm : ∀ y : U, T_U (T'_U y) = T'_U (T_U y) := fun y ↦
    Subtype.ext <| heckeSplit_comm hw _ i i (hU w hwS y.property) (hU _ (h_star w hwS) y.property)
  simpa [T_U, hwS, Subtype.ext_iff] using eigenvector_of_pow_adjoint h_def h_adj h_comm k x hk

/-- For a complex representation `π` of `Gf E n` that is unitary for the form `B`, let `p` be a set
of split finite places closed under conjugation `star`. Let `U` be a finite-dimensional subspace
that is spherical at every place in `p` and stable under every Hecke operator `heckeSplit π _ j` at
those places. Then `U` is spanned by its vectors that are simultaneous eigenvectors of all these
operators, with eigenvalues indexed by pairs of a place satisfying `p` and a degree `j` (a version
of `IsUnitary.le_span_joint_eigenvectors`). -/
lemma IsUnitary.le_span_hecke_eigenvectors [Module ℂ W] {π : Representation ℂ (Gf E n) W}
    {B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hB : IsUnitary π B) {p : FinPlace E → Prop}
    (hp : ∀ w : FinPlace E, p w → w.IsSplit ∧ p (star w))
    {U : Submodule ℂ W} [Module.Finite ℂ U] (hU : ∀ w : FinPlace E, p w → U ≤ sphericalAt π w)
    (h_stable : ∀ (w : FinPlace E) (hw : p w) (j : ℕ),
      ∀ x ∈ U, heckeSplit π (hp w hw).left j x ∈ U) :
    U ≤ Submodule.span ℂ {x ∈ U | ∃ c : Subtype p × ℕ → ℂ,
      ∀ i : Subtype p × ℕ, heckeSplit π (hp i.fst i.fst.property).left i.snd x = c i • x} := by
  refine (hB.le_span_joint_eigenvectors (S := {w | p w}) (fun w hw ↦ (hp w hw).left)
    (fun w hw ↦ (hp w hw).right) hU fun w hw _ ↦ h_stable w hw).trans (Submodule.span_mono ?_)
  rintro x ⟨hx, c, hc⟩
  exact ⟨hx, fun (w, j) ↦ c w j, fun (w, j) ↦ hc w w.property _ j⟩

end SplitHecke

/-! ## The Hecke polynomial at a split place -/

section HeckePolynomial

variable (n : Type*)
  {W E : Type*} [Fintype n] [DecidableEq n] [AddCommGroup W] [Module ℂ W] [Field E] [NumberField E]
  [NumberField.IsCMField E] (π : Representation ℂ (Gf E n) W) (w : FinPlace E)

/-- For a sequence t_i in a complex vector space and X ∈ ℂ, the sum ∑_{i=0}^{n} (−X)^i
q^{binom(i,2)} t_i, with q the order of the residue field at w and n the number of elements of the
index type `n`. -/
noncomputable def heckePolyEval (t : ℕ → W) (X : ℂ) : W :=
  ∑ i ∈ Finset.range (Fintype.card n + 1), ((-X) ^ i * w.q ^ i.choose 2) • t i

variable {n w} (hw : star w ≠ w)

/-- The Hecke polynomial at `w` as a family of operators on `π`: the function sending `X : ℂ` to
`∑ i ≤ n, (-X)^i q^(i choose 2) T_{w,i}`, with `n` the rank and `q` the order of the residue
field at `w`. Here `hw` is a proof that `star w ≠ w`. -/
noncomputable def heckePolyOp : ℂ → Module.End ℂ W := heckePolyEval n w (heckeSplit π hw)

/-- The vector y is spherical at w (`New.sphericalAt`), that is, fixed by the elements of the
maximal compact subgroup whose components away from w and w̄ are 1. Moreover, the Hecke polynomial
`New.heckePolyOp` at each T ∈ ℂ acts on y by p(T). -/
def HasHeckePolynomial (p : ℂ → ℂ) (y : W) : Prop :=
  y ∈ sphericalAt π w ∧ ∀ T : ℂ, heckePolyOp π hw T y = p T • y

end HeckePolynomial

/-!
## Spherical eigenvectors and adjoints of the Hecke polynomial

Eigenvectors of the `T_{w,i}` and of the Hecke polynomial, equivariant maps and adjoints.
-/

section SphericalHecke

open Finset PowerSeries Polynomial NumberField

variable {E n W W' : Type} [Field E] [NumberField E] [IsCMField E] [Fintype n] [DecidableEq n]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
  {π : Representation ℂ (Gf E n) W} {w : FinPlace E} {p : ℂ → ℂ} {y : W}
  {π' : Representation ℂ (Gf E n) W'} {hw : star w ≠ w} {σ : ℂ →+* ℂ} (L : W →ₛₗ[σ] W')

/-- A spherical vector on which each `T_i` acts by `t i` is an eigenvector of the Hecke polynomial,
with eigenvalue the polynomial made from the `t i`. -/
theorem hasHeckePolynomial_of_heckeSplit (hy : y ∈ sphericalAt π w) {t : ℕ → ℂ}
    (h : ∀ i : ℕ, heckeSplit π hw i y = t i • y) :
    HasHeckePolynomial π hw (heckePolyEval n w t) y := by
  show y ∈ sphericalAt π w ∧ ∀ T : ℂ, heckePolyOp π hw T y = heckePolyEval n w t T • y
  refine ⟨hy, fun T ↦ ?_⟩
  -- termwise, `T_i` acts on `y` by `t i`
  calc heckePolyOp π hw T y
      = ∑ i ∈ range (Fintype.card n + 1), ((-T) ^ i * w.q ^ i.choose 2) • heckeSplit π hw i y := by
        simp [heckePolyOp, heckePolyEval]
    _ = heckePolyEval n w t T • y := by simp [heckePolyEval, h, sum_smul, mul_smul]

/-- A scalar multiple of a spherical eigenvector of the Hecke polynomial is one with the same
eigenvalue `p`. -/
theorem HasHeckePolynomial.smul {a : ℂ} (h : HasHeckePolynomial π hw p y) :
    HasHeckePolynomial π hw p (a • y) := by
  obtain ⟨hy, h_eigen⟩ := h
  refine ⟨Submodule.smul_mem _ a hy, fun T ↦ ?_⟩
  rw [map_smul, h_eigen T, smul_comm]

/-- A `σ`-semilinear map that is equivariant on `y` for the elements supported above `w` and
`star w` carries the Hecke polynomial at `T` to the Hecke polynomial at `σ T`. -/
theorem map_heckePolyOp (T : ℂ)
    (hL : ∀ g ∈ Gf.supportedOn n {w}, L (π g y) = π' g (L y)) :
    L (heckePolyOp π hw T y) = heckePolyOp π' hw (σ T) (L y) := by
  -- termwise: `L` commutes with each `T_{w,i}` (`map_heckeSplit`)
  simp [heckePolyOp, heckePolyEval, fun i : ℕ ↦ map_heckeSplit hw i L hL]

/-- Let w be split and B a G_f-invariant pairing of π and π', σ-semilinear in the first
variable. On vectors spherical at w, the adjoint of the Hecke polynomial H_w(X) is
H_{w̄}(σX): B(H_w(X)y, z) = B(y, H_{w̄}(σX)z). -/
theorem heckePolyOp_adjoint (hw : w.IsSplit) {Z : Type*} [AddCommGroup Z] [Module ℂ Z] {z : W'}
    (B : W →ₛₗ[σ] W' →ₗ[ℂ] Z) (hy : y ∈ sphericalAt π w) (hz : z ∈ sphericalAt π' w)
    (hB : ∀ (g : Gf E n) (x : W) (y' : W'), B (π g x) (π' g y') = B x y') (X : ℂ) :
    B (heckePolyOp π hw X y) z = B y (heckePolyOp π' hw.star (σ X) z) := by
  -- termwise: the adjoint of `T_{w,i}` is `T_{w̄,i}` (`heckeSplit_adjoint`)
  simp [heckePolyOp, heckePolyEval, ← heckeSplit_adjoint hw _ B hy hz hB]

/-- If `∑_{i ∈ t} U ^ i • b i = Q(U) • ∑_{i ∈ s} U ^ i • a i` for all complex `U`, with `Q(0) = 1`,
then for each `r ∈ s`, `a r` is the coefficient of `X ^ r` in the power series
`Q⁻¹ * ∑_{i ∈ t} X ^ i • b i`. -/
lemma sum_coeff_invOfUnit_smul_eq {R V : Type*} [CommRing R] [Algebra R ℂ] [AddCommGroup V]
    [Module ℂ V] {a b : ℕ → V} {s t : Finset ℕ} {r : ℕ} {Q : R[X]} (hQ : Q.coeff 0 = 1) (hr : r ∈ s)
    (h_rel : ∀ U : ℂ, ∑ i ∈ t, U ^ i • b i = Q.aeval U • ∑ i ∈ s, U ^ i • a i) :
    ∑ i ∈ t,
      algebraMap R ℂ (PowerSeries.coeff r (invOfUnit Q 1 * PowerSeries.X ^ i)) • b i = a r := by
  -- Test with a linear form `f`: the relation becomes an identity of complex polynomials.
  refine Module.eval_apply_injective ℂ (LinearMap.ext fun f ↦ ?_)
  have h_poly : (∑ i ∈ t, f (b i) • .X ^ i : Polynomial ℂ) =
      Q.map (algebraMap R ℂ) * ∑ i ∈ s, f (a i) • .X ^ i := Polynomial.funext fun U ↦ by
    simpa [Polynomial.eval_finsetSum, mul_comm] using congrArg f (h_rel U)
  -- Multiply by the inverse of `Q` as a power series and read the coefficient of `X ^ r`.
  have h_inv : map (algebraMap R ℂ) (invOfUnit Q 1) * map (algebraMap R ℂ) (Q : R⟦X⟧) = 1 := by
    rw [← map_mul, invOfUnit_mul (Q : R⟦X⟧) 1 (by simpa using hQ), map_one]
  -- The coefficient of `X ^ r` in `Q⁻¹ * X ^ i`, summed against `f (b i)`, is `f (a r)`.
  have h_eq : ∑ i ∈ t,
      algebraMap R ℂ (PowerSeries.coeff r (invOfUnit Q 1 * PowerSeries.X ^ i)) * f (b i) =
        f (a r) :=
    calc _ = PowerSeries.coeff r (map (algebraMap R ℂ) (invOfUnit Q 1) *
          coeToPowerSeries.ringHom (∑ i ∈ t, f (b i) • .X ^ i : Polynomial ℂ)) := by
          simp [mul_sum, mul_comm (f _), ← PowerSeries.coeff_map]
      _ = PowerSeries.coeff r (map (algebraMap R ℂ) (invOfUnit Q 1) *
          coeToPowerSeries.ringHom (Q.map (algebraMap R ℂ) * ∑ i ∈ s, f (a i) • .X ^ i)) := by
          rw [h_poly]
      _ = f (a r) := by simp [← mul_assoc, h_inv, hr]
  simpa [Algebra.smul_def] using h_eq

/-- Let `π` be a complex representation of the finite adelic unitary group `Gf E n` on `W`, and let
`w` be a finite place of the CM field `E` that is split, so `star w ≠ w` (witnessed by `hw`). If a
ℂ-linear subspace `N` of the endomorphisms of `W` contains the Hecke polynomial operator
`heckePolyOp π hw X = ∑ i ≤ n, (-X)^i q^(i choose 2) T_{w,i}` for every `X : ℂ`, then `N` contains
the Hecke operator `heckeSplit π hw i` (that is, `T_{w,i}`) for every `i`. -/
theorem heckeSplit_mem_of_heckePolyOp (N : Submodule ℂ (Module.End ℂ W))
    (hN_mem : ∀ X : ℂ, heckePolyOp π hw X ∈ N) (i : ℕ) :
    heckeSplit π hw i ∈ N := by
  by_cases hi : i ∈ range (Fintype.card n + 1)
  · -- modulo `N` the Hecke polynomial vanishes at every point, so its coefficients vanish
    let a (j : ℕ) : Module.End ℂ W ⧸ N := (w.q ^ j.choose 2 : ℂ) • N.mkQ (heckeSplit π hw j)
    have h_eval (U : ℂ) : ∑ j ∈ range (Fintype.card n + 1), U ^ j • a j = 0 := by
      have h_zero : N.mkQ (heckePolyOp π hw (-U)) = 0 :=
        (Submodule.Quotient.mk_eq_zero N).mpr (hN_mem (-U))
      simpa [a, hw, mul_smul, heckePolyOp, heckePolyEval] using h_zero
    have h_a_zero : a i = 0 := by
      -- test with a linear form `f`: the polynomial `∑ f (a j) X ^ j` vanishes everywhere
      refine (Module.forall_dual_apply_eq_zero_iff ℂ (a i)).mp fun f ↦ ?_
      have h_poly : (∑ j ∈ range (Fintype.card n + 1), f (a j) • .X ^ j : ℂ[X]) = 0 :=
        Polynomial.funext fun U ↦ by
          simpa [Polynomial.eval_finsetSum, mul_comm] using congrArg f (h_eval U)
      simpa [Polynomial.coeff_X_pow, hi] using congrArg (Polynomial.coeff · i) h_poly
    -- the factor, a power of `q`, is nonzero
    have h_mkQ : N.mkQ (heckeSplit π hw i) = 0 :=
      (smul_eq_zero.mp h_a_zero).resolve_left (by simp [w.q_bounds])
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h_mkQ
  · -- for `i > card n` the double coset `basicDoubleCoset` is empty and the operator is zero
    have h_gt : Fintype.card n < i := by simpa [Nat.add_one_le_iff] using hi
    have h_empty : basicDoubleCoset n w i = ∅ :=
      Set.eq_empty_of_forall_notMem fun g hg ↦ (le_card_of_mem_basicDoubleCoset hg).not_gt h_gt
    simp [heckeSplit_eq_heckeFun, h_empty, heckeFun]

/-- The eigenvalue `p` of the Hecke polynomial determines eigenvalues `t i` of the operators `T_i`,
the same for all spherical eigenvectors. -/
theorem exists_heckeSplit_eq_smul (p : ℂ → ℂ) :
    ∃ t : ℕ → ℂ, ∀ y : W, HasHeckePolynomial π hw p y → ∀ i : ℕ, heckeSplit π hw i y = t i • y := by
  -- `N`: the operators that act by a single scalar on all `y` with `HasHeckePolynomial π hw p y`
  let N : Submodule ℂ (Module.End ℂ W) :=
    { carrier := {A | ∃ c : ℂ, ∀ y, HasHeckePolynomial π hw p y → A y = c • y}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := fun ⟨c, hc⟩ ⟨d, hd⟩ ↦ ⟨c + d, by simp +contextual [hc, hd, add_smul]⟩
      smul_mem' := fun a _ ⟨c, hc⟩ ↦ ⟨a * c, by simp +contextual [hc, mul_smul]⟩ }
  -- it contains the Hecke polynomial at every point, hence each Hecke operator
  have h_poly_mem (T : ℂ) : heckePolyOp π hw T ∈ N := by
    refine ⟨p T, fun y hy ↦ ?_⟩
    obtain ⟨-, h_eigen⟩ : y ∈ sphericalAt π w ∧ ∀ T : ℂ, heckePolyOp π hw T y = p T • y := hy
    exact h_eigen T
  have h_mem (i : ℕ) : ∃ c : ℂ, ∀ y : W, HasHeckePolynomial π hw p y → heckeSplit π hw i y = c •
    y :=
    heckeSplit_mem_of_heckePolyOp N h_poly_mem i
  choose t ht using h_mem
  exact ⟨t, fun y hy i ↦ ht i y hy⟩

end SphericalHecke

end New
