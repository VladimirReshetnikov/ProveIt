import Lib.Weil.Construction.FiniteMultiplier

/-!
# Schwartz–Bruhat functions on a set of places and the Schrödinger model there

Functions on finite adelic vectors that only see the components at a set `S` of finite places, and
the action of the Heisenberg group on them when `S` is disjoint from its conjugate.

* `New.IsSchwartzBruhat S Ψ`: `Ψ` is Schwartz–Bruhat above `S`. Examples are the indicator
  `New.boxIndicator` of the vectors integral on `S` and the coset functions `New.cosetIndicator`.
* `New.IsSchwartzBruhat.eq_sum_cosetIndicator`, `New.IsSchwartzBruhat.mem_of_cosets`: such a
  function is a finite linear combination of coset functions.
* `New.schrodingerAct`: the Schrödinger model, with the Heisenberg law
  `New.schrodingerAct_schrodingerAct`. `New.semichar_smul_schrodingerAct` gives its form in the
  normalisation that represents the lattice, and its vacuum is the box function
  (`New.schrodingerAct_boxIndicator`).
* `New.Space.mem_range_schrodingerCombination`: every Schwartz–Bruhat function above `S` is a finite
  combination of Heisenberg translates of the box function.

Notions from other files:
* `New.idem S`: the finite adele with component 1 at the places of `S` and 0 elsewhere, so that
  `idem S • x` is the part of `x` at `S`.
* `New.stdLattice.selfDualAddChar`: a character of the finite adeles for which `Ô^n` is its own dual
  under the pairing `selfDualAddChar E (y* x)`.
* `Set.conjClosure`: the set `S ∪ S̄` of the places in `S` and their complex conjugates;
  `Set.IsConjDisjoint S` says that `S` and `S̄` are disjoint.
* `New.stdLattice.half` is `1 / 2`, `New.stdLattice.traceOneAdele` an integer `c₀` with
  `c₀ + c̄₀ = 1`, and `New.stdLattice.semichar x` is `selfDualAddChar E (c₀ / 2 * x* x)`.

## Relation to the literature

Known; see `Lib.Weil.MixedModel.ZeroTerm` for sources.
-/

noncomputable section

namespace New

open NumberField Filter MeasureTheory Matrix ComplexConjugate AddSubgroup QuotientAddGroup
  OpenAddSubgroup Quotient stdLattice Submodule AddChar Set Prod

section

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]
  (n : Type*) [Fintype n] [DecidableEq n] (S : Set (FinPlace E))

/-! ### The box, coset functions and the partial determinant -/

/-- The additive group of finite adelic n-vectors that are integral at every place of S. -/
def integralBox : AddSubgroup (n → 𝔸f E) :=
  (stdLattice E n).comap (idem S • AddMonoidHom.id (n → 𝔸f E))

open scoped Classical in
/-- The complex-valued indicator function of the finite adelic n-vectors that are integral at
every place of S. -/
def boxIndicator (x : n → 𝔸f E) : ℂ := if x ∈ integralBox n S then (1 : ℂ) else 0

variable {n}

/-- Ψ is Schwartz–Bruhat above S: it depends only on the components at S, is locally constant,
and the S-parts of its support lie in a compact set. -/
@[local grind]
class IsSchwartzBruhat (Ψ : (n → 𝔸f E) → ℂ) where
  /-- `Ψ x` depends only on the components of `x` at the places of `S`. -/
  idem_smul (x : n → 𝔸f E) : Ψ (idem S • x) = Ψ x
  /-- `Ψ` is locally constant. -/
  locally_constant : IsLocallyConstant Ψ
  /-- On the support of `Ψ`, the part of `x` at the places of `S` stays in a compact set. -/
  compact_support : ∃ C : Set (n → 𝔸f E), IsCompact C ∧ ∀ x : n → 𝔸f E, Ψ x ≠ 0 → idem S • x ∈ C

/-- The homomorphism sending g in GL_n of the finite adeles to the idele equal to det g at the
places of S and 1 elsewhere. -/
@[simps! apply_val_fst]
def detOn : GL n (𝔸f E) →* (𝔸 E)ˣ :=
  finIdeleIncl.comp (GeneralLinearGroup.det.comp (cutGL (idem_mul_self S)))

/-- The indicator function of the finite adelic vectors x such that t⁻¹(x − z) is integral at
every place of S. -/
abbrev cosetIndicator (t : (𝔸f E)ˣ) (z x : n → 𝔸f E) : ℂ := boxIndicator n S (t⁻¹.val • (x - z))

variable {S} (g : Gf E n) (hS : S.IsConjDisjoint) {Φ Ψ : (n → 𝔸f E) → ℂ} [hΨ : IsSchwartzBruhat S Ψ]

open scoped Classical in
omit [IsCMField E] [Fintype n] [DecidableEq n] in
@[simp]
lemma boxIndicator_apply (x : n → 𝔸f E) :
    boxIndicator n S x = (if x ∈ integralBox n S then 1 else 0) :=
  rfl

omit [IsCMField E] [Fintype n] [DecidableEq n] in
lemma mem_integralBox {x : n → 𝔸f E} : x ∈ integralBox n S ↔ ∀ i : n, idem S * x i ∈ Ô E := .rfl

omit [IsCMField E] [DecidableEq n] in
lemma isOpen_integralBox : (integralBox n S).IsOpen := isOpen_stdLattice.preimage (by continuity)

open scoped Classical in
/-- The component of the idele `detOn S g` (`g` a finite adelic unitary point) at a finite place
`w`: `det g_w` if `w ∈ S`, and `1` otherwise. -/
@[simp]
lemma detOn_apply (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    (detOn S g.val).val.2 w = (if w ∈ S then (g.atPlace w).val.det else 1) := by
  -- The simp writes the component as the determinant of the cut matrix at `w` (`↓` so that
  -- `RingHom.map_det` applies before the matrix is expanded); at `w ∈ S` it is `g_w`, else `1`.
  simp [detOn, ← evalAt_apply, map_add, Matrix.map_smul', cutGL, ↓ RingHom.map_det]
  by_cases hw : w ∈ S
  · simp [hw, evalAt_apply, Gf.atPlace]
  · simp [hw, evalAt_apply]

/-- For a finite adelic unitary point g (`g : Gf E n`) and a finite set T of finite places, the
idele det g_T is the product over w ∈ T of the ideles with component det g_w at w and 1
elsewhere. -/
lemma detOn_eq_prod (T : Finset (FinPlace E)) :
    detOn T g.val = ∏ w ∈ T, locFullIdele w (g.atPlace w).det := by
  classical
  ext v
  · -- At infinity both sides are `1`.
    simp [locFullIdele, fst_prod]
  · -- At the finite place `v` only the factor `w = v` differs from `1`.
    -- The first call evaluates both sides at `v`; the second evaluates the product over `T`.
    simp [locFullIdele, snd_prod, ← evalAt_apply]
    simp_all [T.prod_eq_ite v, eq_comm]

end

attribute [local grind] IsSchwartzBruhat

variable {E : Type*} [Field E] [CMType E] {n : Type*} [Fintype n] [DecidableEq n]
  (S : Set (FinPlace E)) (g : Gf E n) (hS : S.IsConjDisjoint) {Ψ : (n → 𝔸f E) → ℂ}
  [hΨ : IsSchwartzBruhat S Ψ]

/-! ### The Schrödinger model -/

/-- The Schrödinger model at the places of `S`: the vector `y` acts on functions by
`Ψ ↦ (x ↦ selfDualAddChar E (½ y* (2 x + y)_S) * Ψ (x + y))`, where `z_S = idem S • z` is the part
of `z` at `S`. -/
def schrodingerAct [WeilData E] (y : n → 𝔸f E) : Module.End ℂ ((n → 𝔸f E) → ℂ) :=
  LinearMap.pi fun x ↦ selfDualAddChar E (half * star y ⬝ᵥ idem S • (x + (x + y))) • LinearMap.proj
    (x + y)

omit [DecidableEq n] in
/-- The value of the Schrödinger operator of `y` on `f` at `x`. -/
lemma schrodingerAct_apply [WeilData E] (y x : n → 𝔸f E) (f : (n → 𝔸f E) → ℂ) :
    schrodingerAct S y f x = selfDualAddChar E (half * star y ⬝ᵥ idem S • (x + (x + y))) * f
      (x + y) :=
  rfl

/-- The linear map sending finitely supported coefficients c_y to the function ∑ c_y
`New.schrodingerAct` S y applied to the indicator of vectors integral on S. -/
abbrev schrodingerCombination [WeilData E] : ((n → 𝔸f E) →₀ ℂ) →ₗ[ℂ] (n → 𝔸f E) → ℂ :=
  Finsupp.lift ((n → 𝔸f E) → ℂ) ℂ (n → 𝔸f E) (schrodingerAct S · (boxIndicator n S))

/-- The inner product ∫ conj(Ψ) Ψ′ over the finite adelic vectors integral off S, for the Haar
measure giving Ô^n mass one. -/
def localInner (Ψ Ψ' : (n → 𝔸f E) → ℂ) : ℂ :=
  ∫ x : n → 𝔸f E in integralBox n Sᶜ, conj (Ψ x) * Ψ' x ∂latticeMeasure E n

variable {S}

omit [Fintype n] [DecidableEq n] in
/-- A vector integral off `S` and integral on `S` is integral everywhere. -/
lemma integralBox_compl_inter :
    SetLike.coe (integralBox n Sᶜ) ∩ integralBox n S = stdLattice E n := by
  grind [mem_integralBox, mem_stdLattice, mem_Ô, SetLike.mem_coe, idem_mul_mem_Ô]

lemma isLocallyConstant_selfDualAddChar [WeilData E] : IsLocallyConstant (selfDualAddChar E) := by
  -- `selfDualAddChar E` is invariant under translation by the elements of `Ô E`, a neighbourhood of
  -- `0`.
  refine isLocallyConstant_of_eventually_add ((isOpen_Ô.eventually_mem (zero_mem _)).mono ?_)
  simp_all [map_add_eq_mul, selfDualAddChar_eq_one_of_mem]

open scoped Classical in
/-- The indicator of the vectors integral at every place of `S` is Schwartz–Bruhat above `S`. -/
instance isSchwartzBruhat_boxIndicator : IsSchwartzBruhat S (boxIndicator n S) where
  idem_smul := by simp [integralBox, smul_smul, idem_mul_self]
  -- The box is an open subgroup, hence also closed.
  locally_constant :=
    (LocallyConstant.charFn ℂ (isClopen ⟨integralBox n S, isOpen_integralBox⟩)).isLocallyConstant
  -- Where the box function is not zero, the part at `S` lies in the lattice.
  compact_support := ⟨stdLattice E n, isCompact_stdLattice, by simp [integralBox]⟩

namespace IsSchwartzBruhat

section

omit [DecidableEq n]

/-- Let `Ψ` be Schwartz–Bruhat above `S` (instance `hΨ`), `A` a matrix with a left inverse `B`
(`B A y = y` for all `y`), and `y` a vector. Then `x ↦ Ψ (A x + y)` is
Schwartz–Bruhat above `S`. -/
lemma comp {m : Type*} [Fintype m] {A : Matrix n m (𝔸f E)} (B : Matrix m n (𝔸f E))
    (h_left_inv : ∀ y : m → 𝔸f E, B *ᵥ A *ᵥ y = y) (y : n → 𝔸f E) :
    IsSchwartzBruhat S fun x : m → 𝔸f E ↦ Ψ (A *ᵥ x + y) := by
  -- The image of the compact set for `Ψ` under `z ↦ B (z - idem S • y)` serves.
  obtain ⟨C, hC, h_supp⟩ : ∃ C : Set (n → 𝔸f E), IsCompact C ∧
      ∀ x : n → 𝔸f E, Ψ x ≠ 0 → idem S • x ∈ C := hΨ.compact_support
  have h_smul (x : m → 𝔸f E) : A *ᵥ (idem S • x) + idem S • y = idem S • (A *ᵥ x + y) := by
    rw [mulVec_smul, smul_add]
  have h_cont : Continuous fun z : n → 𝔸f E ↦ B *ᵥ (z - idem S • y) := by fun_prop
  refine ⟨fun x ↦ ?_, hΨ.locally_constant.comp_continuous (by fun_prop),
    (fun z ↦ B *ᵥ (z - idem S • y)) '' C, hC.image h_cont, ?_⟩
  · -- Both arguments of `Ψ` have the same part at `S`.
    have h_part : idem S • (A *ᵥ (idem S • x) + y) = idem S • (A *ᵥ x + y) := by
      rw [← h_smul (idem S • x), ← h_smul x, smul_smul, idem_mul_self]
    rw [← hΨ.idem_smul (A *ᵥ (idem S • x) + y), h_part, hΨ.idem_smul]
  · intro x hx
    refine ⟨idem S • (A *ᵥ x + y), h_supp _ hx, ?_⟩
    simp only [← h_smul, add_sub_cancel_right, h_left_inv]

/-- A translate of a Schwartz–Bruhat function above `S` is Schwartz–Bruhat above `S`. -/
instance comp_add (y : n → 𝔸f E) : IsSchwartzBruhat S fun x : n → 𝔸f E ↦ Ψ (x + y) := by
  simpa using comp (A := diagonal 1) 1 (by simp) y

/-- The composite of a Schwartz–Bruhat function above `S` with an invertible matrix over the finite
adeles is Schwartz–Bruhat above `S`. -/
instance comp_mulVec (g : GL n (𝔸f E)) :
    IsSchwartzBruhat S fun x : n → 𝔸f E ↦ Ψ (g.val *ᵥ x) := by
  simpa using comp g.inv (by simp) 0

/-- Let Ψ be Schwartz–Bruhat above S (instance `hΨ`) and t a finite idele, with Ψ(y) = Ψ(x) when
Ψ(x) ≠ 0 and t⁻¹(y − x) is integral on S. Then there is a finite set A of vectors q with Ψ(q) ≠ 0
such that Ψ = ∑_{q ∈ A} Ψ(q) · `cosetIndicator S t q`. -/
lemma eq_sum_cosetIndicator (t : (𝔸f E)ˣ)
    (h_per : ∀ x : n → 𝔸f E, Ψ x ≠ 0 → ∀ y : n → 𝔸f E,
      t⁻¹.val • (y - x) ∈ integralBox n S → Ψ y = Ψ x) :
    ∃ A : Finset (n → 𝔸f E), (∀ q ∈ A, Ψ q ≠ 0) ∧ Ψ = ∑ q ∈ A, Ψ q • cosetIndicator S t q := by
  classical
  -- Take one representative of each class modulo the open subgroup `U` and keep those at which
  -- `Ψ` does not vanish.
  let U : OpenAddSubgroup (n → 𝔸f E) :=
    comap (smulAddHom _ _ t⁻¹.val) (continuous_const_smul _) ⟨integralBox n S, isOpen_integralBox⟩
  have mem_box_iff {x y : n → 𝔸f E} :
      t⁻¹.val • (y - x) ∈ integralBox n S ↔ (y : _ ⧸ U.toAddSubgroup) = x :=
    (eq_iff_sub_mem (N := U.toAddSubgroup)).symm
  obtain ⟨C, hC, h_supp⟩ := hΨ.compact_support
  -- These classes are finitely many: each meets the compact set `C`, as `x` and `idem S • x`
  -- are congruent modulo `U`, and the quotient is discrete.
  have h_fin : (Function.support fun q : _ ⧸ U.toAddSubgroup ↦ Ψ q.out).Finite := by
    refine (hC.image continuous_mk).finite_of_discrete.subset fun q hq ↦ ⟨_, h_supp _ hq, ?_⟩
    -- `out q` and its part at `S` are congruent modulo `U`.
    have h_mem : t⁻¹.val • (idem S • q.out - q.out) ∈ integralBox n S := by
      simp +contextual [mem_integralBox, idem_mul_mem_Ô]
    exact (mem_box_iff.mp h_mem).trans q.out_eq
  refine ⟨h_fin.toFinset.image out, by simp, ?_⟩
  -- At `x` only the class of `x` contributes, so it suffices that `Ψ x` is the value at the
  -- representative of its class, or zero if that value is zero.
  suffices h_rep : ∀ x : n → 𝔸f E,
      Ψ x = if Ψ (out (x : (n → 𝔸f E) ⧸ U.toAddSubgroup)) = 0 then 0
        else Ψ (out (x : (n → 𝔸f E) ⧸ U.toAddSubgroup)) by
    simpa [funext_iff, mem_box_iff] using h_rep
  intro x
  set q : n → 𝔸f E := out (x : (n → 𝔸f E) ⧸ U.toAddSubgroup)
  have h_class : (q : (n → 𝔸f E) ⧸ U.toAddSubgroup) = x := out_eq _
  split_ifs with h_zero
  · -- `Ψ x ≠ 0` would give `Ψ q = Ψ x ≠ 0`, as `Ψ` is constant on the class.
    by_contra hx
    exact hx ((h_per x hx q (mem_box_iff.mpr h_class)).symm.trans h_zero)
  · exact h_per q h_zero x (mem_box_iff.mpr h_class.symm)

open scoped Pointwise in
/-- For `Ψ` Schwartz–Bruhat above `S` (instance `hΨ`) and a continuous `F`, the product `F Ψ` is
integrable on the vectors integral off `S`, for the measure `New.latticeMeasure` that gives `Ô^n`
mass one. -/
lemma integrableOn_mul {F : (n → 𝔸f E) → ℂ} (hF : Continuous F) :
    IntegrableOn (fun x : n → 𝔸f E ↦ F x * Ψ x) (integralBox n Sᶜ) (latticeMeasure E n) := by
  -- On `integralBox n Sᶜ` the support of `F Ψ` lies in the compact set `C + stdLattice E n`, on
  -- which the continuous function `F Ψ` is integrable.
  obtain ⟨C, hC, h_supp⟩ : ∃ C : Set (n → 𝔸f E), IsCompact C ∧
      ∀ x : n → 𝔸f E, Ψ x ≠ 0 → idem S • x ∈ C := hΨ.compact_support
  have h_int : IntegrableOn (fun x : n → 𝔸f E ↦ F x * Ψ x) (C + (stdLattice E n : Set (n → 𝔸f E)))
      (latticeMeasure E n) :=
    (hC.add isCompact_stdLattice).integrableOn _ (hF.mul hΨ.locally_constant.continuous)
  have h_subset : (integralBox n Sᶜ : Set (n → 𝔸f E)) ∩ Function.support (fun x ↦ F x * Ψ x) ⊆
      C + (stdLattice E n : Set (n → 𝔸f E)) := by
    rintro x ⟨hx_box, hx⟩
    -- `x` is its part at `S`, in `C`, plus its part off `S`, in the lattice.
    have h_split : idem S • x + idem Sᶜ • x = x := by aesop (add simp idem_apply)
    exact ⟨idem S • x, h_supp x (right_ne_zero_of_mul hx), idem Sᶜ • x, hx_box, h_split⟩
  exact .of_inter_support isOpen_integralBox.measurableSet (h_int.mono_set h_subset)

/-- A Schwartz–Bruhat function Ψ above S (instance `hΨ`) lies in a subspace P if each y with
Ψ(y) ≠ 0 has a neighbourhood U such that P contains every coset function `cosetIndicator S t z`,
t an integral idele, whose coset has S-parts in U. -/
lemma mem_of_cosets (P : Submodule ℂ ((n → 𝔸f E) → ℂ))
    (h_small : ∀ y : n → 𝔸f E, Ψ y ≠ 0 → ∃ U ∈ nhds y,
      ∀ (t : (𝔸f E)ˣ) (z : n → 𝔸f E), t.val ∈ Ô E →
        (∀ x : n → 𝔸f E, t⁻¹.val • (x - z) ∈ integralBox n S → idem S • x ∈ U) →
        cosetIndicator S t z ∈ P) :
    Ψ ∈ P := by
  -- By compactness of the support one integer `N` makes every coset of `N` times the box through
  -- the support small enough; `Ψ` is constant on these cosets, so it is a finite sum of them.
  obtain ⟨C, hC, h_supp⟩ : ∃ C : Set (n → 𝔸f E), IsCompact C ∧
      ∀ x : n → 𝔸f E, Ψ x ≠ 0 → idem S • x ∈ C := hΨ.compact_support
  choose! U hU h_coset_mem using h_small
  have h_nhds (y : n → 𝔸f E) : {x | Ψ x = Ψ y ∧ (Ψ y ≠ 0 → x ∈ U y)} ∈ nhds y :=
    (hΨ.locally_constant.eventually_eq y).and (eventually_imp_distrib_left.mpr (hU y))
  -- Take a Lebesgue entourage `W` for the cover of `C` by these neighbourhoods, and `N ≠ 0` such
  -- that points that differ by an element of `N` times the lattice are `W`-close.
  let uniformSpace : UniformSpace (n → 𝔸f E) := IsTopologicalAddGroup.rightUniformSpace (n → 𝔸f E)
  obtain ⟨W, hW, h_ball_subset⟩ : ∃ W ∈ uniformity (n → 𝔸f E), ∀ x ∈ C, ∃ y : n → 𝔸f E,
      UniformSpace.ball x W ⊆ {z | Ψ z = Ψ y ∧ (Ψ y ≠ 0 → z ∈ U y)} :=
    lebesgue_number_lemma_nhds hC fun y _ ↦ h_nhds y
  obtain ⟨N, hN, h_smul_mem⟩ : ∃ N : ℕ, N ≠ 0 ∧ ∀ x ∈ (stdLattice E n).carrier,
      (N : 𝔸f E) • x ∈ {z | ∀ ⦃p : (n → 𝔸f E) × (n → 𝔸f E)⦄, p.2 + -p.1 = z → p ∈ W} :=
    exists_natCast_smul_mem_of_isCompact E isCompact_stdLattice (mem_comap'.mp hW)
  obtain ⟨t, ht⟩ : ∃ t : (𝔸f E)ˣ, (t : 𝔸f E) = N := isUnit_natCast_finAdele hN
  have h_coset_center (q : n → 𝔸f E) (hq : Ψ q ≠ 0) : ∃ y : n → 𝔸f E, ∀ x : n → 𝔸f E,
      t⁻¹.val • (x - q) ∈ integralBox n S →
        Ψ (idem S • x) = Ψ y ∧ (Ψ y ≠ 0 → idem S • x ∈ U y) := by
    obtain ⟨y, hy⟩ : ∃ y : n → 𝔸f E,
        UniformSpace.ball (idem S • q) W ⊆ {z | Ψ z = Ψ y ∧ (Ψ y ≠ 0 → z ∈ U y)} :=
      h_ball_subset _ (h_supp q hq)
    refine ⟨y, fun x hx ↦ hy (h_smul_mem _ hx ?_)⟩
    simp [← ht, mul_left_comm (t : 𝔸f E), sub_eq_add_neg, smul_smul]
  -- Each vector lies in its own coset, so `Ψ` is constant on the cosets through its support.
  have h_mem_self (q : n → 𝔸f E) : t⁻¹.val • (q - q) ∈ integralBox n S := by simp
  have h_per : ∀ x : n → 𝔸f E, Ψ x ≠ 0 → ∀ y : n → 𝔸f E,
      t⁻¹.val • (y - x) ∈ integralBox n S → Ψ y = Ψ x := by
    intro x hx y hy
    obtain ⟨c, hc⟩ := h_coset_center x hx
    rw [← hΨ.idem_smul y, ← hΨ.idem_smul x, (hc y hy).left, (hc x (h_mem_self x)).left]
  obtain ⟨A, hA, h_sum_eq⟩ : ∃ A : Finset (n → 𝔸f E), (∀ q ∈ A, Ψ q ≠ 0) ∧
      Ψ = ∑ q ∈ A, Ψ q • cosetIndicator S t q := hΨ.eq_sum_cosetIndicator t h_per
  rw [h_sum_eq]
  refine sum_smul_mem _ _ fun q hq ↦ ?_
  obtain ⟨y, hy⟩ := h_coset_center q (hA q hq)
  -- `Ψ y = Ψ q`, read at `q` itself, is not zero.
  have hy_ne : Ψ y ≠ 0 := by
    rw [← (hy q (h_mem_self q)).left, hΨ.idem_smul]
    exact hA q hq
  have ht_int : t.val ∈ Ô E := by simp [ht]
  have h_coset : ∀ x : n → 𝔸f E, t⁻¹.val • (x - q) ∈ integralBox n S → idem S • x ∈ U y :=
    fun x hx ↦ (hy x hx).right hy_ne
  exact h_coset_mem y hy_ne t q ht_int h_coset

end

end IsSchwartzBruhat

open scoped Classical in
/-- The coset functions are Schwartz–Bruhat above `S`. -/
instance (t : (𝔸f E)ˣ) (z : n → 𝔸f E) :
    IsSchwartzBruhat S fun x : n → 𝔸f E ↦ cosetIndicator S t z x := by
  -- `using!`: simp unfolds `boxIndicator` only in the goal, and unfolding it in the term times out.
  simpa [sub_eq_add_neg] using! (isSchwartzBruhat_boxIndicator.comp_add _).comp_mulVec (.scalar _ _)

include hS in
/-- For `S` disjoint from its conjugate (hypothesis `hS`), the idempotents of `S` and of `S̄` have
product zero. -/
lemma idem_mul_star : idem S * star (idem S) = 0 := by aesop (add simp [disjoint_left, idem_apply])

include hS in
/-- For `S` disjoint from its conjugate (hypothesis `hS`), the idempotent of `S ∪ S̄` is the sum of
those of `S` and of `S̄`. -/
lemma idem_conjClosure_eq_add_star : idem S.conjClosure = idem S + star (idem S) := by
  aesop (add simp [disjoint_left, idem_apply])

variable [WeilData E]

section

omit [DecidableEq n]

include hS in
/-- The Heisenberg law, for `S` disjoint from its conjugate (hypothesis `hS`): the operators compose
up to the bicharacter `β` of `New.stdLattice.finHeisenberg` at the parts of `y` and `y'` at
`S ∪ S̄`. -/
lemma schrodingerAct_schrodingerAct (y y' : n → 𝔸f E) (f : (n → 𝔸f E) → ℂ) :
    schrodingerAct S y (schrodingerAct S y' f) =
      (stdLattice.finHeisenberg E n).β (idem S.conjClosure • y) (idem S.conjClosure • y') •
        schrodingerAct S (y + y') f := by
  funext x
  simp only [schrodingerAct_apply, Pi.smul_apply, smul_eq_mul]
  -- Both sides are `selfDualAddChar E` of an exponent times `f (x + y + y')`. With `e = idem S`,
  -- the exponents differ by `t + star t` for `t = -(half * e * y* y')`, on which
  -- `selfDualAddChar E` is `1`.
  set t : 𝔸f E := -(half * idem S * star y ⬝ᵥ y') with ht
  have h_exp :
      half * star y ⬝ᵥ idem S • (x + (x + y)) + half * star y' ⬝ᵥ idem S • (x + y + (x + y + y')) =
        half * star (idem S.conjClosure • y') ⬝ᵥ idem S.conjClosure • y +
            half * star (y + y') ⬝ᵥ idem S • (x + (x + (y + y'))) + (t + star t) + 0 := by
    have h_idem_star : star (idem S) * star (idem S) = star (idem S) := by
      rw [← star_mul, idem_mul_self]
    rw [ht, idem_conjClosure_eq_add_star hS]
    simp only [star_smul, star_add, star_neg, star_star, star_mul, star_half, smul_dotProduct,
      dotProduct_smul, add_dotProduct, dotProduct_add, add_smul, smul_add, smul_eq_mul]
    linear_combination
      -(half * (star y' ⬝ᵥ y)) * idem_mul_self S - (half * (star y' ⬝ᵥ y)) * h_idem_star -
        (2 * half * (star y' ⬝ᵥ y)) * idem_mul_star hS +
        (half * star (idem S)) * (Matrix.star_dotProduct y' y).symm
  have h_beta : (stdLattice.finHeisenberg E n).β (idem S.conjClosure • y) (idem S.conjClosure • y')
      = selfDualAddChar E (half * star (idem S.conjClosure • y') ⬝ᵥ idem S.conjClosure • y) := rfl
  rw [h_beta, ← mul_assoc, ← mul_assoc, ← map_add_eq_mul, ← map_add_eq_mul,
    selfDualAddChar_congr t (zero_mem _) h_exp, add_assoc x y y']

include hS in
/-- For `S` disjoint from its conjugate (hypothesis `hS`), the operator of `y`, corrected by the
semicharacter `semichar` of the part of `y` at `S ∪ S̄`, sends `Ψ` to
`x ↦ selfDualAddChar E (y* (x + c₀ y)_S) * Ψ (x + y)`, where `c₀ = traceOneAdele` and
`z_S = idem S • z`. -/
lemma semichar_smul_schrodingerAct (y : n → 𝔸f E) (Ψ : (n → 𝔸f E) → ℂ) :
    semichar (idem S.conjClosure • y) • schrodingerAct S y Ψ =
      fun x : n → 𝔸f E ↦
        selfDualAddChar E (star y ⬝ᵥ idem S • (x + (traceOneAdele : 𝔸f E) • y)) * Ψ (x + y) := by
  -- The two exponents on the left add up to the exponent on the right plus `t + star t`, which
  -- `selfDualAddChar E` kills.
  ext x
  set t : 𝔸f E := star (traceOneAdele : 𝔸f E) * half * idem S ^ 2 * star y ⬝ᵥ y with ht
  have h_exp :
      (traceOneAdele : 𝔸f E) * half * star (idem S.conjClosure • y) ⬝ᵥ idem S.conjClosure • y +
          half * star y ⬝ᵥ idem S • (x + (x + y)) =
        star y ⬝ᵥ idem S • (x + (traceOneAdele : 𝔸f E) • y) + (t + star t) + 0 := by
    -- Expand in `e = idem S`, `c₀`, `half` and the pairings `y* y`, `y* x`; the identity
    -- holds since `e * e = e`, `e * star e = 0`, `c₀ + star c₀ = 1`, `2 * half = 1` and `y* y`
    -- is self-adjoint.
    rw [ht, idem_conjClosure_eq_add_star hS]
    simp only [star_smul, star_add, star_star, star_mul, star_pow, star_half, smul_dotProduct,
      dotProduct_smul, add_dotProduct, dotProduct_add, add_smul, smul_add, smul_eq_mul]
    linear_combination
      (traceOneAdele * idem S * (star y ⬝ᵥ y) + idem S * (star y ⬝ᵥ x)) * two_mul_half (E := E) -
        (half * idem S * (star y ⬝ᵥ y)) * traceOneAdele_add_star (E := E) -
        (traceOneAdele * half * star (idem S) ^ 2) * (Matrix.star_dotProduct y y).symm +
        ((traceOneAdele * half - star traceOneAdele * half) * (star y ⬝ᵥ y)) * idem_mul_self S +
        (2 * traceOneAdele * half * (star y ⬝ᵥ y)) * idem_mul_star hS
  rw [Pi.smul_apply, schrodingerAct_apply, smul_eq_mul, ← mul_assoc, semichar, ← map_add_eq_mul,
    selfDualAddChar_congr t (zero_mem _) h_exp]

include hS in
/-- For `S` disjoint from its conjugate (hypothesis `hS`) and `y` integral on `S ∪ S̄`, the operator
of `y`, corrected by the semicharacter `semichar` of the part of `y` at `S ∪ S̄`, fixes the box
function. -/
lemma schrodingerAct_boxIndicator {y : n → 𝔸f E} (hy : y ∈ integralBox n S.conjClosure) :
    semichar (idem S.conjClosure • y) • schrodingerAct S y (boxIndicator n S) =
      boxIndicator n S := by
  classical
  -- Translation by `y` preserves the box, and on the box the phase of
  -- `semichar_smul_schrodingerAct` is `selfDualAddChar E` of an integral element.
  have h_idem : star (idem S.conjClosure) * idem S = idem S := by
    simp [idem_conjClosure_eq_add_star hS, mul_add, idem_mul_self, mul_comm _ (idem S),
      idem_mul_star hS]
  have hyS : idem S • y ∈ stdLattice E n := by
    simpa [idem_conjClosure_eq_add_star hS, idem_mul_star hS, smul_smul, mul_add,
      idem_mul_self] using smul_mem_stdLattice (idem_mem_Ô S) hy
  have h_phase (x : n → 𝔸f E) (hx : idem S • x ∈ stdLattice E n) :
      selfDualAddChar E (star y ⬝ᵥ idem S • (x + (traceOneAdele : 𝔸f E) • y)) = 1 := by
    have h_vec : idem S • (x + (traceOneAdele : 𝔸f E) • y) ∈ stdLattice E n := by
      rw [smul_add, smul_comm]
      exact add_mem hx (smul_mem_stdLattice traceOneAdele_mem hyS)
    have h_int : star (idem S.conjClosure • y) ⬝ᵥ idem S • (x + (traceOneAdele : 𝔸f E) • y) ∈
        Ô E := star_dotProduct_mem h_vec hy
    rw [star_smul, smul_dotProduct, ← dotProduct_smul, smul_smul, h_idem] at h_int
    exact selfDualAddChar_eq_one_of_mem h_int
  rw [semichar_smul_schrodingerAct hS]
  ext x
  have h_box : x + y ∈ integralBox n S ↔ x ∈ integralBox n S := by
    simp [integralBox, smul_add, add_mem_cancel_right hyS]
  by_cases hx : x ∈ integralBox n S
  · simp only [boxIndicator_apply, h_box, hx, ↓reduceIte, mul_one, h_phase x hx]
  · simp [h_box, hx]

end

namespace IsSchwartzBruhat

include hS in
omit [DecidableEq n] in
/-- For `S` disjoint from its conjugate (hypothesis `hS`) and `Ψ` Schwartz–Bruhat above `S`
(instance `hΨ`), a vector supported on `S` acts on `Ψ` by translation. -/
lemma schrodingerAct_idem (y : n → 𝔸f E) :
    schrodingerAct S (idem S • y) Ψ = fun x : n → 𝔸f E ↦ Ψ (x + y) := by
  -- The phase is `selfDualAddChar E 0 = 1`, as `idem S * star (idem S) = 0`, and `Ψ` only sees the
  -- part at `S`.
  have h_exp (x : n → 𝔸f E) :
      half * star (idem S • y) ⬝ᵥ idem S • (x + (x + idem S • y)) = 0 := by
    simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    linear_combination (half * (star y ⬝ᵥ (x + (x + idem S • y)))) * idem_mul_star hS
  have h_part (x : n → 𝔸f E) : Ψ (x + idem S • y) = Ψ (x + y) := by
    rw [← hΨ.idem_smul (x + idem S • y), ← hΨ.idem_smul (x + y), smul_add, smul_add, smul_smul,
      idem_mul_self]
  funext x
  rw [schrodingerAct_apply, h_exp x, map_zero_eq_one, one_mul, h_part x]

include hS in
omit [DecidableEq n] in
/-- Let `E` be a CM number field with Weil data (instances `CMType E`, `WeilData E`; they fix the
character `selfDualAddChar E`), `n` a finite index type and `S` a set of finite places disjoint
from its conjugate (hypothesis `hS`), and let `Ψ` be Schwartz–Bruhat above `S` (instance `hΨ`).
Then a vector supported on the conjugate of `S` acts on `Ψ` by multiplication with a character. -/
lemma schrodingerAct_star_idem_smul (y : n → 𝔸f E) :
    schrodingerAct S (star (idem S) • y) Ψ =
      fun x : n → 𝔸f E ↦ selfDualAddChar E (star y ⬝ᵥ idem S • x) * Ψ x := by
  -- The exponent is `half * idem S * (2 y* x + star (idem S) y* y)`, that is `idem S * y* x`, as
  -- `2 * half = 1` and `idem S * star (idem S) = 0`; `Ψ` does not see `star (idem S) • y`.
  have h_exp (x : n → 𝔸f E) :
      half * star (star (idem S) • y) ⬝ᵥ idem S • (x + (x + star (idem S) • y)) =
        star y ⬝ᵥ idem S • x := by
    simp only [star_smul, star_star, smul_dotProduct, dotProduct_smul, dotProduct_add, smul_eq_mul]
    linear_combination
      (half * 2 * (star y ⬝ᵥ x) + half * star (idem S) * (star y ⬝ᵥ y)) * idem_mul_self S +
        (half * (star y ⬝ᵥ y)) * idem_mul_star hS + (idem S * (star y ⬝ᵥ x)) * two_mul_half (E := E)
  have h_part (x : n → 𝔸f E) : Ψ (x + star (idem S) • y) = Ψ x := by
    rw [← hΨ.idem_smul (x + star (idem S) • y), ← hΨ.idem_smul x, smul_add, smul_smul,
      idem_mul_star hS, zero_smul, add_zero]
  funext x
  rw [schrodingerAct_apply, h_exp x, h_part x]

include hS in
/-- The Schrödinger operators keep the Schwartz–Bruhat functions above `S`. -/
instance (y : n → 𝔸f E) : IsSchwartzBruhat S (schrodingerAct S y Ψ) := by
  -- `schrodingerAct S y Ψ` is the translate of `Ψ` by `y` times a locally constant function.
  have h_add : IsSchwartzBruhat S fun x : n → 𝔸f E ↦ Ψ (x + y) := hΨ.comp_add y
  refine ⟨?_, (isLocallyConstant_selfDualAddChar.comp_continuous (by fun_prop)).mul
    h_add.locally_constant, ?_⟩
  · intro x
    -- The phase and `Ψ` only see the part of `x` at `S`.
    have h_vec : idem S • (idem S • x + (idem S • x + y)) = idem S • (x + (x + y)) := by
      simp only [smul_add, smul_smul, idem_mul_self]
    rw [schrodingerAct_apply, schrodingerAct_apply, h_vec, ← hΨ.idem_smul,
      ← hΨ.idem_smul (x + y)]
    simp only [smul_add, smul_smul, idem_mul_self]
  · simp only [schrodingerAct_apply]
    -- Where the product is not zero, `Ψ (x + y)` is not zero.
    obtain ⟨C, hC, h_supp⟩ := h_add.compact_support
    exact ⟨C, hC, fun x hx ↦ h_supp x (right_ne_zero_of_mul hx)⟩

/-! ### Translates of the box function span -/

/-- Let `E` be a CM number field with Weil data (instances `CMType E`, `WeilData E`; they fix the
character in `schrodingerAct`), `n` a finite index type and `S` a set of finite places of `E`
disjoint from its complex conjugate. Let `Φ` be a function on finite adelic `n`-vectors that is
Schwartz–Bruhat above `S`: locally constant, depending only on the components at `S`, and with
compact support there. Then `Φ` is a finite combination of Heisenberg translates of the box
function: there are finitely supported coefficients `c` with
`Φ = ∑ c y • schrodingerAct S y (boxIndicator n S)`, which is `schrodingerCombination S c`. Here
`boxIndicator n S` is the indicator of the vectors integral at every place of `S`. -/
lemma _root_.New.Space.mem_range_schrodingerCombination {S : Set (FinPlace E)}
    (hS : S.IsConjDisjoint) {Φ : (n → 𝔸f E) → ℂ} (hΦ : IsSchwartzBruhat S Φ) :
    ∃ c : (n → 𝔸f E) →₀ ℂ, schrodingerCombination S c = Φ := by
  classical
  -- It suffices to treat a coset function. By Fourier inversion on the finite group
  -- `stdLattice / (B ∩ stdLattice)`, with `B` equal to `star t` times the lattice, the coset
  -- function is a multiple of a sum over the classes `q`. Each term is the box function, twisted by
  -- the character of `q` and moved to `z`.
  suffices h_coset : ∀ (t : (𝔸f E)ˣ) (z : n → 𝔸f E), t.val ∈ Ô E →
      cosetIndicator S t z ∈ (schrodingerCombination S).range by
    exact hΦ.mem_of_cosets (schrodingerCombination S).range fun _ _ ↦
      ⟨Set.univ, univ_mem, fun t z ht _ ↦ h_coset t z ht⟩
  intro t z ht
  let B : OpenAddSubgroup (n → 𝔸f E) :=
    comap (smulAddHom (𝔸f E) (n → 𝔸f E) (star t⁻¹.val)) (continuous_const_smul _)
      ⟨stdLattice E n, isOpen_stdLattice⟩
  have h_fintype : Fintype (stdLattice E n ⧸ B.toAddSubgroup.addSubgroupOf (stdLattice E n)) :=
    fintypeOfIndexNeZero (isCompact_stdLattice.relIndex_ne_zero_add B.isOpen)
  let f (q : stdLattice E n ⧸ B.toAddSubgroup.addSubgroupOf (stdLattice E n)) : (n → 𝔸f E) → ℂ :=
    schrodingerAct S (idem S • -z)
      (schrodingerAct S (star (idem S) • -(star t⁻¹.val • (q.out : n → 𝔸f E))) (boxIndicator n S))
  suffices h_eq : cosetIndicator S t z =
      ((latticeMeasure E n).real (B ∩ stdLattice E n) : ℂ) • ∑ q, f q by
    -- By the Heisenberg law each `f q` is a multiple of a translate of the box function.
    have h_translate (y : n → 𝔸f E) :
        schrodingerAct S y (boxIndicator n S) ∈ (schrodingerCombination S).range :=
      ⟨Finsupp.single y 1, by simp⟩
    rw [h_eq]
    refine smul_mem _ _ (sum_mem fun q _ ↦ ?_)
    simp only [f, schrodingerAct_schrodingerAct hS]
    exact smul_mem _ _ (h_translate _)
  -- Evaluate at `x + z`; the two operators in `f q` are a translation and a character.
  funext w
  obtain ⟨x, rfl⟩ : ∃ x : n → 𝔸f E, x + z = w := ⟨w - z, sub_add_cancel w z⟩
  have h_term (q : stdLattice E n ⧸ B.toAddSubgroup.addSubgroupOf (stdLattice E n)) :
      f q (x + z) = selfDualAddChar E (star (idem S • t⁻¹.val • x) ⬝ᵥ (q.out : n → 𝔸f E)) *
        boxIndicator n S x := by
    have h_arg (u : n → 𝔸f E) : star (-(star t⁻¹.val • u)) ⬝ᵥ idem S • x =
        star (-(star (idem S • t⁻¹.val • x) ⬝ᵥ u)) := by
      rw [Matrix.star_dotProduct]
      simp [mul_left_comm]
    simp only [f]
    rw [schrodingerAct_idem hS, schrodingerAct_star_idem_smul hS]
    simp only [add_neg_cancel_right, h_arg, selfDualAddChar_star, neg_neg]
  by_cases hx : x ∈ integralBox n S
  · -- Compute the integral of the character of `t⁻¹ • x` over the lattice in two ways: as a sum
    -- over the cosets of `B`, on which it is constant, and as `1` or `0` by self-duality.
    have h_const : ∀ y₁ y₂ : stdLattice E n, -(y₁ : n → 𝔸f E) + y₂ ∈ B →
        selfDualAddChar E (star (idem S • t⁻¹.val • x) ⬝ᵥ (y₂ : n → 𝔸f E)) =
          selfDualAddChar E (star (idem S • t⁻¹.val • x) ⬝ᵥ (y₁ : n → 𝔸f E)) := by
      -- Two points of one coset differ by a vector pairing integrally with `idem S • t⁻¹ • x`.
      intro y₁ y₂ h_diff
      have h_int : star (idem S • x) ⬝ᵥ star t⁻¹.val • (-(y₁ : n → 𝔸f E) + y₂) ∈ Ô E :=
        star_dotProduct_mem h_diff hx
      have h_split : star (idem S • t⁻¹.val • x) ⬝ᵥ (y₂ : n → 𝔸f E) =
          star (idem S • t⁻¹.val • x) ⬝ᵥ (y₁ : n → 𝔸f E) +
            star (idem S • x) ⬝ᵥ star t⁻¹.val • (-(y₁ : n → 𝔸f E) + y₂) := by
        simp only [star_smul, smul_dotProduct, dotProduct_smul, dotProduct_add, dotProduct_neg,
          smul_eq_mul]
        ring
      rw [h_split, map_add_eq_mul, selfDualAddChar_eq_one_of_mem h_int, mul_one]
    have h_integral_eq_sum : ∫ y in (stdLattice E n : Set (n → 𝔸f E)),
          selfDualAddChar E (star (idem S • t⁻¹.val • x) ⬝ᵥ y) ∂latticeMeasure E n =
        (latticeMeasure E n).real (B ∩ stdLattice E n) •
          ∑ᶠ q : stdLattice E n ⧸ B.toAddSubgroup.addSubgroupOf (stdLattice E n),
            selfDualAddChar E (star (idem S • t⁻¹.val • x) ⬝ᵥ (q.out : n → 𝔸f E)) :=
      setIntegral_eq_finsum (ν := latticeMeasure E n) isCompact_stdLattice B.isOpen
        (F := fun y ↦ selfDualAddChar E (star (idem S • t⁻¹.val • x) ⬝ᵥ y)) h_const
    rw [integral_selfDualAddChar_stdLattice, finsum_eq_sum_of_fintype] at h_integral_eq_sum
    have h_lhs : cosetIndicator S t z (x + z) =
        if idem S • t⁻¹.val • x ∈ stdLattice E n then 1 else 0 := by
      simp [cosetIndicator, integralBox]
    have h_box : boxIndicator n S x = 1 := by simp [hx]
    simp only [h_lhs, h_integral_eq_sum, Pi.smul_apply, Finset.sum_apply, h_term, h_box, mul_one,
      Complex.real_smul, smul_eq_mul]
  · -- Off the box both sides vanish, because `t` is integral.
    have h_not : t⁻¹.val • x ∉ integralBox n S := by
      refine fun h_mem ↦ hx ?_
      have h_t : t.val • idem S • t⁻¹.val • x ∈ stdLattice E n := smul_mem_stdLattice ht h_mem
      rwa [smul_smul, smul_smul, mul_right_comm, Units.mul_inv, one_mul] at h_t
    simp [cosetIndicator, h_term, hx, h_not]

end IsSchwartzBruhat

end New

end
