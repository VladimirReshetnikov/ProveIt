import Lib.General.Groups.ProfiniteCharacters

/-!
# Shapiro's lemma, corestriction and reduction of H² statements to steps of prime index

Let `Γ` be a compact group, `U` an open subgroup and `M` a discrete `Γ`-module. `M.restrictTo U` is
`M` as a `U`-module, and `M.resH2 U` is restriction `H²(Γ, M) → H²(U, M)`. `M.funModule U` is the
module of functions `Γ ⧸ U → M` with `(g F) x = g (F (g⁻¹ x))`. The file proves the parts of
Shapiro's lemma that are needed, the norm from `U` on invariants with a projection formula for the
symbols `(χ, w)`, and the fact that a class in `H²` that dies on `U` is killed by `[Γ : U]`.

## Main definitions and results

* `New.DiscreteModule.shapiroZ1`, `New.DiscreteModule.shapiroH2`: restrict a cocycle to `U` and
  evaluate it at the coset `U`.
* `New.DiscreteModule.shapiro_H0`, `New.DiscreteModule.shapiro_H1`,
  `New.DiscreteModule.shapiroH2_injective`: the parts of Shapiro's lemma that are used. In degree
  zero, every `Γ`-invariant function is `x ↦ x.out y` for some `U`-invariant `y`. In degree one, a
  cocycle whose image is a coboundary is itself a coboundary. In degree two, the map is injective.
* `New.DiscreteModule.corestrictH0`: the norm from `U`.
  `New.DiscreteModule.cyclicClass_corestrictH0` gives the projection formula: if `α` restricts on
  `U` to `(χ|U, w)`, then `(χ, N w)` is `[Γ : U] α`.
* `New.DiscreteModule.mem_of_prime_step`: a class `α` in `H²(Γ, M)` lies in a subgroup `S` if it
  dies on an open normal subgroup `W` and the vanishing of `α - s` (some `s ∈ S`) can be lifted
  through normal steps of prime index. The proof climbs a chain of `l`-subgroups of a finite
  quotient `Γ ⧸ W`, as in Sylow's theorem.
* `New.DiscreteModule.HoldsCorestrictions`: a group of cocycles of `Γ` contains the coboundaries and
  corestrictions of a given group of cocycles of an open subgroup `U`; it is used in local duality.

Notions from other files:
* `New.cyclicClass`: The symbol (χ, w) = δχ ∪ w in H²(G,M) of a continuous character χ: G → ℚ/ℤ
  (`New.QZChar`) and an invariant w. It is the class of (g,h) ↦ carry(χ(g), χ(h))·w.
* `New.H2`: Continuous cohomology H²(G,M): continuous 2-cocycles of ρ modulo coboundaries of
  continuous 1-cochains.

## Relation to the literature

Known; see `Lib.ClassField.GaloisCohomology.KummerCyclicClasses` for sources.
-/

noncomputable section

/-!
## Shapiro's lemma, norms and corestriction for open subgroups

Corestriction on `H²` is not defined as a map. `New.DiscreteModule.mapH2_sum_eq_index_smul`
expresses corestriction after restriction through a class `β` with values in the functions
`Γ ⧸ U → M`. This class is summed over the cosets by `New.DiscreteModule.sum`.
-/

section Corestriction

open QuotientGroup MulAction Function AddMonoidHom Fintype

variable {R Γ : Type} {H : Type*} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Group H] {M : New.DiscreteModule R Γ} [CompactSpace Γ] (U : OpenSubgroup Γ) [TopologicalSpace H]
  (φ : H →ₜ* Γ)

/-- For a continuous homomorphism φ: H → Γ, the additive map from continuous ℚ/ℤ-valued
characters of Γ to those of H, χ ↦ χ∘φ. -/
def New.QZChar.comap : QZChar Γ →+ QZChar H := pairMapZ1 φ LinearMap.id

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
lemma New.QZChar.comap_val_apply (χ : ↥(QZChar Γ)) (h : H) :
    (QZChar.comap φ χ).val h = χ.val (φ h) := rfl

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- The character `χ ∘ φ`, as a homomorphism to `ℚ/ℤ`, takes the value `χ (φ h)` at `h`. -/
lemma New.QZChar.comap_apply [IsTopologicalGroup H] (χ : ↥(QZChar Γ)) (h : H) :
    QZChar.toHom (QZChar.comap φ χ) h = QZChar.toHom χ (φ h) := rfl

/-- An open normal subgroup `U` of the compact group `Γ` with cyclic quotient is the kernel of a
continuous character `Γ → ℚ/ℤ`. -/
lemma New.QZChar.exists_ker_eq_of_isCyclic [U.Normal] (h_cyclic : IsCyclic (Γ ⧸ U.toSubgroup)) :
    ∃ χ : ↥(QZChar Γ), ker χ = U.toSubgroup := by
  -- Compose `Γ → Γ ⧸ U`, an isomorphism with `ZMod n` for `n = [Γ : U]`, and the embedding of
  -- `ZMod n` in `ℚ/ℤ`.
  let f : Γ → ZMod (Nat.card (Γ ⧸ U.toSubgroup)) := fun g ↦
    ((zmodCyclicMulEquiv h_cyclic).symm (g : Γ ⧸ U.toSubgroup)).toAdd
  have hf_cont : Continuous f := by fun_prop
  have hf_cocycle : ∀ g k : Γ, f (g * k) =
      f g + Representation.trivial ℤ Γ (ZMod (Nat.card (Γ ⧸ U.toSubgroup))) g (f k) := by
    simp [f]
  refine ⟨ofZModCocycle _ ⟨f, hf_cont, hf_cocycle⟩, Subgroup.ext fun g ↦ ?_⟩
  have hf_eq_zero : f g = 0 ↔ g ∈ U.toSubgroup := by simp [f, MulEquiv.symm_apply_eq]
  -- The character sends `g` to the image of `f g` in `ℚ/ℤ`, which vanishes exactly when `f g` does.
  show QZ.ofZMod (Nat.card (Γ ⧸ U.toSubgroup)) (f g) = 0 ↔ g ∈ U.toSubgroup
  exact (map_eq_zero_iff _ QZ.ofZMod_injective).trans hf_eq_zero

namespace New.DiscreteModule

/-! ### The Shapiro maps and the norm -/

/-- An element `u` of `U` fixes the coset `U`, so acting by `u` on a function `F : Γ ⧸ U → M`
and evaluating at the coset `U` gives `u` acting on the value `F U`. -/
lemma funModule_apply_one (u : U.toSubgroup) (F : (M.funModule U).V) :
    (M.funModule U).ρ u F ⟦1⟧ = (M.restrictTo U).ρ u (F ⟦1⟧) := by
  -- Both sides are `u` applied to a value of `F`; the arguments agree as `u⁻¹` fixes the coset `U`.
  refine congrArg (_ ∘ F) ?_
  simp [QuotientGroup.eq]

/-- The Shapiro map on continuous 1-cocycles, Z¹(Γ, Fun(Γ/U, M)) → Z¹(U, M): restrict to U and
evaluate at the trivial coset. -/
abbrev shapiroZ1 : ↥(Z1 (M.funModule U).ρ) →+ ↥(Z1 (M.restrictTo U).ρ) :=
  pairMapZ1 (ρ := (M.funModule U).ρ) (subgroupIncl U.1) (LinearMap.proj ⟦1⟧)
    (M.funModule_apply_one U)

/-- The linear map H²(Γ, Fun(Γ/U,M)) → H²(U,M) given by restriction to U followed by evaluation
at the identity coset. -/
abbrev shapiroH2 : New.H2 (M.funModule U).ρ →ₗ[R] New.H2 (M.restrictTo U).ρ :=
  pairMapH2 (ρ := (M.funModule U).ρ) (subgroupIncl U.1) (LinearMap.proj ⟦1⟧)
    (M.funModule_apply_one U)

/-- The norm of a U-invariant y of M: the sum of g·y over the cosets gU in Γ/U. -/
abbrev corestrictH0 (y : (M.restrictTo U).H0) : M.V := M.sum U fun x ↦ M.ρ x.out y

/-! ### Shapiro's lemma -/

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- A section of `Γ → Γ ⧸ U` adapted to `U`: for `U` open in `Γ` there is `s : Γ ⧸ U → Γ` that
sends the coset `U` to `1` (first clause), with `s x` in the coset `x` (second clause), and with
`(s x)⁻¹ g s (g⁻¹ x) ∈ U` for all `x` and `g` (third clause). -/
lemma exists_coset_section :
    ∃ s : Γ ⧸ U.toSubgroup → Γ,
      (∀ g ∈ U.toSubgroup, s g = 1) ∧
      (∀ x : Γ ⧸ (U : Subgroup Γ), (s x)⁻¹ • x = ⟦1⟧) ∧
      ∀ (x : Γ ⧸ (U : Subgroup Γ)) (g : Γ), (s x)⁻¹ * g * s (g⁻¹ • x) ∈ U.toSubgroup := by
  -- Correct the chosen representatives by the inverse of the representative of `U`. Membership in
  -- `U` is tested as fixing the coset `U`.
  -- (`stabilizer_quotient` is removed from the simp set so that it does not undo the rewrite.)
  refine ⟨fun x ↦ x.out * (mk 1 : Γ ⧸ U.toSubgroup).out⁻¹, ?_⟩
  simp +contextual [← eq_inv_smul_iff, ← SetLike.ext_iff.mp (stabilizer_quotient U.toSubgroup),
    mul_smul, -stabilizer_quotient]

/-- Shapiro's lemma in degree zero. A `Γ`-invariant element `F` of the module of functions
`Γ ⧸ U → M` (an equivariant function) is `x ↦ x.out y` for some `U`-invariant `y` in `M`, where
`x.out` is the chosen representative of the coset `x`. This is the function summed in the norm
`New.DiscreteModule.corestrictH0`, so the sum of `F` is the norm of `y`. -/
lemma shapiro_H0 (F : (M.funModule U).H0) :
    ∃ y : (M.restrictTo U).H0, (fun x : Γ ⧸ U.toSubgroup ↦ M.ρ x.out y) = F.val := by
  -- Take for `y` the value of `F` at the coset `U`.
  have h_inv (g : Γ) : (M.funModule U).ρ g F.val = F.val := F.prop g
  refine ⟨⟨F.val ⟦1⟧, fun u ↦ ?_⟩, funext fun x ↦ ?_⟩
  · rw [← funModule_apply_one, h_inv]
  · -- `F x = F (x.out • U) = x.out • F U`, by the invariance of `F` under `x.out`.
    have h_at : M.ρ x.out (F.val (x.out⁻¹ • x)) = F.val x := congrFun (h_inv x.out) x
    simpa [← Quotient.mk_smul_out] using h_at

/-- Shapiro's lemma in degree one, injectivity. If the restriction to `U` of a 1-cocycle `F` with
values in the functions `Γ ⧸ U → M`, evaluated at the coset `U`, is the coboundary of `m`, then
`F` is a coboundary. -/
lemma shapiro_H1 (F : Z1 (M.funModule U).ρ) (m : M.V)
    (h_cob : ∀ u : U.toSubgroup, F.val u ⟦1⟧ = M.ρ u m - m) :
    ∃ n : (M.funModule U).V, ∀ g : Γ, F.val g = ρ (M.funModule U) g n - n := by
  -- Put `n (g U) = g m - F g (g U)`; the hypothesis makes this independent of the representative.
  have h_cocycle (g k : Γ) : F.val (g * k) = F.val g + (M.funModule U).ρ g (F.val k) :=
    F.prop.right g k
  have h_well (g : Γ) (u : U.toSubgroup) :
      M.ρ (g * u) m - F.val (g * u) ↑(g * u) = M.ρ g m - F.val g g := by
    simp [h_cocycle, mk_mul_of_mem g u.prop, h_cob u, ← sub_sub]
  refine ⟨Quotient.lift (fun g : Γ ↦ M.ρ g m - F.val g g) ?_, fun g ↦ funext fun x ↦ ?_⟩
  · rintro _ g ⟨u, rfl⟩
    exact h_well g ⟨_, u.prop⟩
  · -- Every coset is `g * k U`.
    obtain ⟨k, rfl⟩ := (mk_surjective.comp (mul_left_surjective g)) x
    simp [h_cocycle]

/-- Shapiro's lemma in degree two, injectivity: for U open in the compact group Γ, the map
H²(Γ, Fun(Γ/U, M)) → H²(U, M), restriction followed by evaluation at the trivial coset, is
injective. -/
lemma shapiroH2_injective : Injective (M.shapiroH2 U) := by
  -- With a section `s` of `Γ → Γ ⧸ U`, let `t x g = (s x)⁻¹ * g * s (g⁻¹ • x)` in `U`. If the
  -- image of the cocycle `F` is the coboundary of `c`, then `F` is the coboundary of `b` below.
  obtain ⟨s, -, hs_inv, hs_mem⟩ := exists_coset_section U
  let t (x : Γ ⧸ U.toSubgroup) (g : Γ) : U := ⟨(s x)⁻¹ * g * s (g⁻¹ • x), hs_mem x g⟩
  rw [injective_iff_map_eq_zero]
  rintro ⟨F, hF_cont, h_cocycle⟩ h_zero
  obtain ⟨c, hc_cont, hc : ∀ a b : U, F (a, b) ⟦1⟧ = M.ρ a (c b) - c (a * b) + c a⟩ :=
    (QuotientAddGroup.eq_zero_iff _).mp h_zero
  let b (g : Γ) (x : Γ ⧸ U.toSubgroup) : M :=
    M.ρ (s x) (c (t x g)) - F (s x, t x g) x + F (g, s (g⁻¹ • x)) x
  refine (QuotientAddGroup.eq_zero_iff _).mpr ⟨b, by fun_prop, fun g k ↦ funext fun x ↦ ?_⟩
  show F (g, k) x = M.ρ g (b k (g⁻¹ • x)) - b (g * k) x + b g x
  -- Three instances of the cocycle identity, evaluated at `x`.
  have h_cocycle_at (p q r : Γ) :
      F (p * q, r) x = F (p, q * r) x - F (p, q) x + M.ρ p (F (q, r) (p⁻¹ • x)) :=
    congrFun (h_cocycle p q r) x
  -- The identities of `s` and `t` that make the terms match.
  have h_t_mul : (t x g : Γ) * t (g⁻¹ • x) k = t x (g * k) := by simp [t, mul_assoc, mul_smul]
  have h_st (y : Γ ⧸ U.toSubgroup) (h : Γ) : s y * t y h = h * s (h⁻¹ • y) := by
    simp [t, mul_assoc]
  have h_ρ_st (v : M.V) : M.ρ (s x) (M.ρ (t x g) v) = M.ρ g (M.ρ (s (g⁻¹ • x)) v) := by
    simpa using congrArg (fun γ : Γ ↦ M.ρ γ v) (h_st x g)
  -- The value of `F (t x g, t (g⁻¹ • x) k)` at the coset `(s x)⁻¹ • x`, which is `U`, from `hc`.
  have hc_at : F (t x g, t (g⁻¹ • x) k) ((s x)⁻¹ • x) =
      M.ρ (t x g) (c (t (g⁻¹ • x) k)) - c (t x (g * k)) + c (t x g) := by
    rw [hs_inv, hc, (Subtype.ext h_t_mul : t x g * t (g⁻¹ • x) k = t x (g * k))]
  linear_combination (norm := skip) h_cocycle_at g k (s (k⁻¹ • g⁻¹ • x)) +
    h_cocycle_at (s x) (t x g) (t (g⁻¹ • x) k) - h_cocycle_at g (s (g⁻¹ • x)) (t (g⁻¹ • x) k)
  -- Unfold `b` and rewrite by these identities; then all terms cancel.
  simp only [b, hc_at, h_ρ_st, h_st, h_t_mul, map_sub, map_add, mul_inv_rev, mul_smul]
  abel

/-! ### Corestriction and restriction of classes in `H²` -/

lemma index_smul_eq_sum_const (m : M.V) : U.index • m = M.sum U fun _ : Γ ⧸ U.toSubgroup ↦ m := by
  simp [sum, card_eq_nat_card, Subgroup.index_eq_card]

/-- Corestriction after restriction is multiplication by the index. If `β` is a class with values
in the functions `Γ ⧸ U → M` whose Shapiro image is the restriction of `α` to `U`, then summing
`β` over the cosets gives `[Γ : U] α`. -/
lemma mapH2_sum_eq_index_smul (β : New.H2 (M.funModule U).ρ) (α : M.H2) :
    M.resH2 U α = M.shapiroH2 U β → (M.sum U).mapH2 β = U.index • α := by
  refine α.ind' fun x h_res ↦ ?_
  -- The restriction of the class of `x` is the Shapiro image of `x` with values in the constant
  -- functions, so by Shapiro's lemma `β` is that class.
  have h_shapiro : M.shapiroH2 U ((M.const U).mapH2 ⟦x⟧) = M.shapiroH2 U β := h_res
  obtain rfl : (M.const U).mapH2 ⟦x⟧ = β := shapiroH2_injective U h_shapiro
  -- Summing a constant function multiplies by the index.
  refine (congrArg (Quotient.mk _) ?_).symm
  ext p
  show U.index • x.val p = M.sum U fun _ : Γ ⧸ U.toSubgroup ↦ x.val p
  exact index_smul_eq_sum_const U (x.val p)

/-- The projection formula for symbols. Suppose `v` is the norm of the `U`-invariant `w`, and the
restriction of `α` to `U` is `(χ|U, w)`. Here `χ|U` is `QZChar.comap (subgroupIncl U) χ`, `χ`
composed with the inclusion `U → Γ`, and `H0` denotes invariants. Then `(χ, v)` is `[Γ : U] α`. -/
lemma cyclicClass_corestrictH0 (χ : ↥(QZChar Γ))
    (w : ↥(M.restrictTo U).H0) {v : M.H0} (h_norm : M.corestrictH0 U w = v) (α : M.H2)
    (h_res : M.resH2 U α = cyclicClass (M.restrictTo U).ρ (QZChar.comap (subgroupIncl U) χ) w) :
    cyclicClass M.ρ χ v = U.index • α := by
  -- Since `w` is `U`-invariant, `g w` depends only on the coset `gU`.
  have h_out (g : Γ) : M.ρ (g : Γ ⧸ U.toSubgroup).out w = M.ρ g w := by
    obtain ⟨u, hu⟩ := mk_out_eq_mul U.toSubgroup g
    simp [hu, show M.ρ u w = w from w.prop u]
  -- Apply `mapH2_sum_eq_index_smul` to the symbol of `χ` and the invariant function `F : gU ↦ g w`.
  let F : (M.funModule U.toSubgroup).H0 := ⟨fun x : Γ ⧸ U.toSubgroup ↦ M.ρ x.out w,
    by simp [funext_iff, forall_mk, h_out]⟩
  -- The value of `F` at the coset `U` is `w`.
  have h_value : cyclicClass (M.restrictTo U).ρ (QZChar.comap (subgroupIncl U) χ) w =
      M.shapiroH2 U (cyclicClass (M.funModule U).ρ χ F) := by
    have h_F_one : F.val ⟦1⟧ = (w : M.V) := by simpa using h_out 1
    refine congrArg (Quotient.mk _) (Subtype.ext (funext fun p ↦ ?_))
    -- Both sides are `carry (χ u, χ u') •` a value: `w` on the left, `F` at the coset `U` on the
    -- right (the Shapiro image evaluates there).
    show (χ.val p.fst).carry (χ.val p.snd) • (w : M.V) =
      (χ.val p.fst).carry (χ.val p.snd) • F.val ⟦1⟧
    rw [h_F_one]
  -- The sum of the values of `F` is the norm of `w`, which is `v`.
  have h_sum : cyclicClass M.ρ χ v = (M.sum U).mapH2 (cyclicClass (M.funModule U).ρ χ F) := by
    refine congrArg (Quotient.mk _) (Subtype.ext (funext fun p ↦ ?_))
    simp [F, show M.sum U.toSubgroup (fun x ↦ M.ρ x.out w) = v from h_norm]
  rw [h_sum, mapH2_sum_eq_index_smul U _ α (h_res.trans h_value)]

/-- For Γ compact and U an open subgroup, a class in H²(Γ, M) whose restriction to U vanishes is
killed by the index [Γ : U]. -/
lemma index_smul_eq_zero_of_resH2 {x : M.H2} : M.resH2 U x = 0 → U.index • x = 0 := by
  intro h_res
  rw [← mapH2_sum_eq_index_smul U 0 x (by rw [h_res, map_zero]), map_zero]

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- Let `w = k • r` be a `Γ`-invariant element of `M`, and `U` a subgroup of `Γ` that fixes `r`
and on which `k • χ` vanishes. Then the class `(χ, w) = δχ ∪ w` in `H²(Γ, M)` restricts to zero
on `U`. -/
lemma resH2_cyclicClass_eq_zero_of_nsmul_eq {χ : ↥(QZChar Γ)} {k : ℕ} {r : M.V}
    {U : Subgroup Γ} {w : M.H0} (h_w : k • r = ↑w) (h_fix : ∀ g : U, M.ρ g r = r)
    (h_kχ : ∀ g : U, k • χ.val g = 0) : M.resH2 U (cyclicClass M.ρ χ w) = 0 := by
  obtain ⟨w, hw_inv⟩ := w
  obtain rfl : k • r = w := h_w
  -- On `U` the element `r` is itself invariant, and the restricted character is killed by `k`.
  let r' : (M.restrictTo U).H0 := ⟨r, h_fix⟩
  have hχ : k • QZChar.comap (subgroupIncl U) χ = 0 := Subtype.ext (funext h_kχ)
  -- The symbol is additive in both arguments: `(χ, k • r) = (k • χ, r)` on `U`. The first step
  -- holds by definition: restricting a symbol restricts the character and the invariant.
  calc _ = cyclicClass (M.restrictTo U).ρ (QZChar.comap (subgroupIncl U) χ) (k • r') := rfl
    _ = cyclicClass (M.restrictTo U).ρ (k • QZChar.comap (subgroupIncl U) χ) r' := by
      simp only [map_nsmul, nsmul_apply]
    _ = 0 := by rw [hχ, map_zero, AddMonoidHom.zero_apply]

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- `resH2_cyclicClass_eq_zero_of_nsmul_eq` with its two conditions on `U` (`U` fixes `r`, and
`k • χ` vanishes on `U`) joined in one hypothesis. -/
lemma resH2_cyclicClass_eq_zero {χ : ↥(QZChar Γ)} {k : ℕ} {r : M.V} {U : Subgroup Γ} :
    ∀ {w : M.H0}, (k : ℕ) • r = ↑w →
      (∀ g : U, M.ρ g r = r ∧ k • χ.val g = 0) → M.resH2 U (cyclicClass M.ρ χ w) = 0 :=
  fun h_w h_U ↦
    resH2_cyclicClass_eq_zero_of_nsmul_eq h_w (fun g ↦ (h_U g).left) fun g ↦ (h_U g).right

end New.DiscreteModule

end Corestriction

/-! ## Reduction to steps of prime index and corestriction of cocycles -/

section SylowReduction

open QuotientGroup QuotientAddGroup Subgroup

namespace New.DiscreteModule

variable {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {M : DiscreteModule R Γ} [CompactSpace Γ]

/-- The group `Y ≤ Z¹(Γ, M)` of cocycles contains every coboundary and a corestriction of each
cocycle in `Y' ≤ Z¹(U, M)`, for an open subgroup `U` of `Γ`. -/
structure HoldsCorestrictions (U : OpenSubgroup Γ) (Y' : AddSubgroup (Z1 (M.restrictTo U).ρ))
    (Y : AddSubgroup (Z1 M.ρ)) : Prop where
  /-- Every coboundary `g ↦ g m - m` lies in `Y`. -/
  coboundary_mem : ∀ m : M.V, M.coboundary m ∈ Y
  /-- Each `y ∈ Y'` is the Shapiro image (restrict to `U`, evaluate at the trivial coset) of a
  cocycle `F` with values in the functions `Γ ⧸ U → M` whose sum over `Γ ⧸ U` lies in `Y`. -/
  exists_corestriction :
    ∀ y ∈ Y', ∃ F : ↥(Z1 (M.funModule U).ρ), M.shapiroZ1 U F = y ∧ (M.sum U).mapZ1 F ∈ Y

omit [IsTopologicalGroup Γ] [CompactSpace Γ] in
/-- If the restriction of `α` to `U ⊓ V`, seen as a subgroup of `V`, vanishes, then so does
its restriction to `U ⊓ V` seen as a subgroup of `U`. -/
lemma resH2_subgroupOf_eq_zero_symm {U V : Subgroup Γ} {α : M.H2} :
    (M.restrictTo V).resH2 (U.subgroupOf V) (M.resH2 V α) = 0 →
    (M.restrictTo U).resH2 (V.subgroupOf U) (M.resH2 U α) = 0 := by
  -- Pull the vanishing class back along the identification of the two copies of `U ⊓ V`.
  let swap : V.subgroupOf U →ₜ* U.subgroupOf V :=
    .mk (.mk' (fun g ↦ ⟨⟨g, Subgroup.mem_subgroupOf.mp g.prop⟩, g.val.prop⟩) (by tauto))
  intro h_zero
  -- By definition, restricting to `U` and then to `U ⊓ V` is the pull-back along `swap` of
  -- restricting to `V` and then to `U ⊓ V`.
  have h_comp : (M.restrictTo U).resH2 (V.subgroupOf U) (M.resH2 U α) =
      (pairMapH2 swap LinearMap.id) ((M.restrictTo V).resH2 (U.subgroupOf V) (M.resH2 V α)) := by
    induction α using QuotientAddGroup.induction_on
    rfl
  rw [h_comp, h_zero, map_zero]

/-- Let `S ≤ H²(Γ, M)`, and let `α` vanish on an open normal subgroup `W`. Suppose that for
all open `W ≤ V ≤ U` with `V` normal of prime index in `U`: if `α - s` vanishes on `V` for
some `s ∈ S`, then `α - s'` vanishes on `U` for some `s' ∈ S`. Then `α ∈ S`. -/
lemma mem_of_prime_step (S : AddSubgroup M.H2) {α : M.H2} {W : OpenSubgroup Γ} [W.Normal]
    (hW : M.resH2 W α = 0)
    (h_step : ∀ (U : OpenSubgroup Γ) (V : OpenSubgroup U.toSubgroup) [V.Normal], W ≤ U →
      W.toSubgroup.subgroupOf U ≤ V →
      V.index.Prime →
      ∀ s ∈ S,
        (M.restrictTo U).resH2 V (M.resH2 U (α - s)) = 0 → ∃ s' ∈ S, M.resH2 U (α - s') = 0) :
    α ∈ S := by
  -- Suppose that a prime `l` divides the order of `α` modulo `S`.
  suffices addOrderOf (mk' S α) = 1 by simpa
  refine (addOrderOf (mk' S α)).eq_one_iff_not_exists_prime_dvd.mpr fun l l_prime l_dvd ↦ ?_
  have comap_open {L : Subgroup (Γ ⧸ W.1)} : IsOpen (SetLike.coe (comap (mk' W.1) L)) :=
    isOpen_mono (le_comap_mk' _ L) W.isOpen'
  -- Take a maximal `l`-subgroup `K` of `Γ ⧸ W` on whose preimage some `α - s` dies.
  let Dies (U : Subgroup Γ) : Prop := ∃ s ∈ S, M.resH2 U (α - s) = 0
  let Good : Set (Subgroup (Γ ⧸ W.1)) :=
    {L | ∃ n : ℕ, Dies (comap (mk' W.1) L) ∧ Nat.card L = l ^ n}
  -- The trivial subgroup is good: its preimage is `W`, on which `α - 0` dies.
  have hW_dies : M.resH2 (comap (mk' W.1) ⊥) (α - 0) = 0 := by
    rwa [MonoidHom.comap_bot, QuotientGroup.ker_mk', sub_zero]
  have h_bot : ⊥ ∈ Good := ⟨0, ⟨0, S.zero_mem, hW_dies⟩, by simp⟩
  obtain ⟨K, ⟨n, ⟨s, hs, hK_dies⟩, card_K⟩, K_max⟩ :
      ∃ K : Subgroup (Γ ⧸ W.1), Maximal (· ∈ Good) K :=
    Good.toFinite.exists_maximal ⟨⊥, h_bot⟩
  -- A class that dies on an open subgroup is killed by its index. So the index of `K` kills `α`
  -- modulo `S`, `l` divides it, and `K` lies in a subgroup `L` of order `l ^ (n + 1)`.
  have index_kills : K.index • mk' S α = 0 := by
    let UK : OpenSubgroup Γ := ⟨comap (mk' W.1) K, comap_open⟩

    have h_index : UK.index = K.index := by simp [UK, index_comap]
    have hs_zero : mk' S s = 0 := (eq_zero_iff s).mpr hs
    calc K.index • mk' S α = mk' S (UK.index • (α - s)) := by
          rw [map_nsmul, map_sub, hs_zero, sub_zero, h_index]
      _ = 0 := by rw [index_smul_eq_zero_of_resH2 UK hK_dies, map_zero]
  have pow_dvd : l ^ (n + 1) ∣ Nat.card (Γ ⧸ W.1) :=
    calc l ^ (n + 1) = Nat.card K * l := by rw [pow_succ, card_K]
      _ ∣ Nat.card K * K.index :=
        mul_dvd_mul_left (Nat.card K) (l_dvd.trans (addOrderOf_dvd_of_nsmul_eq_zero index_kills))
      _ = Nat.card (Γ ⧸ W.1) := K.card_mul_index
  obtain ⟨L, card_L, K_le⟩ : ∃ L : Subgroup (Γ ⧸ W.1), Nat.card L = l ^ (n + 1) ∧ K ≤ L :=
    Sylow.exists_subgroup_card_pow_succ (hp := ⟨l_prime⟩) pow_dvd card_K
  have index_eq : K.relIndex L = l := by
    -- Indices multiply along `⊥ ≤ K ≤ L`: `l ^ n * [L : K] = l ^ (n + 1)`.
    have h_mul : Nat.card K * K.relIndex L = Nat.card L := by
      simp only [← relIndex_bot_left, relIndex_mul_relIndex ⊥ K L bot_le K_le]
    rw [card_K, card_L, pow_succ] at h_mul
    exact Nat.eq_of_mul_eq_mul_left (pow_pos l_prime.pos n) h_mul
  -- `K` is normal of index `l` in `L`, so `h_step` lifts the vanishing to `L`, against maximality.
  have h_minFac : l = (Nat.card L).minFac := by simp [card_L, l_prime.pow_minFac]
  have hK_normal : (K.subgroupOf L).Normal :=
    normal_of_index_eq_minFac_card (index_eq.trans h_minFac)
  let U : OpenSubgroup Γ := ⟨comap (mk' W.1) L, comap_open⟩
  let V : OpenSubgroup U.1 :=
    ⟨(comap (mk' W.1) K).subgroupOf U, subgroupOf_isOpen _ _ comap_open⟩
  have hV_normal : V.Normal := hK_normal.comap (MonoidHom.subgroupComap (mk' W.1) L)
  have V_prime : V.index.Prime := by
    simp [U, V, ← relIndex.eq_1, relIndex_comap, map_comap_eq_self, index_eq, l_prime]
  have h_dies_V : (M.restrictTo U).resH2 V (M.resH2 U (α - s)) = 0 :=
    resH2_subgroupOf_eq_zero_symm (by rw [hK_dies, map_zero])
  have hW_le_V : W.toSubgroup.subgroupOf U ≤ V := fun _ hg ↦ le_comap_mk' W.1 K hg
  have dies_L : Dies (comap (mk' W.1) L) :=
    h_step U V (le_comap_mk' W.1 L) hW_le_V V_prime s hs h_dies_V
  have L_le : L ≤ K := K_max ⟨n + 1, dies_L, card_L⟩ K_le
  exact l_prime.ne_one (index_eq.symm.trans (relIndex_eq_one.mpr L_le))

end New.DiscreteModule

end SylowReduction

end
