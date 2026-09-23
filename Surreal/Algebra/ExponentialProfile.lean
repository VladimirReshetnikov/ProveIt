import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Order.Interval.Set.OrdConnected
import Surreal.Algebra.SigmaDerivation

/-!
# Exponential profiles and growth-scale rigidity of ordered fields

This file proves the ordered-field and exponential rigidity results of
`docs/surreal/exponential-automorphism-rigidity/article.tex`, built around `thm:profile`.

## Setting

`F` is an ordered field (`[Field F] [LinearOrder F] [IsStrictOrderedRing F]`), `Γ` a linearly
ordered abelian group of any rank, and `w : AddValuation F (WithTop Γ)` a valuation.

* `IsConvexValuation w` is `eq:convex-monotone`: `0 < x ≤ y → w y ≤ w x`. It is equivalent to
  order-convexity of the valuation ring `{x | 0 ≤ w x}`, the source's definition
  (`isConvexValuation_iff_ordConnected`).
* A valuation is *nontrivial* when some nonzero element has nonzero value
  (`∃ x, x ≠ 0 ∧ w x ≠ 0`, as in `Surreal/Algebra/SigmaDerivation.lean`). The source's
  valuations are surjective onto `Γ` by convention; surjectivity is an explicit hypothesis
  `hsurj` exactly where it is used.
* `OrderedExp F` is an ordered exponential: a monotone map `E : F → F` with positive values,
  `E (x + y) = E x * E y`, and onto `F_{>0}`. The source asks for an increasing group
  isomorphism `(F, +) → (F_{>0}, ·)`; injectivity is never used.
* `profile w E : F →+ Γ` is the exponential profile `ν = w ∘ E` of `eq:nu`, and `defect E σ` the
  commutation defect `C_σ x = σ (E x) / E (σ x)` of `eq:defect`. Unital field endomorphisms are
  ring homomorphisms `σ : F →+* F`; displacements `D_σ x = σ x - x` are the σ-derivations of
  `Surreal.SigmaDerivation.isSigmaDerivation_displacement`.

## Main results

* `lt_max_abs_sigmaDerivation`, `sigmaDerivation_cofinal` (`prop:sigma-witness`): for a
  σ-derivation with `δ a ≠ 0` and `B > 0`, the probe `b = 2B(1+|σ a|)/|δ a|` (`probe`) has
  `max |δ b| |δ (a b)| > B`; a nonzero σ-derivation has cofinal and coinitial image. The witness
  `lt_max_abs_of_leibniz` needs only the twisted Leibniz rule for arbitrary maps `σ`, `δ`.
* `lt_max_abs_displacement`, `displacement_cofinal` (`lem:amplify`, `eq:b`, `eq:amplify`), and
  `lt_max_abs_derivation`, `derivation_cofinal` (`lem:derivation-amplify`, for derivations over
  any base ring).
* `exists_abs_lt_of_ordConnected` (`lem:bounded`, in any linearly ordered abelian group) and
  `eq_id_of_displacement_mem`, `eq_id_of_abs_displacement_le` (`cor:bounded-displacement`).
* `profile_antitone`, `profile_surjective`, `mem_ker_profile`, `ker_profile_ordConnected`,
  `ker_profile_ne_top`, `bridge` (`lem:bridge`, `eq:nu`, `eq:H`). Properness of the kernel uses
  only nontriviality of `w`; surjectivity of `ν` uses surjectivity of `w`.
* `eq_id_of_visible_scale` (`thm:visible-scale`, `eq:visible-scale`): `E` need not be onto; one
  `H` with `w (E H) < 0` suffices (positivity of `H` is automatic, `exists_visible_scale`
  supplies such an `H` for an ordered exponential and nontrivial `w`). `eq_id_of_commute`
  is `cor:embedding`.
* `eq_id_of_profile`, `closure_Ioi_eq_top`, `eq_id_of_profile_Ioi` (`thm:profile`,
  `eq:profile-S`), `eq_id_of_tail`, `eq_id_of_tail_valuation` (`cor:tail`), and
  `eq_of_profile_eq`, `ringEquiv_eq_of_profile_eq` (`cor:two-profiles`, where only the second
  map needs to be surjective).
* `motion` (`thm:motion`), `valuation_defect` (`eq:defect-value`), `defect_cofinal`
  (`thm:defect`), `eq_id_of_defect_le`, `eq_id_of_le_defect` (`cor:approx`).
* `derivation_eq_zero_of_nonexpanding` (`thm:derivation`, `eq:nonexpand`), for any
  nowhere-vanishing `E` compatible with the derivation.
* The value-group action `τ_σ` of the conventions section, encoded as any `τ : Γ → Γ` with
  `w (σ y) = τ (w y)`. For `w` onto `Γ` and `σ⁻¹(𝒪_w) = 𝒪_w` (for an automorphism, `σ` stabilizes
  `𝒪_w`), `exists_valueMap` constructs it; it is unique (`valueMap_unique`), additive
  (`valueMap_add`), order-preserving (`valueMap_monotone`), bijective for automorphisms
  (`valueMap_bijective`) and compatible with composition (`valueMap_comp`).
* For such `τ` and `σ` commuting with `E`: `profile_map_of_commute` and
  `profile_displacement_of_commute` (`eq:intertwine`, `eq:displacement-intertwine`),
  `image_profile_displacement` (`eq:image-equality`), `cofinal_value_displacement`
  (`thm:cofinal`, the displacement assertion of `thm:intro`), `eq_of_valuation_eq`
  (`cor:faithful`: trivial kernel, hence injectivity, of `σ ↦ τ_σ`; with `valueMap_comp` it is a
  homomorphism), `eq_id_of_coarsening` (`thm:coarsening`, the coarsening assertion of
  `thm:intro`; the identity on `Γ/Δ` means `τ g - g ∈ Δ` for all `g`), `eq_of_valueMap_eq` and
  `eq_of_coarsening` (`cor:unique-lift`, for `w` and for an invariant coarsening by `Δ` read at
  the level of `w`), and `probes` (`prop:probes`, `eq:probe`, stated in profile form
  `|ν (σ y) - ν y| ≥ η` without assuming that `σ` commutes with `E`); `probes_of_commute` gives
  the literal form `|w (σ (E y)) - w (E y)| ≥ η` of `eq:probe` for `σ` commuting with `E`,
  through `ν (σ y) = w (σ (E y))` (`coe_profile_map_of_commute`).
* `main_rigidity` bundles `thm:intro` for a field automorphism `σ` commuting with `E` and
  stabilizing `𝒪_w`, with `w` onto `Γ`: the action `τ_σ` exists, is an order-preserving additive
  bijection, has cofinal and coinitial displacement image when `σ ≠ id`, is faithful, and is
  faithful on every `Γ/Δ`. The homomorphism `ρ_w : σ ↦ τ_σ` of `cor:faithful` is not bundled as
  a group homomorphism; it is covered by `exists_valueMap`, `valueMap_unique`, `valueMap_add`,
  `valueMap_monotone`, `valueMap_bijective`, `valueMap_comp` and `eq_of_valuation_eq` together.

Coarsenings are handled through `Δ` and `τ` directly: Mathlib has no ordered quotient `Γ/Δ`, so
the coarsened valuation `w_Δ` itself is not constructed. The coarsening clause of
`cor:unique-lift` is proved for automorphisms stabilizing `𝒪_w` whose action stabilizes `Δ`, with
the identity on `Γ/Δ` read as `τ₁ g - τ₂ g ∈ Δ`.

## Pending

The surreal instantiations (`prop:finite-log`, `thm:no`, `cor:question54`, `eq:nonlocal`), which
need the actual surreal exponential and natural valuation, and the later sections of the report
(non-lifting, surcomplex and Laurent examples) are not treated here. Neither is the literal form
of `cor:unique-lift` for `w_Δ` as a valuation in its own right (automorphisms stabilizing only
`𝒪_{w_Δ}`), which needs the ordered quotient `Γ/Δ`.
-/

namespace Surreal.ExponentialProfile

open Surreal.SigmaDerivation

/-! ### Proper convex subgroups are bounded -/

section OrderedGroup

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- `lem:bounded`, in any linearly ordered abelian group: a proper convex subgroup `H` is bounded,
some `B > 0` having `|h| < B` for every `h ∈ H`. -/
theorem exists_abs_lt_of_ordConnected {H : AddSubgroup G} (hc : (H : Set G).OrdConnected)
    (hH : H ≠ ⊤) : ∃ B : G, 0 < B ∧ ∀ h ∈ H, |h| < B := by
  have habs : ∀ x : G, x ∈ H ↔ |x| ∈ H := by
    intro x
    rcases abs_choice x with e | e
    · rw [e]
    · rw [e, neg_mem_iff]
  obtain ⟨b, hb⟩ : ∃ b, b ∉ H := by
    by_contra h
    push Not at h
    exact hH (eq_top_iff.2 fun x _ => h x)
  refine ⟨|b|, abs_pos.2 fun h0 => hb (by rw [h0]; exact H.zero_mem), fun h hh => ?_⟩
  by_contra hle
  exact hb ((habs b).2 (hc.out H.zero_mem ((habs h).1 hh) ⟨abs_nonneg b, not_lt.1 hle⟩))

end OrderedGroup

/-- An *ordered exponential* on an ordered field `F`: a monotone map `E` with positive values,
`E (x + y) = E x * E y`, and onto the positive elements. The source's increasing group
isomorphism `(F, +) → (F_{>0}, ·)` is one; injectivity is never used below. -/
structure OrderedExp (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] where
  /-- The underlying map `E`. -/
  toFun : F → F
  /-- `E` takes positive values. -/
  pos : ∀ x, 0 < toFun x
  /-- The exponential law. -/
  map_add : ∀ x y, toFun (x + y) = toFun x * toFun y
  /-- `E` is increasing. -/
  monotone : Monotone toFun
  /-- `E` is onto `F_{>0}`. -/
  surj : ∀ y, 0 < y → ∃ x, toFun x = y

section OrderedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-! ### The ordered two-point witness -/

/-- The probe `b = 2 B (1 + |s|) / |d|` of `eq:b`, for a bound `B`, the twisted value `s = σ a`
and the output `d = δ a`. -/
def probe (B s d : F) : F :=
  2 * B * (1 + |s|) / |d|

/-- The computation of `prop:sigma-witness`, for arbitrary maps `σ`, `δ` obeying the twisted
Leibniz rule: if `δ a ≠ 0` and `B > 0`, then `max |δ b| |δ (a b)| > B` for the probe `b`. -/
theorem lt_max_abs_of_leibniz {σ δ : F → F} (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a)
    {a B : F} (ha : δ a ≠ 0) (hB : 0 < B) :
    B < max |δ (probe B (σ a) (δ a))| |δ (a * probe B (σ a) (δ a))| := by
  set b := probe B (σ a) (δ a) with hb
  by_contra h
  rw [not_lt, max_le_iff] at h
  have hda : 0 < |δ a| := abs_pos.2 ha
  have hs : 0 ≤ |σ a| := abs_nonneg _
  have h1 : b * δ a = δ (a * b) - σ a * δ b := by rw [hδ]; ring
  have h2 : |b * δ a| = 2 * B * (1 + |σ a|) := by
    have hnum : 0 < 2 * B * (1 + |σ a|) := mul_pos (mul_pos two_pos hB) (by linarith)
    rw [abs_mul, hb, probe, abs_of_nonneg (div_nonneg hnum.le hda.le),
      div_mul_cancel₀ _ hda.ne']
  have h3 : |δ (a * b) - σ a * δ b| ≤ B + |σ a| * B := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    exact add_le_add h.2 (mul_le_mul_of_nonneg_left h.1 hs)
  rw [← h1, h2] at h3
  nlinarith [mul_nonneg hB.le hs]

/-- A nonzero map obeying the twisted Leibniz rule has unbounded absolute values. -/
theorem exists_lt_abs_of_leibniz {σ δ : F → F} (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a)
    (hδ0 : δ ≠ 0) (B : F) : ∃ x, B < |δ x| := by
  obtain ⟨a, ha⟩ : ∃ a, δ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hδ0 (funext h)
  have hB : 0 < |B| + 1 := by positivity
  have hBB : B < |B| + 1 := (le_abs_self B).trans_lt (lt_add_one _)
  rcases lt_max_iff.1 (lt_max_abs_of_leibniz hδ ha hB) with h | h
  · exact ⟨_, hBB.trans h⟩
  · exact ⟨_, hBB.trans h⟩

/-- A nonzero odd map obeying the twisted Leibniz rule has cofinal and coinitial image. -/
theorem exists_lt_and_exists_gt_of_leibniz {σ δ : F → F}
    (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a) (hneg : ∀ x, δ (-x) = -δ x) (hδ0 : δ ≠ 0)
    (c : F) : (∃ x, c < δ x) ∧ ∃ x, δ x < c := by
  obtain ⟨x, hx⟩ := exists_lt_abs_of_leibniz hδ hδ0 |c|
  have h1 := le_abs_self c
  have h2 := neg_abs_le c
  rcases le_or_gt 0 (δ x) with h | h
  · rw [abs_of_nonneg h] at hx
    exact ⟨⟨x, by linarith⟩, ⟨-x, by rw [hneg]; linarith⟩⟩
  · rw [abs_of_neg h] at hx
    exact ⟨⟨-x, by rw [hneg]; linarith⟩, ⟨x, by linarith⟩⟩

/-- A σ-derivation is odd. -/
theorem sigmaDerivation_map_neg {σ : F →+* F} {δ : F → F} (hδ : IsSigmaDerivation σ δ)
    (x : F) : δ (-x) = -δ x := by
  have h0 : δ 0 = 0 := by
    have h := hδ.map_add 0 0
    rw [add_zero] at h
    linarith
  have h := hδ.map_add (-x) x
  rw [neg_add_cancel, h0] at h
  linarith

/-- `prop:sigma-witness`: for a σ-derivation `δ` of an ordered field with `δ a ≠ 0` and `B > 0`,
the probe `b = 2B(1+|σ a|)/|δ a|` has `max |δ b| |δ (a b)| > B`. -/
theorem lt_max_abs_sigmaDerivation {σ : F →+* F} {δ : F → F} (hδ : IsSigmaDerivation σ δ)
    {a B : F} (ha : δ a ≠ 0) (hB : 0 < B) :
    B < max |δ (probe B (σ a) (δ a))| |δ (a * probe B (σ a) (δ a))| :=
  lt_max_abs_of_leibniz hδ.leibniz ha hB

/-- `prop:sigma-witness`, consequence: a nonzero σ-derivation of an ordered field has cofinal and
coinitial image. -/
theorem sigmaDerivation_cofinal {σ : F →+* F} {δ : F → F} (hδ : IsSigmaDerivation σ δ)
    (hδ0 : δ ≠ 0) (c : F) : (∃ x, c < δ x) ∧ ∃ x, δ x < c :=
  exists_lt_and_exists_gt_of_leibniz hδ.leibniz (sigmaDerivation_map_neg hδ) hδ0 c

/-- `lem:amplify` (`eq:b`, `eq:amplify`): if `σ a ≠ a` and `B > 0`, then for the probe
`b = 2B(1+|σ a|)/|σ a - a|` one of the displacements `D_σ b`, `D_σ (a b)` has absolute value
greater than `B`. -/
theorem lt_max_abs_displacement (σ : F →+* F) {a B : F} (ha : σ a ≠ a) (hB : 0 < B) :
    B < max |σ (probe B (σ a) (σ a - a)) - probe B (σ a) (σ a - a)|
      |σ (a * probe B (σ a) (σ a - a)) - a * probe B (σ a) (σ a - a)| :=
  lt_max_abs_of_leibniz (δ := fun x => σ x - x) (isSigmaDerivation_displacement σ).leibniz
    (sub_ne_zero.2 ha) hB

/-- `lem:amplify`, consequence: the displacement image of a nonidentity unital endomorphism of an
ordered field is cofinal and coinitial. -/
theorem displacement_cofinal {σ : F →+* F} (hσ : σ ≠ RingHom.id F) (c : F) :
    (∃ x, c < σ x - x) ∧ ∃ x, σ x - x < c :=
  sigmaDerivation_cofinal (isSigmaDerivation_displacement σ)
    (fun h => hσ (eq_id_of_displacement_eq_zero h)) c

/-- A map obeying the twisted Leibniz rule with absolute values bounded by one `B` vanishes. -/
theorem eq_zero_of_abs_le_of_leibniz {σ δ : F → F}
    (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a) {B : F} (hB : ∀ x, |δ x| ≤ B) : δ = 0 := by
  by_contra h0
  obtain ⟨x, hx⟩ := exists_lt_abs_of_leibniz hδ h0 B
  exact absurd (hB x) (not_le.2 hx)

/-- A σ-derivation of an ordered field with a uniform bound on its absolute values vanishes. -/
theorem sigmaDerivation_eq_zero_of_abs_le {σ : F →+* F} {δ : F → F}
    (hδ : IsSigmaDerivation σ δ) {B : F} (hB : ∀ x, |δ x| ≤ B) : δ = 0 :=
  eq_zero_of_abs_le_of_leibniz hδ.leibniz hB

/-- `cor:bounded-displacement`, general form: a uniform field-valued bound on all absolute
displacements forces the identity. -/
theorem eq_id_of_abs_displacement_le (σ : F →+* F) {B : F} (hB : ∀ x, |σ x - x| ≤ B) :
    σ = RingHom.id F :=
  eq_id_of_displacement_eq_zero (eq_zero_of_abs_le_of_leibniz (δ := fun x => σ x - x)
    (isSigmaDerivation_displacement σ).leibniz hB)

/-- `cor:bounded-displacement`: a unital endomorphism of an ordered field whose displacements lie
in a proper convex additive subgroup is the identity. -/
theorem eq_id_of_displacement_mem (σ : F →+* F) {H : AddSubgroup F}
    (hc : (H : Set F).OrdConnected) (hH : H ≠ ⊤) (h : ∀ x, σ x - x ∈ H) :
    σ = RingHom.id F := by
  obtain ⟨B, -, hB⟩ := exists_abs_lt_of_ordConnected hc hH
  exact eq_id_of_abs_displacement_le σ fun x => (hB _ (h x)).le

section Derivation

variable {R : Type*} [CommRing R] [Algebra R F]

/-- `lem:derivation-amplify`, witness: for a derivation `∂` with `∂ a ≠ 0` and `B > 0`, the probe
`b = 2B(1+|a|)/|∂ a|` has `max |∂ b| |∂ (a b)| > B`. -/
theorem lt_max_abs_derivation (D : Derivation R F F) {a B : F} (ha : D a ≠ 0) (hB : 0 < B) :
    B < max |D (probe B a (D a))| |D (a * probe B a (D a))| :=
  lt_max_abs_of_leibniz (isSigmaDerivation_derivation D).leibniz ha hB

/-- `lem:derivation-amplify`: a nonzero derivation of an ordered field has cofinal and coinitial
image. -/
theorem derivation_cofinal (D : Derivation R F F) (hD : D ≠ 0) (c : F) :
    (∃ x, c < D x) ∧ ∃ x, D x < c :=
  exists_lt_and_exists_gt_of_leibniz (isSigmaDerivation_derivation D).leibniz (map_neg D)
    (fun h => hD (DFunLike.coe_injective (h.trans Derivation.coe_zero.symm))) c

end Derivation

/-! ### Convex valuations -/

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  (w : AddValuation F (WithTop Γ))

/-- A *convex* valuation, in the form `eq:convex-monotone`: `0 < x ≤ y` implies `w y ≤ w x`. -/
def IsConvexValuation : Prop :=
  ∀ ⦃x y : F⦄, 0 < x → x ≤ y → w y ≤ w x

omit [IsStrictOrderedRing F] in
/-- The value of `|x|` is the value of `x`. -/
theorem valuation_abs (x : F) : w |x| = w x := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, w.map_neg]

/-- The equivalence recorded after `eq:convex-monotone`: `w` is convex exactly when its valuation
ring `{x | 0 ≤ w x}` is order-convex. -/
theorem isConvexValuation_iff_ordConnected :
    IsConvexValuation w ↔ {x : F | 0 ≤ w x}.OrdConnected := by
  constructor
  · intro hw
    refine ⟨fun a ha b hb x hx => ?_⟩
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rcases lt_trichotomy x 0 with h | h | h
    · have h' := hw (neg_pos.2 h) (neg_le_neg hx.1)
      rw [w.map_neg, w.map_neg] at h'
      exact ha.trans h'
    · rw [h, w.map_zero]
      exact le_top
    · exact hb.trans (hw h hx.2)
  · intro hc x y hx hxy
    have hy : 0 < y := hx.trans_le hxy
    have h0 : (0 : F) ∈ {x : F | 0 ≤ w x} := by simp
    have h1 : (1 : F) ∈ {x : F | 0 ≤ w x} := by simp
    have hq : x / y ∈ {x : F | 0 ≤ w x} :=
      hc.out h0 h1 ⟨(div_pos hx hy).le, (div_le_one hy).2 hxy⟩
    calc w y ≤ w (x / y) + w y := le_add_of_nonneg_left hq
      _ = w x := by rw [← w.map_mul, div_mul_cancel₀ _ hy.ne']

/-! ### The induced action on values -/

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- For `b ≠ 0`, `w b ≤ w a` exactly when `a / b` lies in the valuation ring. -/
theorem le_valuation_iff_nonneg_div {a b : F} (hb : b ≠ 0) : w b ≤ w a ↔ 0 ≤ w (a / b) := by
  have h : w a = w (a / b) + w b := by rw [← w.map_mul, div_mul_cancel₀ _ hb]
  constructor
  · intro hle
    by_contra hneg
    have h' : w (a / b) + w b < 0 + w b :=
      WithTop.add_lt_add_right (w.ne_top_iff.2 hb) (not_le.1 hneg)
    rw [zero_add, ← h] at h'
    exact absurd hle (not_le.2 h')
  · intro hq
    rw [h]
    exact le_add_of_nonneg_left hq

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The induced value-group action of the conventions section: if `σ⁻¹(𝒪_w) = 𝒪_w` (for a field
automorphism this is `σ (𝒪_w) = 𝒪_w`) and `w` is onto `Γ`, there is `τ : Γ → Γ` with
`w (σ y) = τ (w y)` for every `y ≠ 0`. -/
theorem exists_valueMap (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F}
    (hstab : ∀ y, 0 ≤ w (σ y) ↔ 0 ≤ w y) :
    ∃ τ : Γ → Γ, ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g := by
  have hne : ∀ y : F, y ≠ 0 → w (σ y) ≠ ⊤ := fun y hy => w.ne_top_iff.2 ((map_ne_zero σ).2 hy)
  choose r hr using hsurj
  have hr0 : ∀ g, r g ≠ 0 := fun g h0 => by
    have h' := hr g
    rw [h0, w.map_zero] at h'
    exact WithTop.top_ne_coe h'
  have key : ∀ a b : F, a ≠ 0 → b ≠ 0 → w a = w b → w (σ b) ≤ w (σ a) := by
    intro a b _ hb hab
    rw [le_valuation_iff_nonneg_div w ((map_ne_zero σ).2 hb), ← map_div₀ σ, hstab,
      ← le_valuation_iff_nonneg_div w hb, hab]
  refine ⟨fun g => (w (σ (r g))).untop (hne _ (hr0 g)), fun y g hy => ?_⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [w.map_zero] at hy
    exact WithTop.top_ne_coe hy
  have heq : w y = w (r g) := hy.trans (hr g).symm
  rw [WithTop.coe_untop]
  exact le_antisymm (key _ _ (hr0 g) hy0 heq.symm) (key _ _ hy0 (hr0 g) heq)

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The action of `σ` on values is unique when `w` is onto `Γ`. -/
theorem valueMap_unique (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F} {τ τ' : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g)
    (hτ' : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ' g) : τ = τ' := by
  funext g
  obtain ⟨y, hy⟩ := hsurj g
  exact WithTop.coe_injective ((hτ y g hy).symm.trans (hτ' y g hy))

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- Compatibility with composition (the homomorphism property in `cor:faithful`): if `τ₁`, `τ₂`
are the actions of `σ₁`, `σ₂` on values, then `τ₁ ∘ τ₂` is the action of `σ₁ ∘ σ₂`. -/
theorem valueMap_comp {σ₁ σ₂ : F →+* F} {τ₁ τ₂ : Γ → Γ}
    (h₁ : ∀ (y : F) (g : Γ), w y = g → w (σ₁ y) = τ₁ g)
    (h₂ : ∀ (y : F) (g : Γ), w y = g → w (σ₂ y) = τ₂ g) :
    ∀ (y : F) (g : Γ), w y = g → w ((σ₁.comp σ₂) y) = (τ₁ ∘ τ₂) g :=
  fun y g hy => h₁ (σ₂ y) (τ₂ g) (h₂ y g hy)

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The action of `σ` on values is additive (conventions section). -/
theorem valueMap_add (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F} {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) (g h : Γ) :
    τ (g + h) = τ g + τ h := by
  obtain ⟨y, hy⟩ := hsurj g
  obtain ⟨z, hz⟩ := hsurj h
  have hyz : w (y * z) = ((g + h : Γ) : WithTop Γ) := by
    rw [w.map_mul, hy, hz, WithTop.coe_add]
  apply WithTop.coe_injective
  rw [WithTop.coe_add, ← hτ _ _ hyz, map_mul, w.map_mul, hτ y g hy, hτ z h hz]

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- The action on values of a `σ` with `σ⁻¹(𝒪_w) = 𝒪_w` preserves the order (conventions
section). -/
theorem valueMap_monotone (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F}
    (hstab : ∀ y, 0 ≤ w (σ y) ↔ 0 ≤ w y) {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) : Monotone τ := by
  intro g h hgh
  obtain ⟨y, hy⟩ := hsurj g
  obtain ⟨z, hz⟩ := hsurj h
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [w.map_zero] at hy
    exact WithTop.top_ne_coe hy
  have h1 : w y ≤ w z := by
    rw [hy, hz]
    exact WithTop.coe_le_coe.2 hgh
  rw [le_valuation_iff_nonneg_div w hy0, ← hstab, map_div₀,
    ← le_valuation_iff_nonneg_div w ((map_ne_zero σ).2 hy0), hτ y g hy, hτ z h hz] at h1
  exact WithTop.coe_le_coe.1 h1

omit [LinearOrder F] [IsStrictOrderedRing F] in
/-- For a field automorphism `σ` with `σ (𝒪_w) = 𝒪_w` and `w` onto `Γ`, the action on values is
bijective, with inverse the action of `σ⁻¹` (conventions section). -/
theorem valueMap_bijective (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F ≃+* F}
    (hstab : ∀ y, 0 ≤ w (σ y) ↔ 0 ≤ w y) {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) : Function.Bijective τ := by
  have hstab' : ∀ y, 0 ≤ w (σ.symm y) ↔ 0 ≤ w y := fun y => by
    rw [← hstab, RingEquiv.apply_symm_apply]
  obtain ⟨τ', hτ'⟩ := exists_valueMap w hsurj (σ := (σ.symm : F →+* F)) hstab'
  have h1 : τ ∘ τ' = id :=
    valueMap_unique w hsurj (valueMap_comp w (σ₁ := (σ : F →+* F)) hτ hτ')
      fun y g hy => by simpa using hy
  have h2 : τ' ∘ τ = id :=
    valueMap_unique w hsurj (valueMap_comp w (σ₂ := (σ : F →+* F)) hτ' hτ)
      fun y g hy => by simpa using hy
  exact Function.bijective_iff_has_inverse.2 ⟨τ', congrFun h2, congrFun h1⟩

variable {w}

omit [IsStrictOrderedRing F] in
/-- A positive element with negative convex valuation exceeds `1`. -/
theorem one_lt_of_valuation_neg (hw : IsConvexValuation w) {u : F} (hu : 0 < u)
    (hwu : w u < 0) : 1 < u := by
  by_contra h
  have h' := hw hu (not_lt.1 h)
  rw [w.map_one] at h'
  exact absurd hwu (not_lt.2 h')

/-- A nontrivial convex valuation has an element `u > 1` with `w u < 0`. -/
theorem exists_one_lt_valuation_neg (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) : ∃ u : F, 1 < u ∧ w u < 0 := by
  obtain ⟨t, ht⟩ := exists_valuation_neg w hnt
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  rw [← valuation_abs] at ht
  exact ⟨|t|, one_lt_of_valuation_neg hw (abs_pos.2 ht0) ht, ht⟩

omit [IsStrictOrderedRing F] in
/-- The valuation ring of a convex valuation is bounded by every positive `u` with `w u < 0`. -/
theorem abs_lt_of_valuation_nonneg (hw : IsConvexValuation w) {u : F} (hu : 0 < u)
    (hwu : w u < 0) {y : F} (hy : 0 ≤ w y) : |y| < u := by
  by_contra h
  have h' := hw hu (not_lt.1 h)
  rw [valuation_abs] at h'
  exact absurd (hy.trans h') (not_le.2 hwu)

section Derivation

variable {R : Type*} [CommRing R] [Algebra R F]

/-- `thm:derivation` (`eq:nonexpand`): let `w` be a nontrivial convex valuation, `E : F → F` a
nowhere-vanishing map and `∂` a derivation with `∂ (E x) = E x ∂ x` for all `x`. If
`w (∂ y) ≥ w y` for every `y ≠ 0`, then `∂ = 0`. The source takes `E` to be an ordered
exponential; only `E x ≠ 0` is used. -/
theorem derivation_eq_zero_of_nonexpanding (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) (D : Derivation R F F) {E : F → F} (hE0 : ∀ x, E x ≠ 0)
    (hcomp : ∀ x, D (E x) = E x * D x) (hexp : ∀ y, y ≠ 0 → w y ≤ w (D y)) : D = 0 := by
  obtain ⟨u, hu1, hwu⟩ := exists_one_lt_valuation_neg hw hnt
  have hbound : ∀ x, |D x| ≤ u := fun x => by
    have h := hexp (E x) (hE0 x)
    rw [hcomp, w.map_mul] at h
    have h0 : 0 ≤ w (D x) :=
      (WithTop.add_le_add_iff_left (w.ne_top_iff.2 (hE0 x))).1 (by rwa [add_zero])
    exact (abs_lt_of_valuation_nonneg hw (zero_lt_one.trans hu1) hwu h0).le
  exact DFunLike.coe_injective ((eq_zero_of_abs_le_of_leibniz
    (isSigmaDerivation_derivation D).leibniz hbound).trans Derivation.coe_zero.symm)

end Derivation

/-! ### Rigidity from one visible exponential scale -/

omit [IsStrictOrderedRing F] in
/-- A positive multiplicative map `E` with `E (x + y) = E x * E y` has `E 0 = 1`. -/
theorem exp_zero_eq_one {E : F → F} (hpos : ∀ x, 0 < E x)
    (hadd : ∀ x y, E (x + y) = E x * E y) : E 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hpos 0).ne' (by rw [mul_one, ← h])

/-- The convex subgroup `E⁻¹(𝒪_w^×)` is bounded by every `H` with `w (E H) < 0`. -/
theorem abs_lt_of_valuation_exp_eq_zero (hw : IsConvexValuation w) {E : F → F}
    (hpos : ∀ x, 0 < E x) (hadd : ∀ x y, E (x + y) = E x * E y) (hmono : Monotone E) {H : F}
    (hvis : w (E H) < 0) {y : F} (hy : w (E y) = 0) : |y| < H := by
  have key : ∀ z, w (E z) = 0 → z < H := by
    intro z hz
    by_contra h
    have h' := hw (hpos H) (hmono (not_lt.1 h))
    rw [hz] at h'
    exact absurd hvis (not_lt.2 h')
  have hy' : w (E (-y)) = 0 := by
    have h := w.map_mul (E (-y)) (E y)
    rw [← hadd, neg_add_cancel, exp_zero_eq_one hpos hadd, w.map_one, hy, add_zero] at h
    exact h.symm
  exact abs_lt.2 ⟨by linarith [key _ hy'], key y hy⟩

omit [IsStrictOrderedRing F] in
/-- If `σ` fixes every value and commutes with `E`, then `E (σ x - x)` is a valuation unit. -/
theorem valuation_exp_displacement {E : F → F} (hpos : ∀ x, 0 < E x)
    (hadd : ∀ x y, E (x + y) = E x * E y) {σ : F →+* F}
    (hval : ∀ y, y ≠ 0 → w (σ y) = w y) (hcomm : ∀ x, σ (E x) = E (σ x)) (x : F) :
    w (E (σ x - x)) = 0 := by
  have hsplit : E (σ x) = E (σ x - x) * E x := by rw [← hadd, sub_add_cancel]
  apply WithTop.add_right_cancel (w.ne_top_iff.2 (hpos x).ne')
  rw [zero_add, ← w.map_mul, ← hsplit, ← hcomm, hval _ (hpos x).ne']

/-- `thm:visible-scale`: let `w` be a convex valuation and `E : (F, +) → (F_{>0}, ·)` an
order-preserving homomorphism, not assumed onto, with one visible scale `w (E H) < 0`
(`eq:visible-scale`). A unital endomorphism `σ` with `w (σ y) = w y` for all `y ≠ 0` and
`σ (E x) = E (σ x)` for all `x` is the identity. (The source's `H > 0` follows from
`w (E H) < 0` and is not needed as a hypothesis.) -/
theorem eq_id_of_visible_scale (hw : IsConvexValuation w) {E : F → F} (hpos : ∀ x, 0 < E x)
    (hadd : ∀ x y, E (x + y) = E x * E y) (hmono : Monotone E) {H : F} (hvis : w (E H) < 0)
    {σ : F →+* F} (hval : ∀ y, y ≠ 0 → w (σ y) = w y) (hcomm : ∀ x, σ (E x) = E (σ x)) :
    σ = RingHom.id F :=
  eq_id_of_abs_displacement_le σ fun x => (abs_lt_of_valuation_exp_eq_zero hw hpos hadd hmono
    hvis (valuation_exp_displacement hpos hadd hval hcomm x)).le

/-! ### Ordered exponentials and the bridge -/

namespace OrderedExp

instance : CoeFun (OrderedExp F) fun _ => F → F :=
  ⟨OrderedExp.toFun⟩

variable (E : OrderedExp F)

/-- An ordered exponential never vanishes. -/
theorem ne_zero (x : F) : E x ≠ 0 :=
  (E.pos x).ne'

/-- `E 0 = 1`. -/
theorem map_zero : E 0 = 1 :=
  exp_zero_eq_one E.pos E.map_add

/-- `E (x - y) = E x / E y`. -/
theorem map_sub (x y : F) : E (x - y) = E x / E y := by
  rw [eq_div_iff (E.ne_zero y), ← E.map_add, sub_add_cancel]

end OrderedExp

variable (w) (E : OrderedExp F)

/-- `eq:nu`: the exponential profile `ν = w ∘ E`, an additive map `F → Γ`. -/
noncomputable def profile : F →+ Γ :=
  AddMonoidHom.mk' (fun x => (w (E x)).untop (w.ne_top_iff.2 (E.ne_zero x))) fun x y => by
    rw [WithTop.untop_eq_iff, WithTop.coe_add, WithTop.coe_untop, WithTop.coe_untop, E.map_add,
      w.map_mul]

/-- The profile, read in `WithTop Γ`, is `w (E x)`. -/
theorem coe_profile (x : F) : (profile w E x : WithTop Γ) = w (E x) :=
  WithTop.coe_untop _ _

/-- `ν x = g` exactly when `w (E x) = g`. -/
theorem profile_eq_iff (x : F) (g : Γ) : profile w E x = g ↔ w (E x) = g := by
  rw [← coe_profile w E x, WithTop.coe_eq_coe]

/-- The profile hits the value of every nonzero element: `ν (log |a|) = w a`. -/
theorem exists_profile_eq {a : F} (ha : a ≠ 0) : ∃ x, (profile w E x : WithTop Γ) = w a := by
  obtain ⟨x, hx⟩ := E.surj |a| (abs_pos.2 ha)
  exact ⟨x, by rw [coe_profile, hx, valuation_abs]⟩

/-- `eq:H`: the kernel of the profile is `H_w = {x | E x ∈ 𝒪_w^×}`. -/
theorem mem_ker_profile (x : F) : x ∈ (profile w E).ker ↔ w (E x) = 0 := by
  rw [AddMonoidHom.mem_ker, profile_eq_iff, WithTop.coe_zero]

variable {w}

/-- `lem:bridge`: the profile of a convex valuation is order-reversing. -/
theorem profile_antitone (hw : IsConvexValuation w) : Antitone (profile w E) := by
  intro x y hxy
  have h := hw (E.pos x) (E.monotone hxy)
  rwa [← coe_profile w E, ← coe_profile w E, WithTop.coe_le_coe] at h

/-- `lem:bridge`: the profile is onto `Γ` when `w` is. -/
theorem profile_surjective (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) :
    Function.Surjective (profile w E) := by
  intro γ
  obtain ⟨a, ha⟩ := hsurj γ
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨x, hx⟩ := exists_profile_eq w E ha0
  exact ⟨x, WithTop.coe_injective (hx.trans ha)⟩

/-- `lem:bridge`: the kernel `H_w` of the profile is convex. -/
theorem ker_profile_ordConnected (hw : IsConvexValuation w) :
    ((profile w E).ker : Set F).OrdConnected := by
  refine ⟨fun a ha b hb x hx => ?_⟩
  have h1 := profile_antitone E hw hx.1
  have h2 := profile_antitone E hw hx.2
  simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at ha hb ⊢
  rw [ha] at h1
  rw [hb] at h2
  exact le_antisymm h1 h2

/-- `lem:bridge`: the kernel `H_w` of the profile is proper when `w` is nontrivial. -/
theorem ker_profile_ne_top (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) :
    (profile w E).ker ≠ ⊤ := by
  obtain ⟨u, hu1, hwu⟩ := exists_one_lt_valuation_neg hw hnt
  obtain ⟨x, hx⟩ := E.surj u (zero_lt_one.trans hu1)
  intro htop
  have hmem : x ∈ (profile w E).ker := by
    rw [htop]
    exact AddSubgroup.mem_top x
  rw [mem_ker_profile, hx] at hmem
  exact hwu.ne hmem

/-- `lem:bridge`: for an ordered exponential `E` and a nontrivial convex valuation `w` onto `Γ`,
the profile `ν = w ∘ E` (additive by construction) is order-reversing and onto `Γ`, and its
kernel `H_w` is a proper convex additive subgroup. -/
theorem bridge (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) :
    Antitone (profile w E) ∧ Function.Surjective (profile w E) ∧
      ((profile w E).ker : Set F).OrdConnected ∧ (profile w E).ker ≠ ⊤ :=
  ⟨profile_antitone E hw, profile_surjective E hsurj, ker_profile_ordConnected E hw,
    ker_profile_ne_top E hw hnt⟩

/-- The remark after `thm:visible-scale`: for an ordered exponential and a nontrivial convex
valuation, some `H > 0` has `w (E H) < 0`. -/
theorem exists_visible_scale (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) :
    ∃ H : F, 0 < H ∧ w (E H) < 0 := by
  obtain ⟨u, hu1, hwu⟩ := exists_one_lt_valuation_neg hw hnt
  obtain ⟨H, hH⟩ := E.surj u (zero_lt_one.trans hu1)
  refine ⟨H, lt_of_not_ge fun hle => ?_, hH ▸ hwu⟩
  have h := E.monotone hle
  rw [E.map_zero, hH] at h
  exact absurd hu1 (not_lt.2 h)

/-- `cor:embedding`: a unital self-embedding commuting with an ordered exponential and fixing
every value of a nontrivial convex valuation is the identity. -/
theorem eq_id_of_commute (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    {σ : F →+* F} (hval : ∀ y, y ≠ 0 → w (σ y) = w y) (hcomm : ∀ x, σ (E x) = E (σ x)) :
    σ = RingHom.id F := by
  obtain ⟨H, -, hH⟩ := exists_visible_scale E hw hnt
  exact eq_id_of_visible_scale hw E.pos E.map_add E.monotone hH hval hcomm

/-! ### Profile rigidity -/

/-- `thm:profile` (`eq:profile-S`): let `E` be an ordered exponential, `w` a nontrivial convex
valuation and `σ` a unital field endomorphism. If `S` generates `(F, +)` and
`ν (σ x) = ν x` for every `x ∈ S`, then `σ` is the identity. -/
theorem eq_id_of_profile (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (σ : F →+* F) {S : Set F} (hS : AddSubgroup.closure S = ⊤)
    (hprof : ∀ x ∈ S, w (E (σ x)) = w (E x)) : σ = RingHom.id F := by
  have key : ∀ y, σ y - y ∈ (profile w E).ker := by
    intro y
    have hy : y ∈ AddSubgroup.closure S := by
      rw [hS]
      exact AddSubgroup.mem_top y
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      rw [AddMonoidHom.mem_ker, map_sub, sub_eq_zero]
      exact WithTop.coe_injective (by rw [coe_profile, coe_profile, hprof x hx])
    | zero =>
      rw [map_zero, sub_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add, add_sub_add_comm]
      exact add_mem hx hy
    | neg x _ hx =>
      have h : σ (-x) - -x = -(σ x - x) := by rw [map_neg]; ring
      rw [h]
      exact neg_mem hx
  exact eq_id_of_displacement_mem σ (ker_profile_ordConnected E hw) (ker_profile_ne_top E hw hnt)
    key

/-- Every final interval `(c, ∞)` generates `(F, +)`: `x = (|c| + |x| + 1 + x) - (|c| + |x| + 1)`
(the last part of the proof of `thm:profile`). -/
theorem closure_Ioi_eq_top (c : F) : AddSubgroup.closure (Set.Ioi c) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  have hz : |c| + |x| + 1 ∈ Set.Ioi c := by
    show c < _
    linarith [le_abs_self c, abs_nonneg x]
  have hy : |c| + |x| + 1 + x ∈ Set.Ioi c := by
    show c < _
    linarith [le_abs_self c, neg_abs_le x]
  have h := AddSubgroup.sub_mem _ (AddSubgroup.subset_closure hy) (AddSubgroup.subset_closure hz)
  rwa [add_sub_cancel_left] at h

/-- `thm:profile`, final assertion: it suffices that `ν (σ x) = ν x` for every `x > c`. -/
theorem eq_id_of_profile_Ioi (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (σ : F →+* F) {c : F} (hprof : ∀ x, c < x → w (E (σ x)) = w (E x)) : σ = RingHom.id F :=
  eq_id_of_profile E hw hnt σ (closure_Ioi_eq_top c) hprof

/-- `cor:tail`, weaker tail condition: if `σ` fixes every value and
`w (σ (E x)) = w (E (σ x))` for all `x > c`, then `σ` is the identity. -/
theorem eq_id_of_tail_valuation (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    {σ : F →+* F} (hval : ∀ y, y ≠ 0 → w (σ y) = w y) {c : F}
    (htail : ∀ x, c < x → w (σ (E x)) = w (E (σ x))) : σ = RingHom.id F :=
  eq_id_of_profile_Ioi E hw hnt σ fun x hx => by rw [← htail x hx, hval _ (E.ne_zero x)]

/-- `cor:tail`: if `σ` fixes every value and `σ (E x) = E (σ x)` for all `x > c`, then `σ` is
the identity. -/
theorem eq_id_of_tail (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    {σ : F →+* F} (hval : ∀ y, y ≠ 0 → w (σ y) = w y) {c : F}
    (hcomm : ∀ x, c < x → σ (E x) = E (σ x)) : σ = RingHom.id F :=
  eq_id_of_tail_valuation E hw hnt hval fun x hx => by rw [hcomm x hx]

/-- `cor:two-profiles`: a unital endomorphism `σ` and a field automorphism `τ` with
`ν (σ x) = ν (τ x)` for every `x` are equal. Only `τ` needs to be surjective. -/
theorem eq_of_profile_eq (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (σ : F →+* F) (τ : F ≃+* F) (h : ∀ x, w (E (σ x)) = w (E (τ x))) :
    σ = (τ : F →+* F) := by
  have hρ := eq_id_of_profile E hw hnt (σ.comp (τ.symm : F →+* F)) (S := Set.univ)
    AddSubgroup.closure_univ fun y _ => by
      have h' := h (τ.symm y)
      rwa [RingEquiv.apply_symm_apply] at h'
  ext x
  have h' := RingHom.congr_fun hρ (τ x)
  simpa using h'

/-- `cor:two-profiles` for two field automorphisms. -/
theorem ringEquiv_eq_of_profile_eq (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) (σ τ : F ≃+* F) (h : ∀ x, w (E (σ x)) = w (E (τ x))) :
    σ = τ := by
  have h' := eq_of_profile_eq E hw hnt (σ : F →+* F) τ h
  exact RingEquiv.ext fun x => RingHom.congr_fun h' x

/-! ### Multiplicative motion and commutation defects -/

/-- `thm:motion`: a nonidentity unital endomorphism commuting with an ordered exponential has
cofinal and coinitial multiplicative motion: for every `M > 1` there are `y, z > 0` with
`σ y / y > M` and `0 < σ z / z < 1 / M`. No valuation is used. -/
theorem motion {σ : F →+* F} (hσ : σ ≠ RingHom.id F) (hcomm : ∀ x, σ (E x) = E (σ x)) {M : F}
    (hM : 1 < M) :
    (∃ y, 0 < y ∧ M < σ y / y) ∧ ∃ z, 0 < z ∧ 0 < σ z / z ∧ σ z / z < 1 / M := by
  have hM0 : 0 < M := zero_lt_one.trans hM
  have hratio : ∀ x, σ (E x) / E x = E (σ x - x) := fun x => by rw [hcomm, E.map_sub]
  obtain ⟨l₁, hl₁⟩ := E.surj (2 * M) (by linarith)
  obtain ⟨l₂, hl₂⟩ := E.surj (1 / (2 * M)) (div_pos one_pos (by linarith))
  obtain ⟨x, hx⟩ := (displacement_cofinal hσ l₁).1
  obtain ⟨x', hx'⟩ := (displacement_cofinal hσ l₂).2
  refine ⟨⟨E x, E.pos x, ?_⟩, ⟨E x', E.pos x', ?_, ?_⟩⟩
  · rw [hratio]
    have h := E.monotone hx.le
    rw [hl₁] at h
    linarith
  · rw [hratio]
    exact E.pos _
  · rw [hratio]
    have h := E.monotone hx'.le
    rw [hl₂] at h
    have h' : 1 / (2 * M) < 1 / M := one_div_lt_one_div_of_lt hM0 (by linarith)
    linarith

/-- `eq:defect`: the exponential commutation defect `C_σ x = σ (E x) / E (σ x)`. -/
def defect (σ : F →+* F) (x : F) : F :=
  σ (E x) / E (σ x)

/-- `eq:defect-value`: if `σ` fixes every value, then `w (C_σ x) = -ν (σ x - x)`. -/
theorem valuation_defect {σ : F →+* F} (hval : ∀ y, y ≠ 0 → w (σ y) = w y) (x : F) :
    w (defect E σ x) = ((-profile w E (σ x - x) : Γ) : WithTop Γ) := by
  have hC : defect E σ x ≠ 0 :=
    div_ne_zero ((map_ne_zero σ).2 (E.ne_zero x)) (E.ne_zero _)
  have h1 : defect E σ x * E (σ x) = σ (E x) := div_mul_cancel₀ _ (E.ne_zero _)
  have h2 : w (defect E σ x) + (profile w E (σ x) : WithTop Γ) = (profile w E x : WithTop Γ) := by
    rw [coe_profile, coe_profile, ← w.map_mul, h1, hval _ (E.ne_zero x)]
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.1 (w.ne_top_iff.2 hC)
  rw [← hg] at h2 ⊢
  rw [WithTop.coe_eq_coe, map_sub, neg_sub]
  rw [← WithTop.coe_add, WithTop.coe_eq_coe] at h2
  exact eq_sub_of_add_eq h2

/-- The profile of the displacement image is cofinal and coinitial in `Γ`, with strict
inequalities (the core of `thm:cofinal` and `thm:defect`). -/
theorem exists_profile_displacement (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F}
    (hσ : σ ≠ RingHom.id F) (γ : Γ) :
    (∃ x, γ < profile w E (σ x - x)) ∧ ∃ x, profile w E (σ x - x) < γ := by
  obtain ⟨t, ht⟩ := exists_valuation_neg w hnt
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp at ht
  obtain ⟨η, hη⟩ := WithTop.ne_top_iff_exists.1 (w.ne_top_iff.2 ht0)
  rw [← hη] at ht
  have hη0 : η < 0 := by exact_mod_cast ht
  obtain ⟨r, hr⟩ := profile_surjective E hsurj (γ - η)
  obtain ⟨s, hs⟩ := profile_surjective E hsurj (γ + η)
  obtain ⟨x, hx⟩ := (displacement_cofinal hσ r).2
  obtain ⟨x', hx'⟩ := (displacement_cofinal hσ s).1
  refine ⟨⟨x, ?_⟩, ⟨x', ?_⟩⟩
  · have h := profile_antitone E hw hx.le
    rw [hr] at h
    exact (lt_sub_iff_add_lt.2 (add_lt_iff_neg_left.2 hη0)).trans_le h
  · have h := profile_antitone E hw hx'.le
    rw [hs] at h
    exact h.trans_lt (add_lt_iff_neg_left.2 hη0)

/-- `thm:defect`: let `E` be an ordered exponential, `w` a nontrivial convex valuation onto `Γ`,
and `σ ≠ id` a unital endomorphism with `w (σ y) = w y` for all `y ≠ 0`. Then the values
`w (C_σ x)` of the commutation defects are cofinal and coinitial in `Γ`. -/
theorem defect_cofinal (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F} (hσ : σ ≠ RingHom.id F)
    (hval : ∀ y, y ≠ 0 → w (σ y) = w y) (γ : Γ) :
    (∃ x, (γ : WithTop Γ) < w (defect E σ x)) ∧ ∃ x, w (defect E σ x) < γ := by
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := exists_profile_displacement E hw hnt hsurj hσ (-γ)
  refine ⟨⟨x', ?_⟩, ⟨x, ?_⟩⟩
  · rw [valuation_defect E hval]
    exact WithTop.coe_lt_coe.2 (lt_neg_of_lt_neg hx')
  · rw [valuation_defect E hval]
    exact WithTop.coe_lt_coe.2 (neg_lt_of_neg_lt hx)

/-- `cor:approx`, upper bound: under the hypotheses of `thm:defect` without `σ ≠ id`, if all
`w (C_σ x)` are bounded above, then `σ` is the identity. -/
theorem eq_id_of_defect_le (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F} (hval : ∀ y, y ≠ 0 → w (σ y) = w y)
    {β : Γ} (h : ∀ x, w (defect E σ x) ≤ β) : σ = RingHom.id F := by
  by_contra hσ
  obtain ⟨⟨x, hx⟩, -⟩ := defect_cofinal E hw hnt hsurj hσ hval β
  exact absurd (h x) (not_le.2 hx)

/-- `cor:approx`, lower bound: if all `w (C_σ x)` are bounded below, then `σ` is the identity. -/
theorem eq_id_of_le_defect (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F} (hval : ∀ y, y ≠ 0 → w (σ y) = w y)
    {β : Γ} (h : ∀ x, (β : WithTop Γ) ≤ w (defect E σ x)) : σ = RingHom.id F := by
  by_contra hσ
  obtain ⟨-, ⟨x, hx⟩⟩ := defect_cofinal E hw hnt hsurj hσ hval β
  exact absurd (h x) (not_le.2 hx)

/-! ### The action on the value group -/

/-- `eq:intertwine`: if `σ` commutes with `E` and `w (σ y) = τ (w y)`, then
`ν (σ x) = τ (ν x)`. -/
theorem profile_map_of_commute {σ : F →+* F} (hcomm : ∀ x, σ (E x) = E (σ x)) {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) (x : F) :
    profile w E (σ x) = τ (profile w E x) := by
  apply WithTop.coe_injective
  rw [coe_profile, ← hcomm, hτ (E x) _ (coe_profile w E x).symm]

/-- `eq:displacement-intertwine`: `ν (σ x - x) = τ (ν x) - ν x`. -/
theorem profile_displacement_of_commute {σ : F →+* F} (hcomm : ∀ x, σ (E x) = E (σ x))
    {τ : Γ → Γ} (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) (x : F) :
    profile w E (σ x - x) = τ (profile w E x) - profile w E x := by
  rw [map_sub, profile_map_of_commute E hcomm hτ]

/-- `eq:image-equality`: when `w` is onto `Γ`, `ν (D_σ F) = (τ - id)(Γ)`. -/
theorem image_profile_displacement (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F}
    (hcomm : ∀ x, σ (E x) = E (σ x)) {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) :
    Set.range (fun x => profile w E (σ x - x)) = Set.range (fun g => τ g - g) := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨profile w E x, (profile_displacement_of_commute E hcomm hτ x).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := profile_surjective E hsurj g
    exact ⟨x, profile_displacement_of_commute E hcomm hτ x⟩

/-- `thm:cofinal` (the displacement assertion of `thm:intro`): let `E` be an ordered exponential,
`w` a nontrivial convex valuation onto `Γ`, and `σ ≠ id` a unital endomorphism commuting with
`E` whose action on values is `τ : Γ → Γ` (`w (σ y) = τ (w y)`, as for the induced action
`τ_σ` of `exists_valueMap`). Then `(τ - id)(Γ)` is cofinal and coinitial in `Γ`. -/
theorem cofinal_value_displacement (hw : IsConvexValuation w)
    (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0) (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F}
    (hσ : σ ≠ RingHom.id F) (hcomm : ∀ x, σ (E x) = E (σ x)) {τ : Γ → Γ}
    (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) (γ : Γ) :
    (∃ g, γ < τ g - g) ∧ ∃ g, τ g - g < γ := by
  obtain ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ := exists_profile_displacement E hw hnt hsurj hσ γ
  rw [profile_displacement_of_commute E hcomm hτ] at hx hx'
  exact ⟨⟨_, hx⟩, ⟨_, hx'⟩⟩

/-- `thm:coarsening` (the coarsening assertion of `thm:intro`): with the hypotheses of
`thm:cofinal` except `σ ≠ id`, if `σ` induces the identity on `Γ/Δ` for a proper convex subgroup
`Δ`, that is `τ g - g ∈ Δ` for every `g`, then `σ` is the identity. -/
theorem eq_id_of_coarsening (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) {σ : F →+* F} (hcomm : ∀ x, σ (E x) = E (σ x))
    {τ : Γ → Γ} (hτ : ∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) {Δ : AddSubgroup Γ}
    (hΔc : (Δ : Set Γ).OrdConnected) (hΔ : Δ ≠ ⊤) (hid : ∀ g, τ g - g ∈ Δ) :
    σ = RingHom.id F := by
  by_contra hσ
  obtain ⟨B, -, hB⟩ := exists_abs_lt_of_ordConnected hΔc hΔ
  obtain ⟨⟨g, hg⟩, -⟩ := cofinal_value_displacement E hw hnt hsurj hσ hcomm hτ B
  exact absurd ((le_abs_self _).trans_lt (hB _ (hid g))) (not_lt.2 hg.le)

/-- `cor:faithful` and `cor:unique-lift` (for the valuation `w` itself): for a nontrivial convex
valuation `w`, a unital endomorphism `σ₁` and a field automorphism `σ₂`, both commuting with an
ordered exponential and acting in the same way on values (`w (σ₁ y) = w (σ₂ y)` for `y ≠ 0`), are
equal. This is the injectivity of `σ ↦ τ_σ`; with `σ₂ = id` it is the triviality of its
kernel. -/
theorem eq_of_valuation_eq (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (σ₁ : F →+* F) (σ₂ : F ≃+* F) (hc₁ : ∀ x, σ₁ (E x) = E (σ₁ x))
    (hc₂ : ∀ x, σ₂ (E x) = E (σ₂ x)) (h : ∀ y, y ≠ 0 → w (σ₁ y) = w (σ₂ y)) :
    σ₁ = (σ₂ : F →+* F) :=
  eq_of_profile_eq E hw hnt σ₁ σ₂ fun x => by rw [← hc₁, ← hc₂, h _ (E.ne_zero x)]

/-- `cor:unique-lift` (for the valuation `w` itself): a map `τ : Γ → Γ` is the action on values
of at most one exponential automorphism; here `σ₁` need only be a unital endomorphism. -/
theorem eq_of_valueMap_eq (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (σ₁ : F →+* F) (σ₂ : F ≃+* F) (hc₁ : ∀ x, σ₁ (E x) = E (σ₁ x))
    (hc₂ : ∀ x, σ₂ (E x) = E (σ₂ x)) {τ : Γ → Γ}
    (h₁ : ∀ (y : F) (g : Γ), w y = g → w (σ₁ y) = τ g)
    (h₂ : ∀ (y : F) (g : Γ), w y = g → w (σ₂ y) = τ g) : σ₁ = (σ₂ : F →+* F) :=
  eq_of_valuation_eq E hw hnt σ₁ σ₂ hc₁ hc₂ fun y hy => by
    obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.1 (w.ne_top_iff.2 hy)
    exact (h₁ y g hg.symm).trans (h₂ y g hg.symm).symm

/-- `cor:unique-lift` for an invariant coarsening, stated at the level of `w`: let `w` be a
nontrivial convex valuation onto `Γ` and `σ₁`, `σ₂` field automorphisms commuting with an
ordered exponential, with actions `τ₁`, `τ₂` on values, where `σ₂ (𝒪_w) = 𝒪_w` and `τ₂`
stabilizes a proper convex subgroup `Δ`. If `σ₁` and `σ₂` induce the same map on `Γ/Δ`
(`τ₁ g - τ₂ g ∈ Δ` for all `g`), then `σ₁ = σ₂`. The coarsened valuation `w_Δ` is not
constructed, so automorphisms stabilizing only `𝒪_{w_Δ}` are not covered. -/
theorem eq_of_coarsening (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) (σ₁ σ₂ : F ≃+* F) (hc₁ : ∀ x, σ₁ (E x) = E (σ₁ x))
    (hc₂ : ∀ x, σ₂ (E x) = E (σ₂ x)) (hstab₂ : ∀ y, 0 ≤ w (σ₂ y) ↔ 0 ≤ w y) {τ₁ τ₂ : Γ → Γ}
    (h₁ : ∀ (y : F) (g : Γ), w y = g → w (σ₁ y) = τ₁ g)
    (h₂ : ∀ (y : F) (g : Γ), w y = g → w (σ₂ y) = τ₂ g) {Δ : AddSubgroup Γ}
    (hΔc : (Δ : Set Γ).OrdConnected) (hΔ : Δ ≠ ⊤) (hΔ₂ : ∀ g, τ₂ g ∈ Δ ↔ g ∈ Δ)
    (hq : ∀ g, τ₁ g - τ₂ g ∈ Δ) : σ₁ = σ₂ := by
  have hstab' : ∀ y, 0 ≤ w (σ₂.symm y) ↔ 0 ≤ w y := fun y => by
    rw [← hstab₂, RingEquiv.apply_symm_apply]
  obtain ⟨τ', hτ'⟩ := exists_valueMap w hsurj (σ := (σ₂.symm : F →+* F)) hstab'
  have hinv : τ₂ ∘ τ' = id :=
    valueMap_unique w hsurj (valueMap_comp w (σ₁ := (σ₂ : F →+* F)) h₂ hτ')
      fun y g hy => by simpa using hy
  have hinv' : τ' ∘ τ₂ = id :=
    valueMap_unique w hsurj (valueMap_comp w (σ₂ := (σ₂ : F →+* F)) hτ' h₂)
      fun y g hy => by simpa using hy
  let T : Γ →+ Γ := AddMonoidHom.mk' τ' (valueMap_add w hsurj hτ')
  have hc' : ∀ x, σ₂.symm (E x) = E (σ₂.symm x) := fun x => by
    apply σ₂.injective
    rw [RingEquiv.apply_symm_apply, hc₂, RingEquiv.apply_symm_apply]
  have hρ := eq_id_of_coarsening E hw hnt hsurj
    (σ := (σ₂.symm : F →+* F).comp (σ₁ : F →+* F))
    (fun x => by
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [hc₁, hc'])
    (valueMap_comp w (σ₁ := (σ₂.symm : F →+* F)) (σ₂ := (σ₁ : F →+* F)) hτ' h₁) hΔc hΔ
    fun g => by
      have hg : g = τ' (τ₂ g) := (congrFun hinv' g).symm
      have hmem : τ' (τ₁ g - τ₂ g) ∈ Δ := by
        rw [← hΔ₂]
        have h' : τ₂ (τ' (τ₁ g - τ₂ g)) = τ₁ g - τ₂ g := congrFun hinv (τ₁ g - τ₂ g)
        rw [h']
        exact hq g
      have hsub : τ' (τ₁ g - τ₂ g) = τ' (τ₁ g) - τ' (τ₂ g) := map_sub T _ _
      rw [hsub, ← hg] at hmem
      exact hmem
  ext x
  have h' := RingHom.congr_fun hρ x
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingHom.id_apply] at h'
  have h'' := congrArg σ₂ h'
  rwa [RingEquiv.apply_symm_apply] at h''

/-- `thm:intro`, bundled: let `E` be an ordered exponential, `w` a nontrivial convex valuation onto
`Γ`, and `σ` a field automorphism commuting with `E` with `σ (𝒪_w) = 𝒪_w`. Then there is a map
`τ = τ_σ : Γ → Γ` with `w (σ y) = τ (w y)` for `y ≠ 0`, which is additive, order-preserving and
bijective; if `σ ≠ id`, `(τ - id)(Γ)` is cofinal and coinitial in `Γ`; `τ = id` forces `σ = id`
(faithfulness on `Γ`); and for every proper convex subgroup `Δ`, if `σ` induces the identity on
`Γ/Δ` (`τ g - g ∈ Δ` for all `g`), then `σ = id`. The last clause does not need `τ` to
stabilize `Δ`. -/
theorem main_rigidity (hw : IsConvexValuation w) (hnt : ∃ x : F, x ≠ 0 ∧ w x ≠ 0)
    (hsurj : ∀ γ : Γ, ∃ y : F, w y = γ) (σ : F ≃+* F) (hcomm : ∀ x, σ (E x) = E (σ x))
    (hstab : ∀ y, 0 ≤ w (σ y) ↔ 0 ≤ w y) :
    ∃ τ : Γ → Γ, (∀ (y : F) (g : Γ), w y = g → w (σ y) = τ g) ∧
      (∀ g h, τ (g + h) = τ g + τ h) ∧ Monotone τ ∧ Function.Bijective τ ∧
      (σ ≠ RingEquiv.refl F → ∀ γ : Γ, (∃ g, γ < τ g - g) ∧ ∃ g, τ g - g < γ) ∧
      (τ = id → σ = RingEquiv.refl F) ∧
      ∀ Δ : AddSubgroup Γ, (Δ : Set Γ).OrdConnected → Δ ≠ ⊤ → (∀ g, τ g - g ∈ Δ) →
        σ = RingEquiv.refl F := by
  obtain ⟨τ, hτ⟩ := exists_valueMap w hsurj (σ := (σ : F →+* F)) hstab
  refine ⟨τ, hτ, valueMap_add w hsurj hτ, valueMap_monotone w hsurj hstab hτ,
    valueMap_bijective w hsurj hstab hτ, fun hσ => cofinal_value_displacement E hw hnt hsurj
      (fun h => hσ (RingEquiv.ext fun x => RingHom.congr_fun h x)) hcomm hτ, fun hid => ?_,
    fun Δ hΔc hΔ hq => RingEquiv.ext fun x => RingHom.congr_fun
      (eq_id_of_coarsening E hw hnt hsurj (σ := (σ : F →+* F)) hcomm hτ hΔc hΔ hq) x⟩
  refine RingEquiv.ext fun x => RingHom.congr_fun (eq_of_valuation_eq E hw hnt σ
    (RingEquiv.refl F) hcomm (fun _ => rfl) fun y hy => ?_) x
  obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.1 (w.ne_top_iff.2 hy)
  rw [hτ y g hg.symm, hid, id, hg]
  rfl

/-- Under commutation with `E`, the profile of `σ y` is the value of `σ (E y)`. -/
theorem coe_profile_map_of_commute {σ : F →+* F} (hcomm : ∀ x, σ (E x) = E (σ x)) (y : F) :
    (profile w E (σ y) : WithTop Γ) = w (σ (E y)) := by
  rw [coe_profile, hcomm]

/-- A displacement larger in absolute value than `B`, where `ν B = -η`, has profile at least `η`
in absolute value. -/
theorem le_abs_profile_of_lt_abs (hw : IsConvexValuation w) {B : F} {η : Γ}
    (hB : profile w E B = -η) {d : F} (hd : B < |d|) : η ≤ |profile w E d| := by
  rcases le_or_gt 0 d with h | h
  · rw [abs_of_nonneg h] at hd
    have h' := profile_antitone E hw hd.le
    rw [hB] at h'
    exact (le_neg.1 h').trans (neg_le_abs _)
  · rw [abs_of_neg h] at hd
    have h' := profile_antitone E hw (show d ≤ -B by linarith)
    rw [map_neg, hB, neg_neg] at h'
    exact h'.trans (le_abs_self _)

/-- `prop:probes` (`eq:probe`): let `E` be an ordered exponential, `w` a convex valuation,
`σ a ≠ a` and `η > 0` in `Γ`, and let `B = log c` for a `c` with `w c = -η`, that is
`w (E B) = -η`. Then `B > 0`, the probe `b = 2B(1+|σ a|)/|σ a - a|` is positive, and
`|ν (σ y) - ν y| ≥ η` for `y = b` or `y = a b`. Commutation of `σ` with `E` is not assumed.
When `σ` commutes with `E`, `ν (σ y) = w (σ (E y))` (`coe_profile_map_of_commute`), which gives
the literal form of `eq:probe` (`probes_of_commute`). -/
theorem probes (hw : IsConvexValuation w) {σ : F →+* F} {a : F} (ha : σ a ≠ a) {η : Γ}
    (hη : 0 < η) {B : F} (hB : w (E B) = ((-η : Γ) : WithTop Γ)) :
    0 < B ∧ 0 < probe B (σ a) (σ a - a) ∧
      (η ≤ |profile w E (σ (probe B (σ a) (σ a - a))) - profile w E (probe B (σ a) (σ a - a))|
        ∨ η ≤ |profile w E (σ (a * probe B (σ a) (σ a - a))) -
          profile w E (a * probe B (σ a) (σ a - a))|) := by
  have hνB : profile w E B = -η := (profile_eq_iff w E B (-η)).2 hB
  have hwB : w (E B) < 0 := by
    rw [hB]
    exact WithTop.coe_lt_coe.2 (neg_lt_zero.2 hη)
  have hB0 : 0 < B := by
    have h1 := one_lt_of_valuation_neg hw (E.pos B) hwB
    by_contra hle
    have h2 := E.monotone (not_lt.1 hle)
    rw [E.map_zero] at h2
    exact absurd h1 (not_lt.2 h2)
  refine ⟨hB0, div_pos (mul_pos (mul_pos two_pos hB0) (by positivity))
    (abs_pos.2 (sub_ne_zero.2 ha)), ?_⟩
  rcases lt_max_iff.1 (lt_max_abs_displacement σ ha hB0) with h | h
  · left
    rw [← map_sub (profile w E)]
    exact le_abs_profile_of_lt_abs E hw hνB h
  · right
    rw [← map_sub (profile w E)]
    exact le_abs_profile_of_lt_abs E hw hνB h

/-- `prop:probes` in the literal form `eq:probe`, for `σ` commuting with `E`: under the
hypotheses of `probes`, `B > 0`, the probe `b` is positive, and for some `y ∈ {b, a b}` the
finite values `w (σ (E y)) = g` and `w (E y) = h` satisfy `|g - h| ≥ η`. -/
theorem probes_of_commute (hw : IsConvexValuation w) {σ : F →+* F}
    (hcomm : ∀ x, σ (E x) = E (σ x)) {a : F} (ha : σ a ≠ a) {η : Γ} (hη : 0 < η) {B : F}
    (hB : w (E B) = ((-η : Γ) : WithTop Γ)) :
    0 < B ∧ 0 < probe B (σ a) (σ a - a) ∧
      ∃ y ∈ ({probe B (σ a) (σ a - a), a * probe B (σ a) (σ a - a)} : Set F),
        ∀ g h : Γ, w (σ (E y)) = g → w (E y) = h → η ≤ |g - h| := by
  obtain ⟨hB0, hb0, hy⟩ := probes E hw ha hη hB
  have key : ∀ y, η ≤ |profile w E (σ y) - profile w E y| →
      ∀ g h : Γ, w (σ (E y)) = g → w (E y) = h → η ≤ |g - h| := by
    intro y hy g h hg hh
    rw [← (profile_eq_iff w E (σ y) g).2 (by rw [← hcomm]; exact hg),
      ← (profile_eq_iff w E y h).2 hh]
    exact hy
  rcases hy with hy | hy
  · exact ⟨hB0, hb0, _, Set.mem_insert _ _, key _ hy⟩
  · exact ⟨hB0, hb0, _, Set.mem_insert_of_mem _ (Set.mem_singleton _), key _ hy⟩

end OrderedField

end Surreal.ExponentialProfile
