import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Derivation.Basic

/-!
# Valuation-bounded σ-derivations

This file formalizes `def:sigma-derivation` and proves the twisted product identity
`eq:twisted`, `thm:sigma-derivation`, `prop:valued-amplification`, `cor:detector`,
`thm:derivation-valued` and `cor:no-contraction` of
`docs/surreal/exponential-automorphism-rigidity/article.tex`.

A valuation is an `AddValuation K (WithTop Γ)` on a field `K` of arbitrary characteristic,
with `Γ` any linearly ordered abelian group (no rank restriction). It is *nontrivial* when some
nonzero element has nonzero value, and *surjective* when every `γ : Γ` is a value. A unital
field endomorphism is a ring homomorphism `K →+* K`; it is never assumed to preserve `v`.

* `IsSigmaDerivation σ δ` (`def:sigma-derivation`): `δ` is additive and
  `δ (a b) = σ a δ b + b δ a`. The displacement `x ↦ σ x - x` is one
  (`isSigmaDerivation_displacement`, `eq:twisted`); every derivation is an `id`-derivation and
  every `id`-derivation is a `ℤ`-derivation (the remark after `def:sigma-derivation`).
* `IsSigmaDerivation.eq_zero`, `IsSigmaDerivation.exists_valuation_lt`
  (`thm:sigma-derivation`, both forms): for a nontrivial surjective valuation, a `σ`-derivation
  whose values are all `≥ β` for one `β : Γ` vanishes. The underlying results are more general:
  `exists_valuation_lt_valuation` uses only the twisted Leibniz rule (neither additivity of `δ`
  nor any property of `σ`) and only nontriviality of `v`, and concludes that the values of a
  nonzero `δ` are coinitial in the value group `v(Kˣ)`; `eq_zero_of_forall_le` needs only that
  the values of `v` are coinitial in `Γ`.
* `exists_displacement_lt_valuation` (`prop:valued-amplification`): for a nontrivial valuation
  and a nonidentity endomorphism `σ`, the values `v (σ x - x)` with `σ x ≠ x` are coinitial in
  the value group `v(Kˣ)`; `exists_displacement_lt` is the form with coinitiality in `Γ` for a
  surjective valuation.
* `eq_id_of_detector` (`cor:detector`): the exponential detector `E : (K, +) → (Kˣ, ·)`, with
  `E x` a valuation unit (`v (E x) = 0`) only when `v x ≥ β`, forces every value-preserving unital
  endomorphism commuting with `E` to be the identity. In characteristic `p > 0` every
  homomorphism `(K, +) → (Kˣ, ·)` is trivial (`E x ^ p = E (p x) = 1`), so for a nontrivial
  surjective `v` the hypotheses cannot all hold there and the corollary is only meaningful in
  characteristic `0`.
* `derivation_eq_zero_of_loss`, `exists_loss_lt` (`thm:derivation-valued`, both forms) and
  `not_forall_le`, `not_forall_lt`, `not_forall_le_mul`, `not_forall_lt_mul`
  (`cor:no-contraction`): for any nowhere-vanishing map `E` and any derivation `∂` with
  `∂ (E x) = E x ∂ x`, a bound `v (∂ y) ≥ v y + γ` for all `y ≠ 0` forces `∂ = 0`; with
  `γ = 0` this gives `cor:no-contraction` for `∂` and for every `c ∂` with `c ≠ 0`.

The valuation inequality is used only in the safe direction `min (v x) (v y) ≤ v (x - y)`.
The ordered-field statements of the report (`lem:amplify`, `cor:bounded-displacement`,
`prop:sigma-witness`, `lem:derivation-amplify`, `thm:derivation`, the convex-valuation and
exponential theorems) and the surreal instantiations of `cor:detector` and
`thm:derivation-valued` (via `prop:finite-log` and the Berarducci–Mantova derivation) are not
proved here and remain pending.
-/

namespace Surreal.SigmaDerivation

section Definition

variable {K : Type*} [CommRing K]

/-- `def:sigma-derivation`: for a unital endomorphism `σ`, a `σ`-derivation is an additive map
`δ` satisfying the twisted Leibniz rule `δ (a b) = σ a δ b + b δ a` (`eq:sigma-leibniz`). -/
structure IsSigmaDerivation (σ : K →+* K) (δ : K → K) : Prop where
  map_add : ∀ x y, δ (x + y) = δ x + δ y
  leibniz : ∀ a b, δ (a * b) = σ a * δ b + b * δ a

/-- `eq:twisted`: the displacement `D_σ x = σ x - x` of a unital endomorphism is a
`σ`-derivation, `D_σ (a b) = σ a D_σ b + b D_σ a`. -/
theorem isSigmaDerivation_displacement (σ : K →+* K) :
    IsSigmaDerivation σ fun x => σ x - x where
  map_add x y := by rw [map_add]; ring
  leibniz a b := by rw [map_mul]; ring

/-- Every derivation, over any base ring, is an `id`-derivation (the remark after
`def:sigma-derivation`). -/
theorem isSigmaDerivation_derivation {R : Type*} [CommRing R] [Algebra R K]
    (D : Derivation R K K) : IsSigmaDerivation (RingHom.id K) D where
  map_add := D.map_add
  leibniz a b := by rw [D.leibniz, smul_eq_mul, smul_eq_mul, RingHom.id_apply]

/-- Conversely, an `id`-derivation is a `ℤ`-derivation with the same underlying map, so ordinary
derivations are exactly the `id`-derivations (the remark after `def:sigma-derivation`). -/
def IsSigmaDerivation.toDerivation {δ : K → K} (h : IsSigmaDerivation (RingHom.id K) δ) :
    Derivation ℤ K K :=
  Derivation.mk' (AddMonoidHom.mk' δ h.map_add).toIntLinearMap fun a b => by
    simpa only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul,
      RingHom.id_apply] using h.leibniz a b

@[simp]
theorem IsSigmaDerivation.coe_toDerivation {δ : K → K}
    (h : IsSigmaDerivation (RingHom.id K) δ) : ⇑h.toDerivation = δ :=
  rfl

end Definition

section Valuation

variable {K : Type*} [Field K] {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ]
  [IsOrderedAddMonoid Γ] (v : AddValuation K (WithTop Γ))

/-- The valuation step of `thm:sigma-derivation`: from `b δ a = δ (a b) - σ a δ b`,
`v (b δ a) ≥ min (v (δ (a b))) (v (σ a) + v (δ b))`. Only the twisted Leibniz rule is used. -/
theorem min_le_valuation_mul {σ δ : K → K} (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a)
    (a b : K) : min (v (δ (a * b))) (v (σ a) + v (δ b)) ≤ v (b * δ a) := by
  have h : b * δ a = δ (a * b) - σ a * δ b := by rw [hδ]; ring
  rw [h, ← v.map_mul]
  exact v.map_sub _ _

/-- The two probes `b` and `a b` of `thm:sigma-derivation` and `prop:valued-amplification`:
if `v (b δ a) < min β (v (σ a) + β)`, then `v (δ b) < β` or `v (δ (a b)) < β`. -/
theorem valuation_lt_or_valuation_lt {σ δ : K → K}
    (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a) {a b : K} {β : WithTop Γ}
    (hb : v (b * δ a) < min β (v (σ a) + β)) : v (δ b) < β ∨ v (δ (a * b)) < β := by
  by_contra h
  rw [not_or, not_lt, not_lt] at h
  refine absurd hb (not_lt.2 ((min_le_min h.2 ?_).trans (min_le_valuation_mul v hδ a b)))
  gcongr
  exact h.1

/-- A nontrivial valuation takes a negative value. -/
theorem exists_valuation_neg (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) : ∃ t : K, v t < 0 := by
  obtain ⟨x, hx, hvx⟩ := hnt
  rcases hvx.lt_or_gt with h | h
  · exact ⟨x, h⟩
  · refine ⟨x⁻¹, lt_of_not_ge fun hge => ?_⟩
    have hsum : v x + v x⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
    exact (h.trans_le (le_add_of_nonneg_right hge)).ne' hsum

/-- For a nontrivial valuation, every nonzero `y` has a multiple `b y` of value below that of
any nonzero `z`. -/
theorem exists_valuation_mul_lt (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) {y z : K} (hy : y ≠ 0)
    (hz : z ≠ 0) : ∃ b : K, v (b * y) < v z := by
  obtain ⟨t, ht⟩ := exists_valuation_neg v hnt
  refine ⟨z * t / y, ?_⟩
  rw [div_mul_cancel₀ _ hy, v.map_mul]
  calc v z + v t < v z + 0 := WithTop.add_lt_add_left (v.ne_top_iff.2 hz) ht
    _ = v z := add_zero _

/-- A surjective valuation onto a nontrivial group is nontrivial. -/
theorem exists_valuation_ne_zero [Nontrivial Γ] (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ) :
    ∃ x : K, x ≠ 0 ∧ v x ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_ne (0 : Γ)
  obtain ⟨x, hx⟩ := hsurj g
  refine ⟨x, ?_, ?_⟩
  · rintro rfl
    simp at hx
  · rw [hx]
    exact_mod_cast hg

/-- The values of a nontrivial surjective valuation are coinitial in `Γ`. -/
theorem exists_valuation_lt_of_surjective (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) (γ : Γ) : ∃ x : K, v x < γ := by
  obtain ⟨c, hc⟩ := hsurj γ
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨b, hb⟩ := exists_valuation_mul_lt v hnt one_ne_zero hc0
  exact ⟨b * 1, hc ▸ hb⟩

/-- `thm:sigma-derivation` in value-group form, and in greater generality: for a nontrivial
valuation, the values of a nonzero map `δ` obeying the twisted Leibniz rule for an arbitrary map
`σ` are coinitial in the value group `v(Kˣ)`. Neither additivity of `δ`, nor any property of `σ`,
nor surjectivity of `v` is used. -/
theorem exists_valuation_lt_valuation (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) {σ δ : K → K}
    (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a) (hδ0 : δ ≠ 0) {c : K} (hc : c ≠ 0) :
    ∃ x, v (δ x) < v c := by
  obtain ⟨a, ha⟩ : ∃ a, δ a ≠ 0 := by
    by_contra h
    push Not at h
    exact hδ0 (funext h)
  obtain ⟨c', hc', hM⟩ : ∃ c' : K, c' ≠ 0 ∧ v c' = min (v c) (v (σ a) + v c) := by
    rcases le_total (v c) (v (σ a) + v c) with h | h
    · exact ⟨c, hc, (min_eq_left h).symm⟩
    · refine ⟨σ a * c, fun h0 => hc ?_, by rw [v.map_mul, min_eq_right h]⟩
      rw [← v.map_mul, h0, v.map_zero, top_le_iff] at h
      exact v.top_iff.1 h
  obtain ⟨b, hb⟩ := exists_valuation_mul_lt v hnt ha hc'
  rw [hM] at hb
  rcases valuation_lt_or_valuation_lt v hδ hb with h | h
  · exact ⟨b, h⟩
  · exact ⟨a * b, h⟩

/-- `thm:sigma-derivation`, second form, when the values of `v` are coinitial in `Γ`: a nonzero
map obeying the twisted Leibniz rule has, for every `β : Γ`, a value below `β`. -/
theorem exists_valuation_lt (hcoin : ∀ γ : Γ, ∃ x : K, v x < γ) {σ δ : K → K}
    (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a) (hδ0 : δ ≠ 0) (β : Γ) :
    ∃ x, v (δ x) < β := by
  obtain ⟨c, hc⟩ := hcoin β
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  obtain ⟨t, ht⟩ := hcoin 0
  have hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0 := by
    refine ⟨t, ?_, ?_⟩
    · rintro rfl
      simp at ht
    · rw [WithTop.coe_zero] at ht
      exact ht.ne
  obtain ⟨x, hx⟩ := exists_valuation_lt_valuation v hnt hδ hδ0 hc0
  exact ⟨x, hx.trans hc⟩

/-- `thm:sigma-derivation`, first form, when the values of `v` are coinitial in `Γ`: a map
obeying the twisted Leibniz rule whose values are all `≥ β` for one `β : Γ` vanishes. -/
theorem eq_zero_of_forall_le (hcoin : ∀ γ : Γ, ∃ x : K, v x < γ) {σ δ : K → K}
    (hδ : ∀ a b, δ (a * b) = σ a * δ b + b * δ a) {β : Γ}
    (hβ : ∀ x, (β : WithTop Γ) ≤ v (δ x)) : δ = 0 := by
  by_contra hδ0
  obtain ⟨x, hx⟩ := exists_valuation_lt v hcoin hδ hδ0 β
  exact absurd hx (not_lt.2 (hβ x))

/-- `thm:sigma-derivation`: let `v` be a nontrivial surjective valuation on a field of arbitrary
characteristic, `σ` a unital field endomorphism and `δ` a `σ`-derivation. If there is a single
`β : Γ` with `v (δ x) ≥ β` for every `x` (`eq:uniform-output`), then `δ = 0`. -/
theorem IsSigmaDerivation.eq_zero (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) {σ : K →+* K} {δ : K → K} (hδ : IsSigmaDerivation σ δ)
    {β : Γ} (hβ : ∀ x, (β : WithTop Γ) ≤ v (δ x)) : δ = 0 :=
  eq_zero_of_forall_le v (exists_valuation_lt_of_surjective v hsurj hnt) hδ.leibniz hβ

/-- `thm:sigma-derivation`, equivalent form: for a nontrivial surjective valuation, a nonzero
`σ`-derivation has, for every `β : Γ`, some `x` with `v (δ x) < β`. -/
theorem IsSigmaDerivation.exists_valuation_lt (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) {σ : K →+* K} {δ : K → K} (hδ : IsSigmaDerivation σ δ)
    (hδ0 : δ ≠ 0) (β : Γ) : ∃ x, v (δ x) < β :=
  Surreal.SigmaDerivation.exists_valuation_lt v
    (exists_valuation_lt_of_surjective v hsurj hnt) hδ.leibniz hδ0 β

/-- A unital endomorphism with vanishing displacement is the identity. -/
theorem eq_id_of_displacement_eq_zero {σ : K →+* K} (h : (fun x => σ x - x) = 0) :
    σ = RingHom.id K := by
  ext x
  simpa [sub_eq_zero] using congrFun h x

/-- `prop:valued-amplification`: for a nontrivial valuation `v` and a nonidentity unital field
endomorphism `σ`, the set `{v (σ x - x) : σ x ≠ x}` is coinitial in the value group `v(Kˣ)`:
below the value of every nonzero `c` lies the value of some nonzero displacement. -/
theorem exists_displacement_lt_valuation (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) {σ : K →+* K}
    (hσ : σ ≠ RingHom.id K) {c : K} (hc : c ≠ 0) : ∃ x, σ x ≠ x ∧ v (σ x - x) < v c := by
  obtain ⟨x, hx⟩ := exists_valuation_lt_valuation v hnt (σ := σ) (δ := fun x => σ x - x)
    (isSigmaDerivation_displacement σ).leibniz
    (fun h => hσ (eq_id_of_displacement_eq_zero h)) hc
  refine ⟨x, fun hfix => ?_, hx⟩
  rw [hfix, sub_self, v.map_zero] at hx
  exact not_top_lt hx

/-- `prop:valued-amplification` for a nontrivial surjective valuation, where the value group is
all of `Γ`: for every `γ : Γ` some `x` with `σ x ≠ x` has `v (σ x - x) < γ`. -/
theorem exists_displacement_lt (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) {σ : K →+* K} (hσ : σ ≠ RingHom.id K) (γ : Γ) :
    ∃ x, σ x ≠ x ∧ v (σ x - x) < γ := by
  obtain ⟨c, hc⟩ := hsurj γ
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  rw [← hc]
  exact exists_displacement_lt_valuation v hnt hσ hc0

/-- `cor:detector`: let `v` be a nontrivial surjective valuation on a field of arbitrary
characteristic and `E : (K, +) → (Kˣ, ·)` a group homomorphism such that, for one `β : Γ`,
`E x ∈ 𝒪ᵥˣ` (that is, `v (E x) = 0`) implies `v x ≥ β` (`eq:detector`). Then every unital field
endomorphism `σ` commuting with `E` and with `v (σ y) = v y` for all `y ≠ 0` is the identity.
In characteristic `p > 0` such an `E` is trivial (`E x ^ p = E (p x) = 1`), which contradicts
`eq:detector` for a nontrivial surjective `v`, so the statement is only meaningful in
characteristic `0`. -/
theorem eq_id_of_detector (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) {E : K → K} (hE0 : ∀ x, E x ≠ 0)
    (hE : ∀ x y, E (x + y) = E x * E y) {β : Γ}
    (hdet : ∀ x, v (E x) = 0 → (β : WithTop Γ) ≤ v x) {σ : K →+* K}
    (hcomm : ∀ x, σ (E x) = E (σ x)) (hval : ∀ y, y ≠ 0 → v (σ y) = v y) :
    σ = RingHom.id K := by
  have hbound : ∀ x, (β : WithTop Γ) ≤ v (σ x - x) := by
    intro x
    apply hdet
    have hsplit : E (σ x) = E (σ x - x) * E x := by rw [← hE, sub_add_cancel]
    apply WithTop.add_right_cancel (v.ne_top_iff.2 (hE0 x))
    rw [zero_add, ← v.map_mul, ← hsplit, ← hcomm, hval _ (hE0 x)]
  exact eq_id_of_displacement_eq_zero
    ((isSigmaDerivation_displacement σ).eq_zero v hsurj hnt hbound)

variable {R : Type*} [CommRing R] [Algebra R K]

/-- `thm:derivation-valued`: let `v` be a nontrivial surjective valuation, `E : K → K` any map with
nonzero values and `∂` a derivation with `∂ (E x) = E x ∂ x` for all `x`. If there is a single
`γ : Γ` with `v (∂ y) ≥ v y + γ` for all `y ≠ 0` (`eq:loss-bound`), then `∂ = 0`. -/
theorem derivation_eq_zero_of_loss (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) (D : Derivation R K K) {E : K → K}
    (hE0 : ∀ x, E x ≠ 0) (hcomp : ∀ x, D (E x) = E x * D x) {γ : Γ}
    (hloss : ∀ y, y ≠ 0 → v y + γ ≤ v (D y)) : D = 0 := by
  have hbound : ∀ x, (γ : WithTop Γ) ≤ v (D x) := by
    intro x
    have h := hloss (E x) (hE0 x)
    rw [hcomp, v.map_mul] at h
    exact (WithTop.add_le_add_iff_left (v.ne_top_iff.2 (hE0 x))).1 h
  exact DFunLike.coe_injective
    (((isSigmaDerivation_derivation D).eq_zero v hsurj hnt hbound).trans Derivation.coe_zero.symm)

/-- `thm:derivation-valued`, equivalent form: if `∂ ≠ 0`, then for every `γ : Γ` some `x` has
`v (∂ y) < v y + γ` for `y = E x`, that is `v (∂ y) - v y < γ`. -/
theorem exists_loss_lt (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) (D : Derivation R K K) {E : K → K}
    (hE0 : ∀ x, E x ≠ 0) (hcomp : ∀ x, D (E x) = E x * D x) (hD : D ≠ 0) (γ : Γ) :
    ∃ x, v (D (E x)) < v (E x) + γ := by
  have hD' : (D : K → K) ≠ 0 := fun h =>
    hD (DFunLike.coe_injective (h.trans Derivation.coe_zero.symm))
  obtain ⟨x, hx⟩ := (isSigmaDerivation_derivation D).exists_valuation_lt v hsurj hnt hD' γ
  refine ⟨x, ?_⟩
  rw [hcomp, v.map_mul]
  exact WithTop.add_lt_add_left (v.ne_top_iff.2 (hE0 x)) hx

/-- `cor:no-contraction`: a nonzero derivation `∂` with `∂ (E x) = E x ∂ x` cannot satisfy
`v (∂ y) ≥ v y` for every `y ≠ 0`. -/
theorem not_forall_le (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) (D : Derivation R K K) {E : K → K}
    (hE0 : ∀ x, E x ≠ 0) (hcomp : ∀ x, D (E x) = E x * D x) (hD : D ≠ 0) :
    ¬ ∀ y, y ≠ 0 → v y ≤ v (D y) := fun h =>
  hD (derivation_eq_zero_of_loss v hsurj hnt D hE0 hcomp (γ := 0) fun y hy => by
    rw [WithTop.coe_zero, add_zero]
    exact h y hy)

/-- `cor:no-contraction`: a nonzero derivation `∂` with `∂ (E x) = E x ∂ x` is not globally
contracting, `v (∂ y) > v y` for every `y ≠ 0`. -/
theorem not_forall_lt (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) (D : Derivation R K K) {E : K → K}
    (hE0 : ∀ x, E x ≠ 0) (hcomp : ∀ x, D (E x) = E x * D x) (hD : D ≠ 0) :
    ¬ ∀ y, y ≠ 0 → v y < v (D y) := fun h =>
  not_forall_le v hsurj hnt D hE0 hcomp hD fun y hy => (h y hy).le

/-- For `c ≠ 0`, the rescaled derivation `c ∂` is again nonzero and compatible with `E`. -/
theorem smul_ne_zero_and_comp (D : Derivation R K K) {E : K → K}
    (hcomp : ∀ x, D (E x) = E x * D x) (hD : D ≠ 0) {c : K} (hc : c ≠ 0) :
    c • D ≠ 0 ∧ ∀ x, (c • D) (E x) = E x * (c • D) x := by
  refine ⟨fun h0 => hD ?_, fun x => ?_⟩
  · ext x
    have h := DFunLike.congr_fun h0 x
    rw [Derivation.smul_apply, smul_eq_mul, Derivation.zero_apply, mul_eq_zero] at h
    rw [Derivation.zero_apply]
    exact h.resolve_left hc
  · rw [Derivation.smul_apply, Derivation.smul_apply, hcomp, smul_eq_mul, smul_eq_mul]
    ring

/-- `cor:no-contraction`, rescaled: for every nonzero `c`, the derivation `c ∂` of a nonzero
compatible `∂` cannot satisfy `v (c ∂ y) ≥ v y` for every `y ≠ 0`. -/
theorem not_forall_le_mul (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) (D : Derivation R K K) {E : K → K}
    (hE0 : ∀ x, E x ≠ 0) (hcomp : ∀ x, D (E x) = E x * D x) (hD : D ≠ 0) {c : K}
    (hc : c ≠ 0) : ¬ ∀ y, y ≠ 0 → v y ≤ v (c * D y) := fun h => by
  obtain ⟨hcD, hcomp'⟩ := smul_ne_zero_and_comp D hcomp hD hc
  refine not_forall_le v hsurj hnt (c • D) hE0 hcomp' hcD fun y hy => ?_
  rw [Derivation.smul_apply, smul_eq_mul]
  exact h y hy

/-- `cor:no-contraction`, rescaled: for every nonzero `c`, the derivation `c ∂` of a nonzero
compatible `∂` is not globally contracting, `v (c ∂ y) > v y` for every `y ≠ 0`. -/
theorem not_forall_lt_mul (hsurj : ∀ γ : Γ, ∃ x : K, v x = γ)
    (hnt : ∃ x : K, x ≠ 0 ∧ v x ≠ 0) (D : Derivation R K K) {E : K → K}
    (hE0 : ∀ x, E x ≠ 0) (hcomp : ∀ x, D (E x) = E x * D x) (hD : D ≠ 0) {c : K}
    (hc : c ≠ 0) : ¬ ∀ y, y ≠ 0 → v y < v (c * D y) := fun h =>
  not_forall_le_mul v hsurj hnt D hE0 hcomp hD hc fun y hy => (h y hy).le

end Valuation

end Surreal.SigmaDerivation
