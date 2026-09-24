import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Descending positive profiles and continuum many translation classes

This file proves the ordered-group side of the value-group section of
`docs/surcomplex/nonabelian-support/article.tex`.

* `nab:lem:groups` (and the same lemma `global:lem:descending` of
  `docs/surcomplex/global-divisors/article.tex`): an ordered abelian group has no strictly
  decreasing sequence of positive elements if and only if it is cyclic, i.e. `Γ = 0` or
  `Γ = ℤδ` for a least positive `δ`. It is proved in four equivalent forms:
  `not_exists_isDescendingPositive_iff_isAddCyclic`,
  `not_exists_isDescendingPositive_iff_least_generator` (the printed form, for nonzero `Γ`),
  `not_exists_isDescendingPositive_iff` (the form `Γ = 0` or `Γ = ℤδ`), and
  `not_exists_isDescendingPositive_iff_nonempty_orderAddIso_int` (order-isomorphic to `ℤ`).
* `nab:loc:thm:continuum`, group-theoretic side. For a strictly decreasing `θ` and a binary
  sequence `ε`, the profile `α^ε_n = θ_{2n+ε_n}` (`profile`) is strictly decreasing, positive
  when `θ` is, and distinct binary sequences give distinct profiles. Each class of the
  relation "`β_n - α_n = δ` eventually, for some `δ ∈ Γ`" (`EventualTranslate`) among these
  profiles is countable, and the set of classes has cardinality exactly `𝔠`
  (`mk_quotient_profile`). For every nonzero noncyclic `Γ` (that is, `¬ IsAddCyclic Γ`, the
  trivial group being cyclic) this gives a set of `𝔠` pairwise inequivalent strictly
  decreasing positive profiles (`exists_continuum_pairwise_not_eventualTranslate`), so the
  translation classes of all such profiles number at least `𝔠`.
* `nab:loc:ex:binary`: the rational family `α^ε_n = 1/n + ε_n/(10n(n+1))`, reindexed from
  `n ≥ 1` to `n ≥ 0`, satisfies the printed gap inequality, is strictly decreasing and
  positive, and two members are eventual translates (equivalently, eventually equal) exactly
  when their bit sequences agree eventually.
* `nab:loc:cor:class-enlarge`, ordered-group core: an injective group homomorphism preserves
  and reflects eventual translation and eventual equality of profiles, and an injective
  order-preserving one preserves and reflects strictly decreasing positivity.

Pending: every bundle clause. The passage from profiles to pairwise nonisomorphic rank-`r`
bundles over `MM`, `HH` and `II`, triviality of their determinants, reductions and bounded
restrictions, and the bundle isomorphism criterion in `nab:loc:ex:binary` all rest on
`nab:loc:thm:classification` (sheaves of common-domain Hahn sections and essential
singularities), which is not in the library.
-/

namespace Surreal.DescendingProfiles

open Cardinal Filter Function

universe u

/-! ## Descending positive profiles and the cyclic dichotomy -/

/-- A *descending positive profile*: a strictly decreasing sequence `(α_n)` with `α_n > 0`
for every `n`. -/
def IsDescendingPositive {Γ : Type*} [Preorder Γ] [Zero Γ] (α : ℕ → Γ) : Prop :=
  StrictAnti α ∧ ∀ n, 0 < α n

/-- A strictly decreasing sequence of integers does not stay positive. -/
theorem not_strictAnti_pos_int (K : ℕ → ℤ) (hK : StrictAnti K) : ¬ ∀ n, 0 < K n := by
  intro hpos
  have key : ∀ n : ℕ, K n + n ≤ K 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hK (show n < n + 1 by omega)
      push_cast
      omega
  have h1 := key (K 0).toNat
  have h2 := hpos (K 0).toNat
  have h3 := hpos 0
  omega

section Group

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- The cyclic half of `nab:lem:groups`: a cyclic ordered group has no descending positive
profile. -/
theorem not_exists_isDescendingPositive_of_isAddCyclic [IsAddCyclic Γ] :
    ¬ ∃ θ : ℕ → Γ, IsDescendingPositive θ := by
  rintro ⟨θ, hanti, hpos⟩
  have : Nontrivial Γ := ⟨⟨θ 0, 0, (hpos 0).ne'⟩⟩
  obtain ⟨e⟩ :=
    (LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int (A := Γ)).mp inferInstance
  refine not_strictAnti_pos_int (fun n => e (θ n)) (e.strictMono.comp_strictAnti hanti)
    fun n => ?_
  have := e.strictMono (hpos n)
  rwa [map_zero] at this

omit [IsOrderedAddMonoid Γ] in
/-- Without descending positive profiles, a positive cone that is nonempty has a least
element. -/
theorem exists_least_pos (h : ¬ ∃ θ : ℕ → Γ, IsDescendingPositive θ) {x : Γ} (hx : 0 < x) :
    ∃ δ : Γ, 0 < δ ∧ ∀ g : Γ, 0 < g → δ ≤ g := by
  have hwf : (Set.Ioi (0 : Γ)).IsWF :=
    Set.isWF_iff_no_descending_seq.mpr fun f hf hmem => h ⟨f, hf, hmem⟩
  have hne : (Set.Ioi (0 : Γ)).Nonempty := ⟨x, hx⟩
  exact ⟨hwf.min hne, hwf.min_mem hne, fun g hg => not_lt.mp (hwf.not_lt_min hne hg)⟩

/-- Without descending positive profiles, a least positive element generates the group: for
positive `γ ∉ ℤδ` the elements `γ - nδ` would all be positive and strictly decreasing. -/
theorem mem_zmultiples_of_least (h : ¬ ∃ θ : ℕ → Γ, IsDescendingPositive θ) {δ : Γ}
    (hδ : 0 < δ) (hleast : ∀ g : Γ, 0 < g → δ ≤ g) (γ : Γ) :
    γ ∈ AddSubgroup.zmultiples δ := by
  have hpos : ∀ γ : Γ, 0 < γ → γ ∈ AddSubgroup.zmultiples δ := by
    intro γ hγ
    by_contra hmem
    have key : ∀ n : ℕ, 0 < γ - n • δ := by
      intro n
      induction n with
      | zero => simpa using hγ
      | succ n ih =>
        by_contra hle
        rw [not_lt, succ_nsmul, ← sub_sub, sub_nonpos] at hle
        have heq : γ - n • δ = δ := le_antisymm hle (hleast _ ih)
        apply hmem
        refine AddSubgroup.mem_zmultiples_iff.mpr ⟨((n + 1 : ℕ) : ℤ), ?_⟩
        rw [natCast_zsmul, succ_nsmul, sub_eq_iff_eq_add.mp heq, add_comm]
    refine h ⟨fun n => γ - n • δ, strictAnti_nat_of_succ_lt fun n => ?_, key⟩
    simp only [succ_nsmul, ← sub_sub]
    exact sub_lt_self _ hδ
  rcases lt_trichotomy γ 0 with hγ | rfl | hγ
  · simpa using AddSubgroup.neg_mem _ (hpos (-γ) (neg_pos.mpr hγ))
  · exact AddSubgroup.zero_mem _
  · exact hpos γ hγ

/-- `nab:lem:groups` (equivalently `global:lem:descending`): an ordered abelian group has no
strictly decreasing sequence of positive elements if and only if it is cyclic. -/
theorem not_exists_isDescendingPositive_iff_isAddCyclic :
    (¬ ∃ θ : ℕ → Γ, IsDescendingPositive θ) ↔ IsAddCyclic Γ := by
  refine ⟨fun h => ?_, fun _ => not_exists_isDescendingPositive_of_isAddCyclic⟩
  by_cases hx : ∃ x : Γ, 0 < x
  · obtain ⟨x, hx⟩ := hx
    obtain ⟨δ, hδ, hleast⟩ := exists_least_pos h hx
    exact ⟨⟨δ, fun γ =>
      AddSubgroup.mem_zmultiples_iff.mp (mem_zmultiples_of_least h hδ hleast γ)⟩⟩
  · push Not at hx
    refine ⟨⟨0, fun γ => ⟨0, ?_⟩⟩⟩
    have h1 := hx γ
    have h2 := hx (-γ)
    simp only [zero_smul]
    exact (le_antisymm h1 (neg_nonpos.mp h2)).symm

/-- `nab:lem:groups`, as printed: for a nonzero ordered abelian group `Γ`, the positive cone
contains no infinite strictly decreasing sequence if and only if `Γ = ℤδ` for a least positive
element `δ`. -/
theorem not_exists_isDescendingPositive_iff_least_generator [Nontrivial Γ] :
    (¬ ∃ θ : ℕ → Γ, IsDescendingPositive θ) ↔
      ∃ δ : Γ, 0 < δ ∧ (∀ g : Γ, 0 < g → δ ≤ g) ∧ ∀ g : Γ, g ∈ AddSubgroup.zmultiples δ := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := exists_ne (0 : Γ)
    have hy : ∃ y : Γ, 0 < y := by
      rcases lt_or_gt_of_ne hx with hlt | hlt
      · exact ⟨-x, neg_pos.mpr hlt⟩
      · exact ⟨x, hlt⟩
    obtain ⟨y, hy⟩ := hy
    obtain ⟨δ, hδ, hleast⟩ := exists_least_pos h hy
    exact ⟨δ, hδ, hleast, mem_zmultiples_of_least h hδ hleast⟩
  · rintro ⟨δ, -, -, hgen⟩
    have : IsAddCyclic Γ := ⟨⟨δ, fun g => AddSubgroup.mem_zmultiples_iff.mp (hgen g)⟩⟩
    exact not_exists_isDescendingPositive_of_isAddCyclic

/-- `nab:lem:groups` in the form of `nab:loc:sec:groups`: `Γ` has no strictly decreasing
positive sequence exactly when `Γ = {0}` or `Γ = ℤδ` for a least positive element `δ`. -/
theorem not_exists_isDescendingPositive_iff :
    (¬ ∃ θ : ℕ → Γ, IsDescendingPositive θ) ↔
      (∀ g : Γ, g = 0) ∨
        ∃ δ : Γ, 0 < δ ∧ (∀ g : Γ, 0 < g → δ ≤ g) ∧ ∀ g : Γ, g ∈ AddSubgroup.zmultiples δ := by
  by_cases hΓ : ∀ g : Γ, g = 0
  · refine iff_of_true ?_ (Or.inl hΓ)
    rintro ⟨θ, -, hpos⟩
    exact (hpos 0).ne' (hΓ _)
  · have : Nontrivial Γ := by
      push Not at hΓ
      obtain ⟨g, hg⟩ := hΓ
      exact ⟨⟨g, 0, hg⟩⟩
    rw [not_exists_isDescendingPositive_iff_least_generator]
    exact ⟨Or.inr, fun h => h.resolve_left hΓ⟩

/-- `global:lem:descending`: a nonzero ordered abelian group has no strictly decreasing
positive sequence if and only if it is order-isomorphic to `ℤ`. -/
theorem not_exists_isDescendingPositive_iff_nonempty_orderAddIso_int [Nontrivial Γ] :
    (¬ ∃ θ : ℕ → Γ, IsDescendingPositive θ) ↔ Nonempty (Γ ≃+o ℤ) :=
  not_exists_isDescendingPositive_iff_isAddCyclic.trans
    LinearOrderedAddCommGroup.isAddCyclic_iff_nonempty_equiv_int

/-- `nab:loc:thm:continuum`, first step of the proof (via `nab:lem:groups`), which is also the
step "(i) fails" of `nab:loc:thm:dichotomy`: a noncyclic ordered abelian group (necessarily
nonzero, the trivial group being cyclic) carries a descending positive profile. -/
theorem exists_isDescendingPositive_of_not_isAddCyclic (hΓ : ¬ IsAddCyclic Γ) :
    ∃ θ : ℕ → Γ, IsDescendingPositive θ := by
  by_contra h
  exact hΓ (not_exists_isDescendingPositive_iff_isAddCyclic.mp h)

end Group

/-! ## Eventual translation of profiles -/

section Translation

variable {G : Type*} [AddGroup G]

/-- Two profiles are *eventual translates* when `β_n - α_n = δ` eventually, for some
`δ ∈ G`: the localized classification relation on the right of `nab:loc:eq:full-class` and
`nab:loc:eq:mer-class` in `nab:loc:thm:classification`. -/
def EventualTranslate (α β : ℕ → G) : Prop :=
  ∃ δ : G, ∀ᶠ n in atTop, β n - α n = δ

theorem EventualTranslate.refl (α : ℕ → G) : EventualTranslate α α :=
  ⟨0, Eventually.of_forall fun n => sub_self (α n)⟩

theorem EventualTranslate.symm {α β : ℕ → G} (h : EventualTranslate α β) :
    EventualTranslate β α := by
  obtain ⟨δ, hδ⟩ := h
  exact ⟨-δ, hδ.mono fun n hn => by rw [← hn, neg_sub]⟩

theorem EventualTranslate.trans {α β γ : ℕ → G} (h₁ : EventualTranslate α β)
    (h₂ : EventualTranslate β γ) : EventualTranslate α γ := by
  obtain ⟨δ₁, h₁⟩ := h₁
  obtain ⟨δ₂, h₂⟩ := h₂
  exact ⟨δ₂ + δ₁, (h₁.and h₂).mono fun n hn => by rw [← hn.1, ← hn.2, sub_add_sub_cancel]⟩

variable (G) in
/-- Eventual translation as an equivalence relation on profiles. -/
def translateSetoid : Setoid (ℕ → G) where
  r := EventualTranslate
  iseqv := ⟨EventualTranslate.refl, EventualTranslate.symm, EventualTranslate.trans⟩

theorem translateSetoid_iff {α β : ℕ → G} : translateSetoid G α β ↔ EventualTranslate α β :=
  Iff.rfl

end Translation

/-! ## The binary profiles `α^ε_n = θ_{2n+ε_n}` -/

section BinaryProfiles

variable {Γ : Type*}

/-- The profile `α^ε_n = θ_{2n+ε_n}` of `nab:loc:thm:continuum`, with the bit `ε_n` read as
`0` or `1`. -/
def profile (θ : ℕ → Γ) (ε : ℕ → Bool) (n : ℕ) : Γ :=
  θ (2 * n + (ε n).toNat)

/-- `nab:loc:thm:continuum`: every profile `α^ε` is strictly decreasing, since
`2n + ε_n < 2(n+1) + ε_{n+1}`. -/
theorem profile_strictAnti [Preorder Γ] {θ : ℕ → Γ} (hθ : StrictAnti θ) (ε : ℕ → Bool) :
    StrictAnti (profile θ ε) :=
  strictAnti_nat_of_succ_lt fun n => hθ (by have := Bool.toNat_le (ε n); omega)

/-- `nab:loc:thm:continuum`: for a descending positive `θ`, every `α^ε` is a descending
positive profile. -/
theorem profile_isDescendingPositive [Preorder Γ] [Zero Γ] {θ : ℕ → Γ}
    (hθ : IsDescendingPositive θ) (ε : ℕ → Bool) : IsDescendingPositive (profile θ ε) :=
  ⟨profile_strictAnti hθ.1 ε, fun _ => hθ.2 _⟩

/-- `nab:loc:thm:continuum`: distinct binary sequences give distinct profiles. -/
theorem profile_injective {θ : ℕ → Γ} (hθ : Injective θ) : Injective (profile θ) := by
  intro ε η h
  funext n
  have h1 : 2 * n + (ε n).toNat = 2 * n + (η n).toNat := hθ (congrFun h n)
  have h2 : (ε n).toNat = (η n).toNat := by omega
  revert h2
  cases ε n <;> cases η n <;> simp

/-- `nab:loc:thm:continuum`: each eventual-translation class among the profiles `α^ε` is
countable. The translation lies in the countable set `{θ_j - θ_k}`, and for one translation and
one starting index the tail of the second profile is determined, `θ` being injective. -/
theorem countable_setOf_eventualTranslate_profile [AddGroup Γ] {θ : ℕ → Γ} (hθ : Injective θ)
    (ε : ℕ → Bool) :
    {η : ℕ → Bool | EventualTranslate (profile θ ε) (profile θ η)}.Countable := by
  have hsub : {η : ℕ → Bool | EventualTranslate (profile θ ε) (profile θ η)} ⊆
      ⋃ p : ℕ × ℕ × ℕ, {η : ℕ → Bool | ∀ n, p.2.2 ≤ n →
        profile θ η n - profile θ ε n = θ p.1 - θ p.2.1} := by
    rintro η ⟨δ, hδ⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp hδ
    refine Set.mem_iUnion.mpr ⟨(2 * N + (η N).toNat, 2 * N + (ε N).toNat, N), fun n hn => ?_⟩
    exact (hN n hn).trans (hN N le_rfl).symm
  refine Set.Countable.mono hsub (Set.countable_iUnion fun p => ?_)
  refine Set.MapsTo.countable_of_injOn (f := fun (η : ℕ → Bool) (i : Fin p.2.2) => η i)
    (Set.mapsTo_univ _ _) ?_ Set.countable_univ
  intro η hη η' hη' heq
  funext n
  by_cases hn : n < p.2.2
  · exact congrFun heq ⟨n, hn⟩
  · have h1 : profile θ η n = profile θ η' n :=
      sub_left_inj.mp ((hη n (not_lt.mp hn)).trans (hη' n (not_lt.mp hn)).symm)
    have h2 : 2 * n + (η n).toNat = 2 * n + (η' n).toNat := hθ h1
    have h3 : (η n).toNat = (η' n).toNat := by omega
    revert h3
    cases η n <;> cases η' n <;> simp

end BinaryProfiles

/-! ## Cardinal arithmetic -/

/-- A partition of a set of cardinality `𝔠` into countable classes has exactly `𝔠`
classes. -/
theorem mk_quotient_eq_continuum {α : Type u} (s : Setoid α) (hα : #α = 𝔠)
    (hs : ∀ a : α, {b : α | s a b}.Countable) : #(Quotient s) = 𝔠 := by
  refine le_antisymm (mk_quotient_le.trans hα.le) ?_
  have h1 : #α ≤ #(Quotient s) * ℵ₀ := by
    refine mk_le_mk_mul_of_mk_preimage_le (Quotient.mk s) fun q => ?_
    obtain ⟨a, rfl⟩ := Quotient.mk_surjective q
    have : Quotient.mk s ⁻¹' {Quotient.mk s a} = {b : α | s a b} := by
      ext b
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Set.mem_setOf_eq]
      exact ⟨fun h => s.iseqv.symm h, fun h => s.iseqv.symm h⟩
    rw [this]
    exact le_aleph0_iff_set_countable.mpr (hs a)
  have h2 := h1.trans (mul_le_max _ _)
  rw [hα] at h2
  rcases le_max_iff.mp h2 with h | h
  · rcases le_max_iff.mp h with h | h
    · exact h
    · exact absurd h (not_le.mpr aleph0_lt_continuum)
  · exact absurd h (not_le.mpr aleph0_lt_continuum)

/-- `nab:loc:thm:continuum`: the profiles `α^ε` fall into exactly `𝔠` eventual-translation
classes. -/
theorem mk_quotient_profile {Γ : Type*} [AddGroup Γ] {θ : ℕ → Γ} (hθ : Injective θ) :
    #(Quotient ((translateSetoid Γ).comap (profile θ))) = 𝔠 := by
  refine mk_quotient_eq_continuum _ ?_ fun ε => countable_setOf_eventualTranslate_profile hθ ε
  rw [← power_def, mk_bool, mk_nat, two_power_aleph0]

section Continuum

variable {Γ : Type u} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]

/-- `nab:loc:thm:continuum`, group-theoretic side: in a nonzero noncyclic ordered abelian
group there is an injective family `ε ↦ α^ε` of descending positive profiles, indexed by
binary sequences, whose eventual-translation classes are countable and number exactly `𝔠`. -/
theorem exists_profiles_continuum_classes (hΓ : ¬ IsAddCyclic Γ) :
    ∃ α : (ℕ → Bool) → ℕ → Γ, (∀ ε, IsDescendingPositive (α ε)) ∧ Injective α ∧
      (∀ ε, {η | EventualTranslate (α ε) (α η)}.Countable) ∧
      #(Quotient ((translateSetoid Γ).comap α)) = 𝔠 := by
  obtain ⟨θ, hθ⟩ := exists_isDescendingPositive_of_not_isAddCyclic hΓ
  exact ⟨profile θ, profile_isDescendingPositive hθ, profile_injective hθ.1.injective,
    countable_setOf_eventualTranslate_profile hθ.1.injective,
    mk_quotient_profile hθ.1.injective⟩

/-- `nab:loc:thm:continuum`, group-theoretic side: a nonzero noncyclic ordered abelian group
has `2^ℵ₀` pairwise inequivalent descending positive profiles. -/
theorem exists_continuum_pairwise_not_eventualTranslate (hΓ : ¬ IsAddCyclic Γ) :
    ∃ P : Set (ℕ → Γ), #P = 𝔠 ∧ (∀ α ∈ P, IsDescendingPositive α) ∧
      P.Pairwise fun α β => ¬ EventualTranslate α β := by
  obtain ⟨α, hα, hinj, -, hcard⟩ := exists_profiles_continuum_classes hΓ
  let r : Quotient ((translateSetoid Γ).comap α) → ℕ → Γ := fun q => α q.out
  have hr : Injective r := fun q q' h => by
    rw [← Quotient.out_eq q, ← Quotient.out_eq q', hinj h]
  refine ⟨Set.range r, ?_, ?_, ?_⟩
  · have := mk_range_eq_of_injective hr
    rwa [hcard, lift_continuum, lift_uzero] at this
  · rintro _ ⟨q, rfl⟩
    exact hα _
  · rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ hne htr
    apply hne
    have : Quotient.mk ((translateSetoid Γ).comap α) q.out =
        Quotient.mk ((translateSetoid Γ).comap α) q'.out := Quotient.sound htr
    rw [Quotient.out_eq, Quotient.out_eq] at this
    rw [this]

/-- `nab:loc:thm:continuum`, group-theoretic side: in a nonzero noncyclic ordered abelian
group the descending positive profiles fall into at least `𝔠` eventual-translation
classes. -/
theorem continuum_le_mk_quotient_isDescendingPositive (hΓ : ¬ IsAddCyclic Γ) :
    𝔠 ≤ #(Quotient ((translateSetoid Γ).comap
      (Subtype.val : {α : ℕ → Γ // IsDescendingPositive α} → ℕ → Γ))) := by
  obtain ⟨P, hcard, hpos, hpair⟩ := exists_continuum_pairwise_not_eventualTranslate hΓ
  rw [← hcard]
  refine mk_le_of_injective (f := fun p : P => Quotient.mk _ ⟨p.1, hpos p.1 p.2⟩) ?_
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  by_contra hne
  exact hpair hp hp' (fun e => hne (Subtype.ext e)) (Quotient.exact h)

end Continuum

/-! ## Group enlargement -/

section Enlarge

variable {G G' : Type*} [AddGroup G] [AddGroup G']

/-- `nab:loc:cor:class-enlarge`, ordered-group core: an injective homomorphism `Γ → Γ'`
preserves and reflects eventual translation of profiles. -/
theorem eventualTranslate_comp_iff (f : G →+ G') (hf : Injective f) (α β : ℕ → G) :
    EventualTranslate (f ∘ α) (f ∘ β) ↔ EventualTranslate α β := by
  constructor
  · rintro ⟨δ', h⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    refine ⟨β N - α N, eventually_atTop.mpr ⟨N, fun n hn => hf ?_⟩⟩
    rw [map_sub, map_sub]
    exact (hN n hn).trans (hN N le_rfl).symm
  · rintro ⟨δ, h⟩
    exact ⟨f δ, h.mono fun n hn => by rw [comp_apply, comp_apply, ← map_sub, hn]⟩

/-- `nab:loc:cor:class-enlarge`, integral clause: an injective homomorphism preserves and
reflects eventual equality of profiles. -/
theorem eventually_comp_eq_iff (f : G →+ G') (hf : Injective f) (α β : ℕ → G) :
    (∀ᶠ n in atTop, f (β n) = f (α n)) ↔ ∀ᶠ n in atTop, β n = α n := by
  simp only [hf.eq_iff]

/-- `nab:loc:cor:class-enlarge`: an injective order-preserving homomorphism preserves and
reflects descending positive profiles. -/
theorem isDescendingPositive_comp_iff [LinearOrder G] [PartialOrder G'] (f : G →+ G')
    (hmono : Monotone f) (hf : Injective f) (α : ℕ → G) :
    IsDescendingPositive (f ∘ α) ↔ IsDescendingPositive α := by
  have hs : StrictMono f := hmono.strictMono_of_injective hf
  have hpos : ∀ n, 0 < f (α n) ↔ 0 < α n := fun n => by
    rw [← map_zero f]
    exact hs.lt_iff_lt
  refine ⟨fun h => ⟨fun a b hab => hs.lt_iff_lt.mp (h.1 hab), fun n => (hpos n).mp (h.2 n)⟩,
    fun h => ⟨hs.comp_strictAnti h.1, fun n => (hpos n).mpr (h.2 n)⟩⟩

end Enlarge

/-! ## The rational binary family -/

section Rational

/-- The weight `1/(10(n+1)(n+2))` of the bit in `binaryProfile`. -/
def binaryWeight (n : ℕ) : ℚ :=
  1 / (10 * ((n : ℚ) + 1) * ((n : ℚ) + 2))

/-- `nab:loc:ex:binary`: the rational profile `α^ε_n = 1/n + ε_n/(10n(n+1))`, reindexed so
that the source index `n ≥ 1` becomes `n + 1` with `n ≥ 0`. -/
def binaryProfile (ε : ℕ → Bool) (n : ℕ) : ℚ :=
  1 / ((n : ℚ) + 1) + ((ε n).toNat : ℚ) / (10 * ((n : ℚ) + 1) * ((n : ℚ) + 2))

theorem binaryWeight_pos (n : ℕ) : 0 < binaryWeight n := by
  unfold binaryWeight
  positivity

theorem binaryWeight_succ_lt (n : ℕ) : binaryWeight (n + 1) < binaryWeight n := by
  unfold binaryWeight
  apply one_div_lt_one_div_of_lt (by positivity)
  rw [Nat.cast_add_one]
  nlinarith [(Nat.cast_nonneg n : (0 : ℚ) ≤ n)]

theorem binaryProfile_pos (ε : ℕ → Bool) (n : ℕ) : 0 < binaryProfile ε n := by
  unfold binaryProfile
  positivity

theorem binaryProfile_sub (ε η : ℕ → Bool) (n : ℕ) :
    binaryProfile η n - binaryProfile ε n =
      (((η n).toNat : ℚ) - (ε n).toNat) * binaryWeight n := by
  unfold binaryProfile binaryWeight
  ring

theorem binaryProfile_sub_eq_zero {ε η : ℕ → Bool} {n : ℕ} (h : ε n = η n) :
    binaryProfile η n - binaryProfile ε n = 0 := by
  rw [binaryProfile_sub, h, sub_self, zero_mul]

theorem abs_binaryProfile_sub_of_ne {ε η : ℕ → Bool} {n : ℕ} (h : ε n ≠ η n) :
    |binaryProfile η n - binaryProfile ε n| = binaryWeight n := by
  rw [binaryProfile_sub, abs_mul, abs_of_pos (binaryWeight_pos n)]
  have : |((η n).toNat : ℚ) - (ε n).toNat| = 1 := by
    revert h
    cases ε n <;> cases η n <;> simp
  rw [this, one_mul]

/-- `nab:loc:ex:binary`, the printed gap inequality (reindexed):
`α^ε_n - α^ε_{n+1} ≥ 1/((n+1)(n+2)) - 1/(10(n+2)(n+3))` for every choice of bits. -/
theorem binaryProfile_sub_succ_ge (ε : ℕ → Bool) (n : ℕ) :
    1 / (((n : ℚ) + 1) * ((n : ℚ) + 2)) - 1 / (10 * ((n : ℚ) + 2) * ((n : ℚ) + 3)) ≤
      binaryProfile ε n - binaryProfile ε (n + 1) := by
  have hb : ((ε (n + 1)).toNat : ℚ) ≤ 1 := by exact_mod_cast Bool.toNat_le _
  have hx : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  unfold binaryProfile
  rw [Nat.cast_add_one]
  have e1 : ((n : ℚ) + 1 + 1) = (n : ℚ) + 2 := by ring
  have e2 : ((n : ℚ) + 1 + 2) = (n : ℚ) + 3 := by ring
  rw [e1, e2]
  have h1 : 0 ≤ ((ε n).toNat : ℚ) / (10 * ((n : ℚ) + 1) * ((n : ℚ) + 2)) := by positivity
  have h2 : ((ε (n + 1)).toNat : ℚ) / (10 * ((n : ℚ) + 2) * ((n : ℚ) + 3)) ≤
      1 / (10 * ((n : ℚ) + 2) * ((n : ℚ) + 3)) :=
    div_le_div_of_nonneg_right hb (by positivity)
  have h3 : 1 / ((n : ℚ) + 1) - 1 / ((n : ℚ) + 2) = 1 / (((n : ℚ) + 1) * ((n : ℚ) + 2)) := by
    rw [div_sub_div _ _ (by positivity) (by positivity)]
    ring
  linarith

/-- `nab:loc:ex:binary`: the lower bound of the gap inequality is positive. -/
theorem binaryGap_pos (n : ℕ) :
    0 < 1 / (((n : ℚ) + 1) * ((n : ℚ) + 2)) - 1 / (10 * ((n : ℚ) + 2) * ((n : ℚ) + 3)) := by
  have hx : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  rw [sub_pos]
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith [sq_nonneg (n : ℚ)]

/-- `nab:loc:ex:binary`: every binary profile is strictly decreasing. -/
theorem binaryProfile_strictAnti (ε : ℕ → Bool) : StrictAnti (binaryProfile ε) :=
  strictAnti_nat_of_succ_lt fun n => by
    have := binaryProfile_sub_succ_ge ε n
    have := binaryGap_pos n
    linarith

/-- `nab:loc:ex:binary`: every binary profile is a descending positive profile in `ℚ`. -/
theorem binaryProfile_isDescendingPositive (ε : ℕ → Bool) :
    IsDescendingPositive (binaryProfile ε) :=
  ⟨binaryProfile_strictAnti ε, binaryProfile_pos ε⟩

/-- `nab:loc:ex:binary`: two binary profiles are eventual translates if and only if their bits
agree eventually. A nonzero constant difference is impossible, because a nonzero difference at
index `n` has absolute value `1/(10(n+1)(n+2))`, which is strictly decreasing in `n`. -/
theorem binaryProfile_eventualTranslate_iff (ε η : ℕ → Bool) :
    EventualTranslate (binaryProfile ε) (binaryProfile η) ↔ ∀ᶠ n in atTop, ε n = η n := by
  constructor
  · rintro ⟨δ, h⟩
    obtain ⟨N, hN⟩ := eventually_atTop.mp h
    refine eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    by_contra hne
    have hd : binaryProfile η (n + 1) - binaryProfile ε (n + 1) =
        binaryProfile η n - binaryProfile ε n := (hN (n + 1) (by omega)).trans (hN n hn).symm
    have h1 := abs_binaryProfile_sub_of_ne hne
    have hne' : ε (n + 1) ≠ η (n + 1) := by
      intro heq
      have h0 := binaryProfile_sub_eq_zero heq
      rw [hd] at h0
      rw [h0, abs_zero] at h1
      exact (binaryWeight_pos n).ne h1
    have h2 := abs_binaryProfile_sub_of_ne hne'
    rw [hd, h1] at h2
    exact (binaryWeight_succ_lt n).ne' h2
  · intro h
    exact ⟨0, h.mono fun n hn => binaryProfile_sub_eq_zero hn⟩

/-- `nab:loc:ex:binary`, integral clause: two binary profiles are eventually equal if and only
if their bits agree eventually. -/
theorem binaryProfile_eventuallyEq_iff (ε η : ℕ → Bool) :
    (∀ᶠ n in atTop, binaryProfile η n = binaryProfile ε n) ↔ ∀ᶠ n in atTop, ε n = η n := by
  constructor
  · intro h
    refine h.mono fun n hn => ?_
    by_contra hne
    have h1 := abs_binaryProfile_sub_of_ne hne
    rw [hn, sub_self, abs_zero] at h1
    exact (binaryWeight_pos n).ne h1
  · intro h
    exact h.mono fun n hn => sub_eq_zero.mp (binaryProfile_sub_eq_zero hn)

end Rational

end Surreal.DescendingProfiles
