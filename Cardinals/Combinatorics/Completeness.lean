/-
  Completeness of filters (type-level versions).

  * `IsComplete κ F`: `F` is closed under intersections of fewer than `κ` sets.
  * `isComplete_succ_of_isSingular`: the singular endpoint (synthesis Lemma 4.4,
    report R6): a `κ`-complete filter is `κ⁺`-complete when `κ` is singular.
  * `exists_seed`: the seed of the trace of a complete ultrafilter on a small
    family closed under complements (synthesis Lemma 4.3, first half).

  Everything in this file is proved; there are no admitted statements.
-/
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
import Mathlib.Tactic

universe u

namespace Cardinals.Completeness

open Cardinal Set Order

variable {α : Type u}

/-- `F` is `κ`-complete: closed under intersections of fewer than `κ` members. -/
def IsComplete (κ : Cardinal.{u}) (F : Filter α) : Prop :=
  ∀ (ι : Type u) (s : ι → Set α), #ι < κ → (∀ i, s i ∈ F) → (⋂ i, s i) ∈ F

theorem IsComplete.mono {κ μ : Cardinal.{u}} {F : Filter α} (h : IsComplete κ F)
    (hμ : μ ≤ κ) : IsComplete μ F :=
  fun ι s hι hs => h ι s (hι.trans_le hμ) hs

/-- **The singular endpoint.**  If `κ` is singular, every `κ`-complete filter is
`κ⁺`-complete. -/
theorem isComplete_succ_of_isSingular {κ : Cardinal.{u}} (hκ : κ.IsSingular)
    {F : Filter α} (h : IsComplete κ F) : IsComplete (succ κ) F := by
  intro ι s hι hs
  rw [Order.lt_succ_iff] at hι
  rcases hι.lt_or_eq with hlt | heq
  · exact h ι s hlt hs
  -- `#ι = κ`: transport the index set to `κ.ord.ToType`
  have hmk : #ι = #κ.ord.ToType := by rw [heq, mk_ord_toType]
  obtain ⟨g⟩ := Cardinal.eq.1 hmk
  haveI : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder hκ.aleph0_le
  obtain ⟨T, hT, hTcard⟩ := Order.exists_cof_eq (α := κ.ord.ToType)
  have hTlt : #T < κ := by
    rw [hTcard, Ordinal.cof_toType]
    exact hκ.cof_ord_lt
  -- stage one: intersect along each initial segment
  have hstage : ∀ t : T, (⋂ i : {i : ι // g i < t.1}, s i.1) ∈ F := by
    intro t
    apply h
    · have hinj : Function.Injective
          (fun i : {i : ι // g i < t.1} => (⟨g i.1, i.2⟩ : Iio t.1)) := by
        intro a b hab
        have : g a.1 = g b.1 := congrArg Subtype.val hab
        exact Subtype.ext (g.injective this)
      refine lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) ?_
      have := mk_Iio_lt t.1 (by simp)
      rwa [mk_ord_toType] at this
    · exact fun i => hs i.1
  -- stage two: intersect the `#T < κ` many results
  have hfinal : (⋂ t : T, ⋂ i : {i : ι // g i < t.1}, s i.1) ∈ F := by
    have hshrink : #(Shrink.{u} T) < κ := by
      rw [Cardinal.mk_congr (equivShrink T).symm]; exact hTlt
    have := h (Shrink.{u} T)
      (fun t => ⋂ i : {i : ι // g i < ((equivShrink T).symm t).1}, s i.1) hshrink
      (fun t => hstage _)
    refine Filter.mem_of_superset this ?_
    intro x hx
    simp only [mem_iInter] at hx ⊢
    intro t i
    exact hx (equivShrink T t) ⟨i.1, by rw [Equiv.symm_apply_apply]; exact i.2⟩
  refine Filter.mem_of_superset hfinal ?_
  intro x hx
  simp only [mem_iInter] at hx ⊢
  intro i
  obtain ⟨y, hy⟩ := exists_gt (g i)
  obtain ⟨t, htT, hyt⟩ := hT y
  exact hx ⟨t, htT⟩ ⟨i, lt_of_lt_of_le hy hyt⟩

/-- **The seed of a small trace.**  Let `U` be a `κ`-complete ultrafilter and let
`σ` be a family of fewer than `κ` sets that is closed under complements.  Then
there is a point `β` that decides membership in `U` for every member of `σ`. -/
theorem exists_seed {κ : Cardinal.{u}} (U : Ultrafilter α)
    (hU : IsComplete κ (U : Filter α))
    {ι : Type u} (σ : ι → Set α) (hι : #ι < κ)
    (hcompl : ∀ i, ∃ i', σ i' = (σ i)ᶜ) :
    ∃ β : α, ∀ i, σ i ∈ U ↔ β ∈ σ i := by
  classical
  -- intersect all members of the trace
  let J := {i : ι // σ i ∈ U}
  have hJ : #J < κ := lt_of_le_of_lt (Cardinal.mk_subtype_le _) hι
  have hmem : (⋂ i : J, σ i.1) ∈ (U : Filter α) := hU J (fun i => σ i.1) hJ (fun i => i.2)
  obtain ⟨β, hβ⟩ := U.neBot.nonempty_of_mem hmem
  refine ⟨β, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · exact (mem_iInter.mp hβ) ⟨i, hi⟩
  · by_contra hn
    obtain ⟨i', hi'⟩ := hcompl i
    have hc : σ i' ∈ U := by
      rw [hi']; exact Ultrafilter.compl_mem_iff_notMem.mpr hn
    have := (mem_iInter.mp hβ) ⟨i', hc⟩
    rw [hi'] at this
    exact this hi

/-- **Uniqueness inside the hull.**  If every two distinct candidates in a family
`𝒲` of ultrafilters are separated by a member of `σ`, then an ultrafilter of `𝒲`
is determined, among the members of `𝒲`, by its trace on `σ`. -/
theorem unique_of_trace {ι : Type u} (σ : ι → Set α) (𝒲 : Set (Ultrafilter α))
    (hsep : ∀ U ∈ 𝒲, ∀ W ∈ 𝒲, U ≠ W → ∃ i, ¬ (σ i ∈ U ↔ σ i ∈ W))
    (U : Ultrafilter α) (hU : U ∈ 𝒲) (β : α) (hβ : ∀ i, σ i ∈ U ↔ β ∈ σ i)
    (W : Ultrafilter α) (hW : W ∈ 𝒲) (hβW : ∀ i, σ i ∈ W ↔ β ∈ σ i) : W = U := by
  by_contra hne
  obtain ⟨i, hi⟩ := hsep U hU W hW (Ne.symm hne)
  exact hi ((hβ i).trans (hβW i).symm)

end Cardinals.Completeness
