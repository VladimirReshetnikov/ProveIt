/-
  THE SINGULAR ENDPOINT (synthesis Lemma 4.4, Theorem 5.1 at `q(γ)`, Theorem 6.4).

  * `IsCompleteUF.succ_of_isSingular`: at a singular `γ`, `γ`-complete ultrafilters on
    ordinals are `γ⁺`-complete; hence `CD γ = CD γ⁺` and `HCD γ = HCD γ⁺`.
  * `barrier_singular`, `regular_in_HCD_self`: a `c`-cover-exacting `c.ord` is regular
    in `HCD(c)` itself.
  * `first_regularization`: if moreover `c` is a limit of strongly compact cardinals,
    `c` is exactly the first level of the hierarchy at which `c.ord` is regular.

  No statement is admitted in this file.
-/
import Cardinals.Above

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal Set

/-- **The singular endpoint for ultrafilters on ordinals.** -/
theorem IsCompleteUF.succ_of_isSingular {γ : Cardinal.{u}} (hγ : γ.IsSingular)
    {U : ZFSet.{u}} (hU : IsCompleteUF γ U) : IsCompleteUF (Order.succ γ) U := by
  obtain ⟨τ, hτ, hc⟩ := hU
  refine ⟨τ, hτ, ?_⟩
  intro S hSU hSne hScard
  rw [Order.lt_succ_iff] at hScard
  rcases hScard.lt_or_eq with hlt | heq
  · exact hc S hSU hSne hlt
  -- index `S` by the type `γ.ord.ToType`
  let ι := Shrink.{u} {x // x ∈ S}
  let e : ι → ZFSet.{u} := fun i => ((equivShrink {x // x ∈ S}).symm i).1
  have he : ∀ i, e i ∈ S := fun i => ((equivShrink {x // x ∈ S}).symm i).2
  have hsurj : ∀ z ∈ S, ∃ i, e i = z := fun z hz =>
    ⟨equivShrink _ ⟨z, hz⟩, by simp [e]⟩
  have hmk : #ι = #γ.ord.ToType := by
    rw [mk_ord_toType, ← heq]; rfl
  obtain ⟨g⟩ := Cardinal.eq.1 hmk
  haveI : NoMaxOrder γ.ord.ToType := Cardinal.noMaxOrder hγ.aleph0_le
  obtain ⟨T, hT, hTcard⟩ := Order.exists_cof_eq (α := γ.ord.ToType)
  have hTlt : #T < γ := by
    rw [hTcard, Ordinal.cof_toType]; exact hγ.cof_ord_lt
  -- the pieces
  let St : γ.ord.ToType → ZFSet.{u} := fun t =>
    ZFSet.range (fun i : {i : ι // g i < t} => e i.1)
  have hSt_sub : ∀ t, St t ⊆ S := by
    intro t z hz
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.mp hz
    exact he i.1
  have hSt_card : ∀ t, ZFSet.card (St t) < γ := by
    intro t
    have h1 : ZFSet.card (St t) ≤ #{i : ι // g i < t} := by
      have := ZFSet.lift_card_range_le (f := fun i : {i : ι // g i < t} => e i.1)
      simpa using this
    have hinj : Function.Injective
        (fun i : {i : ι // g i < t} => (⟨g i.1, i.2⟩ : Iio t)) := by
      intro a b hab
      have : g a.1 = g b.1 := congrArg Subtype.val hab
      exact Subtype.ext (g.injective this)
    have h2 : #{i : ι // g i < t} < γ := by
      refine lt_of_le_of_lt (Cardinal.mk_le_of_injective hinj) ?_
      have := mk_Iio_lt t (by simp)
      rwa [mk_ord_toType] at this
    exact lt_of_le_of_lt h1 h2
  -- every element of `S` lies in some piece indexed by `T`
  have hcover : ∀ z ∈ S, ∃ t ∈ T, z ∈ St t := by
    intro z hz
    obtain ⟨i, rfl⟩ := hsurj z hz
    obtain ⟨y, hy⟩ := exists_gt (g i)
    obtain ⟨t, htT, hyt⟩ := hT y
    exact ⟨t, htT, ZFSet.mem_range.mpr ⟨⟨i, lt_of_lt_of_le hy hyt⟩, rfl⟩⟩
  -- stage one
  have hstage : ∀ t, (St t).Nonempty → ⋂₀ (St t) ∈ U := fun t hne =>
    hc (St t) (fun z hz => hSU (hSt_sub t hz)) hne (hSt_card t)
  -- stage two
  let T' := {t : T // (St t.1).Nonempty}
  let D : ZFSet.{u} := ZFSet.range (fun t : T' => ⋂₀ (St t.1.1))
  have hDU : D ⊆ U := by
    intro z hz
    obtain ⟨t, rfl⟩ := ZFSet.mem_range.mp hz
    exact hstage t.1.1 t.2
  have hDne : D.Nonempty := by
    obtain ⟨z, hz⟩ := hSne
    obtain ⟨t, htT, hzt⟩ := hcover z hz
    exact ⟨_, ZFSet.mem_range.mpr ⟨⟨⟨t, htT⟩, ⟨z, hzt⟩⟩, rfl⟩⟩
  have hDcard : ZFSet.card D < γ := by
    have h1 : ZFSet.card D ≤ #T' := by
      have := ZFSet.lift_card_range_le (f := fun t : T' => ⋂₀ (St t.1.1))
      simpa using this
    exact lt_of_le_of_lt (h1.trans (Cardinal.mk_subtype_le _)) hTlt
  have hID : ⋂₀ D ∈ U := hc D hDU hDne hDcard
  -- `⋂₀ D ⊆ ⋂₀ S ⊆ τ`
  have hsubset : ⋂₀ D ⊆ ⋂₀ S := by
    intro x hx
    rw [ZFSet.mem_sInter hSne]
    intro z hz
    obtain ⟨t, htT, hzt⟩ := hcover z hz
    have hmemD : ⋂₀ (St t) ∈ D := ZFSet.mem_range.mpr ⟨⟨⟨t, htT⟩, ⟨z, hzt⟩⟩, rfl⟩
    exact ZFSet.mem_of_mem_sInter (ZFSet.mem_of_mem_sInter hx hmemD) hzt
  have hSτ : ⋂₀ S ⊆ ordZ τ := by
    obtain ⟨z, hz⟩ := hSne
    intro x hx
    exact (mem_powerset.mp (hτ.sub (hSU hz))) (ZFSet.mem_of_mem_sInter hx hz)
  exact hτ.upward _ hID _ hSτ hsubset

/-- At a singular `γ` the classes `CD γ` and `CD γ⁺` coincide. -/
theorem CD_succ_of_isSingular {γ : Cardinal.{u}} (hγ : γ.IsSingular) {x : ZFSet.{u}}
    (hx : CD γ x) : CD (Order.succ γ) x :=
  ODfrom.mono (fun _ hp => hp.succ_of_isSingular hγ) hx

theorem HCD_succ_of_isSingular {γ : Cardinal.{u}} (hγ : γ.IsSingular) {x : ZFSet.{u}}
    (hx : HCD γ x) : HCD (Order.succ γ) x := by
  obtain ⟨t, ht, hxt, hall⟩ := hx
  exact ⟨t, ht, hxt, fun y hy => CD_succ_of_isSingular hγ (hall y hy)⟩

/-- **The barrier at the singular endpoint (synthesis Theorem 5.1 with `q(γ) = γ`).** -/
theorem barrier_singular (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord)
    (hγ : γ.IsSingular) (a : ZFSet.{u}) (ha : ShortCofinal a c.ord) : ¬ CD γ a :=
  fun hcd => barrier c γ hc h a ha (CD_succ_of_isSingular hγ hcd)

/-- A cardinal of countable cofinality above `ℵ₀` is singular. -/
theorem isSingular_of_cofinal_seq (c : Cardinal.{u}) (hc : ℵ₀ < c)
    (s : ℕ → Ordinal.{u}) (hs : StrictMono s) (hlt : ∀ n, s n < c.ord)
    (hcof : ∀ ξ < c.ord, ∃ n, ξ ≤ s n) : c.IsSingular := by
  refine ⟨hc.le, fun heq => ?_⟩
  have hN : #(ULift.{u} ℕ) < c.ord.cof := by rw [heq]; simpa using hc
  have hsup := Ordinal.iSup_lt_of_lt_cof (f := fun n : ULift.{u} ℕ => s n.down) hN
    (fun n => hlt n.down)
  obtain ⟨n, hn⟩ := hcof _ hsup
  have h1 : s (n + 1) ≤ ⨆ i : ULift.{u} ℕ, s i.down :=
    Ordinal.le_iSup (fun i : ULift.{u} ℕ => s i.down) ⟨n + 1⟩
  exact absurd (lt_of_le_of_lt (h1.trans hn) (hs (Nat.lt_succ_self n))) (lt_irrefl _)

/-- A cover-exacting cardinal is singular. -/
theorem isSingular_of_CEx (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) :
    c.IsSingular := by
  obtain ⟨s, hs, hlt, hcof⟩ := cof_omega c γ hc h
  exact isSingular_of_cofinal_seq c (aleph0_lt_of_CEx c γ hc h) s hs hlt hcof

/-- **`CEx_λ(λ)` implies that `λ` is regular in `HCD(λ)`** (synthesis Theorem 5.1,
last sentence; report R6). -/
theorem regular_in_HCD_self (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx c c.ord) :
    RegularIn (HCD c) c.ord :=
  fun a haN ha => barrier_singular c c hc h (isSingular_of_CEx c c hc h) a ha haN.cd

/-- **First regularization (synthesis Theorem 6.4).**  If `c.ord` is `c`-cover exacting
and `c` is a limit of strongly compact cardinals, then `c.ord` is singular in every
`HCD(ρ)` with `ρ < c` and regular in `HCD(c)`: the first regular level is exactly `c`. -/
theorem first_regularization (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx c c.ord)
    (hlim : ∀ ρ < c, ∃ δ, ρ ≤ δ ∧ δ < c ∧ SC δ) :
    RegularIn (HCD c) c.ord ∧ ∀ ρ < c, ¬ RegularIn (HCD ρ) c.ord := by
  refine ⟨regular_in_HCD_self c hc h, fun ρ hρ => ?_⟩
  obtain ⟨δ, hρδ, hδc, hδ⟩ := hlim ρ hρ
  exact not_RegularIn_HCD_of_le δ c c ρ hc hδ hδc h hρδ

end Cardinals
