/-
  EXACTING CARDINALS: DEFINABLE FAMILIES OF COFINAL MAPS (synthesis §8, report R9).

  The only large-cardinal input is the admitted theorem of Aguilera–Bagaria–Lücke that
  an exacting `lam` is regular in `HOD_{V_lam}`, used in its set form
  (`Published.no_short_cofinal_OD`).

  * `proj_OD`, `sups_OD`: the coordinate projections `P_ξ` of a family `F` of maps, and
    the set `{⋃ P_ξ : ξ < μ}` of their suprema, are ordinal definable from `F`
    (explicit formulas, satisfaction computed in a limit rank).
  * `projection_width` (Theorem 8.1): some projection of an `OD_{V_lam}` family of
    cofinal maps `μ → lam`, `μ < lam`, is cofinal in `lam` and has cardinality `|lam|`;
    hence `|F| ≥ |lam|` (Corollary 8.2).
-/
import Cardinals.Foundations.PairForm
import Cardinals.Endpoint

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

namespace Published

/-- An exacting cardinal `lam` is regular in `HOD_{V_lam}`; in set form: no short
cofinal subset of `lam` is ordinal definable from parameters in `V_lam`.
([ABL, Theorem 2.10].) -/
theorem no_short_cofinal_OD (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : Ex c.ord)
    (a : ZFSet.{u}) (ha : ODfrom (fun p => p ∈ V_ c.ord) a) : ¬ ShortCofinal a c.ord := by
  admit

end Published

/-! ### Families of maps and their projections -/

/-- The `ξ`-th coordinate projection `P_ξ = {f(ξ) : f ∈ F}` (as a subset of `lam`). -/
noncomputable def proj (F : ZFSet.{u}) (lam ξ : Ordinal.{u}) : ZFSet.{u} :=
  (ordZ lam).sep (fun w => ∃ f ∈ F, pair (ordZ ξ) w ∈ f)

theorem mem_proj {F : ZFSet.{u}} {lam ξ : Ordinal.{u}} {w : ZFSet.{u}} :
    w ∈ proj F lam ξ ↔ w ∈ ordZ lam ∧ ∃ f ∈ F, pair (ordZ ξ) w ∈ f := mem_sep

/-- The set of suprema `{⋃ P_ξ : ξ < μ}`. -/
noncomputable def sups (F : ZFSet.{u}) (lam μ : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.range (fun ξ : Set.Iio μ => (⋃₀ (proj F lam ξ.1) : ZFSet.{u}))

theorem mem_sups {F : ZFSet.{u}} {lam μ : Ordinal.{u}} {z : ZFSet.{u}} :
    z ∈ sups F lam μ ↔ ∃ ξ < μ, z = ⋃₀ (proj F lam ξ) := by
  unfold sups
  rw [ZFSet.mem_range]
  exact ⟨fun ⟨ξ, h⟩ => ⟨ξ.1, ξ.2, h.symm⟩, fun ⟨ξ, hξ, h⟩ => ⟨⟨ξ, hξ⟩, h.symm⟩⟩

/-- The defining formula of `P_ξ`: `∀ w (w ∈ y ↔ ∃ f (f ∈ F ∧ ⟨ξ, w⟩ ∈ f))`,
with `y = v₀`, `F = v₁`, `ξ = v₂`. -/
def projForm : Form :=
  fAll (SetTheory.fIff (fMem 0 1) (fEx (fAnd (fMem 0 3) (pairMemF 4 1 0))))

/-- The defining formula of `{⋃ P_ξ : ξ < μ}`, with `y = v₀`, `F = v₁`, `μ = v₂`:
`∀ z (z ∈ y ↔ ∃ ξ (ξ ∈ μ ∧ ∀ v (v ∈ z ↔ ∃ w (v ∈ w ∧ ∃ f (f ∈ F ∧ ⟨ξ, w⟩ ∈ f)))))`. -/
def supsForm : Form :=
  fAll (SetTheory.fIff (fMem 0 1)
    (fEx (fAnd (fMem 0 4)
      (fAll (SetTheory.fIff (fMem 0 2)
        (fEx (fAnd (fMem 1 0) (fEx (fAnd (fMem 0 6) (pairMemF 3 1 0))))))))))

section Definability

variable {F : ZFSet.{u}} {lam μ : Ordinal.{u}}

/-- A limit rank above `F` and `lam`. -/
noncomputable def bigRank (F : ZFSet.{u}) (lam : Ordinal.{u}) : Ordinal.{u} :=
  max (rank F) lam + ω

theorem bigRank_limit (F : ZFSet.{u}) (lam : Ordinal.{u}) :
    ∀ a < bigRank F lam, a + 1 < bigRank F lam := by
  intro a ha
  unfold bigRank at ha ⊢
  obtain ⟨n, hn⟩ : ∃ n : ℕ, a < max (rank F) lam + n := by
    rw [Ordinal.lt_add_iff (Ordinal.omega0_ne_zero)] at ha
    obtain ⟨d, hd, had⟩ := ha
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hd
    exact ⟨n + 1, lt_of_le_of_lt had (by
      rw [Nat.cast_succ, ← add_assoc]; exact Order.lt_add_one_iff.mpr le_rfl)⟩
  calc a + 1 ≤ max (rank F) lam + n := Order.add_one_le_of_lt hn
    _ < max (rank F) lam + ω := by
      exact (add_lt_add_iff_left _).mpr (Ordinal.natCast_lt_omega0 n)

theorem lt_bigRank_of_le {a : Ordinal.{u}} (h : a ≤ max (rank F) lam + 1) :
    a < bigRank F lam := by
  unfold bigRank
  refine lt_of_le_of_lt h ?_
  exact (add_lt_add_iff_left _).mpr Ordinal.one_lt_omega0

theorem F_mem_bigRank : F ∈ V_ (bigRank F lam) := by
  rw [mem_vonNeumann]
  exact lt_bigRank_of_le ((le_max_left _ _).trans (le_self_add))

theorem subset_lam_mem_bigRank {x : ZFSet.{u}} (hx : x ⊆ ordZ lam) :
    x ∈ V_ (bigRank F lam) := by
  rw [mem_vonNeumann]
  refine lt_bigRank_of_le ?_
  calc rank x ≤ rank (ordZ lam) := rank_mono hx
    _ = lam := rank_toZFSet lam
    _ ≤ max (rank F) lam + 1 := (le_max_right _ _).trans le_self_add

theorem ord_mem_bigRank {ξ : Ordinal.{u}} (hξ : ξ ≤ lam) : ordZ ξ ∈ V_ (bigRank F lam) :=
  subset_lam_mem_bigRank (Ordinal.toZFSet_subset_toZFSet_iff.mpr hξ)

theorem sUnion_proj_subset (ξ : Ordinal.{u}) : (⋃₀ (proj F lam ξ) : ZFSet.{u}) ⊆ ordZ lam := by
  intro v hv
  obtain ⟨w, hw, hvw⟩ := mem_sUnion.mp hv
  exact (isOrdinal_toZFSet lam).isTransitive.subset_of_mem (mem_proj.mp hw).1 hvw

variable (hfun : ∀ f ∈ F, IsFunc (ordZ μ) (ordZ lam) f)
include hfun

/-- **`P_ξ` is ordinal definable from `F`.** -/
theorem proj_OD (hμ : μ ≤ lam) (ξ : Ordinal.{u}) (hξ : ξ < μ) :
    ODfrom (fun p => p = F) (proj F lam ξ) := by
  have hlim := bigRank_limit F lam
  have hA := isTransitive_vonNeumann (bigRank F lam)
  have hP := pairClosed_vonNeumann hlim
  have hFθ : F ∈ V_ (bigRank F lam) := F_mem_bigRank
  have hξθ : ordZ ξ ∈ V_ (bigRank F lam) := ord_mem_bigRank (hξ.le.trans hμ)
  have h0θ : (∅ : ZFSet.{u}) ∈ V_ (bigRank F lam) := by
    have := ord_mem_bigRank (F := F) (lam := lam) (ξ := 0) bot_le
    simpa using this
  have hprojθ : proj F lam ξ ∈ V_ (bigRank F lam) :=
    subset_lam_mem_bigRank (fun w hw => (mem_proj.mp hw).1)
  refine ⟨bigRank F lam, projForm, ⟨∅, h0θ⟩, [⟨F, hFθ⟩, ⟨ordZ ξ, hξθ⟩], hprojθ,
    isOrdinal_empty, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (isOrdinal_toZFSet ξ)
  · intro y
    have hsat : Sat (memOn (V_ (bigRank F lam)))
        (scons y (envOf ⟨∅, h0θ⟩ [⟨F, hFθ⟩, ⟨ordZ ξ, hξθ⟩])) projForm ↔
        ∀ w : Carrier (V_ (bigRank F lam)), w.1 ∈ y.1 ↔
          ∃ f : Carrier (V_ (bigRank F lam)), f.1 ∈ F ∧ pair (ordZ ξ) w.1 ∈ f.1 := by
      simp only [projForm, Sat, SetTheory.Sat_fIff, pairMemF_spec hA hP, scons, envOf, memOn,
        List.getD_cons_zero, List.getD_cons_succ]
    rw [hsat]
    constructor
    · intro h
      apply Subtype.ext
      ext w
      rw [mem_proj]
      constructor
      · intro hw
        obtain ⟨f, hfF, hpf⟩ := (h ⟨w, hA.subset_of_mem y.2 hw⟩).mp hw
        exact ⟨(pair_mem_prod.mp ((hfun f.1 hfF).1 hpf)).2, f.1, hfF, hpf⟩
      · rintro ⟨hwl, f, hfF, hpf⟩
        have hwθ : w ∈ V_ (bigRank F lam) :=
          hA.subset_of_mem (ord_mem_bigRank le_rfl) hwl
        exact (h ⟨w, hwθ⟩).mpr ⟨⟨f, hA.subset_of_mem hFθ hfF⟩, hfF, hpf⟩
    · intro hy w
      have hyv : y.1 = proj F lam ξ := congrArg Subtype.val hy
      rw [hyv, mem_proj]
      constructor
      · rintro ⟨-, f, hfF, hpf⟩
        exact ⟨⟨f, hA.subset_of_mem hFθ hfF⟩, hfF, hpf⟩
      · rintro ⟨f, hfF, hpf⟩
        exact ⟨(pair_mem_prod.mp ((hfun f.1 hfF).1 hpf)).2, f.1, hfF, hpf⟩

/-- **The set of suprema of the projections is ordinal definable from `F`.** -/
theorem sups_OD (hμ : μ ≤ lam) : ODfrom (fun p => p = F) (sups F lam μ) := by
  have hlim := bigRank_limit F lam
  have hA := isTransitive_vonNeumann (bigRank F lam)
  have hP := pairClosed_vonNeumann hlim
  have hFθ : F ∈ V_ (bigRank F lam) := F_mem_bigRank
  have hμθ : ordZ μ ∈ V_ (bigRank F lam) := ord_mem_bigRank hμ
  have h0θ : (∅ : ZFSet.{u}) ∈ V_ (bigRank F lam) := by
    have := ord_mem_bigRank (F := F) (lam := lam) (ξ := 0) bot_le
    simpa using this
  have hsupθ : ∀ ξ, (⋃₀ (proj F lam ξ) : ZFSet.{u}) ∈ V_ (bigRank F lam) := fun ξ =>
    subset_lam_mem_bigRank (sUnion_proj_subset ξ)
  have hsupsθ : sups F lam μ ∈ V_ (bigRank F lam) := by
    rw [mem_vonNeumann]
    refine lt_bigRank_of_le ?_
    rw [rank_le_iff]
    intro z hz
    obtain ⟨ξ, -, rfl⟩ := mem_sups.mp hz
    refine Order.lt_add_one_iff.mpr ?_
    calc rank (⋃₀ (proj F lam ξ) : ZFSet.{u}) ≤ rank (ordZ lam) :=
          rank_mono (sUnion_proj_subset ξ)
      _ = lam := rank_toZFSet lam
      _ ≤ max (rank F) lam := le_max_right _ _
  refine ⟨bigRank F lam, supsForm, ⟨∅, h0θ⟩, [⟨F, hFθ⟩, ⟨ordZ μ, hμθ⟩], hsupsθ,
    isOrdinal_empty, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (isOrdinal_toZFSet μ)
  · intro y
    have hsat : Sat (memOn (V_ (bigRank F lam)))
        (scons y (envOf ⟨∅, h0θ⟩ [⟨F, hFθ⟩, ⟨ordZ μ, hμθ⟩])) supsForm ↔
        ∀ z : Carrier (V_ (bigRank F lam)), z.1 ∈ y.1 ↔
          ∃ x : Carrier (V_ (bigRank F lam)), x.1 ∈ ordZ μ ∧
            ∀ v : Carrier (V_ (bigRank F lam)), v.1 ∈ z.1 ↔
              ∃ w : Carrier (V_ (bigRank F lam)), v.1 ∈ w.1 ∧
                ∃ f : Carrier (V_ (bigRank F lam)), f.1 ∈ F ∧ pair x.1 w.1 ∈ f.1 := by
      simp only [supsForm, Sat, SetTheory.Sat_fIff, pairMemF_spec hA hP, scons, envOf, memOn,
        List.getD_cons_zero, List.getD_cons_succ]
    rw [hsat]
    -- the inner clause says `z = ⋃₀ (proj F lam ξ)`
    have hinner : ∀ (z : Carrier (V_ (bigRank F lam))) (ξ : Ordinal.{u}),
        (∀ v : Carrier (V_ (bigRank F lam)), v.1 ∈ z.1 ↔
          ∃ w : Carrier (V_ (bigRank F lam)), v.1 ∈ w.1 ∧
            ∃ f : Carrier (V_ (bigRank F lam)), f.1 ∈ F ∧ pair (ordZ ξ) w.1 ∈ f.1) ↔
        z.1 = ⋃₀ (proj F lam ξ) := by
      intro z ξ
      constructor
      · intro h
        ext v
        rw [mem_sUnion]
        constructor
        · intro hv
          obtain ⟨w, hvw, f, hfF, hpf⟩ := (h ⟨v, hA.subset_of_mem z.2 hv⟩).mp hv
          exact ⟨w.1, mem_proj.mpr
            ⟨(pair_mem_prod.mp ((hfun f.1 hfF).1 hpf)).2, f.1, hfF, hpf⟩, hvw⟩
        · rintro ⟨w, hw, hvw⟩
          obtain ⟨hwl, f, hfF, hpf⟩ := mem_proj.mp hw
          have hwθ : w ∈ V_ (bigRank F lam) := hA.subset_of_mem (ord_mem_bigRank le_rfl) hwl
          have hvθ : v ∈ V_ (bigRank F lam) := hA.subset_of_mem hwθ hvw
          exact (h ⟨v, hvθ⟩).mpr ⟨⟨w, hwθ⟩, hvw, ⟨f, hA.subset_of_mem hFθ hfF⟩, hfF, hpf⟩
      · intro hz v
        rw [hz, mem_sUnion]
        constructor
        · rintro ⟨w, hw, hvw⟩
          obtain ⟨hwl, f, hfF, hpf⟩ := mem_proj.mp hw
          have hwθ : w ∈ V_ (bigRank F lam) := hA.subset_of_mem (ord_mem_bigRank le_rfl) hwl
          exact ⟨⟨w, hwθ⟩, hvw, ⟨f, hA.subset_of_mem hFθ hfF⟩, hfF, hpf⟩
        · rintro ⟨w, hvw, f, hfF, hpf⟩
          exact ⟨w.1, mem_proj.mpr
            ⟨(pair_mem_prod.mp ((hfun f.1 hfF).1 hpf)).2, f.1, hfF, hpf⟩, hvw⟩
    constructor
    · intro h
      apply Subtype.ext
      ext z
      rw [mem_sups]
      constructor
      · intro hz
        obtain ⟨x, hxμ, hx⟩ := (h ⟨z, hA.subset_of_mem y.2 hz⟩).mp hz
        obtain ⟨ξ, hξ, hxξ⟩ := Ordinal.mem_toZFSet_iff.mp hxμ
        rw [← hxξ] at hx
        exact ⟨ξ, hξ, (hinner ⟨z, _⟩ ξ).mp hx⟩
      · rintro ⟨ξ, hξ, rfl⟩
        refine (h ⟨_, hsupθ ξ⟩).mpr ⟨⟨ordZ ξ, ord_mem_bigRank (hξ.le.trans hμ)⟩,
          Ordinal.toZFSet_mem_toZFSet_iff.mpr hξ, ?_⟩
        exact (hinner ⟨_, hsupθ ξ⟩ ξ).mpr rfl
    · intro hy z
      have hyv : y.1 = sups F lam μ := congrArg Subtype.val hy
      rw [hyv, mem_sups]
      constructor
      · rintro ⟨ξ, hξ, hz⟩
        exact ⟨⟨ordZ ξ, ord_mem_bigRank (hξ.le.trans hμ)⟩,
          Ordinal.toZFSet_mem_toZFSet_iff.mpr hξ, (hinner z ξ).mpr hz⟩
      · rintro ⟨x, hxμ, hx⟩
        obtain ⟨ξ, hξ, hxξ⟩ := Ordinal.mem_toZFSet_iff.mp hxμ
        rw [← hxξ] at hx
        exact ⟨ξ, hξ, (hinner z ξ).mp hx⟩

end Definability

/-! ### The projection-width theorem -/

/-- A bounded set of ordinals has an ordinal as its union. -/
theorem sUnion_eq_ord_of_bounded {P : ZFSet.{u}} {lam β : Ordinal.{u}} (hP : P ⊆ ordZ lam)
    (hb : ∀ η, β ≤ η → η < lam → ordZ η ∉ P) :
    ∃ ζ ≤ β, (⋃₀ P : ZFSet.{u}) = ordZ ζ := by
  have hmem : ∀ w ∈ P, ∃ η < β, w = ordZ η := by
    intro w hw
    obtain ⟨η, hη, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hP hw)
    refine ⟨η, ?_, rfl⟩
    by_contra hge
    exact hb η (not_lt.mp hge) hη hw
  have hsub : (⋃₀ P : ZFSet.{u}) ⊆ ordZ β := by
    intro v hv
    obtain ⟨w, hw, hvw⟩ := mem_sUnion.mp hv
    obtain ⟨η, hη, rfl⟩ := hmem w hw
    exact Ordinal.toZFSet_subset_toZFSet_iff.mpr hη.le hvw
  have hord : (⋃₀ P : ZFSet.{u}).IsOrdinal := by
    rw [ZFSet.isOrdinal_iff_forall_mem_isOrdinal]
    refine ⟨IsTransitive.sUnion' (fun w hw => ?_), fun v hv => ?_⟩
    · obtain ⟨η, -, rfl⟩ := hmem w hw
      exact (isOrdinal_toZFSet η).isTransitive
    · exact (isOrdinal_toZFSet β).mem (hsub hv)
  refine ⟨rank (⋃₀ P : ZFSet.{u}), ?_, hord.toZFSet_rank_eq.symm⟩
  calc rank (⋃₀ P : ZFSet.{u}) ≤ rank (ordZ β) := rank_mono hsub
    _ = β := rank_toZFSet β

/-- A subset of `lam` that is not cofinal is bounded. -/
theorem exists_bound_of_not_cofinal {a : ZFSet.{u}} {lam : Ordinal.{u}} (ha : SubOrd a lam)
    (hnc : ¬ CofinalIn a lam) : ∃ β < lam, ∀ η, β ≤ η → η < lam → ordZ η ∉ a := by
  by_contra hcon
  push Not at hcon
  exact hnc ⟨ha, fun ξ hξ => by
    obtain ⟨η, h1, h2, h3⟩ := hcon ξ hξ
    exact ⟨η, h1, h2, h3⟩⟩

/-- `f` is a cofinal map from `μ` to `lam`. -/
def IsCofinalMap (f : ZFSet.{u}) (μ lam : Ordinal.{u}) : Prop :=
  IsFunc (ordZ μ) (ordZ lam) f ∧
    ∀ β < lam, ∃ ξ < μ, ∃ η, β ≤ η ∧ pair (ordZ ξ) (ordZ η) ∈ f

theorem card_sups_le (F : ZFSet.{u}) (lam μ : Ordinal.{u}) :
    ZFSet.card (sups F lam μ) ≤ μ.card := by
  have h := ZFSet.lift_card_range_le
    (f := fun ξ : Set.Iio μ => (⋃₀ (proj F lam ξ.1) : ZFSet.{u}))
  have h2 : Cardinal.lift.{u + 1, u} (ZFSet.card (sups F lam μ)) ≤
      Cardinal.lift.{u + 1, u} μ.card := by
    simpa [sups, Ordinal.lift_card] using h
  exact Cardinal.lift_le.mp h2

/-- **Projection width (synthesis Theorem 8.1).**  Let `c.ord` be exacting, `μ < c.ord`,
and let `F` be a nonempty family of cofinal maps `μ → c.ord` that is ordinal definable
from parameters in `V_{c.ord}`.  Then some coordinate projection of `F` is cofinal in
`c.ord` and has cardinality at least `c`.  No member of `F` is assumed definable. -/
theorem projection_width (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hEx : Ex c.ord)
    (μ : Ordinal.{u}) (hμ : μ < c.ord) (F : ZFSet.{u})
    (hF : ODfrom (fun p => p ∈ V_ c.ord) F) (hne : F.Nonempty)
    (hmaps : ∀ f ∈ F, IsCofinalMap f μ c.ord) :
    ∃ ξ < μ, CofinalIn (proj F c.ord ξ) c.ord ∧ c ≤ ZFSet.card (proj F c.ord ξ) := by
  have hfun : ∀ f ∈ F, IsFunc (ordZ μ) (ordZ c.ord) f := fun f hf => (hmaps f hf).1
  have hFF : ∀ p, p = F → ODfrom (fun p => p ∈ V_ c.ord) p := fun p hp => hp ▸ hF
  have hsubP : ∀ ξ, SubOrd (proj F c.ord ξ) c.ord := fun ξ =>
    subOrd_iff_subset.mpr (fun w hw => (mem_proj.mp hw).1)
  -- a cofinal projection is automatically large
  have hlarge : ∀ ξ < μ, CofinalIn (proj F c.ord ξ) c.ord → c ≤ ZFSet.card (proj F c.ord ξ) := by
    intro ξ hξ hcof
    by_contra hlt
    rw [not_le] at hlt
    have hOD := Published.ODfrom_trans _ _ _ (proj_OD hfun hμ.le ξ hξ) hFF
    exact Published.no_short_cofinal_OD c hc hEx _ hOD ⟨hcof, by rwa [card_ord]⟩
  by_contra hcon
  push Not at hcon
  have hnocof : ∀ ξ < μ, ¬ CofinalIn (proj F c.ord ξ) c.ord :=
    fun ξ hξ hcof => absurd (hlarge ξ hξ hcof) (not_le.mpr (hcon ξ hξ hcof))
  -- every projection is bounded, so the set of suprema consists of ordinals below `c.ord`
  have hsupord : ∀ ξ < μ, ∃ ζ < c.ord, (⋃₀ (proj F c.ord ξ) : ZFSet.{u}) = ordZ ζ := by
    intro ξ hξ
    obtain ⟨β, hβ, hb⟩ := exists_bound_of_not_cofinal (hsubP ξ) (hnocof ξ hξ)
    obtain ⟨ζ, hζ, heq⟩ := sUnion_eq_ord_of_bounded
      (subOrd_iff_subset.mp (hsubP ξ)) hb
    exact ⟨ζ, lt_of_le_of_lt hζ hβ, heq⟩
  have hBsub : SubOrd (sups F c.ord μ) c.ord := by
    intro z hz
    obtain ⟨ξ, hξ, rfl⟩ := mem_sups.mp hz
    obtain ⟨ζ, hζ, heq⟩ := hsupord ξ hξ
    exact ⟨ζ, hζ, heq⟩
  have hBcard : ZFSet.card (sups F c.ord μ) < c :=
    lt_of_le_of_lt (card_sups_le F c.ord μ) (Cardinal.lt_ord.mp hμ)
  have hBOD := Published.ODfrom_trans _ _ _ (sups_OD hfun hμ.le) hFF
  have hBnc : ¬ CofinalIn (sups F c.ord μ) c.ord := fun hcof =>
    Published.no_short_cofinal_OD c hc hEx _ hBOD ⟨hcof, by rwa [card_ord]⟩
  obtain ⟨β₀, hβ₀, hb₀⟩ := exists_bound_of_not_cofinal hBsub hBnc
  -- but a cofinal member of `F` exceeds `β₀` somewhere
  obtain ⟨f, hfF⟩ := hne
  obtain ⟨ξ, hξ, η, hβη, hpair⟩ := (hmaps f hfF).2 β₀ hβ₀
  have hηlam : η < c.ord :=
    Ordinal.toZFSet_mem_toZFSet_iff.mp (pair_mem_prod.mp ((hfun f hfF).1 hpair)).2
  have hηP : ordZ η ∈ proj F c.ord ξ :=
    mem_proj.mpr ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr hηlam, f, hfF, hpair⟩
  obtain ⟨ζ, hζ, heq⟩ := hsupord ξ hξ
  have hζB : ordZ ζ ∈ sups F c.ord μ := mem_sups.mpr ⟨ξ, hξ, heq.symm⟩
  have hζβ : ζ < β₀ := by
    by_contra hge
    exact hb₀ ζ (not_lt.mp hge) hζ hζB
  have hηζ : η ≤ ζ := by
    have hsub : ordZ η ⊆ (⋃₀ (proj F c.ord ξ) : ZFSet.{u}) :=
      fun v hv => mem_sUnion.mpr ⟨ordZ η, hηP, hv⟩
    rw [heq] at hsub
    exact Ordinal.toZFSet_subset_toZFSet_iff.mp hsub
  exact absurd (hβη.trans hηζ) (not_le.mpr hζβ)

/-- The value at `ξ` of a member of the family (junk value `∅` outside the domain). -/
noncomputable def valueAt (ξ : Ordinal.{u}) (f : ZFSet.{u}) : ZFSet.{u} :=
  open Classical in if h : ∃ w, pair (ordZ ξ) w ∈ f then h.choose else ∅

/-- A projection is no larger than the family. -/
theorem card_proj_le {F : ZFSet.{u}} {lam μ ξ : Ordinal.{u}}
    (hfun : ∀ f ∈ F, IsFunc (ordZ μ) (ordZ lam) f) (hξ : ξ < μ) :
    ZFSet.card (proj F lam ξ) ≤ ZFSet.card F := by
  have hsub : proj F lam ξ ⊆ ZFSet.range (fun f : {f // f ∈ F} => valueAt ξ f.1) := by
    intro w hw
    obtain ⟨-, f, hfF, hpf⟩ := mem_proj.mp hw
    refine ZFSet.mem_range.mpr ⟨⟨f, hfF⟩, ?_⟩
    have hex : ∃ w, pair (ordZ ξ) w ∈ f := ⟨w, hpf⟩
    have huniq := (hfun f hfF).2 (ordZ ξ) (Ordinal.toZFSet_mem_toZFSet_iff.mpr hξ)
    simp only [valueAt, dif_pos hex]
    exact huniq.unique hex.choose_spec hpf
  refine (card_mono hsub).trans ?_
  have h := ZFSet.lift_card_range_le (f := fun f : {f // f ∈ F} => valueAt ξ f.1)
  rw [ZFSet.cardinalMk_coe_sort] at h
  simpa using h

/-- **Small-family incompatibility (synthesis Corollary 8.2).**  An `OD_{V_lam}` family of
cofinal maps from a fixed `μ < lam` into an exacting `lam` has at least `|lam|` members. -/
theorem card_family_ge (c : Cardinal.{u}) (hc : ℵ₀ ≤ c) (hEx : Ex c.ord)
    (μ : Ordinal.{u}) (hμ : μ < c.ord) (F : ZFSet.{u})
    (hF : ODfrom (fun p => p ∈ V_ c.ord) F) (hne : F.Nonempty)
    (hmaps : ∀ f ∈ F, IsCofinalMap f μ c.ord) : c ≤ ZFSet.card F := by
  obtain ⟨ξ, hξ, -, hcard⟩ := projection_width c hc hEx μ hμ F hF hne hmaps
  exact hcard.trans (card_proj_le (fun f hf => (hmaps f hf).1) hξ)

end Cardinals
