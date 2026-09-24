/-
  FIXED SMALL SETS (synthesis Lemma 8.4), for the actual embedding of a witness.

  Let `w : RelWitness c.ord α Y` be an exacting witness at the cardinal `λ = c.ord`, at a
  limit height `α`, with critical point `κ = w.crit`.

  * `fixed_small_subset` (Lemma 8.4(a)): if `S ∈ X`, `S ⊆ λ`, `j(S) = S` and `|S| < λ`,
    then `S ⊆ κ`.  The proof is the one of the synthesis: the least ordinal `μ` mapping
    onto `S` is definable from the fixed parameters `λ, S`, hence fixed, hence below `κ`;
    a surjection `f : μ → S` in `X` gives `j '' S = S`; and an order-preserving
    bijection of a set of ordinals is the identity.
  * `no_small_fixed_family` (Lemma 8.4(b) for families with a common size bound, in
    particular subfamilies of `D_λ`): there is no nonempty `F ∈ X` with `j(F) = F`,
    `|F| < λ`, whose members are cofinal subsets of `λ` of size `≤ ν < λ`.

  Nothing is admitted in this file; the only admitted input used is
  `Published.critSeq_cofinal` (through `RelWitness.moved`).
-/
import Cardinals.Foundations.Witness
import Cardinals.Foundations.SetForms
import Cardinals.Combinatorics.SecondRound

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

/-! ### Auxiliary facts -/

theorem mem_V_of_subset {x : ZFSet.{u}} {β α : Ordinal.{u}} (h : x ⊆ V_ β) (hβ : β < α) :
    x ∈ V_ α := by
  rw [mem_vonNeumann]
  refine lt_of_le_of_lt ?_ hβ
  rw [rank_le_iff]
  intro y hy
  exact mem_vonNeumann.mp (h hy)

theorem ordZ_subset_V (lam : Ordinal.{u}) : ordZ lam ⊆ V_ lam := by
  intro x hx
  obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
  exact ordZ_mem_V hξ

theorem ordZ_inj {a b : Ordinal.{u}} (h : ordZ a = ordZ b) : a = b := by
  have := congrArg ZFSet.rank h
  rwa [rank_toZFSet, rank_toZFSet] at this

theorem limit_ord {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) : ∀ a < c.ord, a + 1 < c.ord := by
  intro a ha
  have := (Cardinal.isSuccLimit_ord hc).succ_lt ha
  simpa using this

/-- `|⋃ F| ≤ |F| · ν` if every member of `F` has size at most `ν`. -/
theorem card_sUnion_le (F : ZFSet.{u}) (ν : Cardinal.{u}) (h : ∀ b ∈ F, ZFSet.card b ≤ ν) :
    ZFSet.card (⋃₀ F) ≤ ZFSet.card F * ν := by
  let A : Set (Set ZFSet.{u}) := (fun b : ZFSet.{u} => (b : Set ZFSet.{u})) '' (F : Set ZFSet.{u})
  have hU : ((⋃₀ F : ZFSet.{u}) : Set ZFSet.{u}) = ⋃₀ A := by
    ext t
    simp only [SetLike.mem_coe, mem_sUnion, Set.mem_sUnion, A, Set.mem_image]
    constructor
    · rintro ⟨b, hb, ht⟩
      exact ⟨(b : Set ZFSet.{u}), ⟨b, hb, rfl⟩, ht⟩
    · rintro ⟨s, ⟨b, hb, rfl⟩, ht⟩
      exact ⟨b, hb, ht⟩
  have h1 := Cardinal.mk_sUnion_le A
  have h2 : #A ≤ Cardinal.lift.{u + 1, u} (ZFSet.card F) := by
    have := Cardinal.mk_image_le (f := fun b : ZFSet.{u} => (b : Set ZFSet.{u}))
      (s := (F : Set ZFSet.{u}))
    refine this.trans (le_of_eq ?_)
    exact ZFSet.cardinalMk_coe_sort
  have h3 : (⨆ s : A, #s) ≤ Cardinal.lift.{u + 1, u} ν := by
    refine ciSup_le' (fun s => ?_)
    obtain ⟨b, hb, hs⟩ := s.2
    have : #(s : Set ZFSet.{u}) = Cardinal.lift.{u + 1, u} (ZFSet.card b) := by
      rw [← hs]
      exact ZFSet.cardinalMk_coe_sort
    rw [this]
    exact Cardinal.lift_le.mpr (h b hb)
  have h4 : #((⋃₀ F : ZFSet.{u}) : Set ZFSet.{u}) = Cardinal.lift.{u + 1, u} (ZFSet.card (⋃₀ F)) :=
    ZFSet.cardinalMk_coe_sort
  rw [hU] at h4
  rw [h4] at h1
  have h5 := h1.trans (mul_le_mul' h2 h3)
  rw [← Cardinal.lift_mul] at h5
  exact Cardinal.lift_le.mp h5

namespace RelWitness

variable {α : Ordinal.{u}} {Y : ZFSet.{u}} {c : Cardinal.{u}} (w : RelWitness c.ord α Y)

include w in
theorem lam_lt_height : c.ord < α := by
  have := w.X_sub w.lam_mem
  rwa [mem_vonNeumann, rank_toZFSet] at this

/-- `j` preserves and reflects membership of ordered pairs. -/
theorem pair_mem_iff (hα : ∀ a < α, a + 1 < α) (x y f : Str w.X Y) :
    pair x.1 y.1 ∈ f.1 ↔ pair (w.jv x) (w.jv y) ∈ w.jv f := by
  have h := w.elem (pairMemF 0 1 2) (scons x (scons y (fun _ => f)))
  rw [pairMemF_spec (isTransitive_vonNeumann α) (pairClosed_vonNeumann hα),
    pairMemF_spec (isTransitive_vonNeumann α) (pairClosed_vonNeumann hα)] at h
  exact h

/-- `ordZ ξ ∈ S ↔ ordZ (j ξ) ∈ j(S)`. -/
theorem ord_mem_iff {ξ : Ordinal.{u}} (hξ : ξ < c.ord) (S : Str w.X Y) :
    ordZ ξ ∈ S.1 ↔ ordZ (w.jOrd ξ) ∈ w.jv S := by
  have := w.mem_iff (w.ordX ξ hξ) S
  rwa [jv_ordX] at this

/-! ### Transfer of simple set-theoretic facts through `j` -/

theorem nonempty_iff (b : Str w.X Y) : (∃ t, t ∈ b.1) ↔ ∃ t, t ∈ w.jv b := by
  have hA := isTransitive_vonNeumann α
  have h := w.elem (nonemptyF 0) (fun _ => b)
  rw [nonemptyF_spec hA, nonemptyF_spec hA] at h
  exact h

theorem insert_iff (b x b' : Str w.X Y) :
    b.1 = insert x.1 b'.1 ↔ w.jv b = insert (w.jv x) (w.jv b') := by
  have hA := isTransitive_vonNeumann α
  have h := w.elem (insertF 0 1 2) (scons b (scons x (fun _ => b')))
  rw [insertF_spec hA, insertF_spec hA] at h
  exact h

theorem inter_iff (b x y : Str w.X Y) :
    b.1 = x.1 ∩ y.1 ↔ w.jv b = w.jv x ∩ w.jv y := by
  have hA := isTransitive_vonNeumann α
  have h := w.elem (interF 0 1 2) (scons b (scons x (fun _ => y)))
  rw [interF_spec hA, interF_spec hA] at h
  exact h

/-- `j` preserves "`f` maps `m` onto `S`". -/
theorem surj_iff (hα : ∀ a < α, a + 1 < α) (f m S : Str w.X Y) :
    SurjSem (V_ α) f.1 m.1 S.1 ↔ SurjSem (V_ α) (w.jv f) (w.jv m) (w.jv S) := by
  have h := w.elem (surjF 0 1 2) (scons f (scons m (fun _ => S)))
  rw [surjF_spec (isTransitive_vonNeumann α) (pairClosed_vonNeumann hα),
    surjF_spec (isTransitive_vonNeumann α) (pairClosed_vonNeumann hα)] at h
  exact h

/-- A surjection in `V_ α` between elements of `X` can be found in `X`. -/
theorem surj_in_X (hα : ∀ a < α, a + 1 < α) (m S : Str w.X Y)
    (h : ∃ f ∈ V_ α, SurjSem (V_ α) f m.1 S.1) : ∃ f : Str w.X Y, SurjSem (V_ α) f.1 m.1 S.1 := by
  have hA := isTransitive_vonNeumann α
  have hP := pairClosed_vonNeumann hα
  obtain ⟨f, hfA, hfs⟩ := h
  obtain ⟨d, hd⟩ := w.tarski_vaught (surjF 0 1 2) (scons m (fun _ => S))
    ⟨⟨f, hfA⟩, (surjF_spec hA hP _ 0 1 2).mpr hfs⟩
  exact ⟨d, (surjF_spec hA hP _ 0 1 2).mp hd⟩

/-- Step 1: a small set of ordinals is the image of an ordinal below `λ` under a function
in `V_ α`. -/
theorem exists_surj (hc : ℵ₀ ≤ c) (S : ZFSet.{u}) (hS : S ⊆ ordZ c.ord)
    (hcard : ZFSet.card S < c) (hlamα : c.ord < α) :
    ∃ μ, μ < c.ord ∧ ∃ f ∈ V_ α, SurjSem (V_ α) f (ordZ μ) S := by
  have hPl := pairClosed_vonNeumann (limit_ord hc)
  let μ₀ := (ZFSet.card S).ord
  have hμ₀ : μ₀ < c.ord := Cardinal.ord_lt_ord.mpr hcard
  have e1 : #{x // x ∈ ordZ μ₀} = #{x // x ∈ S} := by
    have h1 : #{x // x ∈ ordZ μ₀} = Cardinal.lift.{u + 1, u} (ZFSet.card (ordZ μ₀)) :=
      ZFSet.cardinalMk_coe_sort
    have h2 : #{x // x ∈ S} = Cardinal.lift.{u + 1, u} (ZFSet.card S) :=
      ZFSet.cardinalMk_coe_sort
    rw [h1, h2, card_toZFSet, card_ord]
  obtain ⟨E⟩ := Cardinal.eq.mp e1
  let f₀ : ZFSet.{u} :=
    ZFSet.sep (fun p => ∃ u : {x // x ∈ ordZ μ₀}, p = pair u.1 (E u).1) (prod (ordZ μ₀) S)
  have hf₀ : ∀ a b, pair a b ∈ f₀ ↔ ∃ u : {x // x ∈ ordZ μ₀}, a = u.1 ∧ b = (E u).1 := by
    intro a b
    rw [mem_sep]
    constructor
    · rintro ⟨-, u, hu⟩
      exact ⟨u, (pair_inj.mp hu).1, (pair_inj.mp hu).2⟩
    · rintro ⟨u, rfl, rfl⟩
      exact ⟨pair_mem_prod.mpr ⟨u.2, (E u).2⟩, u, rfl⟩
  refine ⟨μ₀, hμ₀, f₀, ?_, ?_, ?_, ?_⟩
  · refine mem_V_of_subset (β := c.ord) (fun p hp => ?_) hlamα
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.mp (mem_sep.mp hp).1
    have haV : a ∈ V_ c.ord := by
      obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
      exact ordZ_mem_V (hξ.trans hμ₀)
    have hbV : b ∈ V_ c.ord := ordZ_subset_V _ (hS hb)
    show ({{a}, {a, b}} : ZFSet.{u}) ∈ V_ c.ord
    exact hPl _ (hPl.singleton_mem haV) _ (hPl _ haV _ hbV)
  · intro u hu
    exact ⟨(E ⟨u, hu⟩).1, (E ⟨u, hu⟩).2, (hf₀ _ _).mpr ⟨⟨u, hu⟩, rfl, rfl⟩⟩
  · intro u _ v _ v' _ h1 h2
    obtain ⟨u1, h11, h12⟩ := (hf₀ _ _).mp h1
    obtain ⟨u2, h21, h22⟩ := (hf₀ _ _).mp h2
    have : u1 = u2 := Subtype.ext (h11.symm.trans h21)
    subst this
    exact h12.trans h22.symm
  · intro v hv
    refine ⟨(E.symm ⟨v, hv⟩).1, (E.symm ⟨v, hv⟩).2, (hf₀ _ _).mpr ⟨E.symm ⟨v, hv⟩, rfl, ?_⟩⟩
    simp

/-- Steps 2-3: the least ordinal mapping onto a fixed `S` is definable from the fixed
parameters `λ` and `S`, hence is fixed by `j`. -/
theorem least_surj_fixed (hα : ∀ a < α, a + 1 < α) (S : Str w.X Y) (hfix : w.jv S = S.1)
    (μ : Ordinal.{u}) (hμ : μ < c.ord) (hμs : ∃ f ∈ V_ α, SurjSem (V_ α) f (ordZ μ) S.1)
    (hmin : ∀ ν, ν < μ → ¬ ∃ f ∈ V_ α, SurjSem (V_ α) f (ordZ ν) S.1) : w.jOrd μ = μ := by
  have hA := isTransitive_vonNeumann α
  have hP := pairClosed_vonNeumann hα
  have hμA : ordZ μ ∈ V_ α := ordZ_mem_V (hμ.trans w.lam_lt_height)
  have hpar : ∀ k, w.j (scons w.lamX (fun _ => S) k) = w.up (scons w.lamX (fun _ => S) k) := by
    intro k
    cases k with
    | zero => exact Subtype.ext w.j_lam
    | succ k => exact Subtype.ext hfix
  have hx : Sat (memOn (V_ α))
      (scons ⟨ordZ μ, hμA⟩ (fun k => w.up (scons w.lamX (fun _ => S) k))) minSurjF := by
    refine (minSurjF_spec hA hP _).mpr
      ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr hμ, hμs, fun ν hν => ?_⟩
    obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hν
    exact hmin ξ hξ
  have huniq : ∀ y, Sat (memOn (V_ α))
      (scons y (fun k => w.up (scons w.lamX (fun _ => S) k))) minSurjF → y = ⟨ordZ μ, hμA⟩ := by
    intro y hy
    obtain ⟨hy1, hy2, hy3⟩ := (minSurjF_spec hA hP _).mp hy
    have hy1' : y.1 ∈ ordZ c.ord := hy1
    have hy2' : ∃ f ∈ V_ α, SurjSem (V_ α) f y.1 S.1 := hy2
    have hy3' : ∀ ν ∈ y.1, ¬ ∃ f ∈ V_ α, SurjSem (V_ α) f ν S.1 := hy3
    obtain ⟨ξ, hξ, hyξ⟩ := Ordinal.mem_toZFSet_iff.mp hy1'
    have hyξ' : y.1 = ordZ ξ := by
      first
        | exact hyξ
        | exact hyξ.symm
    apply Subtype.ext
    show y.1 = ordZ μ
    rw [hyξ'] at hy2' hy3' ⊢
    rcases lt_trichotomy ξ μ with h | h | h
    · exact absurd hy2' (hmin ξ h)
    · rw [h]
    · exact absurd hμs (hy3' (ordZ μ) (Ordinal.toZFSet_mem_toZFSet_iff.mpr h))
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed minSurjF _ hpar ⟨ordZ μ, hμA⟩ hx huniq
  have hd0 : (w.up d).1 = ordZ μ := congrArg Subtype.val hd
  have hd1 : d = w.ordX μ hμ := Subtype.ext hd0
  have hjd1 : w.jv d = ordZ μ := congrArg Subtype.val hjd
  rw [hd1, jv_ordX] at hjd1
  exact ordZ_inj hjd1

/-- **Fixed small sets of ordinals (synthesis Lemma 8.4(a)).** -/
theorem fixed_small_subset (hc : ℵ₀ ≤ c) (hα : ∀ a < α, a + 1 < α) (S : Str w.X Y)
    (hS : S.1 ⊆ ordZ c.ord) (hfix : w.jv S = S.1) (hcard : ZFSet.card S.1 < c) :
    S.1 ⊆ ordZ w.crit := by
  have hlamα := w.lam_lt_height
  -- the least ordinal mapping onto `S`
  have hex := exists_surj (α := α) hc S.1 hS hcard hlamα
  obtain ⟨μ, hμP, hmin⟩ : ∃ μ, (μ < c.ord ∧ ∃ f ∈ V_ α, SurjSem (V_ α) f (ordZ μ) S.1) ∧
      ∀ ν, ν < μ → ¬ ∃ f ∈ V_ α, SurjSem (V_ α) f (ordZ ν) S.1 := by
    let P : Set Ordinal.{u} := {μ | μ < c.ord ∧ ∃ f ∈ V_ α, SurjSem (V_ α) f (ordZ μ) S.1}
    have hPne : P.Nonempty := hex
    refine ⟨wellFounded_lt.min P hPne, wellFounded_lt.min_mem P hPne, fun ν hν hf => ?_⟩
    have hνP : ν ∈ P := ⟨hν.trans (wellFounded_lt.min_mem P hPne).1, hf⟩
    exact wellFounded_lt.not_lt_min P hνP hν
  have hμ : μ < c.ord := hμP.1
  have hfixed : w.jOrd μ = μ := w.least_surj_fixed hα S hfix μ hμ hμP.2 hmin
  have hμκ : μ < w.crit := (w.fixed_iff_lt_crit hc hμ).mp hfixed
  -- a surjection in `X`, and its image
  obtain ⟨fX, hsX⟩ := w.surj_in_X hα (w.ordX μ hμ) S hμP.2
  have hsJ : SurjSem (V_ α) (w.jv fX) (ordZ μ) S.1 := by
    have h3 := (w.surj_iff hα fX (w.ordX μ hμ) S).mp hsX
    rwa [jv_ordX, hfixed, hfix] at h3
  have hsX' : SurjSem (V_ α) fX.1 (ordZ μ) S.1 := hsX
  -- `j '' S = S`
  let Sset : Set Ordinal.{u} := {ξ | ordZ ξ ∈ S.1}
  have hSlt : ∀ ξ ∈ Sset, ξ < c.ord := fun ξ hξ => Ordinal.toZFSet_mem_toZFSet_iff.mp (hS hξ)
  have himage : w.jOrd '' Sset = Sset := by
    apply Set.Subset.antisymm
    · rintro _ ⟨ξ, hξ, rfl⟩
      have := (w.ord_mem_iff (hSlt ξ hξ) S).mp hξ
      rwa [hfix] at this
    · intro η hη
      obtain ⟨u, hu, hp⟩ := hsJ.2.2 (ordZ η) hη
      obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hu
      obtain ⟨v', hv', hp'⟩ := hsX'.1 _ hu
      obtain ⟨η', hη', rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hS hv')
      have hζlam : ζ < c.ord := hζ.trans hμ
      have hp'' := (w.pair_mem_iff hα (w.ordX ζ hζlam) (w.ordX η' hη') fX).mp hp'
      rw [jv_ordX, jv_ordX, w.jOrd_of_lt_crit (hζ.trans hμκ)] at hp''
      have heq : ordZ η = ordZ (w.jOrd η') :=
        hsJ.2.1 (ordZ ζ) (ordZ_mem_V (hζlam.trans hlamα))
          (ordZ η) (ordZ_mem_V ((hSlt η hη).trans hlamα))
          (ordZ (w.jOrd η')) (ordZ_mem_V ((w.jOrd_lt hη').trans hlamα)) hp hp''
      exact ⟨η', hv', (ordZ_inj heq).symm⟩
  -- an order-preserving self-bijection of a set of ordinals is the identity
  have hbelow := SecondRound.fixed_small_set_below_crit w.jOrd c.ord w.crit
    (fun a b hab hb => w.jOrd_strictMono hab hb) (fun ξ h1 h2 => w.moved hc h1 h2)
    Sset hSlt himage
  intro x hx
  obtain ⟨ξ, -, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hS hx)
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hbelow ξ hx)

/-- **No small fixed family of short cofinal sets (synthesis Lemma 8.4(b)),** for
families whose members have a common size bound `ν < λ` -- in particular for families of
cofinal sets of order type `ω`. -/
theorem no_small_fixed_family (hc : ℵ₀ ≤ c) (hα : ∀ a < α, a + 1 < α) (F : Str w.X Y)
    (hfix : w.jv F = F.1) (ν : Cardinal.{u}) (hν : ν < c)
    (hmem : ∀ b ∈ F.1, CofinalIn b c.ord ∧ ZFSet.card b ≤ ν) (hcard : ZFSet.card F.1 < c) :
    F.1 = ∅ := by
  by_contra hne
  obtain ⟨b, hb⟩ := (ZFSet.eq_empty_or_nonempty F.1).resolve_left hne
  have hA := isTransitive_vonNeumann α
  have hlamα := w.lam_lt_height
  have husub : (⋃₀ F.1 : ZFSet.{u}) ⊆ ordZ c.ord := by
    intro t ht
    obtain ⟨b', hb', htb'⟩ := mem_sUnion.mp ht
    exact subOrd_iff_subset.mp (hmem b' hb').1.1 htb'
  have huA : (⋃₀ F.1 : ZFSet.{u}) ∈ V_ α :=
    mem_V_of_subset (fun t ht => ordZ_subset_V _ (husub ht)) hlamα
  obtain ⟨d, hd, hjd⟩ := w.definable_fixed (sUnionF 0 1) (fun _ => F)
    (fun _ => Subtype.ext hfix) ⟨⋃₀ F.1, huA⟩
    ((sUnionF_spec hA _ 0 1).mpr rfl)
    (fun y hy => Subtype.ext ((sUnionF_spec hA _ 0 1).mp hy))
  have hd1 : d.1 = ⋃₀ F.1 := congrArg Subtype.val hd
  have hjd1 : w.jv d = d.1 := (congrArg Subtype.val hjd).trans hd1.symm
  have hcardu : ZFSet.card d.1 < c := by
    rw [hd1]
    exact lt_of_le_of_lt (card_sUnion_le F.1 ν (fun b' hb' => (hmem b' hb').2))
      (Cardinal.mul_lt_of_lt hc hcard hν)
  have hsmall := w.fixed_small_subset hc hα d (hd1 ▸ husub) hjd1 hcardu
  obtain ⟨η, hκη, hηlam, hηb⟩ := (hmem b hb).1.2 w.crit w.crit_lt
  have : ordZ η ∈ ordZ w.crit := hsmall (hd1 ▸ mem_sUnion.mpr ⟨b, hb, hηb⟩)
  exact absurd (Ordinal.toZFSet_mem_toZFSet_iff.mp this) (not_lt.mpr hκη)

end RelWitness

end Cardinals
