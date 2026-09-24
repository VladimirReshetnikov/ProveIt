/-
  BASIC LARGE-CARDINAL FACTS ABOUT AN EXACTING WITNESS, PROVED FROM THE EMBEDDING.

  For `w : RelWitness c.ord α Y` of limit height, with the cofinality of the critical
  sequence (`Published.critSeq_cofinal`, i.e. the Kunen inconsistency) as the only input:

  * `jOrd_nat`, `omega_le_crit`, `aleph0_lt`: `j` fixes the finite ordinals, the critical
    point is infinite, and `λ` is uncountable;
  * `jv_subset_fixed`: `j` fixes every subset of an ordinal below the critical point;
  * `no_surj_pow_crit`, `two_pow_lt_crit`: the critical point `κ` satisfies `2^μ < κ` for
    `μ < κ` (the classical argument: a surjection `f : 𝒫(μ) → κ` in `X` would satisfy
    `ran j(f) = j '' ran f = κ ≠ j(κ)`);
  * `slSem_critSeq`: the same for every `κ_n`, by elementarity (formula `slF`);
  * `strongLimit`: `λ` is a strong limit cardinal.

  These replace the formerly admitted statements `aleph0_lt_of_witness`,
  `cof_omega_of_witness` and `strongLimit_of_witness` of `Published.lean`.
  Nothing is admitted in this file.
-/
import Cardinals.FixedSets

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

theorem subset_mem_V {x y : ZFSet.{u}} {α : Ordinal.{u}} (h : x ⊆ y) (hy : y ∈ V_ α) :
    x ∈ V_ α := by
  rw [mem_vonNeumann] at *
  refine lt_of_le_of_lt ?_ hy
  rw [rank_le_iff]
  intro z hz
  exact rank_lt_of_mem (h hz)

theorem powerset_mem_V {y : ZFSet.{u}} {α : Ordinal.{u}} (hα : ∀ a < α, a + 1 < α)
    (hy : y ∈ V_ α) : powerset y ∈ V_ α := by
  rw [mem_vonNeumann] at *
  rw [rank_powerset]
  simpa using hα _ hy

/-- A surjection between sets of rank below `λ`, as a set of pairs in `V_ α`. -/
theorem exists_surj_of_card_le {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) {α : Ordinal.{u}}
    (hlamα : c.ord < α) (m S : ZFSet.{u}) (hm : m ⊆ V_ c.ord) (hS : S ⊆ V_ c.ord)
    (hne : S.Nonempty) (hcard : ZFSet.card S ≤ ZFSet.card m) :
    ∃ f ∈ V_ α, SurjSem (V_ α) f m S := by
  have hPl := pairClosed_vonNeumann (limit_ord hc)
  have hle : #{x // x ∈ S} ≤ #{x // x ∈ m} := by
    have h1 : #{x // x ∈ S} = Cardinal.lift.{u + 1, u} (ZFSet.card S) := ZFSet.cardinalMk_coe_sort
    have h2 : #{x // x ∈ m} = Cardinal.lift.{u + 1, u} (ZFSet.card m) := ZFSet.cardinalMk_coe_sort
    rw [h1, h2]
    exact Cardinal.lift_le.mpr hcard
  obtain ⟨e⟩ := hle
  obtain ⟨s₀, hs₀⟩ := hne
  haveI : Nonempty {x // x ∈ S} := ⟨⟨s₀, hs₀⟩⟩
  let g : {x // x ∈ m} → {x // x ∈ S} := Function.invFun e
  have hg : Function.Surjective g := Function.invFun_surjective e.injective
  let f₀ : ZFSet.{u} :=
    ZFSet.sep (fun p => ∃ u : {x // x ∈ m}, p = pair u.1 (g u).1) (prod m S)
  have hf₀ : ∀ a b, pair a b ∈ f₀ ↔ ∃ u : {x // x ∈ m}, a = u.1 ∧ b = (g u).1 := by
    intro a b
    rw [mem_sep]
    constructor
    · rintro ⟨-, u, hu⟩
      exact ⟨u, (pair_inj.mp hu).1, (pair_inj.mp hu).2⟩
    · rintro ⟨u, rfl, rfl⟩
      exact ⟨pair_mem_prod.mpr ⟨u.2, (g u).2⟩, u, rfl⟩
  refine ⟨f₀, ?_, ?_, ?_, ?_⟩
  · refine mem_V_of_subset (β := c.ord) (fun p hp => ?_) hlamα
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_prod.mp (mem_sep.mp hp).1
    show ({{a}, {a, b}} : ZFSet.{u}) ∈ V_ c.ord
    exact hPl _ (hPl.singleton_mem (hm ha)) _ (hPl _ (hm ha) _ (hS hb))
  · intro u hu
    exact ⟨(g ⟨u, hu⟩).1, (g ⟨u, hu⟩).2, (hf₀ _ _).mpr ⟨⟨u, hu⟩, rfl, rfl⟩⟩
  · intro u _ v _ v' _ h1 h2
    obtain ⟨u1, h11, h12⟩ := (hf₀ _ _).mp h1
    obtain ⟨u2, h21, h22⟩ := (hf₀ _ _).mp h2
    have : u1 = u2 := Subtype.ext (h11.symm.trans h21)
    subst this
    exact h12.trans h22.symm
  · intro v hv
    obtain ⟨u, hu⟩ := hg ⟨v, hv⟩
    exact ⟨u.1, u.2, (hf₀ _ _).mpr ⟨u, rfl, by rw [hu]⟩⟩

namespace RelWitness

variable {α : Ordinal.{u}} {Y : ZFSet.{u}} {c : Cardinal.{u}} (w : RelWitness c.ord α Y)

/-! ### Finite ordinals -/

theorem jOrd_zero : w.jOrd 0 = 0 := by
  have h0 : (0 : Ordinal.{u}) < c.ord := lt_of_le_of_lt zero_le w.crit_lt
  by_contra hne
  have hpos : 0 < w.jOrd 0 := pos_iff_ne_zero.mpr hne
  have hex : ∃ t, t ∈ w.jv (w.ordX 0 h0) :=
    ⟨ordZ 0, by rw [jv_ordX]; exact Ordinal.toZFSet_mem_toZFSet_iff.mpr hpos⟩
  obtain ⟨t, ht⟩ := (w.nonempty_iff _).mpr hex
  have ht' : t ∈ (∅ : ZFSet.{u}) := by
    rw [← Ordinal.toZFSet_zero]
    exact ht
  exact ZFSet.notMem_empty t ht'

theorem jOrd_add_one {ξ : Ordinal.{u}} (h : ξ + 1 < c.ord) : w.jOrd (ξ + 1) = w.jOrd ξ + 1 := by
  have hξ : ξ < c.ord := lt_trans (Order.lt_add_one_iff.mpr le_rfl) h
  have h1 : (w.ordX (ξ + 1) h).1 = insert (w.ordX ξ hξ).1 (w.ordX ξ hξ).1 :=
    Ordinal.toZFSet_add_one ξ
  have h2 := (w.insert_iff _ _ _).mp h1
  rw [jv_ordX, jv_ordX, ← Ordinal.toZFSet_add_one] at h2
  exact ordZ_inj h2

theorem omega_le_lam (hc : ℵ₀ ≤ c) : ω ≤ c.ord := by
  rw [← Cardinal.ord_aleph0]
  exact Cardinal.ord_le_ord.mpr hc

theorem jOrd_nat (hc : ℵ₀ ≤ c) (n : ℕ) : w.jOrd (n : Ordinal.{u}) = n := by
  induction n with
  | zero => simpa using w.jOrd_zero
  | succ n ih =>
    have hlt : ((n : Ordinal.{u}) + 1) < c.ord := by
      have := Ordinal.natCast_lt_omega0 (n + 1)
      rw [Nat.cast_succ] at this
      exact this.trans_le (omega_le_lam hc)
    rw [Nat.cast_succ, w.jOrd_add_one hlt, ih]

/-- The critical point is infinite. -/
theorem omega_le_crit (hc : ℵ₀ ≤ c) : ω ≤ w.crit := by
  by_contra h
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (not_le.mp h)
  exact w.jOrd_crit_ne (by rw [hn, w.jOrd_nat hc])

include w in
/-- **An exacting cardinal is uncountable.** -/
theorem aleph0_lt (hc : ℵ₀ ≤ c) : ℵ₀ < c := by
  have h : ω < c.ord := (w.omega_le_crit hc).trans_lt w.crit_lt
  have := Cardinal.lt_ord.mp h
  rwa [Ordinal.card_omega0] at this

/-! ### Subsets of small ordinals are fixed -/

theorem jv_subset_fixed (x : Str w.X Y) {μ : Ordinal.{u}} (hμ : μ < w.crit)
    (hx : x.1 ⊆ ordZ μ) : w.jv x = x.1 := by
  have hμlam : μ < c.ord := hμ.trans w.crit_lt
  have h1 : x.1 = x.1 ∩ (w.ordX μ hμlam).1 := by
    ext t
    rw [mem_inter]
    exact ⟨fun ht => ⟨ht, hx ht⟩, fun ht => ht.1⟩
  have h2 := (w.inter_iff x x (w.ordX μ hμlam)).mp h1
  rw [jv_ordX, w.jOrd_of_lt_crit hμ] at h2
  ext y
  constructor
  · intro hy
    rw [h2] at hy
    obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (mem_inter.mp hy).2
    have hfix := w.jOrd_of_lt_crit (hξ.trans hμ)
    have := (w.ord_mem_iff (hξ.trans hμlam) x).mpr (by rw [hfix]; exact (mem_inter.mp hy).1)
    exact this
  · intro hy
    obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp (hx hy)
    have hfix := w.jOrd_of_lt_crit (hξ.trans hμ)
    have := (w.ord_mem_iff (hξ.trans hμlam) x).mp hy
    rwa [hfix] at this

/-! ### The critical point is a strong limit -/

theorem pow_iff (p m : Str w.X Y) :
    p.1 = powerset m.1 ↔ w.jv p = powerset (w.jv m) := by
  have hA := isTransitive_vonNeumann α
  have hsub : ∀ y ∈ V_ α, ∀ t, t ⊆ y → t ∈ V_ α := fun y hy t ht => subset_mem_V ht hy
  have h := w.elem (powF 0 1) (scons p (fun _ => m))
  rw [powF_spec hA hsub, powF_spec hA hsub] at h
  exact h

theorem sl_iff (hα : ∀ a < α, a + 1 < α) (k : Str w.X Y) :
    SLSem (V_ α) k.1 ↔ SLSem (V_ α) (w.jv k) := by
  have hA := isTransitive_vonNeumann α
  have hP := pairClosed_vonNeumann hα
  have hsub : ∀ y ∈ V_ α, ∀ t, t ⊆ y → t ∈ V_ α := fun y hy t ht => subset_mem_V ht hy
  have hpow : ∀ y ∈ V_ α, powerset y ∈ V_ α := fun y hy => powerset_mem_V hα hy
  have h := w.elem (slF 0) (fun _ => k)
  rw [slF_spec hA hP hsub hpow, slF_spec hA hP hsub hpow] at h
  exact h

theorem powerset_ord_mem_V (hc : ℵ₀ ≤ c) {μ : Ordinal.{u}} (hμ : μ < c.ord) :
    powerset (ordZ μ) ∈ V_ c.ord :=
  powerset_mem_V (limit_ord hc) (ordZ_mem_V hμ)

/-- No function in `V_ α` maps `𝒫(μ)` onto the critical point, for `μ < κ`. -/
theorem no_surj_pow_crit (hc : ℵ₀ ≤ c) (hα : ∀ a < α, a + 1 < α) :
    SLSem (V_ α) (ordZ w.crit) := by
  intro μz hμz hex
  obtain ⟨μ, hμ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hμz
  have hlamα := w.lam_lt_height
  have hμlam : μ < c.ord := hμ.trans w.crit_lt
  let pX : Str w.X Y := ⟨powerset (ordZ μ), w.base (powerset_ord_mem_V hc hμlam)⟩
  let kX : Str w.X Y := w.ordX w.crit w.crit_lt
  obtain ⟨fX, hsX⟩ := w.surj_in_X hα pX kX hex
  have hsJ := (w.surj_iff hα fX pX kX).mp hsX
  have hpJ : w.jv pX = powerset (ordZ μ) := by
    have := (w.pow_iff pX (w.ordX μ hμlam)).mp rfl
    rwa [jv_ordX, w.jOrd_of_lt_crit hμ] at this
  have hkJ : w.jv kX = ordZ (w.jOrd w.crit) := w.jv_ordX w.crit_lt
  rw [hpJ, hkJ] at hsJ
  -- `κ ∈ j(κ)` is a value of `j(f)`
  obtain ⟨u, hu, hp⟩ := hsJ.2.2 (ordZ w.crit)
    (Ordinal.toZFSet_mem_toZFSet_iff.mpr w.crit_lt_jOrd)
  have hsX' : SurjSem (V_ α) fX.1 (powerset (ordZ μ)) (ordZ w.crit) := hsX
  obtain ⟨v, hv, hp'⟩ := hsX'.1 u hu
  obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hv
  have huV : u ∈ V_ c.ord :=
    (isTransitive_vonNeumann _).subset_of_mem (powerset_ord_mem_V hc hμlam) hu
  let uX : Str w.X Y := ⟨u, w.base huV⟩
  have hζlam : ζ < c.ord := hζ.trans w.crit_lt
  have hp'' := (w.pair_mem_iff hα uX (w.ordX ζ hζlam) fX).mp hp'
  rw [w.jv_subset_fixed uX hμ (mem_powerset.mp hu), jv_ordX, w.jOrd_of_lt_crit hζ] at hp''
  have huA : u ∈ V_ α := w.X_sub uX.2
  have heq : ordZ w.crit = ordZ ζ :=
    hsJ.2.1 u huA (ordZ w.crit) (ordZ_mem_V (w.crit_lt.trans hlamα))
      (ordZ ζ) (ordZ_mem_V (hζlam.trans hlamα)) hp hp''
  exact absurd (ordZ_inj heq) (ne_of_gt hζ)

/-- The same for every point of the critical sequence, by elementarity. -/
theorem slSem_critSeq (hc : ℵ₀ ≤ c) (hα : ∀ a < α, a + 1 < α) (n : ℕ) :
    SLSem (V_ α) (ordZ (w.critSeq n)) := by
  induction n with
  | zero => exact w.no_surj_pow_crit hc hα
  | succ n ih =>
    have h := (w.sl_iff hα (w.ordX _ (w.critSeq_lt n))).mp ih
    rw [jv_ordX] at h
    rw [critSeq, Function.iterate_succ_apply']
    exact h

include w in
/-- **An exacting cardinal is a strong limit.** -/
theorem strongLimit (hc : ℵ₀ ≤ c) (hα : ∀ a < α, a + 1 < α) :
    ∀ μ < c, (2 : Cardinal.{u}) ^ μ < c := by
  intro μ hμ
  have hlamα := w.lam_lt_height
  have hμord : μ.ord < c.ord := Cardinal.ord_lt_ord.mpr hμ
  obtain ⟨n, hn⟩ := Published.critSeq_cofinal c hc w μ.ord hμord
  have hκlam := w.critSeq_lt n
  by_contra hcon
  -- otherwise `|κ_n| ≤ 2^μ`, and a surjection `𝒫(μ) → κ_n` exists in `V_ α`
  have hle : (w.critSeq n).card ≤ (2 : Cardinal.{u}) ^ μ := by
    by_contra h2
    exact hcon ((not_le.mp h2).trans (Cardinal.lt_ord.mp hκlam))
  have hcard : ZFSet.card (ordZ (w.critSeq n)) ≤ ZFSet.card (powerset (ordZ μ.ord)) := by
    rw [card_powerset, card_toZFSet, card_toZFSet, card_ord]
    exact hle
  have hne : (ordZ (w.critSeq n)).Nonempty :=
    ⟨ordZ 0, Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_of_le_of_lt zero_le hn)⟩
  have hex := exists_surj_of_card_le hc hlamα (powerset (ordZ μ.ord)) (ordZ (w.critSeq n))
    (fun t ht => (isTransitive_vonNeumann _).subset_of_mem (powerset_ord_mem_V hc hμord) ht)
    (fun t ht => by
      obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      exact ordZ_mem_V (hξ.trans hκlam)) hne hcard
  exact w.slSem_critSeq hc hα n (ordZ μ.ord) (Ordinal.toZFSet_mem_toZFSet_iff.mpr hn) hex

end RelWitness

end Cardinals
