/-
  THE COVER BOUND IS AT LEAST `λ` (Blue–Goldberg, remark after Definition 3.1; synthesis
  Lemma 3.5), PROVED.

  If `λ` is `γ`-cover exacting then `λ ≤ γ`.  Formerly admitted as `Published.le_of_CEx`.
  The proof "refutes relativized exacting cardinals" as the notes say, but some care is
  needed because a countable cofinal `a ⊆ λ` is only an *element* of the covering
  predicate `Y`, not a subset of it:

  * `jOrd_omega`: `j(ω) = ω` (the set `ω` has no limit elements, a first-order property);
  * `trace_fixed_of`: for a fixed `p ∈ X`, the trace `Y ∩ p` is in `X` and fixed;
  * with `p = 𝒫(λ)` this makes `D = Y ∩ 𝒫(λ)` a fixed element of `X`; the union `T` of the
    members of `D` that are countable in `V_α` is definable from `D` and `ω`, hence fixed;
  * `|T| ≤ |Y| · ℵ₀ ≤ γ · ℵ₀ < λ` if `γ < λ`, while `a ⊆ T` makes `T` cofinal --
    contradicting `fixed_small_subset`.

  Nothing is admitted in this file.
-/
import Cardinals.ObservationOne

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal FirstOrder FirstOrder.Language
open SetTheory (Form Sat scons)
open SetTheory.Form

/-- A function onto `S` from `m` bounds the size of `S`. -/
theorem card_le_of_surjSem {A f m S : ZFSet.{u}} (hA : IsTransitive A) (hmA : m ∈ A)
    (hSA : S ∈ A) (h : SurjSem A f m S) : ZFSet.card S ≤ ZFSet.card m := by
  have hch : ∀ v : {x // x ∈ S}, ∃ u, u ∈ m ∧ pair u v.1 ∈ f := fun v => h.2.2 v.1 v.2
  choose g hg using hch
  have hinj : Function.Injective (fun v : {x // x ∈ S} => (⟨g v, (hg v).1⟩ : {x // x ∈ m})) := by
    intro v v' hvv'
    have hgv : g v = g v' := congrArg Subtype.val hvv'
    apply Subtype.ext
    exact h.2.1 (g v) (hA.subset_of_mem hmA (hg v).1) v.1 (hA.subset_of_mem hSA v.2)
      v'.1 (hA.subset_of_mem hSA v'.2) (hg v).2 (hgv ▸ (hg v').2)
  have := Cardinal.mk_le_of_injective hinj
  have hx : #{a // a ∈ S} = Cardinal.lift.{u + 1, u} (ZFSet.card S) := ZFSet.cardinalMk_coe_sort
  have hy : #{b // b ∈ m} = Cardinal.lift.{u + 1, u} (ZFSet.card m) := ZFSet.cardinalMk_coe_sort
  rw [hx, hy] at this
  exact Cardinal.lift_le.mp this

namespace RelWitness

section General

variable {lam α : Ordinal.{u}} {Y : ZFSet.{u}} (w : RelWitness lam α Y)

/-- **For a fixed `p ∈ X`, the trace `Y ∩ p` of the predicate is in `X` and fixed.** -/
theorem trace_fixed_of (p : Str w.X Y) (hp : w.jv p = p.1) :
    ∃ d : Str w.X Y, d.1 = Y ∩ p.1 ∧ w.jv d = Y ∩ p.1 := by
  have hA := isTransitive_vonNeumann α
  have hpA : p.1 ∈ V_ α := w.X_sub p.2
  have hTA : Y ∩ p.1 ∈ V_ α := subset_mem_V (fun t ht => (mem_inter.mp ht).2) hpA
  have hext : ∀ y : Carrier (V_ α),
      (∀ z : Str (V_ α) Y, z.1 ∈ y.1 ↔ (z.1 ∈ p.1 ∧ z.1 ∈ Y)) → y.1 = Y ∩ p.1 := by
    intro y hy
    ext t
    rw [mem_inter]
    constructor
    · intro ht
      have := (hy ⟨t, hA.subset_of_mem y.2 ht⟩).mp ht
      exact ⟨this.2, this.1⟩
    · rintro ⟨h1, h2⟩
      exact (hy ⟨t, hA.subset_of_mem hpA h2⟩).mpr ⟨h2, h1⟩
  let pV : Str (V_ α) Y := ⟨p.1, hpA⟩
  have hV : @BoundedFormula.Realize Lex (Str (V_ α) Y) _ _ _ ObsOne.traceExF
      (fun _ : Fin 1 => pV) default := by
    rw [ObsOne.realize_traceExF (V_ α) Y]
    refine ⟨(⟨Y ∩ p.1, hTA⟩ : Str (V_ α) Y), fun z => ?_⟩
    show z.1 ∈ Y ∩ p.1 ↔ _
    rw [mem_inter]
    exact and_comm
  have hX : ObsOne.traceExF.Realize (fun _ : Fin 1 => p) default := by
    have h := w.incl.map_boundedFormula ObsOne.traceExF (fun _ : Fin 1 => p) default
    refine h.mp ?_
    have e1 : (w.incl ∘ fun _ : Fin 1 => p) = fun _ : Fin 1 => pV := by
      funext i
      exact Subtype.ext (w.incl_val _)
    rw [e1, show (w.incl ∘ (default : Fin 0 → Str w.X Y)) = default from Subsingleton.elim _ _]
    exact hV
  rw [ObsOne.realize_traceExF w.X Y] at hX
  obtain ⟨d, hd⟩ := hX
  let v : Fin 2 → Str w.X Y := fun i => if i = 0 then d else p
  have hXd : ObsOne.traceF.Realize v default := by
    rw [ObsOne.realize_traceF w.X Y]
    exact hd
  refine ⟨d, ?_, ?_⟩
  · have h := (w.incl.map_boundedFormula ObsOne.traceF v default).mpr hXd
    rw [show (w.incl ∘ (default : Fin 0 → Str w.X Y)) = default from Subsingleton.elim _ _,
      ObsOne.realize_traceF (V_ α) Y] at h
    have h' : ∀ z : Str (V_ α) Y, z.1 ∈ (w.incl d).1 ↔ (z.1 ∈ (w.incl p).1 ∧ z.1 ∈ Y) := h
    rw [w.incl_val, w.incl_val] at h'
    exact hext ⟨d.1, w.X_sub d.2⟩ h'
  · have h := (w.j.map_boundedFormula ObsOne.traceF v default).mpr hXd
    rw [show (w.j ∘ (default : Fin 0 → Str w.X Y)) = default from Subsingleton.elim _ _,
      ObsOne.realize_traceF (V_ α) Y] at h
    have h' : ∀ z : Str (V_ α) Y, z.1 ∈ (w.j d).1 ↔ (z.1 ∈ (w.j p).1 ∧ z.1 ∈ Y) := h
    have hjp : (w.j p).1 = p.1 := hp
    rw [hjp] at h'
    exact hext (w.j d) h'

end General

variable {α : Ordinal.{u}} {Y : ZFSet.{u}} {c : Cardinal.{u}} (w : RelWitness c.ord α Y)

/-! ### `j(ω) = ω` -/

theorem noLimit_iff (x : Str w.X Y) : NoLimitSem x.1 ↔ NoLimitSem (w.jv x) := by
  have hA := isTransitive_vonNeumann α
  have h := w.elem (noLimitF 0) (fun _ => x)
  rw [noLimitF_spec hA, noLimitF_spec hA] at h
  exact h

include w in
theorem omega_lt_lam (hc : ℵ₀ ≤ c) : ω < c.ord := (w.omega_le_crit hc).trans_lt w.crit_lt

theorem noLimitSem_omega : NoLimitSem (ordZ (ω : Ordinal.{u})) := by
  intro y hy
  obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hy
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hξ
  cases n with
  | zero => left; simp
  | succ n =>
    right
    refine ⟨ordZ (n : Ordinal.{u}), Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n), ?_⟩
    rw [Nat.cast_succ]
    exact Ordinal.toZFSet_add_one _

theorem jOrd_omega (hc : ℵ₀ ≤ c) : w.jOrd ω = ω := by
  have hω := w.omega_lt_lam hc
  by_contra hne
  have hlt : ω < w.jOrd ω := lt_of_le_of_ne (w.le_jOrd hω) (Ne.symm hne)
  have h1 := (w.noLimit_iff (w.ordX ω hω)).mp noLimitSem_omega
  rw [jv_ordX] at h1
  rcases h1 (ordZ ω) (Ordinal.toZFSet_mem_toZFSet_iff.mpr hlt) with h0 | ⟨z, hz, hins⟩
  · have : ordZ (0 : Ordinal.{u}) ∈ ordZ (ω : Ordinal.{u}) :=
      Ordinal.toZFSet_mem_toZFSet_iff.mpr Ordinal.omega0_pos
    rw [h0] at this
    exact ZFSet.notMem_empty _ this
  · obtain ⟨ζ, -, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
    rw [← Ordinal.toZFSet_add_one] at hins
    have hζ : ω = ζ + 1 := ordZ_inj hins
    have hζlt : ζ < ω := by rw [hζ]; exact Order.lt_add_one_iff.mpr le_rfl
    have := Ordinal.isSuccLimit_omega0.succ_lt hζlt
    rw [Order.succ_eq_add_one, ← hζ] at this
    exact lt_irrefl _ this

/-! ### The union of the countable members of a fixed family -/

theorem cntUnion_iff (hα : ∀ a < α, a + 1 < α) (T D om : Str w.X Y) :
    T.1 = ⋃₀ (CntPart (V_ α) D.1 om.1) ↔ w.jv T = ⋃₀ (CntPart (V_ α) (w.jv D) (w.jv om)) := by
  have hA := isTransitive_vonNeumann α
  have hP := pairClosed_vonNeumann hα
  have h := w.elem (cntUnionF 0 1 2) (scons T (scons D (fun _ => om)))
  rw [cntUnionF_spec hA hP, cntUnionF_spec hA hP] at h
  exact h

theorem cntUnion_in_X (hα : ∀ a < α, a + 1 < α) (D om : Str w.X Y)
    (hTA : ⋃₀ (CntPart (V_ α) D.1 om.1) ∈ V_ α) :
    ∃ T : Str w.X Y, T.1 = ⋃₀ (CntPart (V_ α) D.1 om.1) := by
  have hA := isTransitive_vonNeumann α
  have hP := pairClosed_vonNeumann hα
  obtain ⟨d, hd⟩ := w.tarski_vaught (cntUnionF 0 1 2) (scons D (fun _ => om))
    ⟨⟨_, hTA⟩, (cntUnionF_spec hA hP _ 0 1 2).mpr rfl⟩
  exact ⟨d, (cntUnionF_spec hA hP _ 0 1 2).mp hd⟩

theorem pow_lam_fixed (hα : ∀ a < α, a + 1 < α) :
    ∃ p : Str w.X Y, p.1 = powerset (ordZ c.ord) ∧ w.jv p = powerset (ordZ c.ord) := by
  have hA := isTransitive_vonNeumann α
  have hsub : ∀ y ∈ V_ α, ∀ t, t ⊆ y → t ∈ V_ α := fun y hy t ht => subset_mem_V ht hy
  have hpA : powerset (ordZ c.ord) ∈ V_ α := powerset_mem_V hα (w.X_sub w.lam_mem)
  obtain ⟨d, hd⟩ := w.tarski_vaught (powF 0 1) (fun _ => w.lamX)
    ⟨⟨_, hpA⟩, (powF_spec hA hsub _ 0 1).mpr rfl⟩
  have hd1 : d.1 = powerset (ordZ c.ord) := (powF_spec hA hsub _ 0 1).mp hd
  refine ⟨d, hd1, ?_⟩
  have := (w.pow_iff d w.lamX).mp hd1
  rwa [jv_lamX] at this

end RelWitness

/-- **The cover bound is at least `λ`.** -/
theorem le_of_CEx (c γ : Cardinal.{u}) (hc : ℵ₀ ≤ c) (h : CEx γ c.ord) : c ≤ γ := by
  by_contra hcon
  have hγ : γ < c := not_le.mp hcon
  -- a limit height
  let α : Ordinal.{u} := c.ord + ω
  have hlim : Order.IsSuccLimit α := Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
  have hα : ∀ b < α, b + 1 < α := fun b hb => by simpa using hlim.succ_lt hb
  have hlamα : c.ord < α := (lt_add_iff_pos_right _).mpr Ordinal.omega0_pos
  have hA := isTransitive_vonNeumann α
  -- a first witness gives a countable cofinal set `a`
  obtain ⟨Y₀, -, ⟨w₀⟩⟩ := h.nonempty_witness hlamα
  have hc' : ℵ₀ < c := w₀.aleph0_lt hc
  let a : ZFSet.{u} := seqSet w₀.critSeq
  have hasub : a ⊆ ordZ c.ord := fun t ht => by
    obtain ⟨n, rfl⟩ := mem_seqSet.mp ht
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (w₀.critSeq_lt n)
  have haA : a ∈ V_ α := mem_V_of_subset (fun t ht => ordZ_subset_V _ (hasub ht)) hlamα
  -- cover `a`
  obtain ⟨Y, -, haY, hYcard, ⟨w⟩⟩ := h α hlamα a haA
  have hωlam : ω < c.ord := w.omega_lt_lam hc
  obtain ⟨p, hp, hjp⟩ := w.pow_lam_fixed hα
  obtain ⟨D, hD, hjD⟩ := w.trace_fixed_of p (hjp.trans hp.symm)
  rw [hp] at hD hjD
  let om : Str w.X Y := w.ordX ω hωlam
  have hjom : w.jv om = om.1 := by
    show w.jv (w.ordX ω hωlam) = ordZ ω
    rw [RelWitness.jv_ordX, w.jOrd_omega hc]
  -- the union of the countable members of `D`
  have hTsub : ⋃₀ (CntPart (V_ α) D.1 om.1) ⊆ ordZ c.ord := by
    intro z hz
    obtain ⟨t, ht, hzt⟩ := mem_sUnion.mp hz
    have htD : t ∈ D.1 := (mem_sep.mp ht).1
    rw [hD] at htD
    exact mem_powerset.mp (mem_inter.mp htD).2 hzt
  have hTA : ⋃₀ (CntPart (V_ α) D.1 om.1) ∈ V_ α :=
    mem_V_of_subset (fun t ht => ordZ_subset_V _ (hTsub ht)) hlamα
  obtain ⟨T, hT⟩ := w.cntUnion_in_X hα D om hTA
  have hjT : w.jv T = T.1 := by
    have := (w.cntUnion_iff hα T D om).mp hT
    rw [this, hT, hjD, hjom, hD]
  -- `a ⊆ T`
  have haCnt : a ∈ CntPart (V_ α) D.1 om.1 := by
    refine mem_sep.mpr ⟨?_, ?_⟩
    · rw [hD]
      exact mem_inter.mpr ⟨haY, mem_powerset.mpr hasub⟩
    · refine exists_surj_of_card_le hc hlamα (ordZ ω) a
        (fun t ht => by
          obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
          exact ordZ_mem_V (hξ.trans hωlam))
        (fun t ht => ordZ_subset_V _ (hasub ht))
        ⟨ordZ (w₀.critSeq 0), mem_seqSet.mpr ⟨0, rfl⟩⟩ ?_
      rw [card_toZFSet, Ordinal.card_omega0]
      exact card_seqSet_le _
  have haT : a ⊆ T.1 := fun t ht => hT ▸ mem_sUnion.mpr ⟨a, haCnt, ht⟩
  -- `|T| < λ`
  have hTcard : ZFSet.card T.1 < c := by
    rw [hT]
    have h1 : ∀ t ∈ CntPart (V_ α) D.1 om.1, ZFSet.card t ≤ ℵ₀ := by
      intro t ht
      obtain ⟨htD, f, -, hf⟩ := mem_sep.mp ht
      have htA : t ∈ V_ α := hA.subset_of_mem (w.X_sub D.2) htD
      have := card_le_of_surjSem hA (w.X_sub om.2) htA hf
      rwa [show om.1 = ordZ ω from rfl, card_toZFSet, Ordinal.card_omega0] at this
    have h2 : ZFSet.card (CntPart (V_ α) D.1 om.1) ≤ γ := by
      refine (card_mono (fun t ht => ?_)).trans hYcard
      have := (mem_sep.mp ht).1
      rw [hD] at this
      exact (mem_inter.mp this).1
    exact lt_of_le_of_lt ((card_sUnion_le _ ℵ₀ h1).trans (mul_le_mul' h2 le_rfl))
      (Cardinal.mul_lt_of_lt hc hγ hc')
  have hsmall := w.fixed_small_subset hc hα T (hT ▸ hTsub) hjT hTcard
  -- but `a`, hence `T`, is cofinal
  obtain ⟨n, hn⟩ := Published.critSeq_cofinal c hc w₀ w.crit w.crit_lt
  have : ordZ (w₀.critSeq n) ∈ ordZ w.crit := hsmall (haT (mem_seqSet.mpr ⟨n, rfl⟩))
  exact absurd (Ordinal.toZFSet_mem_toZFSet_iff.mp this) (not_lt.mpr hn.le)

end Cardinals
