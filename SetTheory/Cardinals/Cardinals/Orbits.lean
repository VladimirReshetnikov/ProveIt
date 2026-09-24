/-
  ORBIT CLASSES OF AN ULTRAEXACTING WITNESS (synthesis Lemma 12.1, Theorem 12.3,
  Corollary 12.4(1), Theorem 13.2), for the actual embedding.

  `w : RelWitness c.ord α Y` is an exacting witness at `λ = c.ord` of limit height;
  `w.IsUltra` says that (the graph of) `j ↾ V_λ` belongs to `X`.

  * `orb r = {j^n(r) : n < ω}`; `orb_mem_X`: every orbit belongs to `X` (it is the least
    set containing `r` and closed under `j ↾ V_λ ∈ X`);
  * `jv_eq_image`: `j(a) = j '' a` for every `a ∈ X`, `a ⊆ λ`, all of whose proper
    initial segments are finite -- proved through finite pieces `a ∩ κ_n ∈ V_λ`, with no
    enumeration of `a`;
  * `jv_orb`: `j(orb r) = orb (j r)`, i.e. `orb r` minus its first point;
  * `zero_or_full` (Theorem 12.3 / Corollary 12.4(1) for fixed sets): if `T ∈ X`,
    `j(T) = T`, and the members of `T` are countable cofinal subsets of `λ`, then the
    set of members of `T` that agree eventually with `orb r` is empty or has size `≥ λ`;
  * `tail_decision`, `regressive_const` (Theorem 13.2): a fixed set contains all or none
    of an orbit; a fixed relation that sends `κ` below `κ` sends the whole critical
    sequence to the same value.

  Nothing is admitted in this file.
-/
import Cardinals.FixedSets
import Cardinals.Below

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

theorem mem_V_of_subset_mem {x y : ZFSet.{u}} {α : Ordinal.{u}} (h : x ⊆ y) (hy : y ∈ V_ α) :
    x ∈ V_ α := by
  rw [mem_vonNeumann] at *
  refine lt_of_le_of_lt ?_ hy
  rw [rank_le_iff]
  intro z hz
  exact rank_lt_of_mem (h hz)

theorem ordZ_subset_of_le {a b : Ordinal.{u}} (h : a ≤ b) : ordZ a ⊆ ordZ b := by
  intro z hz
  obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hζ.trans_le h)

/-! ### Eventual agreement is an equivalence relation -/

theorem EvAgreeZ.symm {lam b a : ZFSet.{u}} (h : EvAgreeZ lam b a) : EvAgreeZ lam a b := by
  obtain ⟨η, hη, h⟩ := h
  exact ⟨η, hη, fun z hz hzη => (h z hz hzη).symm⟩

theorem EvAgreeZ.trans {lam : Ordinal.{u}} {a b d : ZFSet.{u}}
    (h₁ : EvAgreeZ (ordZ lam) a b) (h₂ : EvAgreeZ (ordZ lam) b d) : EvAgreeZ (ordZ lam) a d := by
  obtain ⟨η₁, hη₁, h₁⟩ := h₁
  obtain ⟨η₂, hη₂, h₂⟩ := h₂
  obtain ⟨ξ₁, hξ₁, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hη₁
  obtain ⟨ξ₂, hξ₂, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hη₂
  refine ⟨ordZ (max ξ₁ ξ₂), Ordinal.toZFSet_mem_toZFSet_iff.mpr (max_lt hξ₁ hξ₂),
    fun z hz hzη => ?_⟩
  have n1 : z ∉ ordZ ξ₁ := fun hh => hzη (ordZ_subset_of_le (le_max_left _ _) hh)
  have n2 : z ∉ ordZ ξ₂ := fun hh => hzη (ordZ_subset_of_le (le_max_right _ _) hh)
  exact (h₁ z hz n1).trans (h₂ z hz n2)

namespace RelWitness

variable {α : Ordinal.{u}} {Y : ZFSet.{u}} {c : Cardinal.{u}} (w : RelWitness c.ord α Y)

/-- The witness is *ultraexacting*: the graph of `j ↾ V_λ` is an element of `X`. -/
def IsUltra : Prop :=
  ∃ e : Str w.X Y, ∀ p, p ∈ e.1 ↔
    ∃ (x : ZFSet.{u}) (h : x ∈ V_ c.ord), p = pair x (w.jv ⟨x, w.base h⟩)

theorem ultra_pair {e : Str w.X Y}
    (he : ∀ p, p ∈ e.1 ↔ ∃ (x : ZFSet.{u}) (h : x ∈ V_ c.ord), p = pair x (w.jv ⟨x, w.base h⟩))
    {ξ : Ordinal.{u}} (hξ : ξ < c.ord) (v : ZFSet.{u}) :
    pair (ordZ ξ) v ∈ e.1 ↔ v = ordZ (w.jOrd ξ) := by
  rw [he]
  constructor
  · rintro ⟨x, h, hp⟩
    obtain ⟨h1, h2⟩ := pair_inj.mp hp
    subst h1
    rw [h2]
    exact w.jv_ordX hξ
  · rintro rfl
    exact ⟨ordZ ξ, ordZ_mem_V hξ, by rw [← w.jv_ordX hξ]; rfl⟩

/-! ### Orbits -/

/-- The forward orbit of `r` as a sequence. -/
noncomputable def orbSeq (r : Ordinal.{u}) (n : ℕ) : Ordinal.{u} := w.jOrd^[n] r

/-- The forward orbit of `r` as a set. -/
noncomputable def orb (r : Ordinal.{u}) : ZFSet.{u} := seqSet (w.orbSeq r)

theorem orbSeq_succ (r : Ordinal.{u}) (n : ℕ) : w.orbSeq r (n + 1) = w.jOrd (w.orbSeq r n) :=
  Function.iterate_succ_apply' _ _ _

theorem orbSeq_shift (r : Ordinal.{u}) (n : ℕ) : w.orbSeq r (n + 1) = w.orbSeq (w.jOrd r) n :=
  Function.iterate_succ_apply _ _ _

theorem orbSeq_lt {r : Ordinal.{u}} (hr : r < c.ord) (n : ℕ) : w.orbSeq r n < c.ord := by
  induction n with
  | zero => exact hr
  | succ n ih => rw [orbSeq_succ]; exact w.jOrd_lt ih

theorem le_orbSeq {r : Ordinal.{u}} (hr : r < c.ord) (n : ℕ) : r ≤ w.orbSeq r n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [orbSeq_succ]; exact ih.trans (w.le_jOrd (w.orbSeq_lt hr n))

theorem critSeq_le_orbSeq {r : Ordinal.{u}} (hκ : w.crit ≤ r) (hr : r < c.ord) (n : ℕ) :
    w.critSeq n ≤ w.orbSeq r n := by
  induction n with
  | zero => exact hκ
  | succ n ih =>
    rw [orbSeq_succ, critSeq, Function.iterate_succ_apply']
    exact w.jOrd_mono ih (w.orbSeq_lt hr n)

theorem orbSeq_strictMono (hc : ℵ₀ ≤ c) {r : Ordinal.{u}} (hκ : w.crit ≤ r) (hr : r < c.ord) :
    StrictMono (w.orbSeq r) := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  rw [orbSeq_succ]
  exact w.moved hc (hκ.trans (w.le_orbSeq hr n)) (w.orbSeq_lt hr n)

theorem mem_orb {r : Ordinal.{u}} {x : ZFSet.{u}} : x ∈ w.orb r ↔ ∃ n, ordZ (w.orbSeq r n) = x :=
  mem_seqSet

theorem orb_subset {r : Ordinal.{u}} (hr : r < c.ord) : w.orb r ⊆ ordZ c.ord := by
  intro x hx
  obtain ⟨n, rfl⟩ := w.mem_orb.mp hx
  exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (w.orbSeq_lt hr n)

theorem cofinalIn_orb (hc : ℵ₀ ≤ c) {r : Ordinal.{u}} (hκ : w.crit ≤ r) (hr : r < c.ord) :
    CofinalIn (w.orb r) c.ord := by
  refine ⟨subOrd_iff_subset.mpr (w.orb_subset hr), fun ξ hξ => ?_⟩
  obtain ⟨n, hn⟩ := Published.critSeq_cofinal c hc w ξ hξ
  exact ⟨w.orbSeq r n, (hn.le).trans (w.critSeq_le_orbSeq hκ hr n), w.orbSeq_lt hr n,
    w.mem_orb.mpr ⟨n, rfl⟩⟩

theorem card_orb_le (r : Ordinal.{u}) : ZFSet.card (w.orb r) ≤ ℵ₀ := card_seqSet_le _

/-- Proper initial segments of an orbit are finite. -/
theorem orb_locally_finite (hc : ℵ₀ ≤ c) {r : Ordinal.{u}} (hκ : w.crit ≤ r) (hr : r < c.ord)
    (η : Ordinal.{u}) (hη : η < c.ord) : {ξ | ξ < η ∧ ordZ ξ ∈ w.orb r}.Finite := by
  obtain ⟨N, hN⟩ := Published.critSeq_cofinal c hc w η hη
  refine ((Set.finite_lt_nat N).image (w.orbSeq r)).subset ?_
  rintro ξ ⟨hξη, hξ⟩
  obtain ⟨n, hn⟩ := w.mem_orb.mp hξ
  have hn' : w.orbSeq r n = ξ := ordZ_inj hn
  refine ⟨n, ?_, hn'⟩
  by_contra hcon
  have h1 : w.orbSeq r N ≤ w.orbSeq r n := (w.orbSeq_strictMono hc hκ hr).monotone (not_lt.mp hcon)
  have h2 : η < w.orbSeq r n := hN.trans_le ((w.critSeq_le_orbSeq hκ hr N).trans h1)
  rw [hn'] at h2
  exact lt_asymm h2 hξη

/-- **Every orbit belongs to `X`** (synthesis Lemma 12.1(2), first half). -/
theorem orb_mem_X (hU : w.IsUltra) (hα : ∀ a < α, a + 1 < α) {r : Ordinal.{u}}
    (hr : r < c.ord) : ∃ d : Str w.X Y, d.1 = w.orb r := by
  have hA := isTransitive_vonNeumann α
  have hP := pairClosed_vonNeumann hα
  have hlamα := w.lam_lt_height
  obtain ⟨e, he⟩ := hU
  have horbA : w.orb r ∈ V_ α :=
    mem_V_of_subset (fun t ht => ordZ_subset_V _ (w.orb_subset hr ht)) hlamα
  -- the orbit is the least closed set
  have hall : ∀ n : ℕ, ∀ b ∈ V_ α, ClosedSem (V_ α) b (ordZ r) e.1 →
      ordZ (w.orbSeq r n) ∈ b := by
    intro n
    induction n with
    | zero => exact fun b _ hcl => hcl.1
    | succ n ih =>
      intro b hb hcl
      refine hcl.2 _ (ih b hb hcl) _
        (ordZ_mem_V ((w.orbSeq_lt hr (n + 1)).trans hlamα)) ?_
      rw [w.ultra_pair he (w.orbSeq_lt hr n), orbSeq_succ]
  have hchar : ∀ z ∈ V_ α, z ∈ w.orb r ↔
      ∀ b ∈ V_ α, ClosedSem (V_ α) b (ordZ r) e.1 → z ∈ b := by
    intro z _
    constructor
    · intro hz b hb hcl
      obtain ⟨n, rfl⟩ := w.mem_orb.mp hz
      exact hall n b hb hcl
    · intro h
      refine h (w.orb r) horbA ⟨w.mem_orb.mpr ⟨0, rfl⟩, fun u hu v _ hp => ?_⟩
      obtain ⟨n, rfl⟩ := w.mem_orb.mp hu
      rw [w.ultra_pair he (w.orbSeq_lt hr n)] at hp
      exact w.mem_orb.mpr ⟨n + 1, by rw [hp, orbSeq_succ]⟩
  obtain ⟨d, hd, -⟩ := w.definable (orbF 0 1 2) (scons (w.ordX r hr) (fun _ => e))
    ⟨w.orb r, horbA⟩ ((orbF_spec hA hP _ 0 1 2).mpr hchar)
    (fun y hy => by
      have hy' := (orbF_spec hA hP _ 0 1 2).mp hy
      apply Subtype.ext
      show y.1 = w.orb r
      ext z
      constructor
      · intro hz
        have hzA := hA.subset_of_mem y.2 hz
        exact (hchar z hzA).mpr ((hy' z hzA).mp hz)
      · intro hz
        have hzA := hA.subset_of_mem horbA hz
        exact (hy' z hzA).mpr ((hchar z hzA).mp hz))
  exact ⟨d, congrArg Subtype.val hd⟩

/-! ### `j(a) = j '' a` for locally finite `a ⊆ λ` -/

/-- `j` of a finite set of ordinals below `λ` is its pointwise image. -/
theorem jv_finite (s : Finset Ordinal.{u}) :
    ∀ (η : Ordinal.{u}), η < c.ord → ∀ b : Str w.X Y,
      (∀ x, x ∈ b.1 ↔ ∃ ξ ∈ s, x = ordZ ξ) → (∀ ξ ∈ s, ξ < η) →
      ∀ y, y ∈ w.jv b ↔ ∃ ξ ∈ s, y = ordZ (w.jOrd ξ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro η _ b hb _ y
    constructor
    · intro hy
      obtain ⟨t, ht⟩ := (w.nonempty_iff b).mpr ⟨y, hy⟩
      obtain ⟨ξ, hξ, -⟩ := (hb t).mp ht
      exact absurd hξ (Finset.notMem_empty ξ)
    · rintro ⟨ξ, hξ, -⟩
      exact absurd hξ (Finset.notMem_empty ξ)
  | insert ξ₀ s hξ₀ ih =>
    intro η hη b hb hlt y
    have hξ₀η : ξ₀ < η := hlt ξ₀ (Finset.mem_insert_self _ _)
    let b' : ZFSet.{u} := ZFSet.sep (fun x => ∃ ξ ∈ s, x = ordZ ξ) b.1
    have hb'mem : ∀ x, x ∈ b' ↔ ∃ ξ ∈ s, x = ordZ ξ := by
      intro x
      rw [mem_sep]
      constructor
      · exact fun h => h.2
      · rintro ⟨ξ, hξ, rfl⟩
        exact ⟨(hb _).mpr ⟨ξ, Finset.mem_insert_of_mem hξ, rfl⟩, ξ, hξ, rfl⟩
    have hb'V : b' ∈ V_ c.ord := by
      refine mem_V_of_subset (β := η) (fun x hx => ?_) hη
      obtain ⟨ξ, hξ, rfl⟩ := (hb'mem x).mp hx
      exact ordZ_mem_V (hlt ξ (Finset.mem_insert_of_mem hξ))
    let b'X : Str w.X Y := ⟨b', w.base hb'V⟩
    have hins : b.1 = insert (w.ordX ξ₀ (hξ₀η.trans hη)).1 b'X.1 := by
      ext x
      rw [mem_insert_iff, hb x]
      constructor
      · rintro ⟨ξ, hξ, rfl⟩
        rcases Finset.mem_insert.mp hξ with rfl | hξ
        · exact Or.inl rfl
        · exact Or.inr ((hb'mem _).mpr ⟨ξ, hξ, rfl⟩)
      · rintro (rfl | hx)
        · exact ⟨ξ₀, Finset.mem_insert_self _ _, rfl⟩
        · obtain ⟨ξ, hξ, rfl⟩ := (hb'mem x).mp hx
          exact ⟨ξ, Finset.mem_insert_of_mem hξ, rfl⟩
    have hj := (w.insert_iff b _ b'X).mp hins
    rw [jv_ordX] at hj
    have ih' := ih η hη b'X hb'mem (fun ξ hξ => hlt ξ (Finset.mem_insert_of_mem hξ)) y
    rw [hj, mem_insert_iff, ih']
    constructor
    · rintro (rfl | ⟨ξ, hξ, rfl⟩)
      · exact ⟨ξ₀, Finset.mem_insert_self _ _, rfl⟩
      · exact ⟨ξ, Finset.mem_insert_of_mem hξ, rfl⟩
    · rintro ⟨ξ, hξ, rfl⟩
      rcases Finset.mem_insert.mp hξ with rfl | hξ
      · exact Or.inl rfl
      · exact Or.inr ⟨ξ, hξ, rfl⟩

/-- **`j(a) = j '' a`** for `a ∈ X`, `a ⊆ λ`, with finite proper initial segments. -/
theorem jv_eq_image (hc : ℵ₀ ≤ c) (a : Str w.X Y) (ha : a.1 ⊆ ordZ c.ord)
    (hfin : ∀ η < c.ord, {ξ | ξ < η ∧ ordZ ξ ∈ a.1}.Finite) (y : ZFSet.{u}) :
    y ∈ w.jv a ↔ ∃ ξ, ordZ ξ ∈ a.1 ∧ y = ordZ (w.jOrd ξ) := by
  classical
  constructor
  · intro hy
    -- `j(a) ⊆ λ`
    have h1 : a.1 = a.1 ∩ w.lamX.1 := by
      ext x
      rw [mem_inter]
      exact ⟨fun hx => ⟨hx, ha hx⟩, fun hx => hx.1⟩
    have h2 := (w.inter_iff a a w.lamX).mp h1
    rw [jv_lamX] at h2
    have hylam : y ∈ ordZ c.ord := by
      rw [h2] at hy
      exact (mem_inter.mp hy).2
    obtain ⟨υ, hυ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hylam
    obtain ⟨n, hn⟩ := Published.critSeq_cofinal c hc w υ hυ
    have hη : w.critSeq n < c.ord := w.critSeq_lt n
    -- the finite piece `a ∩ κ_n`
    let b : ZFSet.{u} := a.1 ∩ ordZ (w.critSeq n)
    have hbV : b ∈ V_ c.ord :=
      mem_V_of_subset (β := w.critSeq n)
        (fun x hx => ordZ_subset_V _ (mem_inter.mp hx).2) hη
    let bX : Str w.X Y := ⟨b, w.base hbV⟩
    have h3 := (w.inter_iff bX a (w.ordX _ hη)).mp rfl
    rw [jv_ordX] at h3
    have hyb : ordZ υ ∈ w.jv bX := by
      rw [h3, mem_inter]
      exact ⟨hy, Ordinal.toZFSet_mem_toZFSet_iff.mpr (hn.trans_le (w.le_jOrd hη))⟩
    have hbmem : ∀ x, x ∈ bX.1 ↔ ∃ ξ ∈ (hfin _ hη).toFinset, x = ordZ ξ := by
      intro x
      show x ∈ a.1 ∩ ordZ (w.critSeq n) ↔ _
      rw [mem_inter]
      constructor
      · rintro ⟨hxa, hxη⟩
        obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hxη
        exact ⟨ξ, (Set.Finite.mem_toFinset _).mpr ⟨hξ, hxa⟩, rfl⟩
      · rintro ⟨ξ, hξ, rfl⟩
        obtain ⟨h4, h5⟩ := (Set.Finite.mem_toFinset _).mp hξ
        exact ⟨h5, Ordinal.toZFSet_mem_toZFSet_iff.mpr h4⟩
    obtain ⟨ξ, hξ, hyξ⟩ := (w.jv_finite _ _ hη bX hbmem
      (fun ξ hξ => ((Set.Finite.mem_toFinset _).mp hξ).1) _).mp hyb
    exact ⟨ξ, ((Set.Finite.mem_toFinset _).mp hξ).2, hyξ⟩
  · rintro ⟨ξ, hξ, rfl⟩
    exact (w.ord_mem_iff (Ordinal.toZFSet_mem_toZFSet_iff.mp (ha hξ)) a).mp hξ

/-- **`j(orb r) = orb (j r)`** (synthesis Lemma 12.1(2)): the orbit minus its first
point. -/
theorem jv_orb (hc : ℵ₀ ≤ c) {r : Ordinal.{u}} (hκ : w.crit ≤ r) (hr : r < c.ord)
    (d : Str w.X Y) (hd : d.1 = w.orb r) : w.jv d = w.orb (w.jOrd r) := by
  ext y
  rw [w.jv_eq_image hc d (hd ▸ w.orb_subset hr)
    (fun η hη => hd ▸ w.orb_locally_finite hc hκ hr η hη), mem_orb]
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    rw [hd] at hξ
    obtain ⟨n, hn⟩ := w.mem_orb.mp hξ
    exact ⟨n, by rw [← orbSeq_shift, orbSeq_succ, ordZ_inj hn]⟩
  · rintro ⟨n, rfl⟩
    refine ⟨w.orbSeq r n, hd ▸ w.mem_orb.mpr ⟨n, rfl⟩, ?_⟩
    rw [← orbSeq_shift, orbSeq_succ]

/-- An orbit and its shift agree above the first point. -/
theorem evAgree_orb_shift (hc : ℵ₀ ≤ c) {r : Ordinal.{u}} (hr : r < c.ord) :
    EvAgreeZ (ordZ c.ord) (w.orb (w.jOrd r)) (w.orb r) := by
  refine ⟨ordZ (r + 1), Ordinal.toZFSet_mem_toZFSet_iff.mpr (limit_ord hc r hr),
    fun z hz hzr => ?_⟩
  obtain ⟨ξ, -, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
  have hξ : r < ξ := by
    by_contra hcon
    exact hzr (Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (lt_of_le_of_lt (not_lt.mp hcon) (Order.lt_add_one_iff.mpr le_rfl)))
  rw [mem_orb, mem_orb]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by rw [orbSeq_shift]; exact hn⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      have : r = ξ := ordZ_inj hn
      exact absurd this (ne_of_lt hξ)
    | succ n => exact ⟨n, by rw [← orbSeq_shift]; exact hn⟩

/-! ### Zero-or-full traces -/

/-- `j` preserves "`i` is the set of members of `T` agreeing eventually with `a`". -/
theorem agree_iff (i T a : Str w.X Y) :
    i.1 = ZFSet.sep (fun b => EvAgreeZ w.lamX.1 b a.1) T.1 ↔
      w.jv i = ZFSet.sep (fun b => EvAgreeZ (w.jv w.lamX) b (w.jv a)) (w.jv T) := by
  have hA := isTransitive_vonNeumann α
  have h := w.elem (agreeF 0 1 2 3) (scons i (scons T (scons a (fun _ => w.lamX))))
  rw [agreeF_spec hA, agreeF_spec hA] at h
  exact h

/-- The set of members of `T ∈ X` agreeing eventually with `a ∈ X` belongs to `X`. -/
theorem agree_in_X (T a : Str w.X Y) :
    ∃ d : Str w.X Y, d.1 = ZFSet.sep (fun b => EvAgreeZ w.lamX.1 b a.1) T.1 := by
  have hA := isTransitive_vonNeumann α
  have hFA : ZFSet.sep (fun b => EvAgreeZ w.lamX.1 b a.1) T.1 ∈ V_ α :=
    mem_V_of_subset_mem (fun b hb => (mem_sep.mp hb).1) (w.X_sub T.2)
  obtain ⟨d, hd⟩ := w.tarski_vaught (agreeF 0 1 2 3) (scons T (scons a (fun _ => w.lamX)))
    ⟨⟨_, hFA⟩, (agreeF_spec hA _ 0 1 2 3).mpr rfl⟩
  exact ⟨d, (agreeF_spec hA _ 0 1 2 3).mp hd⟩

/-- **Zero-or-full traces on an orbit class (synthesis Theorem 12.3, Corollary 12.4(1), for
sets fixed by the embedding).**  Let `T ∈ X` with `j(T) = T` consist of countable cofinal
subsets of `λ`, and let `r ∈ [κ, λ)`.  Then the set of members of `T` that agree
eventually with the orbit of `r` is empty or has cardinality at least `λ`. -/
theorem zero_or_full (hc : ℵ₀ < c) (hα : ∀ a < α, a + 1 < α) (hU : w.IsUltra)
    (T : Str w.X Y) (hT : w.jv T = T.1)
    (hTmem : ∀ b ∈ T.1, CofinalIn b c.ord ∧ ZFSet.card b ≤ ℵ₀)
    {r : Ordinal.{u}} (hκ : w.crit ≤ r) (hr : r < c.ord) :
    ZFSet.sep (fun b => EvAgreeZ (ordZ c.ord) b (w.orb r)) T.1 = ∅ ∨
      c ≤ ZFSet.card (ZFSet.sep (fun b => EvAgreeZ (ordZ c.ord) b (w.orb r)) T.1) := by
  obtain ⟨aX, haX⟩ := w.orb_mem_X hU hα hr
  obtain ⟨d, hd⟩ := w.agree_in_X T aX
  have hd1 : d.1 = ZFSet.sep (fun b => EvAgreeZ (ordZ c.ord) b (w.orb r)) T.1 := by
    rw [hd, haX]
    rfl
  have hjd := (w.agree_iff d T aX).mp hd
  rw [jv_lamX, w.jv_orb hc.le hκ hr aX haX, hT] at hjd
  have hfix : w.jv d = d.1 := by
    rw [hjd, hd1]
    ext b
    rw [mem_sep, mem_sep]
    exact and_congr Iff.rfl ⟨fun h => h.trans (w.evAgree_orb_shift hc.le hr),
      fun h => h.trans (w.evAgree_orb_shift hc.le hr).symm⟩
  rw [← hd1]
  by_cases hsmall : ZFSet.card d.1 < c
  · left
    exact w.no_small_fixed_family hc.le hα d hfix ℵ₀ hc
      (fun b hb => hTmem b (mem_sep.mp (hd1 ▸ hb)).1) hsmall
  · right
    exact not_lt.mp hsmall

/-! ### Tail decisions (synthesis Theorem 13.2) -/

/-- A fixed set contains the whole orbit of `r` or none of it. -/
theorem tail_decision (A : Str w.X Y) (hA : w.jv A = A.1) {r : Ordinal.{u}} (hr : r < c.ord)
    (n : ℕ) : ordZ (w.orbSeq r n) ∈ A.1 ↔ ordZ r ∈ A.1 := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    rw [orbSeq_succ, ← ih]
    have := w.ord_mem_iff (w.orbSeq_lt hr n) A
    rw [hA] at this
    exact this.symm

/-- **Normality.**  A fixed relation `f` that relates the critical point `κ` to some
`β < κ` relates every point of the critical sequence to the same `β`. -/
theorem regressive_const (hα : ∀ a < α, a + 1 < α) (f : Str w.X Y) (hf : w.jv f = f.1)
    {β : Ordinal.{u}} (hβ : β < w.crit) (h0 : pair (ordZ w.crit) (ordZ β) ∈ f.1) (n : ℕ) :
    pair (ordZ (w.critSeq n)) (ordZ β) ∈ f.1 := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    have h := (w.pair_mem_iff hα (w.ordX _ (w.critSeq_lt n))
      (w.ordX β (hβ.trans w.crit_lt)) f).mp ih
    rw [jv_ordX, jv_ordX, w.jOrd_of_lt_crit hβ, hf] at h
    rw [critSeq, Function.iterate_succ_apply']
    exact h

end RelWitness

end Cardinals
