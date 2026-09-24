/-
  WITNESSES OVER A TRANSITIVE SET MODEL (research note "Exacting embeddings of countable
  structures", Definitions 2.1 and 2.2).

  In Lean's `ZFSet` every function on a set is itself a set, so an embedding "that exists
  only in a forcing extension" cannot be modelled by a `RelWitness` (whose target is a rank
  `V_ α` of the ambient universe: there the Kunen inconsistency applies).  Instead we let
  the ambient universe play the role of `V[G]` and let an arbitrary *transitive set* `A`
  play the role of the ground structure (`V_ζ` of the ground model, or a countable `L_ζ`):

    `TWitness A lam Y` : `X ≺ A`, `A ∩ V_lam ∪ {lam} ⊆ X`, and an elementary
                         `j : X → A` with `j lam = lam`, `j ↾ lam ≠ id`.

  Nothing requires `j ∈ A`.  A virtual exacting witness, and an `L`-exacting witness at a
  countable ordinal, are exactly `TWitness`es (for `A = V_ζ^V`, respectively `A = L_ζ`).
  A genuine witness is the special case `A = V_ α` (`RelWitness.toTWitness`).

  This file ports the basic API of `Foundations/Bridge.lean` and `Foundations/Witness.lean`.
  Nothing is admitted.
-/
import Cardinals.KunenFree

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal FirstOrder FirstOrder.Language
open SetTheory (Form Sat scons)
open SetTheory.Form

/-- An exacting witness over the transitive set `A` (the embedding need not belong to
`A`). -/
structure TWitness (A : ZFSet.{u}) (lam : Ordinal.{u}) (Y : ZFSet.{u}) where
  X : ZFSet.{u}
  X_sub : X ⊆ A
  trans : A.IsTransitive
  incl : Str X Y ↪ₑ[Lex] Str A Y
  incl_val : ∀ x, (incl x).1 = x.1
  j : Str X Y ↪ₑ[Lex] Str A Y
  base : ∀ x, x ∈ A → x ∈ V_ lam → x ∈ X
  lam_mem : ordZ lam ∈ X
  j_lam : (j ⟨ordZ lam, lam_mem⟩).1 = ordZ lam
  moves : ∃ ξ < lam, ∃ h : ordZ ξ ∈ X, (j ⟨ordZ ξ, h⟩).1 ≠ ordZ ξ

/-- A genuine witness is a witness over `V_ α`. -/
def RelWitness.toTWitness {lam α : Ordinal.{u}} {Y : ZFSet.{u}} (w : RelWitness lam α Y) :
    TWitness (V_ α) lam Y where
  X := w.X
  X_sub := w.X_sub
  trans := isTransitive_vonNeumann α
  incl := w.incl
  incl_val := w.incl_val
  j := w.j
  base := fun _ _ hx => w.base hx
  lam_mem := w.lam_mem
  j_lam := w.j_lam
  moves := w.moves

namespace TWitness

variable {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}} (w : TWitness A lam Y)

/-- The value of `j` as a set. -/
noncomputable def jv (x : Str w.X Y) : ZFSet.{u} := (w.j x).1

/-- The inclusion of `X` into `A`, on carriers. -/
noncomputable def up (x : Str w.X Y) : Carrier A := ⟨x.1, w.X_sub x.2⟩

theorem incl_eq (x : Str w.X Y) : w.incl x = w.up x := Subtype.ext (w.incl_val x)

theorem sat_j (φ : Form) (e : ℕ → Str w.X Y) :
    Sat (memOn A) (fun k => w.j (e k)) φ ↔ Sat (memOn w.X) e φ :=
  Bridge.sat_of_elementary w.j φ e

theorem sat_incl (φ : Form) (e : ℕ → Str w.X Y) :
    Sat (memOn A) (fun k => w.up (e k)) φ ↔ Sat (memOn w.X) e φ := by
  have h := Bridge.sat_of_elementary w.incl φ e
  simp only [incl_eq] at h
  exact h

/-- Elementarity: `A ⊨ φ[x⃗] ↔ A ⊨ φ[j x⃗]` for `x⃗ ∈ X`. -/
theorem elem (φ : Form) (e : ℕ → Str w.X Y) :
    Sat (memOn A) (fun k => w.up (e k)) φ ↔ Sat (memOn A) (fun k => w.j (e k)) φ :=
  (w.sat_incl φ e).trans (w.sat_j φ e).symm

/-- Tarski–Vaught. -/
theorem tarski_vaught (φ : Form) (e : ℕ → Str w.X Y)
    (h : ∃ d : Carrier A, Sat (memOn A) (scons d (fun k => w.up (e k))) φ) :
    ∃ d : Str w.X Y, Sat (memOn A) (scons (w.up d) (fun k => w.up (e k))) φ := by
  have h1 : Sat (memOn A) (fun k => w.up (e k)) (fEx φ) := h
  rw [w.sat_incl] at h1
  obtain ⟨d, hd⟩ := h1
  refine ⟨d, ?_⟩
  have h2 := (w.sat_incl φ (scons d e)).mpr hd
  refine (SetTheory.Sat_ext φ _ _ (fun k => ?_)).mp h2
  cases k <;> rfl

theorem mem_iff (x y : Str w.X Y) : x.1 ∈ y.1 ↔ w.jv x ∈ w.jv y :=
  w.elem (fMem 0 1) (scons x (fun _ => y))

theorem eq_iff (x y : Str w.X Y) : x = y ↔ w.j x = w.j y := by
  have h := w.elem (fEq 0 1) (scons x (fun _ => y))
  constructor
  · intro hxy; rw [hxy]
  · intro hj
    have h1 : w.up x = w.up y := h.mpr hj
    have h2 : (w.up x).1 = (w.up y).1 := congrArg Subtype.val h1
    exact Subtype.ext h2

/-- An element of `A` definable from parameters in `X` lies in `X`, and its image satisfies
the same definition from the images of the parameters. -/
theorem definable (φ : Form) (e : ℕ → Str w.X Y) (x : Carrier A)
    (hx : Sat (memOn A) (scons x (fun k => w.up (e k))) φ)
    (huniq : ∀ y, Sat (memOn A) (scons y (fun k => w.up (e k))) φ → y = x) :
    ∃ d : Str w.X Y, w.up d = x ∧ Sat (memOn A) (scons (w.j d) (fun k => w.j (e k))) φ := by
  obtain ⟨d, hd⟩ := w.tarski_vaught φ e ⟨x, hx⟩
  refine ⟨d, huniq _ hd, ?_⟩
  have h := w.elem φ (scons d e)
  rw [map_scons, map_scons] at h
  exact h.mp hd

/-- An element definable from fixed parameters is a fixed element of `X`. -/
theorem definable_fixed (φ : Form) (e : ℕ → Str w.X Y) (hfix : ∀ k, w.j (e k) = w.up (e k))
    (x : Carrier A)
    (hx : Sat (memOn A) (scons x (fun k => w.up (e k))) φ)
    (huniq : ∀ y, Sat (memOn A) (scons y (fun k => w.up (e k))) φ → y = x) :
    ∃ d : Str w.X Y, w.up d = x ∧ w.j d = x := by
  obtain ⟨d, hd, hj⟩ := w.definable φ e x hx huniq
  refine ⟨d, hd, huniq _ ?_⟩
  have : (fun k => w.j (e k)) = fun k => w.up (e k) := funext hfix
  rwa [this] at hj

/-! ### The action on ordinals -/

include w in
theorem lam_mem_A : ordZ lam ∈ A := w.X_sub w.lam_mem

include w in
theorem ord_mem_A {ξ : Ordinal.{u}} (h : ξ < lam) : ordZ ξ ∈ A :=
  w.trans.subset_of_mem w.lam_mem_A (Ordinal.toZFSet_mem_toZFSet_iff.mpr h)

/-- The ordinal `ξ < lam` as an element of `X`. -/
noncomputable def ordX (ξ : Ordinal.{u}) (h : ξ < lam) : Str w.X Y :=
  ⟨ordZ ξ, w.base _ (w.ord_mem_A h) (ordZ_mem_V h)⟩

/-- `lam` as an element of `X`. -/
noncomputable def lamX : Str w.X Y := ⟨ordZ lam, w.lam_mem⟩

theorem jv_lamX : w.jv w.lamX = ordZ lam := w.j_lam

theorem exists_jOrd {ξ : Ordinal.{u}} (h : ξ < lam) :
    ∃ η, η < lam ∧ w.jv (w.ordX ξ h) = ordZ η := by
  have h1 : (w.ordX ξ h).1 ∈ w.lamX.1 := Ordinal.toZFSet_mem_toZFSet_iff.mpr h
  have h2 := (w.mem_iff _ _).mp h1
  rw [jv_lamX] at h2
  obtain ⟨η, hη, he⟩ := Ordinal.mem_toZFSet_iff.mp h2
  first
    | exact ⟨η, hη, he⟩
    | exact ⟨η, hη, he.symm⟩

open Classical in
/-- The action of `j` on the ordinals below `lam`. -/
noncomputable def jOrd (ξ : Ordinal.{u}) : Ordinal.{u} :=
  if h : ξ < lam then Classical.choose (w.exists_jOrd h) else ξ

theorem jOrd_lt {ξ : Ordinal.{u}} (h : ξ < lam) : w.jOrd ξ < lam := by
  rw [jOrd, dif_pos h]
  exact (Classical.choose_spec (w.exists_jOrd h)).1

theorem jv_ordX {ξ : Ordinal.{u}} (h : ξ < lam) : w.jv (w.ordX ξ h) = ordZ (w.jOrd ξ) := by
  rw [jOrd, dif_pos h]
  exact (Classical.choose_spec (w.exists_jOrd h)).2

theorem jOrd_strictMono {ξ η : Ordinal.{u}} (h : ξ < η) (hη : η < lam) :
    w.jOrd ξ < w.jOrd η := by
  have h1 : (w.ordX ξ (h.trans hη)).1 ∈ (w.ordX η hη).1 :=
    Ordinal.toZFSet_mem_toZFSet_iff.mpr h
  have h2 := (w.mem_iff _ _).mp h1
  rw [jv_ordX, jv_ordX] at h2
  exact Ordinal.toZFSet_mem_toZFSet_iff.mp h2

theorem jOrd_mono {ξ η : Ordinal.{u}} (h : ξ ≤ η) (hη : η < lam) : w.jOrd ξ ≤ w.jOrd η := by
  rcases h.lt_or_eq with h | rfl
  · exact (w.jOrd_strictMono h hη).le
  · exact le_rfl

theorem le_jOrd {ξ : Ordinal.{u}} (h : ξ < lam) : ξ ≤ w.jOrd ξ := by
  by_contra hcon
  let bad : Set Ordinal.{u} := {ξ | ξ < lam ∧ w.jOrd ξ < ξ}
  have hne : bad.Nonempty := ⟨ξ, h, not_le.mp hcon⟩
  let m := wellFounded_lt.min bad hne
  have hm : m ∈ bad := wellFounded_lt.min_mem bad hne
  have hlt : w.jOrd m < lam := w.jOrd_lt hm.1
  have : w.jOrd m ∈ bad := ⟨hlt, w.jOrd_strictMono hm.2 hm.1⟩
  exact wellFounded_lt.not_lt_min bad this hm.2

theorem exists_moved : ∃ ξ, ξ < lam ∧ w.jOrd ξ ≠ ξ := by
  obtain ⟨ξ, hξ, h, hne⟩ := w.moves
  refine ⟨ξ, hξ, fun heq => hne ?_⟩
  have := w.jv_ordX hξ
  rw [heq] at this
  exact this

/-- The critical point of `j`. -/
noncomputable def crit : Ordinal.{u} :=
  wellFounded_lt.min {ξ | ξ < lam ∧ w.jOrd ξ ≠ ξ} w.exists_moved

theorem crit_lt : w.crit < lam := (wellFounded_lt.min_mem _ w.exists_moved).1

theorem jOrd_crit_ne : w.jOrd w.crit ≠ w.crit := (wellFounded_lt.min_mem _ w.exists_moved).2

theorem jOrd_of_lt_crit {ξ : Ordinal.{u}} (h : ξ < w.crit) : w.jOrd ξ = ξ := by
  by_contra hne
  have hmem : ξ ∈ {ξ | ξ < lam ∧ w.jOrd ξ ≠ ξ} := ⟨h.trans w.crit_lt, hne⟩
  exact wellFounded_lt.not_lt_min _ hmem h

theorem crit_lt_jOrd : w.crit < w.jOrd w.crit :=
  lt_of_le_of_ne (w.le_jOrd w.crit_lt) (Ne.symm w.jOrd_crit_ne)

/-- The critical sequence `κ_n = j^n(κ)`. -/
noncomputable def critSeq (n : ℕ) : Ordinal.{u} := w.jOrd^[n] w.crit

theorem critSeq_lt (n : ℕ) : w.critSeq n < lam := by
  induction n with
  | zero => exact w.crit_lt
  | succ n ih =>
    rw [critSeq, Function.iterate_succ_apply']
    exact w.jOrd_lt ih

theorem critSeq_succ (n : ℕ) : w.critSeq (n + 1) = w.jOrd (w.critSeq n) :=
  Function.iterate_succ_apply' _ _ _

theorem critSeq_strictMono : StrictMono w.critSeq := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  induction n with
  | zero =>
    show w.crit < w.jOrd^[1] w.crit
    exact w.crit_lt_jOrd
  | succ n ih =>
    rw [critSeq_succ, critSeq_succ]
    exact w.jOrd_strictMono ih (w.critSeq_lt (n + 1))

/-- The witness is of **cofinal type**: the critical sequence is cofinal in `lam`.  For
genuine witnesses this is the Kunen inconsistency; for virtual ones it is a hypothesis. -/
def CofinalType : Prop := ∀ ξ < lam, ∃ n : ℕ, ξ < w.critSeq n

/-- For a witness of cofinal type every ordinal in `[crit, lam)` is moved. -/
theorem moved (hcof : w.CofinalType) {ξ : Ordinal.{u}} (hκ : w.crit ≤ ξ) (hξ : ξ < lam) :
    ξ < w.jOrd ξ :=
  OrdinalLemmas.moved_above_crit w.jOrd lam w.crit (fun _ _ h hb => w.jOrd_mono h hb)
    hcof ξ hκ hξ

theorem fixed_iff_lt_crit (hcof : w.CofinalType) {ξ : Ordinal.{u}} (hξ : ξ < lam) :
    w.jOrd ξ = ξ ↔ ξ < w.crit := by
  constructor
  · intro h
    by_contra hcon
    exact absurd h (ne_of_gt (w.moved hcof (not_lt.mp hcon) hξ))
  · exact w.jOrd_of_lt_crit

end TWitness

namespace RelWitness

variable {lam α : Ordinal.{u}} {Y : ZFSet.{u}} (w : RelWitness lam α Y)

theorem toT_jOrd : w.toTWitness.jOrd = w.jOrd := by
  funext ξ
  by_cases h : ξ < lam
  · have h1 := w.toTWitness.jv_ordX h
    have h2 := w.jv_ordX h
    have h3 : w.toTWitness.jv (w.toTWitness.ordX ξ h) = w.jv (w.ordX ξ h) := rfl
    rw [h3, h2] at h1
    exact (ordZ_inj h1).symm
  · rw [TWitness.jOrd, dif_neg h, RelWitness.jOrd, dif_neg h]

theorem toT_crit : w.toTWitness.crit = w.crit := by
  unfold TWitness.crit RelWitness.crit
  simp only [toT_jOrd]

theorem toT_critSeq (n : ℕ) : w.toTWitness.critSeq n = w.critSeq n := by
  unfold TWitness.critSeq RelWitness.critSeq
  rw [toT_jOrd, toT_crit]

end RelWitness

/-- A genuine witness at a cardinal is of cofinal type (the Kunen inconsistency, admitted
as `Published.critSeq_cofinal`). -/
theorem RelWitness.cofinalType_toTWitness {α : Ordinal.{u}} {Y : ZFSet.{u}} (c : Cardinal.{u})
    (hc : ℵ₀ ≤ c) (w : RelWitness c.ord α Y) : w.toTWitness.CofinalType := by
  intro ξ hξ
  obtain ⟨n, hn⟩ := Published.critSeq_cofinal c hc w ξ hξ
  exact ⟨n, by rw [w.toT_critSeq]; exact hn⟩

end Cardinals
