/-
  THE EMBEDDING OF AN EXACTING WITNESS, CONCRETELY (synthesis Lemma 3.1).

  For a witness `w : RelWitness lam α Y` this file derives, from elementarity alone:

  * `mem_iff`, `jv_inj`: `j` preserves and reflects `∈` and `=`;
  * `definable`: an element of `V_ α` that is definable from parameters in `X` lies in
    `X`, and its image satisfies the same definition from the images of the parameters;
    `definable_fixed`: if the parameters are fixed, so is the element;
  * the action `jOrd` of `j` on the ordinals below `lam`: strictly increasing, maps `lam`
    into itself, `ξ ≤ jOrd ξ`; the critical point `crit`, below which `jOrd` is the
    identity and which is moved;
  * with the (admitted, published) cofinality of the critical sequence: every ordinal in
    `[crit, lam)` is moved, and the fixed ordinals below `lam` are those below `crit`.

  One published statement is admitted: `Published.critSeq_cofinal`.
-/
import Cardinals.Foundations.Bridge
import Cardinals.Combinatorics.Ordinals

universe u

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons)
open SetTheory.Form

theorem map_scons {M N : Type*} (f : M → N) (d : M) (e : ℕ → M) :
    (fun k => f (scons d e k)) = scons (f d) (fun k => f (e k)) := by
  funext k
  cases k <;> rfl

theorem ordZ_mem_V {ξ lam : Ordinal.{u}} (h : ξ < lam) : ordZ ξ ∈ V_ lam := by
  rw [mem_vonNeumann, rank_toZFSet]
  exact h

namespace RelWitness

variable {lam α : Ordinal.{u}} {Y : ZFSet.{u}} (w : RelWitness lam α Y)

/-! ### Membership and equality -/

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

theorem jv_inj {x y : Str w.X Y} (h : w.jv x = w.jv y) : x = y :=
  (w.eq_iff x y).mpr (Subtype.ext h)

/-! ### Definable elements -/

/-- If `x ∈ V_ α` is the unique solution of `φ(·, p⃗)` with parameters `p⃗ ∈ X`, then
`x ∈ X` and `j x` solves `φ(·, j p⃗)`. -/
theorem definable (φ : Form) (e : ℕ → Str w.X Y) (x : Carrier (V_ α))
    (hx : Sat (memOn (V_ α)) (scons x (fun k => w.up (e k))) φ)
    (huniq : ∀ y, Sat (memOn (V_ α)) (scons y (fun k => w.up (e k))) φ → y = x) :
    ∃ d : Str w.X Y, w.up d = x ∧
      Sat (memOn (V_ α)) (scons (w.j d) (fun k => w.j (e k))) φ := by
  obtain ⟨d, hd⟩ := w.tarski_vaught φ e ⟨x, hx⟩
  refine ⟨d, huniq _ hd, ?_⟩
  have h := w.elem φ (scons d e)
  rw [map_scons, map_scons] at h
  exact h.mp hd

/-- An element definable from *fixed* parameters is a fixed element of `X`. -/
theorem definable_fixed (φ : Form) (e : ℕ → Str w.X Y) (hfix : ∀ k, w.j (e k) = w.up (e k))
    (x : Carrier (V_ α))
    (hx : Sat (memOn (V_ α)) (scons x (fun k => w.up (e k))) φ)
    (huniq : ∀ y, Sat (memOn (V_ α)) (scons y (fun k => w.up (e k))) φ → y = x) :
    ∃ d : Str w.X Y, w.up d = x ∧ w.j d = x := by
  obtain ⟨d, hd, hj⟩ := w.definable φ e x hx huniq
  refine ⟨d, hd, huniq _ ?_⟩
  have : (fun k => w.j (e k)) = fun k => w.up (e k) := funext hfix
  rwa [this] at hj

/-! ### The action on ordinals -/

/-- The ordinal `ξ < lam` as an element of `X`. -/
noncomputable def ordX (ξ : Ordinal.{u}) (h : ξ < lam) : Str w.X Y :=
  ⟨ordZ ξ, w.base (ordZ_mem_V h)⟩

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
/-- The action of `j` on the ordinals below `lam` (the identity elsewhere). -/
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

theorem critSeq_strictMono : StrictMono w.critSeq := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  induction n with
  | zero =>
    show w.crit < w.jOrd^[1] w.crit
    exact w.crit_lt_jOrd
  | succ n ih =>
    rw [critSeq, critSeq, Function.iterate_succ_apply', Function.iterate_succ_apply' (n := n + 1)]
    exact w.jOrd_strictMono ih (w.critSeq_lt (n + 1))

end RelWitness

/-! ### The admitted published input -/

namespace Published

/-- The critical sequence of an exacting witness at a cardinal `λ` is cofinal in `λ`.

Reference: [ABL] J. P. Aguilera, J. Bagaria, P. Lücke, "Large cardinals, structural
reflection, and the HOD Conjecture", arXiv:2411.11568v4, Section 2 (discussion around
Definition 2.4 and Lemma 2.3): the restriction of an exact embedding to `V_λ` is an
`I3`-embedding, i.e. `λ` is the supremum of its critical sequence.  The reason is the Kunen
inconsistency: if `κ_ω = sup κ_n < λ` then `j ↾ V_{κ_ω+2}` would be a nontrivial
elementary embedding of `V_{κ_ω+2}` into itself; see K. Kunen, "Elementary embeddings and
infinitary combinatorics", J. Symb. Log. 36 (1971) 407-413, and A. Kanamori, "The Higher
Infinite", 2nd ed., Corollary 23.14.  (Synthesis Lemma 3.1.) -/
theorem critSeq_cofinal {α : Ordinal.{u}} {Y : ZFSet.{u}} (c : Cardinal.{u}) (hc : ℵ₀ ≤ c)
    (w : RelWitness c.ord α Y) : ∀ ξ < c.ord, ∃ n : ℕ, ξ < w.critSeq n := by
  admit

end Published

namespace RelWitness

variable {α : Ordinal.{u}} {Y : ZFSet.{u}} {c : Cardinal.{u}} (w : RelWitness c.ord α Y)

/-- Every ordinal in `[crit, λ)` is moved upwards (synthesis Lemma 3.1). -/
theorem moved (hc : ℵ₀ ≤ c) {ξ : Ordinal.{u}} (hκ : w.crit ≤ ξ) (hξ : ξ < c.ord) :
    ξ < w.jOrd ξ :=
  OrdinalLemmas.moved_above_crit w.jOrd c.ord w.crit (fun _ _ h hb => w.jOrd_mono h hb)
    (Published.critSeq_cofinal c hc w) ξ hκ hξ

/-- The ordinals below `λ` fixed by `j` are exactly those below the critical point. -/
theorem fixed_iff_lt_crit (hc : ℵ₀ ≤ c) {ξ : Ordinal.{u}} (hξ : ξ < c.ord) :
    w.jOrd ξ = ξ ↔ ξ < w.crit := by
  constructor
  · intro h
    by_contra hcon
    exact absurd h (ne_of_gt (w.moved hc (not_lt.mp hcon) hξ))
  · exact w.jOrd_of_lt_crit

end RelWitness

end Cardinals
