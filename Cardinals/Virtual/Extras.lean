/-
  FURTHER FORMALIZED PARTS OF THE RESEARCH NOTE
  "Exacting embeddings of countable structures".

  * `elementary_iff_assignment`, `exists_free_bound`, `assignment_iff_branch`: the
    combinatorial heart of the Gitman–Schindler absoluteness lemma (note, Lemma 2.3): for a
    countable structure `M`, an elementary embedding `M → N` exists iff some assignment
    `b : ℕ → N` satisfies the same formulas as a fixed enumeration of `M`, iff the tree of
    finite approximations has a branch.  (The absoluteness itself -- a branch in a larger
    universe yields one in a smaller -- is the absoluteness of well-foundedness, a
    metatheorem about two models, and is not expressible inside one Lean universe.)
  * `TWitness.restrictTo`, `no_fixed_point_of_minimal`: a fixed point `β ∈ (crit, lam)` of
    `j` carries a witness with the same `X` and `j`; so at a *least* witnessed ordinal every
    ordinal above the critical point is moved (note, proof of Theorem 6.1(3)).
  * `exists_root`: every point of `[κ, lam)` lies on the forward orbit of a root
    (note, Proposition 7.1; synthesis Lemma 12.1(1)).
  * `Published.kunen_in_model` (ADMITTED: the Kunen inconsistency, relativized to a
    transitive set model of ZFC) and `TWitness.cofinalType_of_ultra` (note, Prop. 5.3).

  NOT formalized: Theorems 4.1 and 6.1 of the note.  They speak about `L`, `0^#`, Silver
  indiscernibles, Shoenfield absoluteness and stable ordinals; neither Mathlib nor ProveIt
  has the constructible hierarchy, so these statements cannot even be written down here
  without first developing `L`.
-/
import Cardinals.Virtual.Core

universe u v

namespace Cardinals

open ZFSet Ordinal Cardinal
open SetTheory (Form Sat scons Free)
open SetTheory.Form

/-! ### The heart of the absoluteness lemma -/

section Absoluteness

variable {M : Type u} {N : Type v} (memM : M → M → Prop) (memN : N → N → Prop)

/-- For an enumeration `a` of `M`: an elementary embedding `M → N` exists iff some
assignment `b` in `N` satisfies exactly the formulas that `a` satisfies in `M`. -/
theorem elementary_iff_assignment (a : ℕ → M) (ha : Function.Surjective a) :
    (∃ j : M → N, ∀ (φ : Form) (e : ℕ → M), Sat memM e φ ↔ Sat memN (fun k => j (e k)) φ) ↔
      ∃ b : ℕ → N, ∀ φ : Form, Sat memM a φ ↔ Sat memN b φ := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨fun k => j (a k), fun φ => hj φ a⟩
  · rintro ⟨b, hb⟩
    choose idx hidx using ha
    refine ⟨fun x => b (idx x), fun φ e => ?_⟩
    -- reindex `e` through the enumeration
    let σ : ℕ → ℕ := fun k => idx (e k)
    have h1 : Sat memM e φ ↔ Sat memM a (SetTheory.rename σ φ) := by
      rw [SetTheory.Sat_rename]
      exact SetTheory.Sat_ext φ _ _ (fun k => (hidx (e k)).symm)
    rw [h1, hb, SetTheory.Sat_rename]

/-- Every formula has only finitely many free variables. -/
theorem exists_free_bound (φ : Form) : ∃ n, ∀ k, Free k φ → k < n := by
  induction φ with
  | fMem i j => exact ⟨max i j + 1, fun k hk => by rcases hk with rfl | rfl <;> omega⟩
  | fEq i j => exact ⟨max i j + 1, fun k hk => by rcases hk with rfl | rfl <;> omega⟩
  | fBot => exact ⟨0, fun k hk => hk.elim⟩
  | fImp a b iha ihb =>
    obtain ⟨n, hn⟩ := iha
    obtain ⟨m, hm⟩ := ihb
    exact ⟨max n m, fun k hk => by
      rcases hk with h | h
      · exact lt_of_lt_of_le (hn k h) (le_max_left _ _)
      · exact lt_of_lt_of_le (hm k h) (le_max_right _ _)⟩
  | fAnd a b iha ihb =>
    obtain ⟨n, hn⟩ := iha
    obtain ⟨m, hm⟩ := ihb
    exact ⟨max n m, fun k hk => by
      rcases hk with h | h
      · exact lt_of_lt_of_le (hn k h) (le_max_left _ _)
      · exact lt_of_lt_of_le (hm k h) (le_max_right _ _)⟩
  | fOr a b iha ihb =>
    obtain ⟨n, hn⟩ := iha
    obtain ⟨m, hm⟩ := ihb
    exact ⟨max n m, fun k hk => by
      rcases hk with h | h
      · exact lt_of_lt_of_le (hn k h) (le_max_left _ _)
      · exact lt_of_lt_of_le (hm k h) (le_max_right _ _)⟩
  | fAll a iha =>
    obtain ⟨n, hn⟩ := iha
    exact ⟨n, fun k hk => by have := hn (k + 1) hk; omega⟩
  | fEx a iha =>
    obtain ⟨n, hn⟩ := iha
    exact ⟨n, fun k hk => by have := hn (k + 1) hk; omega⟩

/-- `b` is correct on the formulas with free variables below `n`: a node of height `n` of
the tree of finite approximations. -/
def ApproxUpTo (a : ℕ → M) (b : ℕ → N) (n : ℕ) : Prop :=
  ∀ φ : Form, (∀ k, Free k φ → k < n) → (Sat memM a φ ↔ Sat memN b φ)

/-- A branch through the tree of finite approximations is the same as a correct
assignment.  So the existence of an elementary embedding of a countable structure is the
ill-foundedness of a tree -- which is why it is absolute. -/
theorem assignment_iff_branch (a : ℕ → M) (b : ℕ → N) :
    (∀ φ : Form, Sat memM a φ ↔ Sat memN b φ) ↔ ∀ n, ApproxUpTo memM memN a b n := by
  constructor
  · exact fun h n φ _ => h φ
  · intro h φ
    obtain ⟨n, hn⟩ := exists_free_bound φ
    exact h n φ hn

end Absoluteness

/-! ### Fixed points carry witnesses -/

namespace TWitness

variable {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}} (w : TWitness A lam Y)

/-- If `β ∈ (crit, lam)` is fixed by `j`, the same `X` and `j` form a witness at `β`. -/
noncomputable def restrictTo (β : Ordinal.{u}) (hβ : β < lam) (hfix : w.jOrd β = β)
    (hcrit : w.crit < β) : TWitness A β Y where
  X := w.X
  X_sub := w.X_sub
  trans := w.trans
  incl := w.incl
  incl_val := w.incl_val
  j := w.j
  base := fun x hxA hx => w.base x hxA (by
    rw [mem_vonNeumann] at hx ⊢
    exact hx.trans hβ)
  lam_mem := (w.ordX β hβ).2
  j_lam := by
    have := w.jv_ordX hβ
    rw [hfix] at this
    exact this
  moves := by
    refine ⟨w.crit, hcrit, (w.ordX w.crit w.crit_lt).2, ?_⟩
    have := w.jv_ordX w.crit_lt
    intro h
    have h' : w.jv (w.ordX w.crit w.crit_lt) = ordZ w.crit := h
    rw [this] at h'
    exact w.jOrd_crit_ne (ordZ_inj h')

/-- At a least ordinal carrying a witness over `A`, no ordinal strictly between the
critical point and `lam` is fixed. -/
theorem no_fixed_point_of_minimal (hmin : ∀ β < lam, IsEmpty (TWitness A β Y))
    {β : Ordinal.{u}} (hcrit : w.crit < β) (hβ : β < lam) : w.jOrd β ≠ β :=
  fun hfix => (hmin β hβ).false (w.restrictTo β hβ hfix hcrit)

end TWitness

/-! ### Every point lies on the orbit of a root -/

/-- Let `e` map `[κ, lam)` into itself with `e ξ > ξ`.  Every `ξ ∈ [κ, lam)` is of the form
`e^n r` for a root `r`, i.e. a point of `[κ, lam)` outside `e '' [κ, lam)`. -/
theorem exists_root (e : Ordinal.{u} → Ordinal.{u}) (κ lam : Ordinal.{u})
    (hmove : ∀ ξ, κ ≤ ξ → ξ < lam → ξ < e ξ) :
    ∀ ξ, κ ≤ ξ → ξ < lam → ∃ (n : ℕ) (r : Ordinal.{u}), κ ≤ r ∧ r < lam ∧
      (∀ η, κ ≤ η → η < lam → e η ≠ r) ∧ e^[n] r = ξ := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | _ ξ ih =>
    intro hκ hξ
    by_cases hroot : ∀ η, κ ≤ η → η < lam → e η ≠ ξ
    · exact ⟨0, ξ, hκ, hξ, hroot, rfl⟩
    · push Not at hroot
      obtain ⟨η, hκη, hηlam, hη⟩ := hroot
      have hlt : η < ξ := by rw [← hη]; exact hmove η hκη hηlam
      obtain ⟨n, r, h1, h2, h3, h4⟩ := ih η hlt hκη hηlam
      exact ⟨n + 1, r, h1, h2, h3, by rw [Function.iterate_succ_apply', h4, hη]⟩

/-! ### Proposition 5.3: ultraexactingness does not virtualize -/

/-- `A` is a (set) model of ZFC. -/
def IsSetModelZFC (A : ZFSet.{u}) : Prop :=
  (∀ φ, SetTheory.ZFax φ → ∀ e : ℕ → Carrier A, Sat (memOn A) e φ) ∧
    ∀ e : ℕ → Carrier A, Sat (memOn A) e LeanProofs.BoundedZFCConsistency.Choice_form

/-- The witness over `A` is *ultra*: the graph of `j ↾ (A ∩ V_lam)` is an element of `A`.
(In the note: `j ↾ V_λ ∈ X`, and `X ⊆ A`.) -/
def TWitness.IsUltra {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}}
    (w : TWitness A lam Y) : Prop :=
  ∃ e ∈ A, ∀ p, p ∈ e ↔
    ∃ (x : ZFSet.{u}) (hA : x ∈ A) (hV : x ∈ V_ lam), p = pair x (w.jv ⟨x, w.base x hA hV⟩)

namespace Published

/-- The Kunen inconsistency inside a transitive model of ZFC: if the restriction of the
embedding to `V_lam^A` is an element of `A`, then the critical sequence is cofinal in `lam`
-- otherwise `A` would contain a nontrivial elementary embedding of its `V_{κ_ω+2}` into
itself.

Reference: K. Kunen, "Elementary embeddings and infinitary combinatorics", J. Symb. Log. 36
(1971) 407-413; A. Kanamori, "The Higher Infinite", 2nd ed., Corollary 23.14 ("there is no
nontrivial elementary `j : V_{δ+2} → V_{δ+2}`").  The theorem is a theorem of ZFC and is
applied here inside the model `A`; the embedding `V_lam^A → V_lam^A` is elementary in the
sense of `A` because `j` is elementary and fixes `lam`. -/
theorem kunen_in_model {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}}
    (hZFC : IsSetModelZFC A) (hlim : ∀ a < lam, a + 1 < lam) (w : TWitness A lam Y)
    (hU : w.IsUltra) : w.CofinalType := by
  admit

end Published

/-- **Note, Proposition 5.3.**  An ultra witness over a model of ZFC is of cofinal type; so
all of Theorem 5.1 applies to it, and (the embedding being a set of the model) the model
sees a genuine rank-into-rank embedding. -/
theorem TWitness.cofinalType_of_ultra {A : ZFSet.{u}} {lam : Ordinal.{u}} {Y : ZFSet.{u}}
    (hZFC : IsSetModelZFC A) (hlim : ∀ a < lam, a + 1 < lam) (w : TWitness A lam Y)
    (hU : w.IsUltra) : w.CofinalType :=
  Published.kunen_in_model hZFC hlim w hU

end Cardinals
