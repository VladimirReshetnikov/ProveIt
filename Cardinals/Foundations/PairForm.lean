/-
  First-order formulas for Kuratowski pairs, evaluated in transitive set structures.

  `pairMemF j k f` expresses `⟨v_j, v_k⟩ ∈ v_f`; its satisfaction in `(A, ∈)` for a
  transitive `A` is the genuine statement `pair (e j) (e k) ∈ e f`.

  No statement is admitted in this file.
-/
import Cardinals.Foundations.Basic

universe u

namespace Cardinals

open ZFSet
open SetTheory (Form Sat scons)
open SetTheory.Form

/-- `v_i = {v_j}`. -/
def singF (i j : ℕ) : Form := fAll (SetTheory.fIff (fMem 0 (i + 1)) (fEq 0 (j + 1)))

/-- `v_i = {v_j, v_k}`. -/
def upairF (i j k : ℕ) : Form :=
  fAll (SetTheory.fIff (fMem 0 (i + 1)) (fOr (fEq 0 (j + 1)) (fEq 0 (k + 1))))

/-- `v_i = ⟨v_j, v_k⟩` (Kuratowski). -/
def kpairF (i j k : ℕ) : Form :=
  fAll (SetTheory.fIff (fMem 0 (i + 1)) (fOr (singF 0 (j + 1)) (upairF 0 (j + 1) (k + 1))))

/-- `⟨v_j, v_k⟩ ∈ v_f`. -/
def pairMemF (j k f : ℕ) : Form := fEx (fAnd (fMem 0 (f + 1)) (kpairF 0 (j + 1) (k + 1)))

variable {A : ZFSet.{u}}

theorem singF_spec (hA : IsTransitive A) (e : ℕ → Carrier A) (i j : ℕ) :
    Sat (memOn A) e (singF i j) ↔ (e i).1 = {(e j).1} := by
  simp only [singF, Sat, SetTheory.Sat_fIff, scons, memOn]
  constructor
  · intro h
    ext t
    rw [mem_singleton]
    constructor
    · intro ht
      have := (h ⟨t, hA.subset_of_mem (e i).2 ht⟩).mp ht
      exact congrArg Subtype.val this
    · rintro rfl
      exact (h (e j)).mpr rfl
  · intro h d
    rw [h, mem_singleton]
    exact ⟨fun hd => Subtype.ext hd, fun hd => congrArg Subtype.val hd⟩

theorem upairF_spec (hA : IsTransitive A) (e : ℕ → Carrier A) (i j k : ℕ) :
    Sat (memOn A) e (upairF i j k) ↔ (e i).1 = {(e j).1, (e k).1} := by
  simp only [upairF, Sat, SetTheory.Sat_fIff, scons, memOn]
  constructor
  · intro h
    ext t
    rw [mem_pair]
    constructor
    · intro ht
      rcases (h ⟨t, hA.subset_of_mem (e i).2 ht⟩).mp ht with h1 | h1
      · exact Or.inl (congrArg Subtype.val h1)
      · exact Or.inr (congrArg Subtype.val h1)
    · rintro (rfl | rfl)
      · exact (h (e j)).mpr (Or.inl rfl)
      · exact (h (e k)).mpr (Or.inr rfl)
  · intro h d
    rw [h, mem_pair]
    exact ⟨fun hd => hd.imp (fun h1 => Subtype.ext h1) (fun h1 => Subtype.ext h1),
      fun hd => hd.imp (fun h1 => congrArg Subtype.val h1) (fun h1 => congrArg Subtype.val h1)⟩

/-- `A` is closed under unordered pairs (true of `V_ θ` for limit `θ`). -/
def PairClosed (A : ZFSet.{u}) : Prop := ∀ x ∈ A, ∀ y ∈ A, ({x, y} : ZFSet.{u}) ∈ A

theorem PairClosed.singleton_mem (hP : PairClosed A) {x : ZFSet.{u}} (hx : x ∈ A) :
    ({x} : ZFSet.{u}) ∈ A := by
  have := hP x hx x hx
  rwa [ZFSet.pair_eq_singleton] at this

theorem kpairF_spec (hA : IsTransitive A) (hP : PairClosed A) (e : ℕ → Carrier A) (i j k : ℕ) :
    Sat (memOn A) e (kpairF i j k) ↔ (e i).1 = pair (e j).1 (e k).1 := by
  have key : Sat (memOn A) e (kpairF i j k) ↔
      ∀ d : Carrier A, d.1 ∈ (e i).1 ↔ (d.1 = {(e j).1} ∨ d.1 = {(e j).1, (e k).1}) := by
    unfold kpairF
    simp only [Sat, SetTheory.Sat_fIff]
    refine forall_congr' (fun d => ?_)
    have h1 := singF_spec hA (scons d e) 0 (j + 1)
    have h2 := upairF_spec hA (scons d e) 0 (j + 1) (k + 1)
    simp only [scons] at h1 h2
    rw [h1, h2]
    rfl
  rw [key]
  constructor
  · intro h
    ext t
    rw [pair, mem_pair]
    constructor
    · intro ht
      exact (h ⟨t, hA.subset_of_mem (e i).2 ht⟩).mp ht
    · intro ht
      have htA : t ∈ A := by
        rcases ht with rfl | rfl
        · exact hP.singleton_mem (e j).2
        · exact hP _ (e j).2 _ (e k).2
      exact (h ⟨t, htA⟩).mpr ht
  · intro h d
    rw [h, pair, mem_pair]

theorem pairMemF_spec (hA : IsTransitive A) (hP : PairClosed A) (e : ℕ → Carrier A)
    (j k f : ℕ) :
    Sat (memOn A) e (pairMemF j k f) ↔ pair (e j).1 (e k).1 ∈ (e f).1 := by
  unfold pairMemF
  simp only [Sat]
  constructor
  · rintro ⟨d, hd, hk⟩
    have := (kpairF_spec hA hP (scons d e) 0 (j + 1) (k + 1)).mp hk
    simp only [scons] at this
    rw [← this]
    exact hd
  · intro h
    refine ⟨⟨_, hA.subset_of_mem (e f).2 h⟩, h, ?_⟩
    exact (kpairF_spec hA hP (scons _ e) 0 (j + 1) (k + 1)).mpr rfl

/-- `V_ θ` is closed under unordered pairs when `θ` is a limit ordinal. -/
theorem pairClosed_vonNeumann {θ : Ordinal.{u}} (hθ : ∀ a < θ, a + 1 < θ) :
    PairClosed (V_ θ) := by
  intro x hx y hy
  rw [mem_vonNeumann] at hx hy ⊢
  have hr : rank ({x, y} : ZFSet.{u}) ≤ max (rank x) (rank y) + 1 := by
    rw [rank_le_iff]
    intro z hz
    rw [mem_pair] at hz
    rcases hz with rfl | rfl
    · exact lt_of_le_of_lt (le_max_left _ _) (Order.lt_add_one_iff.mpr le_rfl)
    · exact lt_of_le_of_lt (le_max_right _ _) (Order.lt_add_one_iff.mpr le_rfl)
  exact lt_of_le_of_lt hr (hθ _ (max_lt hx hy))

end Cardinals
