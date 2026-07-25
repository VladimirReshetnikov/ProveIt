import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Squaring the square: basic definitions

An axis-parallel closed square in the real plane is recorded by its
bottom-left corner `(x, y)` and its side `s`.  A *dissection* of the square
`[0, S] × [0, S]` is a finite list of such squares with positive sides whose
open interiors are pairwise disjoint and whose closed pieces cover the big
square exactly.  A dissection is *perfect* when it has at least two pieces and
the pieces are pairwise non-congruent.

Congruence is taken in the strongest reasonable sense for the negative
statements: two subsets of the plane are congruent when some bijection between
them preserves squared Euclidean distances.  Every plane isometry restricts to
such a bijection, so `¬ Congruent` below rules out congruence by arbitrary
isometries as well.  The key elementary invariant is the squared diameter: an
axis-parallel closed square of side `s > 0` has maximal squared distance
`2 * s ^ 2`, attained by opposite corners, so congruent squares have equal
sides.
-/

namespace LeanProofs

namespace SquaredSquare

/-- An axis-parallel square in the plane, described by its bottom-left corner
`(x, y)` and its side `s`. -/
structure Sq where
  x : ℝ
  y : ℝ
  s : ℝ

/-- The closed square realized by `q`. -/
def Sq.toSet (q : Sq) : Set (ℝ × ℝ) :=
  Set.Icc q.x (q.x + q.s) ×ˢ Set.Icc q.y (q.y + q.s)

/-- The open square realized by `q`; for `0 < q.s` this is the topological
interior of `q.toSet` (see `Sq.interior_toSet`). -/
def Sq.inn (q : Sq) : Set (ℝ × ℝ) :=
  Set.Ioo q.x (q.x + q.s) ×ˢ Set.Ioo q.y (q.y + q.s)

theorem Sq.mem_toSet {q : Sq} {p : ℝ × ℝ} :
    p ∈ q.toSet ↔ (q.x ≤ p.1 ∧ p.1 ≤ q.x + q.s) ∧ q.y ≤ p.2 ∧ p.2 ≤ q.y + q.s := by
  simp only [Sq.toSet, Set.mem_prod, Set.mem_Icc]

theorem Sq.mem_inn {q : Sq} {p : ℝ × ℝ} :
    p ∈ q.inn ↔ (q.x < p.1 ∧ p.1 < q.x + q.s) ∧ q.y < p.2 ∧ p.2 < q.y + q.s := by
  simp only [Sq.inn, Set.mem_prod, Set.mem_Ioo]

/-- The explicit open square is the topological interior of the closed one. -/
theorem Sq.interior_toSet (q : Sq) : interior q.toSet = q.inn := by
  unfold Sq.toSet Sq.inn
  rw [interior_prod_eq, interior_Icc, interior_Icc]

/-- The open square is contained in the closed square. -/
theorem Sq.inn_subset_toSet (q : Sq) : q.inn ⊆ q.toSet := by
  intro p hp
  rw [Sq.mem_inn] at hp
  rw [Sq.mem_toSet]
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2.1.le, hp.2.2.le⟩

/-- The centre of a square with positive side lies in its open interior. -/
theorem Sq.center_mem_inn {q : Sq} (hs : 0 < q.s) :
    (q.x + q.s / 2, q.y + q.s / 2) ∈ q.inn := by
  rw [Sq.mem_inn]
  constructor <;> constructor <;> simp <;> linarith

/-- The closed square `[0, S] × [0, S]` being dissected. -/
def bigSquare (S : ℝ) : Set (ℝ × ℝ) :=
  Set.Icc 0 S ×ˢ Set.Icc 0 S

theorem mem_bigSquare {S : ℝ} {p : ℝ × ℝ} :
    p ∈ bigSquare S ↔ (0 ≤ p.1 ∧ p.1 ≤ S) ∧ 0 ≤ p.2 ∧ p.2 ≤ S := by
  simp only [bigSquare, Set.mem_prod, Set.mem_Icc]

/-- `IsDissection S l`: the squares listed in `l` have positive sides,
pairwise disjoint open interiors, and their closed pieces cover
`[0, S] × [0, S]` exactly.  This is the standard notion of cutting the square
of side `S` into the listed square pieces. -/
structure IsDissection (S : ℝ) (l : List Sq) : Prop where
  pos : ∀ q ∈ l, 0 < q.s
  disj : l.Pairwise fun p q => Disjoint p.inn q.inn
  cover : (⋃ q ∈ l, q.toSet) = bigSquare S

/-- Squared Euclidean distance in the plane. -/
def sqDist (p q : ℝ × ℝ) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Two plane sets are congruent when some bijection between them preserves
squared Euclidean distances.  Any plane isometry mapping `A` onto `B`
restricts to such a bijection, so the *negation* of this predicate is the
strongest natural non-congruence statement. -/
def Congruent (A B : Set (ℝ × ℝ)) : Prop :=
  ∃ f : ℝ × ℝ → ℝ × ℝ, Set.BijOn f A B ∧
    ∀ p ∈ A, ∀ q ∈ A, sqDist (f p) (f q) = sqDist p q

/-- Any two points of a closed square of side `s ≥ 0` are at squared distance
at most `2 * s ^ 2`. -/
theorem sqDist_le_of_mem {q : Sq} {p r : ℝ × ℝ}
    (hp : p ∈ q.toSet) (hr : r ∈ q.toSet) : sqDist p r ≤ 2 * q.s ^ 2 := by
  rw [Sq.mem_toSet] at hp hr
  have h1 : (p.1 - r.1) ^ 2 ≤ q.s ^ 2 :=
    sq_le_sq' (by linarith [hp.1.1, hr.1.2]) (by linarith [hp.1.2, hr.1.1])
  have h2 : (p.2 - r.2) ^ 2 ≤ q.s ^ 2 :=
    sq_le_sq' (by linarith [hp.2.1, hr.2.2]) (by linarith [hp.2.2, hr.2.1])
  unfold sqDist
  linarith

/-- Opposite corners of a square realize squared distance `2 * s ^ 2`. -/
theorem sqDist_corners (q : Sq) :
    sqDist (q.x, q.y) (q.x + q.s, q.y + q.s) = 2 * q.s ^ 2 := by
  unfold sqDist
  ring

theorem corner_bl_mem {q : Sq} (hs : 0 ≤ q.s) : (q.x, q.y) ∈ q.toSet := by
  rw [Sq.mem_toSet]
  constructor <;> constructor <;> simp <;> linarith

theorem corner_tr_mem {q : Sq} (hs : 0 ≤ q.s) :
    (q.x + q.s, q.y + q.s) ∈ q.toSet := by
  rw [Sq.mem_toSet]
  constructor <;> constructor <;> simp <;> linarith

/-- Congruent squares (with positive sides) have equal sides: the squared
diameter `2 * s ^ 2` is preserved by any squared-distance-preserving
bijection. -/
theorem side_eq_of_congruent {q₁ q₂ : Sq} (h₁ : 0 < q₁.s) (h₂ : 0 < q₂.s)
    (h : Congruent q₁.toSet q₂.toSet) : q₁.s = q₂.s := by
  obtain ⟨f, hf, hd⟩ := h
  -- forward: the image of opposite corners of `q₁` lies in `q₂`
  have hfwd : 2 * q₁.s ^ 2 ≤ 2 * q₂.s ^ 2 := by
    have hc1 := corner_bl_mem (q := q₁) h₁.le
    have hc2 := corner_tr_mem (q := q₁) h₁.le
    have hpres := hd _ hc1 _ hc2
    rw [sqDist_corners] at hpres
    have hb := sqDist_le_of_mem (hf.mapsTo hc1) (hf.mapsTo hc2)
    linarith
  -- backward: opposite corners of `q₂` have preimages in `q₁`
  have hbwd : 2 * q₂.s ^ 2 ≤ 2 * q₁.s ^ 2 := by
    obtain ⟨p, hp, hfp⟩ := hf.surjOn (corner_bl_mem (q := q₂) h₂.le)
    obtain ⟨r, hr, hfr⟩ := hf.surjOn (corner_tr_mem (q := q₂) h₂.le)
    have hpres := hd _ hp _ hr
    rw [hfp, hfr, sqDist_corners] at hpres
    have hb := sqDist_le_of_mem hp hr
    linarith
  have hsq : q₁.s ^ 2 = q₂.s ^ 2 := by linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · nlinarith
  · nlinarith

/-- Squares of equal side are congruent, via the translation matching their
bottom-left corners. -/
theorem congruent_of_side_eq {q₁ q₂ : Sq} (h : q₁.s = q₂.s) :
    Congruent q₁.toSet q₂.toSet := by
  refine ⟨fun p => (p.1 + (q₂.x - q₁.x), p.2 + (q₂.y - q₁.y)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    rw [Sq.mem_toSet] at hp ⊢
    constructor <;> constructor <;> simp <;> linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
  · intro a _ b _ hab
    have h1 : a.1 = b.1 := by
      have := congrArg Prod.fst hab
      simpa using this
    have h2 : a.2 = b.2 := by
      have := congrArg Prod.snd hab
      simpa using this
    exact Prod.ext h1 h2
  · intro b hb
    refine ⟨(b.1 - (q₂.x - q₁.x), b.2 - (q₂.y - q₁.y)), ?_, ?_⟩
    · rw [Sq.mem_toSet] at hb ⊢
      constructor <;> constructor <;> simp <;> linarith [hb.1.1, hb.1.2, hb.2.1, hb.2.2]
    · simp
  · intro p _ r _
    unfold sqDist
    ring

/-- Squares of different (positive) sides are not congruent — not even via an
arbitrary squared-distance-preserving bijection. -/
theorem noncongruent_of_side_ne {q₁ q₂ : Sq} (h₁ : 0 < q₁.s) (h₂ : 0 < q₂.s)
    (h : q₁.s ≠ q₂.s) : ¬Congruent q₁.toSet q₂.toSet :=
  fun hc => h (side_eq_of_congruent h₁ h₂ hc)

/-- A *perfect squared square* of side `S`: a dissection of `[0, S] × [0, S]`
into at least two squares that are pairwise non-congruent. -/
def IsPerfectSquaredSquare (S : ℝ) (l : List Sq) : Prop :=
  IsDissection S l ∧ 2 ≤ l.length ∧
    l.Pairwise fun p q => ¬Congruent p.toSet q.toSet

end SquaredSquare

end LeanProofs
