import SquaredSquare.Basic
import SquaredSquare.Intervals

/-!
# Small orders are impossible: a perfect squared square has at least 7 pieces

This module proves the elementary part of the minimality statement for
squared squares: a dissection of a square into at least two pairwise
non-congruent squares needs at least seven pieces.

The arguments are the classical corner/edge ones:

* every corner of the big square is covered by a unique *corner tile*, and no
  tile can contain two corners (its side would be `S`), so a nontrivial
  dissection has at least four pieces;
* the tiles touching a fixed edge of the big square partition it, so their
  sides sum to `S` (via `interval_cover_sum`);
* a non-corner tile can touch at most one edge, so with at most two
  non-corner pieces some pair of adjacent edges is touched by corner tiles
  only; the resulting linear equations force two opposite corner tiles to
  have equal sides, contradicting pairwise non-congruence.  With exactly two
  extra pieces on opposite edges, the two edge partitions force the extra
  sides to satisfy `e₁ + e₂ = 0`, again a contradiction.

The remaining gap of the true minimality statement (no perfect squared
square with `7 ≤ n ≤ 20` pieces, so that Duijvestijn's order-21 dissection
is optimal) is Duijvestijn's exhaustive computer search and is *not*
formalized here; see the project README for its status.
-/

namespace LeanProofs

namespace SquaredSquare

/-! ## Generic list helpers -/

/-- Extract the relation of a `Pairwise` list between two distinct members,
in one order or the other. -/
theorem pairwise_of_mem_ne {α : Type*} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b →
      R a b ∨ R b a := by
  intro l
  induction l with
  | nil => intro _ a b ha; cases ha
  | cons x t ih =>
    intro h a b ha hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · exact Or.inl (h.1 b hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr (h.1 a ha')
      · exact ih h.2 ha' hb' hab

/-- `Pairwise` implication that may use membership of both endpoints. -/
theorem pairwise_imp_mem {α : Type*} {R T : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R →
      (∀ a ∈ l, ∀ b ∈ l, R a b → T a b) → l.Pairwise T := by
  intro l
  induction l with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons x t ih =>
    intro h H
    rw [List.pairwise_cons] at h ⊢
    exact ⟨fun b hb => H x (List.mem_cons_self ..) b (List.mem_cons_of_mem _ hb)
        (h.1 b hb),
      ih h.2 fun a ha b hb hr =>
        H a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hr⟩

/-! ## Geometry of a dissection -/

variable {S : ℝ} {l : List Sq}

theorem tile_subset (hd : IsDissection S l) {q : Sq} (hq : q ∈ l) :
    q.toSet ⊆ bigSquare S := by
  intro p hp
  rw [← hd.cover]
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨q, hq, hp⟩

/-- Every tile of a dissection sits inside `[0, S]²`. -/
theorem tile_bounds (hd : IsDissection S l) {q : Sq} (hq : q ∈ l) :
    (0 ≤ q.x ∧ q.x + q.s ≤ S) ∧ 0 ≤ q.y ∧ q.y + q.s ≤ S := by
  have hs := (hd.pos q hq).le
  have h1 := tile_subset hd hq (corner_bl_mem hs)
  have h2 := tile_subset hd hq (corner_tr_mem hs)
  rw [mem_bigSquare] at h1 h2
  exact ⟨⟨h1.1.1, h2.1.2⟩, h1.2.1, h2.2.2⟩

theorem side_pos_of_dissection (hd : IsDissection S l) (hne : l ≠ []) :
    0 < S := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil l hne
  have hb := tile_bounds hd hq
  have := hd.pos q hq
  linarith [hb.1.1, hb.1.2]

/-- In a dissection with at least two pieces, every side is smaller than the
side of the big square. -/
theorem side_lt_of_two_le (hd : IsDissection S l) (h2 : 2 ≤ l.length)
    {q : Sq} (hq : q ∈ l) : q.s < S := by
  have hb := tile_bounds hd hq
  have hle : q.s ≤ S := by linarith [hb.1.1, hb.1.2]
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  -- if q.s = S then q fills the square and any other piece has nowhere to go
  exfalso
  have hx0 : q.x = 0 := by linarith [hb.1.1, hb.1.2]
  have hy0 : q.y = 0 := by linarith [hb.2.1, hb.2.2]
  match l, h2, hd, hq with
  | x :: y :: t, _, hd, hq =>
    have hdisj := hd.disj
    rw [List.pairwise_cons] at hdisj
    -- the interior of any piece is inside the interior of q
    have hsub : ∀ r ∈ x :: y :: t, r.inn ⊆ q.inn := by
      intro r hr p hp
      have hbr := tile_bounds hd hr
      rw [Sq.mem_inn] at hp ⊢
      rw [hx0, hy0, h]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
        linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2,
          hbr.1.1, hbr.1.2, hbr.2.1, hbr.2.2]
    rcases List.mem_cons.mp hq with rfl | hq'
    · -- q is the head; the second piece's interior meets q's interior
      have hy := hdisj.1 y (List.mem_cons_self ..)
      have hyc := Sq.center_mem_inn (hd.pos y (by simp))
      exact Set.disjoint_left.mp hy (hsub y (by simp) hyc) hyc
    · -- q is later; the head's interior meets q's interior
      have hx := hdisj.1 q hq'
      have hxc := Sq.center_mem_inn (hd.pos x (by simp))
      exact Set.disjoint_left.mp hx hxc (hsub x (by simp) hxc)

/-! ## Corner tiles -/

theorem exists_corner_bl (hd : IsDissection S l) (hS : 0 < S) :
    ∃ q ∈ l, q.x = 0 ∧ q.y = 0 := by
  have hc : ((0 : ℝ), (0 : ℝ)) ∈ bigSquare S := by
    rw [mem_bigSquare]; constructor <;> constructor <;> simp <;> linarith
  rw [← hd.cover] at hc
  simp only [Set.mem_iUnion, exists_prop] at hc
  obtain ⟨q, hq, hqc⟩ := hc
  rw [Sq.mem_toSet] at hqc
  have hb := tile_bounds hd hq
  exact ⟨q, hq, by linarith [hqc.1.1, hb.1.1], by linarith [hqc.2.1, hb.2.1]⟩

theorem exists_corner_br (hd : IsDissection S l) (hS : 0 < S) :
    ∃ q ∈ l, q.x + q.s = S ∧ q.y = 0 := by
  have hc : ((S : ℝ), (0 : ℝ)) ∈ bigSquare S := by
    rw [mem_bigSquare]; constructor <;> constructor <;> simp <;> linarith
  rw [← hd.cover] at hc
  simp only [Set.mem_iUnion, exists_prop] at hc
  obtain ⟨q, hq, hqc⟩ := hc
  rw [Sq.mem_toSet] at hqc
  have hb := tile_bounds hd hq
  exact ⟨q, hq, by linarith [hqc.1.2, hb.1.2], by linarith [hqc.2.1, hb.2.1]⟩

theorem exists_corner_tl (hd : IsDissection S l) (hS : 0 < S) :
    ∃ q ∈ l, q.x = 0 ∧ q.y + q.s = S := by
  have hc : ((0 : ℝ), (S : ℝ)) ∈ bigSquare S := by
    rw [mem_bigSquare]; constructor <;> constructor <;> simp <;> linarith
  rw [← hd.cover] at hc
  simp only [Set.mem_iUnion, exists_prop] at hc
  obtain ⟨q, hq, hqc⟩ := hc
  rw [Sq.mem_toSet] at hqc
  have hb := tile_bounds hd hq
  exact ⟨q, hq, by linarith [hqc.1.1, hb.1.1], by linarith [hqc.2.2, hb.2.2]⟩

theorem exists_corner_tr (hd : IsDissection S l) (hS : 0 < S) :
    ∃ q ∈ l, q.x + q.s = S ∧ q.y + q.s = S := by
  have hc : ((S : ℝ), (S : ℝ)) ∈ bigSquare S := by
    rw [mem_bigSquare]; constructor <;> constructor <;> simp <;> linarith
  rw [← hd.cover] at hc
  simp only [Set.mem_iUnion, exists_prop] at hc
  obtain ⟨q, hq, hqc⟩ := hc
  rw [Sq.mem_toSet] at hqc
  have hb := tile_bounds hd hq
  exact ⟨q, hq, by linarith [hqc.1.2, hb.1.2], by linarith [hqc.2.2, hb.2.2]⟩

/-- Two distinct members of a dissection have disjoint interiors. -/
theorem disjoint_of_mem_ne (hd : IsDissection S l) {p q : Sq}
    (hp : p ∈ l) (hq : q ∈ l) (hne : p ≠ q) : Disjoint p.inn q.inn := by
  rcases pairwise_of_mem_ne hd.disj hp hq hne with h | h
  · exact h
  · exact h.symm

/-- Helper: two tiles whose open x- and y-ranges both overlap share an
interior point. -/
theorem exists_mem_inn_inter {p q : Sq}
    (hx1 : q.x < p.x + p.s) (hx2 : p.x < q.x + q.s)
    (hy1 : q.y < p.y + p.s) (hy2 : p.y < q.y + q.s)
    (hps : 0 < p.s) (hqs : 0 < q.s) :
    ∃ w, w ∈ p.inn ∧ w ∈ q.inn := by
  have hxm : max p.x q.x < min (p.x + p.s) (q.x + q.s) :=
    max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨by linarith, hx2⟩,
      lt_min_iff.mpr ⟨hx1, by linarith⟩⟩
  have hym : max p.y q.y < min (p.y + p.s) (q.y + q.s) :=
    max_lt_iff.mpr ⟨lt_min_iff.mpr ⟨by linarith, hy2⟩,
      lt_min_iff.mpr ⟨hy1, by linarith⟩⟩
  refine ⟨((max p.x q.x + min (p.x + p.s) (q.x + q.s)) / 2,
           (max p.y q.y + min (p.y + p.s) (q.y + q.s)) / 2), ?_, ?_⟩ <;>
    rw [Sq.mem_inn] <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · linarith [le_max_left p.x q.x]
  · linarith [min_le_left (p.x + p.s) (q.x + q.s)]
  · linarith [le_max_left p.y q.y]
  · linarith [min_le_left (p.y + p.s) (q.y + q.s)]
  · linarith [le_max_right p.x q.x]
  · linarith [min_le_right (p.x + p.s) (q.x + q.s)]
  · linarith [le_max_right p.y q.y]
  · linarith [min_le_right (p.y + p.s) (q.y + q.s)]

/-- Two corner tiles at the same corner coincide.  Stated for a generic
corner point `(cx, cy)` given membership of the corner in both tiles'
closures at matching corner position; specialized below. -/
theorem eq_of_shared_interior_point (hd : IsDissection S l) {p q : Sq}
    (hp : p ∈ l) (hq : q ∈ l)
    (h : ∃ w, w ∈ p.inn ∧ w ∈ q.inn) : p = q := by
  by_contra hne
  obtain ⟨w, hw1, hw2⟩ := h
  exact Set.disjoint_left.mp (disjoint_of_mem_ne hd hp hq hne) hw1 hw2

/-- Tiles at the bottom-left corner are unique. -/
theorem corner_bl_unique (hd : IsDissection S l) {p q : Sq}
    (hp : p ∈ l) (hq : q ∈ l)
    (hpc : p.x = 0 ∧ p.y = 0) (hqc : q.x = 0 ∧ q.y = 0) : p = q := by
  have hps := hd.pos p hp
  have hqs := hd.pos q hq
  refine eq_of_shared_interior_point hd hp hq
    (exists_mem_inn_inter ?_ ?_ ?_ ?_ hps hqs) <;>
    linarith [hpc.1, hpc.2, hqc.1, hqc.2]

theorem corner_br_unique (hd : IsDissection S l) {p q : Sq}
    (hp : p ∈ l) (hq : q ∈ l)
    (hpc : p.x + p.s = S ∧ p.y = 0) (hqc : q.x + q.s = S ∧ q.y = 0) :
    p = q := by
  have hps := hd.pos p hp
  have hqs := hd.pos q hq
  refine eq_of_shared_interior_point hd hp hq
    (exists_mem_inn_inter ?_ ?_ ?_ ?_ hps hqs) <;>
    linarith [hpc.1, hpc.2, hqc.1, hqc.2]

theorem corner_tl_unique (hd : IsDissection S l) {p q : Sq}
    (hp : p ∈ l) (hq : q ∈ l)
    (hpc : p.x = 0 ∧ p.y + p.s = S) (hqc : q.x = 0 ∧ q.y + q.s = S) :
    p = q := by
  have hps := hd.pos p hp
  have hqs := hd.pos q hq
  refine eq_of_shared_interior_point hd hp hq
    (exists_mem_inn_inter ?_ ?_ ?_ ?_ hps hqs) <;>
    linarith [hpc.1, hpc.2, hqc.1, hqc.2]

theorem corner_tr_unique (hd : IsDissection S l) {p q : Sq}
    (hp : p ∈ l) (hq : q ∈ l)
    (hpc : p.x + p.s = S ∧ p.y + p.s = S)
    (hqc : q.x + q.s = S ∧ q.y + q.s = S) : p = q := by
  have hps := hd.pos p hp
  have hqs := hd.pos q hq
  refine eq_of_shared_interior_point hd hp hq
    (exists_mem_inn_inter ?_ ?_ ?_ ?_ hps hqs) <;>
    linarith [hpc.1, hpc.2, hqc.1, hqc.2]

/-! ## Edge partitions -/

/-- Interior-disjoint tiles whose open `y`-ranges overlap are `x`-separated. -/
theorem sep1x_of_disjoint {p q : Sq} (hps : 0 < p.s) (hqs : 0 < q.s)
    (hdisj : Disjoint p.inn q.inn)
    (hy1 : q.y < p.y + p.s) (hy2 : p.y < q.y + q.s) :
    sep1 (p.x, p.s) (q.x, q.s) := by
  by_contra h
  simp only [sep1, not_or, not_le] at h
  obtain ⟨w, hw1, hw2⟩ :=
    exists_mem_inn_inter h.1 h.2 hy1 hy2 hps hqs
  exact Set.disjoint_left.mp hdisj hw1 hw2

/-- Interior-disjoint tiles whose open `x`-ranges overlap are `y`-separated. -/
theorem sep1y_of_disjoint {p q : Sq} (hps : 0 < p.s) (hqs : 0 < q.s)
    (hdisj : Disjoint p.inn q.inn)
    (hx1 : q.x < p.x + p.s) (hx2 : p.x < q.x + q.s) :
    sep1 (p.y, p.s) (q.y, q.s) := by
  by_contra h
  simp only [sep1, not_or, not_le] at h
  obtain ⟨w, hw1, hw2⟩ :=
    exists_mem_inn_inter hx1 hx2 h.1 h.2 hps hqs
  exact Set.disjoint_left.mp hdisj hw1 hw2

/-- The tiles touching the bottom edge (`q.y = 0`), collected without
repetition in `B`, have sides summing to `S`. -/
theorem bottom_sum (hd : IsDissection S l) (hS : 0 < S) {B : List Sq}
    (hBmem : ∀ q ∈ B, q ∈ l) (hBy : ∀ q ∈ B, q.y = 0)
    (hBall : ∀ q ∈ l, q.y = 0 → q ∈ B) (hBne : B.Pairwise (· ≠ ·)) :
    (B.map Sq.s).sum = S := by
  have hpos : ∀ p ∈ B.map (fun q => (q.x, q.s)), 0 < p.2 := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hd.pos q (hBmem q hq)
  have hbnd : ∀ p ∈ B.map (fun q => (q.x, q.s)), 0 ≤ p.1 ∧ p.1 + p.2 ≤ S := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (tile_bounds hd (hBmem q hq)).1
  have hsep : (B.map fun q => (q.x, q.s)).Pairwise sep1 := by
    rw [List.pairwise_map]
    refine pairwise_imp_mem hBne ?_
    intro a ha b hb hne
    have hda := hd.pos a (hBmem a ha)
    have hdb := hd.pos b (hBmem b hb)
    refine sep1x_of_disjoint hda hdb
      (disjoint_of_mem_ne hd (hBmem a ha) (hBmem b hb) hne) ?_ ?_ <;>
      rw [hBy a ha, hBy b hb] <;> linarith
  have hcov : ∀ x, 0 < x → x ≤ S →
      ∃ p ∈ B.map (fun q => (q.x, q.s)), p.1 ≤ x ∧ x ≤ p.1 + p.2 := by
    intro x hx1 hx2
    have hc : ((x : ℝ), (0 : ℝ)) ∈ bigSquare S := by
      rw [mem_bigSquare]
      exact ⟨⟨hx1.le, hx2⟩, le_rfl, hS.le⟩
    rw [← hd.cover] at hc
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨r, hr, hrc⟩ := hc
    rw [Sq.mem_toSet] at hrc
    have hb := tile_bounds hd hr
    have hry : r.y = 0 := by linarith [hrc.2.1, hb.2.1]
    refine ⟨(r.x, r.s), ?_, hrc.1.1, hrc.1.2⟩
    rw [List.mem_map]
    exact ⟨r, hBall r hr hry, rfl⟩
  have key := interval_cover_sum' (B.map fun q => (q.x, q.s)) 0 S hS.le
    hpos hbnd hsep hcov
  have hmaps : (B.map fun q => (q.x, q.s)).map Prod.snd = B.map Sq.s := by
    rw [List.map_map]
    rfl
  rw [hmaps] at key
  linarith

/-- The tiles touching the top edge (`q.y + q.s = S`) have sides summing to
`S`. -/
theorem top_sum (hd : IsDissection S l) (hS : 0 < S) {B : List Sq}
    (hBmem : ∀ q ∈ B, q ∈ l) (hBy : ∀ q ∈ B, q.y + q.s = S)
    (hBall : ∀ q ∈ l, q.y + q.s = S → q ∈ B) (hBne : B.Pairwise (· ≠ ·)) :
    (B.map Sq.s).sum = S := by
  have hpos : ∀ p ∈ B.map (fun q => (q.x, q.s)), 0 < p.2 := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hd.pos q (hBmem q hq)
  have hbnd : ∀ p ∈ B.map (fun q => (q.x, q.s)), 0 ≤ p.1 ∧ p.1 + p.2 ≤ S := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (tile_bounds hd (hBmem q hq)).1
  have hsep : (B.map fun q => (q.x, q.s)).Pairwise sep1 := by
    rw [List.pairwise_map]
    refine pairwise_imp_mem hBne ?_
    intro a ha b hb hne
    have hda := hd.pos a (hBmem a ha)
    have hdb := hd.pos b (hBmem b hb)
    refine sep1x_of_disjoint hda hdb
      (disjoint_of_mem_ne hd (hBmem a ha) (hBmem b hb) hne) ?_ ?_ <;>
      linarith [hBy a ha, hBy b hb]
  have hcov : ∀ x, 0 < x → x ≤ S →
      ∃ p ∈ B.map (fun q => (q.x, q.s)), p.1 ≤ x ∧ x ≤ p.1 + p.2 := by
    intro x hx1 hx2
    have hc : ((x : ℝ), (S : ℝ)) ∈ bigSquare S := by
      rw [mem_bigSquare]
      exact ⟨⟨hx1.le, hx2⟩, hS.le, le_rfl⟩
    rw [← hd.cover] at hc
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨r, hr, hrc⟩ := hc
    rw [Sq.mem_toSet] at hrc
    have hb := tile_bounds hd hr
    have hry : r.y + r.s = S := by linarith [hrc.2.2, hb.2.2]
    refine ⟨(r.x, r.s), ?_, hrc.1.1, hrc.1.2⟩
    rw [List.mem_map]
    exact ⟨r, hBall r hr hry, rfl⟩
  have key := interval_cover_sum' (B.map fun q => (q.x, q.s)) 0 S hS.le
    hpos hbnd hsep hcov
  have hmaps : (B.map fun q => (q.x, q.s)).map Prod.snd = B.map Sq.s := by
    rw [List.map_map]
    rfl
  rw [hmaps] at key
  linarith

/-- The tiles touching the left edge (`q.x = 0`) have sides summing to `S`. -/
theorem left_sum (hd : IsDissection S l) (hS : 0 < S) {B : List Sq}
    (hBmem : ∀ q ∈ B, q ∈ l) (hBx : ∀ q ∈ B, q.x = 0)
    (hBall : ∀ q ∈ l, q.x = 0 → q ∈ B) (hBne : B.Pairwise (· ≠ ·)) :
    (B.map Sq.s).sum = S := by
  have hpos : ∀ p ∈ B.map (fun q => (q.y, q.s)), 0 < p.2 := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hd.pos q (hBmem q hq)
  have hbnd : ∀ p ∈ B.map (fun q => (q.y, q.s)), 0 ≤ p.1 ∧ p.1 + p.2 ≤ S := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (tile_bounds hd (hBmem q hq)).2
  have hsep : (B.map fun q => (q.y, q.s)).Pairwise sep1 := by
    rw [List.pairwise_map]
    refine pairwise_imp_mem hBne ?_
    intro a ha b hb hne
    have hda := hd.pos a (hBmem a ha)
    have hdb := hd.pos b (hBmem b hb)
    refine sep1y_of_disjoint hda hdb
      (disjoint_of_mem_ne hd (hBmem a ha) (hBmem b hb) hne) ?_ ?_ <;>
      rw [hBx a ha, hBx b hb] <;> linarith
  have hcov : ∀ y, 0 < y → y ≤ S →
      ∃ p ∈ B.map (fun q => (q.y, q.s)), p.1 ≤ y ∧ y ≤ p.1 + p.2 := by
    intro y hy1 hy2
    have hc : ((0 : ℝ), (y : ℝ)) ∈ bigSquare S := by
      rw [mem_bigSquare]
      exact ⟨⟨le_rfl, hS.le⟩, hy1.le, hy2⟩
    rw [← hd.cover] at hc
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨r, hr, hrc⟩ := hc
    rw [Sq.mem_toSet] at hrc
    have hb := tile_bounds hd hr
    have hrx : r.x = 0 := by linarith [hrc.1.1, hb.1.1]
    refine ⟨(r.y, r.s), ?_, hrc.2.1, hrc.2.2⟩
    rw [List.mem_map]
    exact ⟨r, hBall r hr hrx, rfl⟩
  have key := interval_cover_sum' (B.map fun q => (q.y, q.s)) 0 S hS.le
    hpos hbnd hsep hcov
  have hmaps : (B.map fun q => (q.y, q.s)).map Prod.snd = B.map Sq.s := by
    rw [List.map_map]
    rfl
  rw [hmaps] at key
  linarith

/-- The tiles touching the right edge (`q.x + q.s = S`) have sides summing to
`S`. -/
theorem right_sum (hd : IsDissection S l) (hS : 0 < S) {B : List Sq}
    (hBmem : ∀ q ∈ B, q ∈ l) (hBx : ∀ q ∈ B, q.x + q.s = S)
    (hBall : ∀ q ∈ l, q.x + q.s = S → q ∈ B) (hBne : B.Pairwise (· ≠ ·)) :
    (B.map Sq.s).sum = S := by
  have hpos : ∀ p ∈ B.map (fun q => (q.y, q.s)), 0 < p.2 := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hd.pos q (hBmem q hq)
  have hbnd : ∀ p ∈ B.map (fun q => (q.y, q.s)), 0 ≤ p.1 ∧ p.1 + p.2 ≤ S := by
    intro p hp
    rw [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact (tile_bounds hd (hBmem q hq)).2
  have hsep : (B.map fun q => (q.y, q.s)).Pairwise sep1 := by
    rw [List.pairwise_map]
    refine pairwise_imp_mem hBne ?_
    intro a ha b hb hne
    have hda := hd.pos a (hBmem a ha)
    have hdb := hd.pos b (hBmem b hb)
    refine sep1y_of_disjoint hda hdb
      (disjoint_of_mem_ne hd (hBmem a ha) (hBmem b hb) hne) ?_ ?_ <;>
      linarith [hBx a ha, hBx b hb]
  have hcov : ∀ y, 0 < y → y ≤ S →
      ∃ p ∈ B.map (fun q => (q.y, q.s)), p.1 ≤ y ∧ y ≤ p.1 + p.2 := by
    intro y hy1 hy2
    have hc : ((S : ℝ), (y : ℝ)) ∈ bigSquare S := by
      rw [mem_bigSquare]
      exact ⟨⟨hS.le, le_rfl⟩, hy1.le, hy2⟩
    rw [← hd.cover] at hc
    simp only [Set.mem_iUnion, exists_prop] at hc
    obtain ⟨r, hr, hrc⟩ := hc
    rw [Sq.mem_toSet] at hrc
    have hb := tile_bounds hd hr
    have hrx : r.x + r.s = S := by linarith [hrc.1.2, hb.1.2]
    refine ⟨(r.y, r.s), ?_, hrc.2.1, hrc.2.2⟩
    rw [List.mem_map]
    exact ⟨r, hBall r hr hrx, rfl⟩
  have key := interval_cover_sum' (B.map fun q => (q.y, q.s)) 0 S hS.le
    hpos hbnd hsep hcov
  have hmaps : (B.map fun q => (q.y, q.s)).map Prod.snd = B.map Sq.s := by
    rw [List.map_map]
    rfl
  rw [hmaps] at key
  linarith

/-! ## Corner data and the pair contradictions -/

/-- The four corner tiles of a dissection. -/
structure CornerData (S : ℝ) (l : List Sq) where
  BL : Sq
  BR : Sq
  TL : Sq
  TR : Sq
  hBL : BL ∈ l
  hBLx : BL.x = 0
  hBLy : BL.y = 0
  hBR : BR ∈ l
  hBRx : BR.x + BR.s = S
  hBRy : BR.y = 0
  hTL : TL ∈ l
  hTLx : TL.x = 0
  hTLy : TL.y + TL.s = S
  hTR : TR ∈ l
  hTRx : TR.x + TR.s = S
  hTRy : TR.y + TR.s = S

theorem exists_cornerData (hd : IsDissection S l) (hS : 0 < S) :
    Nonempty (CornerData S l) := by
  obtain ⟨BL, hBLm, hBLc⟩ := exists_corner_bl hd hS
  obtain ⟨BR, hBRm, hBRc⟩ := exists_corner_br hd hS
  obtain ⟨TL, hTLm, hTLc⟩ := exists_corner_tl hd hS
  obtain ⟨TR, hTRm, hTRc⟩ := exists_corner_tr hd hS
  exact ⟨⟨BL, BR, TL, TR, hBLm, hBLc.1, hBLc.2, hBRm, hBRc.1, hBRc.2,
    hTLm, hTLc.1, hTLc.2, hTRm, hTRc.1, hTRc.2⟩⟩

/-- The four corner tiles are pairwise distinct (their coincidence would
force a piece of side `S`). -/
theorem CornerData.ne_all (hd : IsDissection S l) (h2 : 2 ≤ l.length)
    (cd : CornerData S l) :
    cd.BL ≠ cd.BR ∧ cd.BL ≠ cd.TL ∧ cd.BL ≠ cd.TR ∧
    cd.BR ≠ cd.TL ∧ cd.BR ≠ cd.TR ∧ cd.TL ≠ cd.TR := by
  have hltBL := side_lt_of_two_le hd h2 cd.hBL
  have hltBR := side_lt_of_two_le hd h2 cd.hBR
  have hltTL := side_lt_of_two_le hd h2 cd.hTL
  have hltTR := side_lt_of_two_le hd h2 cd.hTR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro he
  · have h1 : cd.BL.x + cd.BL.s = S := by rw [he]; exact cd.hBRx
    rw [cd.hBLx] at h1; linarith
  · have h1 : cd.BL.y + cd.BL.s = S := by rw [he]; exact cd.hTLy
    rw [cd.hBLy] at h1; linarith
  · have h1 : cd.BL.x + cd.BL.s = S := by rw [he]; exact cd.hTRx
    rw [cd.hBLx] at h1; linarith
  · have h1 : cd.BR.y + cd.BR.s = S := by rw [he]; exact cd.hTLy
    rw [cd.hBRy] at h1; linarith
  · have h1 : cd.BR.y + cd.BR.s = S := by rw [he]; exact cd.hTRy
    rw [cd.hBRy] at h1; linarith
  · have h1 : cd.TL.x + cd.TL.s = S := by rw [he]; exact cd.hTRx
    rw [cd.hTLx] at h1; linarith

/-- Two distinct pieces of equal side contradict pairwise non-congruence. -/
theorem no_congruent_pair
    (hnc : l.Pairwise fun p q => ¬Congruent p.toSet q.toSet)
    {p q : Sq} (hp : p ∈ l) (hq : q ∈ l) (hne : p ≠ q) (hs : p.s = q.s) :
    False := by
  rcases pairwise_of_mem_ne hnc hp hq hne with h | h
  · exact h (congruent_of_side_eq hs)
  · exact h (congruent_of_side_eq hs.symm)

/-- A non-corner piece can touch at most one edge of the big square. -/
theorem flag_unique (hd : IsDissection S l) (h2 : 2 ≤ l.length)
    (cd : CornerData S l) {E : Sq} (hE : E ∈ l)
    (hEBL : E ≠ cd.BL) (hEBR : E ≠ cd.BR) (hETL : E ≠ cd.TL)
    (hETR : E ≠ cd.TR) :
    (E.y = 0 → E.y + E.s ≠ S ∧ E.x ≠ 0 ∧ E.x + E.s ≠ S) ∧
    (E.y + E.s = S → E.x ≠ 0 ∧ E.x + E.s ≠ S) ∧
    (E.x = 0 → E.x + E.s ≠ S) := by
  have hlt := side_lt_of_two_le hd h2 hE
  refine ⟨fun hB => ⟨?_, ?_, ?_⟩, fun hT => ⟨?_, ?_⟩, fun hL => ?_⟩
  · intro hT; rw [hB] at hT; linarith
  · intro hL
    exact hEBL (corner_bl_unique hd hE cd.hBL ⟨hL, hB⟩ ⟨cd.hBLx, cd.hBLy⟩)
  · intro hR
    exact hEBR (corner_br_unique hd hE cd.hBR ⟨hR, hB⟩ ⟨cd.hBRx, cd.hBRy⟩)
  · intro hL
    exact hETL (corner_tl_unique hd hE cd.hTL ⟨hL, hT⟩ ⟨cd.hTLx, cd.hTLy⟩)
  · intro hR
    exact hETR (corner_tr_unique hd hE cd.hTR ⟨hR, hT⟩ ⟨cd.hTRx, cd.hTRy⟩)
  · intro hR; rw [hL] at hR; linarith

section SumLemmas

variable (hd : IsDissection S l) (h2 : 2 ≤ l.length)
  (cd : CornerData S l) (hS : 0 < S)

include hd h2 hS

/-- Bottom edge touched only by `BL, BR`: their sides sum to `S`. -/
theorem bottom_two (honly : ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR) :
    cd.BL.s + cd.BR.s = S := by
  obtain ⟨h1, -, -, -, -, -⟩ := cd.ne_all hd h2
  have hsum := bottom_sum hd hS (B := [cd.BL, cd.BR])
    (by intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact cd.hBL
        · rw [List.mem_singleton] at hq'; rw [hq']; exact cd.hBR)
    (by intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact cd.hBLy
        · rw [List.mem_singleton] at hq'; rw [hq']; exact cd.hBRy)
    (by intro q hql hqy
        rcases honly q hql hqy with rfl | rfl
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
    (by rw [List.pairwise_cons]
        exact ⟨fun b hb => by rw [List.mem_singleton] at hb; rw [hb]; exact h1,
          List.pairwise_singleton _ _⟩)
  simpa using hsum

/-- Top edge touched only by `TL, TR`: their sides sum to `S`. -/
theorem top_two (honly : ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR) :
    cd.TL.s + cd.TR.s = S := by
  obtain ⟨-, -, -, -, -, h1⟩ := cd.ne_all hd h2
  have hsum := top_sum hd hS (B := [cd.TL, cd.TR])
    (by intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact cd.hTL
        · rw [List.mem_singleton] at hq'; rw [hq']; exact cd.hTR)
    (by intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact cd.hTLy
        · rw [List.mem_singleton] at hq'; rw [hq']; exact cd.hTRy)
    (by intro q hql hqy
        rcases honly q hql hqy with rfl | rfl
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
    (by rw [List.pairwise_cons]
        exact ⟨fun b hb => by rw [List.mem_singleton] at hb; rw [hb]; exact h1,
          List.pairwise_singleton _ _⟩)
  simpa using hsum

/-- Left edge touched only by `BL, TL`: their sides sum to `S`. -/
theorem left_two (honly : ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL) :
    cd.BL.s + cd.TL.s = S := by
  obtain ⟨-, h1, -, -, -, -⟩ := cd.ne_all hd h2
  have hsum := left_sum hd hS (B := [cd.BL, cd.TL])
    (by intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact cd.hBL
        · rw [List.mem_singleton] at hq'; rw [hq']; exact cd.hTL)
    (by intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact cd.hBLx
        · rw [List.mem_singleton] at hq'; rw [hq']; exact cd.hTLx)
    (by intro q hql hqx
        rcases honly q hql hqx with rfl | rfl
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
    (by rw [List.pairwise_cons]
        exact ⟨fun b hb => by rw [List.mem_singleton] at hb; rw [hb]; exact h1,
          List.pairwise_singleton _ _⟩)
  simpa using hsum

/-- Right edge touched only by `BR, TR`: their sides sum to `S`. -/
theorem right_two (honly : ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR) :
    cd.BR.s + cd.TR.s = S := by
  obtain ⟨-, -, -, -, h1, -⟩ := cd.ne_all hd h2
  have hsum := right_sum hd hS (B := [cd.BR, cd.TR])
    (by intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact cd.hBR
        · rw [List.mem_singleton] at hq'; rw [hq']; exact cd.hTR)
    (by intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact cd.hBRx
        · rw [List.mem_singleton] at hq'; rw [hq']; exact cd.hTRx)
    (by intro q hql hqx
        rcases honly q hql hqx with rfl | rfl
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))
    (by rw [List.pairwise_cons]
        exact ⟨fun b hb => by rw [List.mem_singleton] at hb; rw [hb]; exact h1,
          List.pairwise_singleton _ _⟩)
  simpa using hsum

end SumLemmas

section PairLemmas

variable (hd : IsDissection S l) (h2 : 2 ≤ l.length)
  (hnc : l.Pairwise fun p q => ¬Congruent p.toSet q.toSet)
  (cd : CornerData S l) (hS : 0 < S)

include hd h2 hnc hS

/-- Adjacent clean pair bottom+left forces `BR.s = TL.s` — impossible. -/
theorem clean_bottom_left
    (hbot : ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR)
    (hleft : ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL) : False := by
  obtain ⟨-, -, -, h1, -, -⟩ := cd.ne_all hd h2
  have e1 := bottom_two hd h2 cd hS hbot
  have e2 := left_two hd h2 cd hS hleft
  exact no_congruent_pair hnc cd.hBR cd.hTL h1 (by linarith)

/-- Adjacent clean pair bottom+right forces `BL.s = TR.s` — impossible. -/
theorem clean_bottom_right
    (hbot : ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR)
    (hright : ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR) : False := by
  obtain ⟨-, -, h1, -, -, -⟩ := cd.ne_all hd h2
  have e1 := bottom_two hd h2 cd hS hbot
  have e2 := right_two hd h2 cd hS hright
  exact no_congruent_pair hnc cd.hBL cd.hTR h1 (by linarith)

/-- Adjacent clean pair top+left forces `BL.s = TR.s` — impossible. -/
theorem clean_top_left
    (htop : ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR)
    (hleft : ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL) : False := by
  obtain ⟨-, -, h1, -, -, -⟩ := cd.ne_all hd h2
  have e1 := top_two hd h2 cd hS htop
  have e2 := left_two hd h2 cd hS hleft
  exact no_congruent_pair hnc cd.hBL cd.hTR h1 (by linarith)

/-- Adjacent clean pair top+right forces `BR.s = TL.s` — impossible. -/
theorem clean_top_right
    (htop : ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR)
    (hright : ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR) : False := by
  obtain ⟨-, -, -, h1, -, -⟩ := cd.ne_all hd h2
  have e1 := top_two hd h2 cd hS htop
  have e2 := right_two hd h2 cd hS hright
  exact no_congruent_pair hnc cd.hBR cd.hTL h1 (by linarith)

end PairLemmas

/-! ## At least four pieces -/

theorem four_le_length (h : IsPerfectSquaredSquare S l) : 4 ≤ l.length := by
  obtain ⟨hd, h2, hnc⟩ := h
  have hne : l ≠ [] := by
    intro h0
    rw [h0] at h2
    simp at h2
  have hS : 0 < S := side_pos_of_dissection hd hne
  obtain ⟨cd⟩ := exists_cornerData hd hS
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cd.ne_all hd h2
  have hsub : [cd.BL, cd.BR, cd.TL, cd.TR] ⊆ l := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact cd.hBL
    · exact cd.hBR
    · exact cd.hTL
    · exact cd.hTR
  have hnd : [cd.BL, cd.BR, cd.TL, cd.TR].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, not_false⟩
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

/-! ## Extracting the corner tiles from the list -/

theorem corners_subperm (hd : IsDissection S l) (h2 : 2 ≤ l.length)
    (cd : CornerData S l) :
    List.Subperm [cd.BL, cd.BR, cd.TL, cd.TR] l := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cd.ne_all hd h2
  refine List.subperm_of_subset ?_ ?_
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨n1, n2, n3⟩, ⟨n4, n5⟩, n6, not_false⟩
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact cd.hBL
    · exact cd.hBR
    · exact cd.hTL
    · exact cd.hTR

theorem exists_rest (hd : IsDissection S l) (h2 : 2 ≤ l.length)
    (cd : CornerData S l) :
    ∃ rest : List Sq, l.Perm ([cd.BL, cd.BR, cd.TL, cd.TR] ++ rest) ∧
      rest.length + 4 = l.length := by
  obtain ⟨mid, hmp, hms⟩ := corners_subperm hd h2 cd
  obtain ⟨rest, hperm⟩ := List.Sublist.exists_perm_append hms
  have hfull : l.Perm ([cd.BL, cd.BR, cd.TL, cd.TR] ++ rest) :=
    hperm.trans (hmp.append_right rest)
  refine ⟨rest, hfull, ?_⟩
  have := hfull.length_eq
  simp only [List.length_append, List.length_cons, List.length_nil] at this
  omega

/-- Members of the remainder are distinct from all four corner tiles. -/
theorem rest_facts (hd : IsDissection S l) {rest : List Sq}
    (cd : CornerData S l)
    (hperm : l.Perm ([cd.BL, cd.BR, cd.TL, cd.TR] ++ rest)) {E : Sq}
    (hE : E ∈ rest) :
    E ∈ l ∧ E ≠ cd.BL ∧ E ≠ cd.BR ∧ E ≠ cd.TL ∧ E ≠ cd.TR := by
  have hEl : E ∈ l := hperm.mem_iff.mpr (List.mem_append.mpr (Or.inr hE))
  have hdisj := (hperm.pairwise_iff (fun {_ _} h => h.symm)).mp hd.disj
  rw [List.pairwise_append] at hdisj
  obtain ⟨-, -, hcross⟩ := hdisj
  refine ⟨hEl, ?_, ?_, ?_, ?_⟩ <;> intro he
  · have hdj := hcross cd.BL (by simp) E hE
    rw [he] at hdj
    have hc := Sq.center_mem_inn (hd.pos cd.BL cd.hBL)
    exact Set.disjoint_left.mp hdj hc hc
  · have hdj := hcross cd.BR (by simp) E hE
    rw [he] at hdj
    have hc := Sq.center_mem_inn (hd.pos cd.BR cd.hBR)
    exact Set.disjoint_left.mp hdj hc hc
  · have hdj := hcross cd.TL (by simp) E hE
    rw [he] at hdj
    have hc := Sq.center_mem_inn (hd.pos cd.TL cd.hTL)
    exact Set.disjoint_left.mp hdj hc hc
  · have hdj := hcross cd.TR (by simp) E hE
    rw [he] at hdj
    have hc := Sq.center_mem_inn (hd.pos cd.TR cd.hTR)
    exact Set.disjoint_left.mp hdj hc hc

/-! ## Opposite-edge partitions -/

section OppositeLemmas

variable (hd : IsDissection S l) (h2 : 2 ≤ l.length)
  (cd : CornerData S l) (hS : 0 < S)

include hd h2 hS

/-- One extra piece on the bottom edge and one on the top edge, with left and
right edges clean: the two three-piece partitions and the two two-piece
partitions force `E1.s + E2.s = 0` — impossible. -/
theorem opposite_bottom_top {E1 E2 : Sq}
    (hE1 : E1 ∈ l) (hE2 : E2 ∈ l)
    (hE1BL : E1 ≠ cd.BL) (hE1BR : E1 ≠ cd.BR)
    (hE2TL : E2 ≠ cd.TL) (hE2TR : E2 ≠ cd.TR)
    (hE1y : E1.y = 0) (hE2y : E2.y + E2.s = S)
    (hbot : ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR ∨ q = E1)
    (htop : ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR ∨ q = E2)
    (hleft : ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL)
    (hright : ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR) : False := by
  obtain ⟨n1, -, -, -, -, n6⟩ := cd.ne_all hd h2
  have hb3 : cd.BL.s + cd.BR.s + E1.s = S := by
    have hsum := bottom_sum hd hS (B := [cd.BL, cd.BR, E1])
      (by intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact cd.hBL
          · exact cd.hBR
          · exact hE1)
      (by intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact cd.hBLy
          · exact cd.hBRy
          · exact hE1y)
      (by intro q hql hqy
          rcases hbot q hql hqy with rfl | rfl | rfl
          · simp
          · simp
          · simp)
      (by rw [List.pairwise_cons]
          refine ⟨?_, ?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact n1
            · rw [List.mem_singleton] at hb'
              rw [hb']
              exact fun he => hE1BL he.symm
          · rw [List.pairwise_cons]
            refine ⟨?_, List.pairwise_singleton _ _⟩
            intro b hb
            rw [List.mem_singleton] at hb
            rw [hb]
            exact fun he => hE1BR he.symm)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hsum
    linarith
  have ht3 : cd.TL.s + cd.TR.s + E2.s = S := by
    have hsum := top_sum hd hS (B := [cd.TL, cd.TR, E2])
      (by intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact cd.hTL
          · exact cd.hTR
          · exact hE2)
      (by intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact cd.hTLy
          · exact cd.hTRy
          · exact hE2y)
      (by intro q hql hqy
          rcases htop q hql hqy with rfl | rfl | rfl
          · simp
          · simp
          · simp)
      (by rw [List.pairwise_cons]
          refine ⟨?_, ?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact n6
            · rw [List.mem_singleton] at hb'
              rw [hb']
              exact fun he => hE2TL he.symm
          · rw [List.pairwise_cons]
            refine ⟨?_, List.pairwise_singleton _ _⟩
            intro b hb
            rw [List.mem_singleton] at hb
            rw [hb]
            exact fun he => hE2TR he.symm)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hsum
    linarith
  have hl2 := left_two hd h2 cd hS hleft
  have hr2 := right_two hd h2 cd hS hright
  have p1 := hd.pos E1 hE1
  have p2 := hd.pos E2 hE2
  linarith

/-- One extra piece on the left edge and one on the right edge, with bottom
and top edges clean — impossible. -/
theorem opposite_left_right {E1 E2 : Sq}
    (hE1 : E1 ∈ l) (hE2 : E2 ∈ l)
    (hE1BL : E1 ≠ cd.BL) (hE1TL : E1 ≠ cd.TL)
    (hE2BR : E2 ≠ cd.BR) (hE2TR : E2 ≠ cd.TR)
    (hE1x : E1.x = 0) (hE2x : E2.x + E2.s = S)
    (hbot : ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR)
    (htop : ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR)
    (hleft : ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL ∨ q = E1)
    (hright : ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR ∨ q = E2) :
    False := by
  obtain ⟨-, n2, -, -, n5, -⟩ := cd.ne_all hd h2
  have hl3 : cd.BL.s + cd.TL.s + E1.s = S := by
    have hsum := left_sum hd hS (B := [cd.BL, cd.TL, E1])
      (by intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact cd.hBL
          · exact cd.hTL
          · exact hE1)
      (by intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact cd.hBLx
          · exact cd.hTLx
          · exact hE1x)
      (by intro q hql hqx
          rcases hleft q hql hqx with rfl | rfl | rfl
          · simp
          · simp
          · simp)
      (by rw [List.pairwise_cons]
          refine ⟨?_, ?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact n2
            · rw [List.mem_singleton] at hb'
              rw [hb']
              exact fun he => hE1BL he.symm
          · rw [List.pairwise_cons]
            refine ⟨?_, List.pairwise_singleton _ _⟩
            intro b hb
            rw [List.mem_singleton] at hb
            rw [hb]
            exact fun he => hE1TL he.symm)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hsum
    linarith
  have hr3 : cd.BR.s + cd.TR.s + E2.s = S := by
    have hsum := right_sum hd hS (B := [cd.BR, cd.TR, E2])
      (by intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact cd.hBR
          · exact cd.hTR
          · exact hE2)
      (by intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl
          · exact cd.hBRx
          · exact cd.hTRx
          · exact hE2x)
      (by intro q hql hqx
          rcases hright q hql hqx with rfl | rfl | rfl
          · simp
          · simp
          · simp)
      (by rw [List.pairwise_cons]
          refine ⟨?_, ?_⟩
          · intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact n5
            · rw [List.mem_singleton] at hb'
              rw [hb']
              exact fun he => hE2BR he.symm
          · rw [List.pairwise_cons]
            refine ⟨?_, List.pairwise_singleton _ _⟩
            intro b hb
            rw [List.mem_singleton] at hb
            rw [hb]
            exact fun he => hE2TR he.symm)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero] at hsum
    linarith
  have hb2 := bottom_two hd h2 cd hS hbot
  have ht2 := top_two hd h2 cd hS htop
  have p1 := hd.pos E1 hE1
  have p2 := hd.pos E2 hE2
  linarith

end OppositeLemmas

/-! ## The impossibility theorems -/

theorem length_ne_four (h : IsPerfectSquaredSquare S l) : l.length ≠ 4 := by
  intro hlen
  obtain ⟨hd, h2, hnc⟩ := h
  have hne : l ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
  have hS : 0 < S := side_pos_of_dissection hd hne
  obtain ⟨cd⟩ := exists_cornerData hd hS
  obtain ⟨rest, hperm, hrl⟩ := exists_rest hd h2 cd
  have hrest0 : rest = [] := List.length_eq_zero_iff.mp (by omega)
  subst hrest0
  have hmem : ∀ q ∈ l, q = cd.BL ∨ q = cd.BR ∨ q = cd.TL ∨ q = cd.TR := by
    intro q hq
    have := hperm.mem_iff.mp hq
    simp only [List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at this
    exact this
  refine clean_bottom_right hd h2 hnc cd hS ?_ ?_
  · intro q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRy]
  · intro q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLx]
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLx]
    · exact Or.inr rfl

theorem length_ne_five (h : IsPerfectSquaredSquare S l) : l.length ≠ 5 := by
  intro hlen
  obtain ⟨hd, h2, hnc⟩ := h
  have hne : l ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
  have hS : 0 < S := side_pos_of_dissection hd hne
  obtain ⟨cd⟩ := exists_cornerData hd hS
  obtain ⟨rest, hperm, hrl⟩ := exists_rest hd h2 cd
  obtain ⟨E, hrestE⟩ : ∃ E, rest = [E] :=
    List.length_eq_one_iff.mp (by omega)
  subst hrestE
  obtain ⟨hEl, hEBL, hEBR, hETL, hETR⟩ :=
    rest_facts hd cd hperm (List.mem_singleton.mpr rfl)
  have hflag := flag_unique hd h2 cd hEl hEBL hEBR hETL hETR
  have hmem : ∀ q ∈ l,
      q = cd.BL ∨ q = cd.BR ∨ q = cd.TL ∨ q = cd.TR ∨ q = E := by
    intro q hq
    have := hperm.mem_iff.mp hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at this
    tauto
  have hbotc : E.y ≠ 0 → ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR := by
    intro hEy q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRy]
    · exact absurd hqy hEy
  have htopc : E.y + E.s ≠ S →
      ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR := by
    intro hEy q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBR
      linarith [cd.hBRy]
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hqy hEy
  have hleftc : E.x ≠ 0 → ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL := by
    intro hEx q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBR
      linarith [cd.hBRx]
    · exact Or.inr rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRx]
    · exact absurd hqx hEx
  have hrightc : E.x + E.s ≠ S →
      ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR := by
    intro hEx q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLx]
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLx]
    · exact Or.inr rfl
    · exact absurd hqx hEx
  by_cases hpB : E.y = 0
  · obtain ⟨hnT, hnL, hnR⟩ := hflag.1 hpB
    exact clean_top_left hd h2 hnc cd hS (htopc hnT) (hleftc hnL)
  · by_cases hpT : E.y + E.s = S
    · obtain ⟨hnL, hnR⟩ := hflag.2.1 hpT
      exact clean_bottom_left hd h2 hnc cd hS (hbotc hpB) (hleftc hnL)
    · by_cases hpL : E.x = 0
      · have hnR := hflag.2.2 hpL
        exact clean_bottom_right hd h2 hnc cd hS (hbotc hpB) (hrightc hnR)
      · exact clean_bottom_left hd h2 hnc cd hS (hbotc hpB) (hleftc hpL)

theorem length_ne_six (h : IsPerfectSquaredSquare S l) : l.length ≠ 6 := by
  intro hlen
  obtain ⟨hd, h2, hnc⟩ := h
  have hne : l ≠ [] := by intro h0; rw [h0] at hlen; simp at hlen
  have hS : 0 < S := side_pos_of_dissection hd hne
  obtain ⟨cd⟩ := exists_cornerData hd hS
  obtain ⟨rest, hperm, hrl⟩ := exists_rest hd h2 cd
  obtain ⟨E1, E2, hrest2⟩ : ∃ a b, rest = [a, b] :=
    List.length_eq_two.mp (by omega)
  subst hrest2
  have hf1 := rest_facts hd cd hperm (E := E1) (by simp)
  have hf2 := rest_facts hd cd hperm (E := E2) (by simp)
  have hflag1 := flag_unique hd h2 cd hf1.1 hf1.2.1 hf1.2.2.1
    hf1.2.2.2.1 hf1.2.2.2.2
  have hflag2 := flag_unique hd h2 cd hf2.1 hf2.2.1 hf2.2.2.1
    hf2.2.2.2.1 hf2.2.2.2.2
  have hmem : ∀ q ∈ l, q = cd.BL ∨ q = cd.BR ∨ q = cd.TL ∨ q = cd.TR ∨
      q = E1 ∨ q = E2 := by
    intro q hq
    have := hperm.mem_iff.mp hq
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at this
    rcases this with (h | h | h | h) | (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  -- clean-edge characterizations, conditional on the extras avoiding it
  have hbotc : E1.y ≠ 0 → E2.y ≠ 0 →
      ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR := by
    intro h1 h2' q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRy]
    · exact absurd hqy h1
    · exact absurd hqy h2'
  have htopc : E1.y + E1.s ≠ S → E2.y + E2.s ≠ S →
      ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR := by
    intro h1 h2' q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBR
      linarith [cd.hBRy]
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hqy h1
    · exact absurd hqy h2'
  have hleftc : E1.x ≠ 0 → E2.x ≠ 0 →
      ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL := by
    intro h1 h2' q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBR
      linarith [cd.hBRx]
    · exact Or.inr rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRx]
    · exact absurd hqx h1
    · exact absurd hqx h2'
  have hrightc : E1.x + E1.s ≠ S → E2.x + E2.s ≠ S →
      ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR := by
    intro h1 h2' q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLx]
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLx]
    · exact Or.inr rfl
    · exact absurd hqx h1
    · exact absurd hqx h2'
  -- three-piece characterizations for the opposite-edge configurations
  have hbot31 : E2.y ≠ 0 →
      ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR ∨ q = E1 := by
    intro h2' q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRy]
    · exact Or.inr (Or.inr rfl)
    · exact absurd hqy h2'
  have hbot32 : E1.y ≠ 0 →
      ∀ q ∈ l, q.y = 0 → q = cd.BL ∨ q = cd.BR ∨ q = E2 := by
    intro h1 q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRy]
    · exact absurd hqy h1
    · exact Or.inr (Or.inr rfl)
  have htop31 : E2.y + E2.s ≠ S →
      ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR ∨ q = E1 := by
    intro h2' q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBR
      linarith [cd.hBRy]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hqy h2'
  have htop32 : E1.y + E1.s ≠ S →
      ∀ q ∈ l, q.y + q.s = S → q = cd.TL ∨ q = cd.TR ∨ q = E2 := by
    intro h1 q hql hqy
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLy]
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBR
      linarith [cd.hBRy]
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hqy h1
    · exact Or.inr (Or.inr rfl)
  have hleft31 : E2.x ≠ 0 →
      ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL ∨ q = E1 := by
    intro h2' q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBR
      linarith [cd.hBRx]
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRx]
    · exact Or.inr (Or.inr rfl)
    · exact absurd hqx h2'
  have hleft32 : E1.x ≠ 0 →
      ∀ q ∈ l, q.x = 0 → q = cd.BL ∨ q = cd.TL ∨ q = E2 := by
    intro h1 q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBR
      linarith [cd.hBRx]
    · exact Or.inr (Or.inl rfl)
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTR
      linarith [cd.hTRx]
    · exact absurd hqx h1
    · exact Or.inr (Or.inr rfl)
  have hright31 : E2.x + E2.s ≠ S →
      ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR ∨ q = E1 := by
    intro h2' q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLx]
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLx]
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hqx h2'
  have hright32 : E1.x + E1.s ≠ S →
      ∀ q ∈ l, q.x + q.s = S → q = cd.BR ∨ q = cd.TR ∨ q = E2 := by
    intro h1 q hql hqx
    rcases hmem q hql with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hBL
      linarith [cd.hBLx]
    · exact Or.inl rfl
    · exfalso
      have := side_lt_of_two_le hd h2 cd.hTL
      linarith [cd.hTLx]
    · exact Or.inr (Or.inl rfl)
    · exact absurd hqx h1
    · exact Or.inr (Or.inr rfl)
  -- decision tree over the edges occupied by the two extras
  by_cases hoB1 : E1.y = 0
  · obtain ⟨h1nT, h1nL, h1nR⟩ := hflag1.1 hoB1
    by_cases hoT2 : E2.y + E2.s = S
    · obtain ⟨h2nL, h2nR⟩ := hflag2.2.1 hoT2
      have h2nB : E2.y ≠ 0 := fun h => (hflag2.1 h).1 hoT2
      exact opposite_bottom_top hd h2 cd hS hf1.1 hf2.1 hf1.2.1 hf1.2.2.1
        hf2.2.2.2.1 hf2.2.2.2.2 hoB1 hoT2 (hbot31 h2nB) (htop32 h1nT)
        (hleftc h1nL h2nL) (hrightc h1nR h2nR)
    · by_cases hoL2 : E2.x = 0
      · have h2nR := hflag2.2.2 hoL2
        exact clean_top_right hd h2 hnc cd hS (htopc h1nT hoT2)
          (hrightc h1nR h2nR)
      · exact clean_top_left hd h2 hnc cd hS (htopc h1nT hoT2)
          (hleftc h1nL hoL2)
  · by_cases hoT1 : E1.y + E1.s = S
    · obtain ⟨h1nL, h1nR⟩ := hflag1.2.1 hoT1
      by_cases hoB2 : E2.y = 0
      · obtain ⟨h2nT, h2nL, h2nR⟩ := hflag2.1 hoB2
        exact opposite_bottom_top hd h2 cd hS hf2.1 hf1.1 hf2.2.1 hf2.2.2.1
          hf1.2.2.2.1 hf1.2.2.2.2 hoB2 hoT1 (hbot32 hoB1) (htop31 h2nT)
          (hleftc h1nL h2nL) (hrightc h1nR h2nR)
      · by_cases hoL2 : E2.x = 0
        · have h2nR := hflag2.2.2 hoL2
          exact clean_bottom_right hd h2 hnc cd hS (hbotc hoB1 hoB2)
            (hrightc h1nR h2nR)
        · exact clean_bottom_left hd h2 hnc cd hS (hbotc hoB1 hoB2)
            (hleftc h1nL hoL2)
    · by_cases hoL1 : E1.x = 0
      · have h1nR := hflag1.2.2 hoL1
        by_cases hoR2 : E2.x + E2.s = S
        · have h2nB : E2.y ≠ 0 := fun h => (hflag2.1 h).2.2 hoR2
          have h2nT : E2.y + E2.s ≠ S := fun h => (hflag2.2.1 h).2 hoR2
          have h2nL : E2.x ≠ 0 := fun h => hflag2.2.2 h hoR2
          exact opposite_left_right hd h2 cd hS hf1.1 hf2.1 hf1.2.1
            hf1.2.2.2.1 hf2.2.2.1 hf2.2.2.2.2 hoL1 hoR2
            (hbotc hoB1 h2nB) (htopc hoT1 h2nT)
            (hleft31 h2nL) (hright32 h1nR)
        · by_cases hoB2 : E2.y = 0
          · obtain ⟨h2nT, h2nL, h2nR⟩ := hflag2.1 hoB2
            exact clean_top_right hd h2 hnc cd hS (htopc hoT1 h2nT)
              (hrightc h1nR hoR2)
          · exact clean_bottom_right hd h2 hnc cd hS (hbotc hoB1 hoB2)
              (hrightc h1nR hoR2)
      · by_cases hoR1 : E1.x + E1.s = S
        · by_cases hoL2 : E2.x = 0
          · have h2nB : E2.y ≠ 0 := fun h => (hflag2.1 h).2.1 hoL2
            have h2nT : E2.y + E2.s ≠ S := fun h => (hflag2.2.1 h).1 hoL2
            have h2nR : E2.x + E2.s ≠ S := hflag2.2.2 hoL2
            have h1nB : E1.y ≠ 0 := fun h => (hflag1.1 h).2.2 hoR1
            have h1nT : E1.y + E1.s ≠ S := fun h => (hflag1.2.1 h).2 hoR1
            exact opposite_left_right hd h2 cd hS hf2.1 hf1.1 hf2.2.1
              hf2.2.2.2.1 hf1.2.2.1 hf1.2.2.2.2 hoL2 hoR1
              (hbotc h1nB h2nB) (htopc h1nT h2nT)
              (hleft32 hoL1) (hright31 h2nR)
          · by_cases hoB2 : E2.y = 0
            · obtain ⟨h2nT, h2nL, h2nR⟩ := hflag2.1 hoB2
              exact clean_top_left hd h2 hnc cd hS (htopc hoT1 h2nT)
                (hleftc hoL1 h2nL)
            · by_cases hoT2 : E2.y + E2.s = S
              · obtain ⟨h2nL, h2nR⟩ := hflag2.2.1 hoT2
                exact clean_bottom_left hd h2 hnc cd hS (hbotc hoB1 hoB2)
                  (hleftc hoL1 h2nL)
              · exact clean_bottom_left hd h2 hnc cd hS (hbotc hoB1 hoB2)
                  (hleftc hoL1 hoL2)
        · by_cases hoB2 : E2.y = 0
          · obtain ⟨h2nT, h2nL, h2nR⟩ := hflag2.1 hoB2
            exact clean_top_left hd h2 hnc cd hS (htopc hoT1 h2nT)
              (hleftc hoL1 h2nL)
          · by_cases hoT2 : E2.y + E2.s = S
            · obtain ⟨h2nL, h2nR⟩ := hflag2.2.1 hoT2
              exact clean_bottom_left hd h2 hnc cd hS (hbotc hoB1 hoB2)
                (hleftc hoL1 h2nL)
            · by_cases hoL2 : E2.x = 0
              · have h2nR := hflag2.2.2 hoL2
                exact clean_bottom_right hd h2 hnc cd hS (hbotc hoB1 hoB2)
                  (hrightc hoR1 h2nR)
              · exact clean_bottom_left hd h2 hnc cd hS (hbotc hoB1 hoB2)
                  (hleftc hoL1 hoL2)

/-- **A perfect squared square has at least 7 pieces.**  Together with
Duijvestijn's dissection this brackets the minimum order in `[7, 21]`; the
sharp bound 21 rests on Duijvestijn's exhaustive search of the orders
`7..20`, which is not formalized here. -/
theorem seven_le_length (h : IsPerfectSquaredSquare S l) : 7 ≤ l.length := by
  have h4 := four_le_length h
  have n4 := length_ne_four h
  have n5 := length_ne_five h
  have n6 := length_ne_six h
  omega

end SquaredSquare

end LeanProofs
