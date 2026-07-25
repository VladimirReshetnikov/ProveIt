import SquaredSquare.Duijvestijn

/-!
# Scaling a perfect squared square

Dissections scale: applying the dilation `p ↦ c • p` (for `c > 0`) to a
dissection of `[0, S]²` yields a dissection of `[0, c * S]²`, and
non-congruence of pieces is preserved because congruences can be conjugated by
the dilation.  Combined with Duijvestijn's dissection of the side-112 square
this shows that *every* square can be cut into 21 pairwise non-congruent
squares.
-/

namespace LeanProofs

namespace SquaredSquare

/-- Scale a placed square by the factor `c`. -/
def Sq.scale (c : ℝ) (q : Sq) : Sq :=
  ⟨c * q.x, c * q.y, c * q.s⟩

theorem Sq.scale_mem_toSet {c : ℝ} (hc : 0 < c) {q : Sq} {p : ℝ × ℝ} :
    p ∈ (q.scale c).toSet ↔ (p.1 / c, p.2 / c) ∈ q.toSet := by
  rw [Sq.mem_toSet, Sq.mem_toSet]
  simp only [Sq.scale]
  rw [le_div_iff₀ hc, div_le_iff₀ hc, le_div_iff₀ hc, div_le_iff₀ hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith [mul_comm q.x c], by nlinarith⟩, by nlinarith, by nlinarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

theorem Sq.scale_mem_inn {c : ℝ} (hc : 0 < c) {q : Sq} {p : ℝ × ℝ} :
    p ∈ (q.scale c).inn ↔ (p.1 / c, p.2 / c) ∈ q.inn := by
  rw [Sq.mem_inn, Sq.mem_inn]
  simp only [Sq.scale]
  rw [lt_div_iff₀ hc, div_lt_iff₀ hc, lt_div_iff₀ hc, div_lt_iff₀ hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

theorem mem_bigSquare_scale {c S : ℝ} (hc : 0 < c) {p : ℝ × ℝ} :
    p ∈ bigSquare (c * S) ↔ (p.1 / c, p.2 / c) ∈ bigSquare S := by
  rw [mem_bigSquare, mem_bigSquare]
  simp only
  rw [le_div_iff₀ hc, div_le_iff₀ hc, le_div_iff₀ hc, div_le_iff₀ hc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by nlinarith, by nlinarith⟩, by nlinarith, by nlinarith⟩

/-- Squared distances scale by `c ^ 2` under the dilation. -/
theorem sqDist_scale (c : ℝ) (p r : ℝ × ℝ) :
    sqDist (c * p.1, c * p.2) (c * r.1, c * r.2) = c ^ 2 * sqDist p r := by
  unfold sqDist
  ring

/-- Congruence descends along the dilation `p ↦ c • p`: if the scaled squares
are congruent then so were the originals (conjugate the bijection by the
dilation). -/
theorem congruent_of_scale_congruent {c : ℝ} (hc : 0 < c) {q₁ q₂ : Sq}
    (h : Congruent (q₁.scale c).toSet (q₂.scale c).toSet) :
    Congruent q₁.toSet q₂.toSet := by
  obtain ⟨f, hf, hd⟩ := h
  have hcne : c ≠ 0 := hc.ne'
  -- the conjugated map
  refine ⟨fun a => ((f (c * a.1, c * a.2)).1 / c, (f (c * a.1, c * a.2)).2 / c),
    ⟨?_, ?_, ?_⟩, ?_⟩
  · -- MapsTo
    intro a ha
    have hmem : (c * a.1, c * a.2) ∈ (q₁.scale c).toSet := by
      rw [Sq.scale_mem_toSet hc]
      simpa [mul_div_cancel_left₀ _ hcne] using ha
    have := hf.mapsTo hmem
    rw [Sq.scale_mem_toSet hc] at this
    exact this
  · -- InjOn
    intro a ha b hb hab
    have hmema : (c * a.1, c * a.2) ∈ (q₁.scale c).toSet := by
      rw [Sq.scale_mem_toSet hc]
      simpa [mul_div_cancel_left₀ _ hcne] using ha
    have hmemb : (c * b.1, c * b.2) ∈ (q₁.scale c).toSet := by
      rw [Sq.scale_mem_toSet hc]
      simpa [mul_div_cancel_left₀ _ hcne] using hb
    have h1 : (f (c * a.1, c * a.2)).1 / c = (f (c * b.1, c * b.2)).1 / c :=
      congrArg Prod.fst hab
    have h2 : (f (c * a.1, c * a.2)).2 / c = (f (c * b.1, c * b.2)).2 / c :=
      congrArg Prod.snd hab
    have hfa : f (c * a.1, c * a.2) = f (c * b.1, c * b.2) := by
      apply Prod.ext
      · field_simp at h1
        exact h1
      · field_simp at h2
        exact h2
    have := hf.injOn hmema hmemb hfa
    have e1 : c * a.1 = c * b.1 := congrArg Prod.fst this
    have e2 : c * a.2 = c * b.2 := congrArg Prod.snd this
    exact Prod.ext (mul_left_cancel₀ hcne e1) (mul_left_cancel₀ hcne e2)
  · -- SurjOn
    intro b hb
    have hmem : (c * b.1, c * b.2) ∈ (q₂.scale c).toSet := by
      rw [Sq.scale_mem_toSet hc]
      simpa [mul_div_cancel_left₀ _ hcne] using hb
    obtain ⟨w, hw, hfw⟩ := hf.surjOn hmem
    have hw' : (w.1 / c, w.2 / c) ∈ q₁.toSet := by
      rw [← Sq.scale_mem_toSet hc]
      exact hw
    refine ⟨(w.1 / c, w.2 / c), hw', ?_⟩
    have hcw : (c * (w.1 / c), c * (w.2 / c)) = w := by
      apply Prod.ext <;> simp [mul_div_cancel₀, hcne]
    simp only [hcw, hfw]
    apply Prod.ext <;> simp [mul_div_cancel_left₀, hcne]
  · -- squared distances
    intro a ha b hb
    have hmema : (c * a.1, c * a.2) ∈ (q₁.scale c).toSet := by
      rw [Sq.scale_mem_toSet hc]
      simpa [mul_div_cancel_left₀ _ hcne] using ha
    have hmemb : (c * b.1, c * b.2) ∈ (q₁.scale c).toSet := by
      rw [Sq.scale_mem_toSet hc]
      simpa [mul_div_cancel_left₀ _ hcne] using hb
    have hpres := hd _ hmema _ hmemb
    have hsc : sqDist (c * a.1, c * a.2) (c * b.1, c * b.2)
        = c ^ 2 * sqDist a b := sqDist_scale c a b
    -- write both sides explicitly and cancel `c ^ 2`
    have hc2 : (c : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hcne
    unfold sqDist at *
    field_simp
    nlinarith [hpres, hsc]

/-- Scaling a dissection by `c > 0` dissects the scaled square. -/
theorem IsDissection.scale {S c : ℝ} (hc : 0 < c) {l : List Sq}
    (h : IsDissection S l) : IsDissection (c * S) (l.map (Sq.scale c)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have := h.pos r hr
    show 0 < c * r.s
    positivity
  · rw [List.pairwise_map]
    refine h.disj.imp ?_
    intro p q hpq
    rw [Set.disjoint_left] at hpq ⊢
    intro a ha ha'
    rw [Sq.scale_mem_inn hc] at ha ha'
    exact hpq ha ha'
  · ext p
    simp only [Set.mem_iUnion, exists_prop, List.mem_map]
    constructor
    · rintro ⟨q, ⟨r, hr, rfl⟩, hpq⟩
      rw [Sq.scale_mem_toSet hc] at hpq
      rw [mem_bigSquare_scale hc]
      have hcov : (p.1 / c, p.2 / c) ∈ bigSquare S := by
        rw [← h.cover]
        simp only [Set.mem_iUnion, exists_prop]
        exact ⟨r, hr, hpq⟩
      exact hcov
    · intro hp
      rw [mem_bigSquare_scale hc, ← h.cover] at hp
      simp only [Set.mem_iUnion, exists_prop] at hp
      obtain ⟨r, hr, hpr⟩ := hp
      exact ⟨r.scale c, ⟨r, hr, rfl⟩, (Sq.scale_mem_toSet hc).mpr hpr⟩

/-- Scaling a perfect squared square by `c > 0` gives a perfect squared square
of the scaled side. -/
theorem IsPerfectSquaredSquare.scale {S c : ℝ} (hc : 0 < c) {l : List Sq}
    (h : IsPerfectSquaredSquare S l) :
    IsPerfectSquaredSquare (c * S) (l.map (Sq.scale c)) := by
  obtain ⟨hd, hl, hnc⟩ := h
  refine ⟨hd.scale hc, by rw [List.length_map]; exact hl, ?_⟩
  rw [List.pairwise_map]
  refine hnc.imp ?_
  intro p q hpq hcong
  exact hpq (congruent_of_scale_congruent hc hcong)

/-- **Squaring the square, any side.**  Every square can be cut into 21
pairwise non-congruent squares. -/
theorem exists_perfect_squared_square_of_side {S : ℝ} (hS : 0 < S) :
    ∃ l : List Sq, l.length = 21 ∧ IsPerfectSquaredSquare S l := by
  have hc : 0 < S / 112 := by positivity
  have h := duijvestijn_perfect.scale hc
  rw [div_mul_cancel₀ S (by norm_num : (112 : ℝ) ≠ 0)] at h
  exact ⟨duijvestijnTiles.map (Sq.scale (S / 112)),
    by rw [List.length_map, duijvestijnTiles_length], h⟩

end SquaredSquare

end LeanProofs
