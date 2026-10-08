import GowersSzemeredi.Proofs16FreimanBilinearReadout

/-! Gluing bi-affine pieces along a shared square.

A bi-affine function `A + B i + C j + D i j` on an index grid is determined
by its values on any `2 × 2` square `{i₀, i₀+1} × {j₀, j₀+1}`. The four
values give, by unimodular elimination, `D`, then `B` and `C`, then `A`.
So two bi-affine descriptions that agree on one shared square agree
everywhere.

Consequence for the readout (R), research notes J.2: if a Freiman
bihomomorphism is bi-affine on two overlapping product boxes inside its
domain, and the overlap contains a `2 × 2` square, one bi-affine (hence
multilinear) function describes it on the union. Connected chains of
overlapping boxes inside `V` are therefore covered by a single multilinear
function, which is the linking option for partial cells. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The bi-affine function with coefficients `(A, B, C, D)`. -/
def biaffineAt {R : Type*} [CommRing R] (A B C D : R) (i j : Nat) : R :=
  A + (i : R) * B + (j : R) * C + ((i : R) * j) * D

/-- **Bi-affine functions are determined by a square.** -/
theorem biaffine_coeffs_eq_of_square {R : Type*} [CommRing R] {A B C D A' B' C' D' : R}
    (i₀ j₀ : Nat)
    (h00 : biaffineAt A B C D i₀ j₀ = biaffineAt A' B' C' D' i₀ j₀)
    (h10 : biaffineAt A B C D (i₀ + 1) j₀ = biaffineAt A' B' C' D' (i₀ + 1) j₀)
    (h01 : biaffineAt A B C D i₀ (j₀ + 1) = biaffineAt A' B' C' D' i₀ (j₀ + 1))
    (h11 : biaffineAt A B C D (i₀ + 1) (j₀ + 1) = biaffineAt A' B' C' D' (i₀ + 1) (j₀ + 1)) :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  unfold biaffineAt at h00 h10 h01 h11
  push_cast at h00 h10 h01 h11
  have hD : D = D' := by linear_combination h11 - h10 - h01 + h00
  have hB : B = B' := by
    linear_combination h10 - h00 - (j₀ : R) * (h11 - h10 - h01 + h00)
  have hC : C = C' := by
    linear_combination h01 - h00 - (i₀ : R) * (h11 - h10 - h01 + h00)
  have hA : A = A' := by
    linear_combination h00 - (i₀ : R) * (h10 - h00 - (j₀ : R) * (h11 - h10 - h01 + h00)) -
      (j₀ : R) * (h01 - h00 - (i₀ : R) * (h11 - h10 - h01 + h00)) -
      ((i₀ : R) * j₀) * (h11 - h10 - h01 + h00)
  exact ⟨hA, hB, hC, hD⟩

/-- **Gluing.** If `f` agrees with one bi-affine function on a set `S₁`,
with another on `S₂`, and both sets contain a common square, then the two
functions coincide; so one bi-affine function describes `f` on
`S₁ ∪ S₂`. -/
theorem biaffine_glue {R : Type*} [CommRing R] (f : Nat → Nat → R)
    {S₁ S₂ : Set (Nat × Nat)} {A B C D A' B' C' D' : R}
    (h₁ : ∀ p ∈ S₁, f p.1 p.2 = biaffineAt A B C D p.1 p.2)
    (h₂ : ∀ p ∈ S₂, f p.1 p.2 = biaffineAt A' B' C' D' p.1 p.2)
    (i₀ j₀ : Nat)
    (hsq : ∀ a b : Nat, a ≤ 1 → b ≤ 1 → (i₀ + a, j₀ + b) ∈ S₁ ∧ (i₀ + a, j₀ + b) ∈ S₂) :
    ∀ p ∈ S₁ ∪ S₂, f p.1 p.2 = biaffineAt A B C D p.1 p.2 := by
  have hpt : ∀ a b : Nat, a ≤ 1 → b ≤ 1 →
      biaffineAt A B C D (i₀ + a) (j₀ + b) = biaffineAt A' B' C' D' (i₀ + a) (j₀ + b) := by
    intro a b ha hb
    obtain ⟨m1, m2⟩ := hsq a b ha hb
    rw [← h₁ _ m1, ← h₂ _ m2]
  obtain ⟨hA, hB, hC, hD⟩ := biaffine_coeffs_eq_of_square i₀ j₀
    (by simpa using hpt 0 0 (by omega) (by omega)) (hpt 1 0 le_rfl (by omega))
    (by simpa using hpt 0 1 (by omega) le_rfl) (hpt 1 1 le_rfl le_rfl)
  intro p hp
  rcases hp with hp | hp
  · exact h₁ p hp
  · rw [h₂ p hp, hA, hB, hC, hD]

/-- The readout of `freiman_bihom_biaffine_on_product`, in `biaffineAt` form. -/
theorem freiman_bihom_biaffineAt_on_product {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0})
    (a d b e : ZMod N) (L₁ L₂ : Nat) (hL₁ : 2 ≤ L₁) (hL₂ : 2 ≤ L₂)
    (hsub : ∀ i j, i < L₁ → j < L₂ → (a + (i : ZMod N) * d, b + (j : ZMod N) * e) ∈ V) :
    let f : Nat → Nat → ZMod N := fun i j => Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e)
    ∀ i j, i < L₁ → j < L₂ →
      f i j = biaffineAt (f 0 0) (f 1 0 - f 0 0) (f 0 1 - f 0 0) (f 1 1 - f 1 0 - f 0 1 + f 0 0) i j := by
  intro f i j hi hj
  have h : f i j = f 0 0 + i • (f 1 0 - f 0 0) + j • (f 0 1 - f 0 0) +
      (i * j) • (f 1 1 - f 1 0 - f 0 1 + f 0 0) :=
    freiman_bihom_biaffine_on_product hΦ a d b e L₁ L₂ hL₁ hL₂ hsub i j hi hj
  rw [h]
  unfold biaffineAt
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- Shifting the base point of a bi-affine function keeps it bi-affine. -/
theorem biaffineAt_unshift {R : Type*} [CommRing R] (A B C D : R) (i₀ j₀ : Nat) :
    ∃ A' B' C' D' : R, ∀ i j, i₀ ≤ i → j₀ ≤ j →
      biaffineAt A B C D (i - i₀) (j - j₀) = biaffineAt A' B' C' D' i j := by
  refine ⟨A - B * i₀ - C * j₀ + D * (i₀ * j₀), B - D * j₀, C - D * i₀, D, ?_⟩
  intro i j hi hj
  unfold biaffineAt
  rw [Nat.cast_sub hi, Nat.cast_sub hj]
  ring

/-- **The readout on a chain of overlapping boxes.** Let boxes
`[iₜ, iₜ + wₜ) × [jₜ, jₜ + hₜ)` (with `wₜ, hₜ ≥ 2`) map into `V` under
`(i, j) ↦ (a + i d, b + j e)`, and let each consecutive pair share a
`2 × 2` square. Then one bi-affine function describes the Freiman
bihomomorphism on all of them. -/
theorem freiman_bihom_biaffine_on_chain {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0}) (a d b e : ZMod N)
    (T : Nat) (bi bj bw bh : Nat → Nat) (hw : ∀ t, 2 ≤ bw t) (hh : ∀ t, 2 ≤ bh t)
    (hsub : ∀ t, t < T → ∀ i j, bi t ≤ i → i < bi t + bw t → bj t ≤ j → j < bj t + bh t →
      (a + (i : ZMod N) * d, b + (j : ZMod N) * e) ∈ V)
    (sq : Nat → Nat × Nat)
    (hsq : ∀ t, t + 1 < T → ∀ x y : Nat, x ≤ 1 → y ≤ 1 →
      (bi t ≤ (sq t).1 + x ∧ (sq t).1 + x < bi t + bw t ∧ bj t ≤ (sq t).2 + y ∧
        (sq t).2 + y < bj t + bh t) ∧
      (bi (t + 1) ≤ (sq t).1 + x ∧ (sq t).1 + x < bi (t + 1) + bw (t + 1) ∧
        bj (t + 1) ≤ (sq t).2 + y ∧ (sq t).2 + y < bj (t + 1) + bh (t + 1))) :
    ∃ A B C D : ZMod N, ∀ t, t < T → ∀ i j, bi t ≤ i → i < bi t + bw t → bj t ≤ j →
      j < bj t + bh t → Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e) = biaffineAt A B C D i j := by
  set f : Nat → Nat → ZMod N := fun i j => Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e)
  -- the readout on a single box, in absolute coordinates
  have hbox : ∀ t, t < T → ∃ A B C D : ZMod N, ∀ i j, bi t ≤ i → i < bi t + bw t →
      bj t ≤ j → j < bj t + bh t → f i j = biaffineAt A B C D i j := by
    intro t ht
    have hloc := freiman_bihom_biaffineAt_on_product hΦ (a + (bi t : ZMod N) * d) d
      (b + (bj t : ZMod N) * e) e (bw t) (bh t) (hw t) (hh t)
      (fun i j hi hj => by
        have := hsub t ht (bi t + i) (bj t + j) (by omega) (by omega) (by omega) (by omega)
        push_cast at this
        convert this using 2 <;> ring)
    set g : Nat → Nat → ZMod N := fun i j =>
      Φ (a + (bi t : ZMod N) * d + (i : ZMod N) * d, b + (bj t : ZMod N) * e + (j : ZMod N) * e)
    obtain ⟨A', B', C', D', hsh⟩ := biaffineAt_unshift (g 0 0) (g 1 0 - g 0 0) (g 0 1 - g 0 0)
      (g 1 1 - g 1 0 - g 0 1 + g 0 0) (bi t) (bj t)
    refine ⟨A', B', C', D', fun i j hi1 hi2 hj1 hj2 => ?_⟩
    have h1 := hloc (i - bi t) (j - bj t) (by omega) (by omega)
    rw [← hsh i j hi1 hj1, ← h1]
    show Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e) =
      Φ (a + (bi t : ZMod N) * d + ((i - bi t : Nat) : ZMod N) * d,
        b + (bj t : ZMod N) * e + ((j - bj t : Nat) : ZMod N) * e)
    rw [Nat.cast_sub hi1, Nat.cast_sub hj1]
    congr 1 <;> ring_nf
  -- induction along the chain
  have hind : ∀ n, n ≤ T → 0 < n → ∃ A B C D : ZMod N, ∀ t, t < n → ∀ i j, bi t ≤ i →
      i < bi t + bw t → bj t ≤ j → j < bj t + bh t → f i j = biaffineAt A B C D i j := by
    intro n
    induction n with
    | zero => intro _ h; omega
    | succ n ih =>
      intro hn _
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0
        obtain ⟨A, B, C, D, hA⟩ := hbox 0 (by omega)
        exact ⟨A, B, C, D, fun t ht => by
          have : t = 0 := by omega
          subst this; exact hA⟩
      · obtain ⟨A, B, C, D, hprev⟩ := ih (by omega) hpos
        obtain ⟨A', B', C', D', hlast⟩ := hbox n (by omega)
        -- glue along the square shared by boxes `n - 1` and `n`
        have hglue := biaffine_glue f
          (S₁ := {p | ∃ t, t < n ∧ bi t ≤ p.1 ∧ p.1 < bi t + bw t ∧ bj t ≤ p.2 ∧ p.2 < bj t + bh t})
          (S₂ := {p | bi n ≤ p.1 ∧ p.1 < bi n + bw n ∧ bj n ≤ p.2 ∧ p.2 < bj n + bh n})
          (A := A) (B := B) (C := C) (D := D) (A' := A') (B' := B') (C' := C') (D' := D')
          (fun p ⟨t, ht, h1, h2, h3, h4⟩ => hprev t ht p.1 p.2 h1 h2 h3 h4)
          (fun p ⟨h1, h2, h3, h4⟩ => hlast p.1 p.2 h1 h2 h3 h4)
          (sq (n - 1)).1 (sq (n - 1)).2
          (fun x y hx hy => by
            obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩ := hsq (n - 1) (by omega) x y hx hy
            have hn1 : n - 1 + 1 = n := by omega
            rw [hn1] at b1 b2 b3 b4
            exact ⟨⟨n - 1, by omega, a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩)
        refine ⟨A, B, C, D, fun t ht i j h1 h2 h3 h4 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp ht with hlt | heq
        · exact hprev t hlt i j h1 h2 h3 h4
        · subst heq
          exact hglue (i, j) (Or.inr ⟨h1, h2, h3, h4⟩)
  rcases Nat.eq_zero_or_pos T with hT | hT
  · exact ⟨0, 0, 0, 0, fun t ht => by omega⟩
  · exact hind T le_rfl hT

/-- The left end and right end of three consecutive row intervals. -/
def lo3 (l : Nat → Nat) (t : Nat) : Nat := max (max (l t) (l (t + 1))) (l (t + 2))
def hi3 (r : Nat → Nat) (t : Nat) : Nat := min (min (r t) (r (t + 1))) (r (t + 2))

theorem le_lo3 (l : Nat → Nat) (t : Nat) :
    l t ≤ lo3 l t ∧ l (t + 1) ≤ lo3 l t ∧ l (t + 2) ≤ lo3 l t := by
  unfold lo3; omega

theorem hi3_le (r : Nat → Nat) (t : Nat) :
    hi3 r t ≤ r t ∧ hi3 r t ≤ r (t + 1) ∧ hi3 r t ≤ r (t + 2) := by
  unfold hi3; omega

theorem lo3_succ_le (l : Nat → Nat) (t : Nat) : lo3 l (t + 1) ≤ max (lo3 l t) (l (t + 3)) := by
  unfold lo3
  rw [show t + 1 + 1 = t + 2 by omega, show t + 1 + 2 = t + 3 by omega]
  omega

theorem min_le_hi3_succ (r : Nat → Nat) (t : Nat) : min (hi3 r t) (r (t + 3)) ≤ hi3 r (t + 1) := by
  unfold hi3
  rw [show t + 1 + 1 = t + 2 by omega, show t + 1 + 2 = t + 3 by omega]
  omega

/-- **Staircases.** Suppose rows `j < M` of an index grid meet `V` in
intervals `[l j, r j)`. Suppose every three consecutive intervals share at
least two columns, and every four consecutive ones also share at least
two. Then the height-3 boxes `[lo3 t, hi3 t) × {t, t+1, t+2}` form a chain
whose consecutive members share a `2 × 2` square, and one bi-affine
function describes the Freiman bihomomorphism on their union. -/
theorem freiman_bihom_biaffine_on_staircase {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0}) (a d b e : ZMod N)
    (M : Nat) (l r : Nat → Nat)
    (hrow : ∀ j, j < M → ∀ i, l j ≤ i → i < r j →
      (a + (i : ZMod N) * d, b + (j : ZMod N) * e) ∈ V)
    (htri : ∀ t, t + 2 < M → lo3 l t + 2 ≤ hi3 r t)
    (hquad : ∀ t, t + 3 < M → max (lo3 l t) (l (t + 3)) + 2 ≤ min (hi3 r t) (r (t + 3))) :
    ∃ A B C D : ZMod N, ∀ t, t + 2 < M → ∀ i, lo3 l t ≤ i → i < hi3 r t → ∀ k, k ≤ 2 →
      Φ (a + (i : ZMod N) * d, b + ((t + k : Nat) : ZMod N) * e) = biaffineAt A B C D i (t + k) := by
  have hT : ∀ t, t + 2 < M → lo3 l t + (hi3 r t - lo3 l t) = hi3 r t := by
    intro t ht; have := htri t ht; omega
  obtain ⟨A, B, C, D, hchain⟩ := freiman_bihom_biaffine_on_chain hΦ a d b e (M - 2) (lo3 l) id
    (fun t => max 2 (hi3 r t - lo3 l t)) (fun _ => 3) (fun t => le_max_left _ _) (fun _ => by norm_num)
    (by
      intro t ht i j h1 h2 h3 h4
      have hbt := htri t (by omega)
      simp only [id] at h3 h4
      have hmax : max 2 (hi3 r t - lo3 l t) = hi3 r t - lo3 l t := by omega
      rw [hmax] at h2
      have hl := le_lo3 l t
      have hr := hi3_le r t
      have hj : j = t ∨ j = t + 1 ∨ j = t + 2 := by omega
      rcases hj with rfl | rfl | rfl
      · exact hrow j (by omega) i (by omega) (by omega)
      · exact hrow (t + 1) (by omega) i (by omega) (by omega)
      · exact hrow (t + 2) (by omega) i (by omega) (by omega))
    (fun t => (max (lo3 l t) (l (t + 3)), t + 1))
    (by
      intro t ht x y hx hy
      have hq := hquad t (by omega)
      have hb0 := htri t (by omega)
      have hb1 := htri (t + 1) (by omega)
      have hm0 : max 2 (hi3 r t - lo3 l t) = hi3 r t - lo3 l t := by omega
      have hm1 : max 2 (hi3 r (t + 1) - lo3 l (t + 1)) = hi3 r (t + 1) - lo3 l (t + 1) := by omega
      simp only [id]
      rw [hm0, hm1]
      have hs1 := lo3_succ_le l t
      have hs2 := min_le_hi3_succ r t
      have hl0 := le_lo3 l t
      have hl1 := le_lo3 l (t + 1)
      refine ⟨⟨by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega⟩⟩)
  refine ⟨A, B, C, D, fun t ht i hi1 hi2 k hk => ?_⟩
  have hb := htri t ht
  have hm : max 2 (hi3 r t - lo3 l t) = hi3 r t - lo3 l t := by omega
  exact hchain t (by omega) i (t + k) hi1 (by rw [hm]; omega) (by simp only [id]; omega)
    (by simp only [id]; omega)

end LeanProofs.GowersSzemeredi
