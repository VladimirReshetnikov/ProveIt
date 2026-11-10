import DiophantineConsistency.ZRows.PellValuationIndex

/-! # The intersective polynomial `(t³ − t − 1)(t² + 23)` in models of `𝗜𝚺₁`

In every model `V` of `𝗜𝚺₁`, every `m > 0` divides `(t³ − t − 1)(t² + 23)` for some `t`
(`root`, and with a natural `t` in residue form, `root_nat`). The cubic has discriminant `−23`
and no root modulo `2` or `3`, so the classical argument goes through the splitting of primes
in the Hilbert class field of `ℚ(√−23)`. The proof here replaces it by a Pell computation.

* `cubic_of_tau` (any commutative ring): if `p ∣ τ³ − 3τ − 25` and `9` is invertible modulo `p`
  (`α·p + β·9 = 1`), then `p ∣ g(β·(τ + 2)(τ − 1))` for `g(t) = t³ − t − 1`. This is Cardano's
  formula read backwards: with `v = u + ū`, `u·ū = 1/3`, `u³ + ū³ = 1`, the number `ε = 3u²` has
  `ε·ε̄ = 1` and `ε³ = (25 + √621)/2`, so `τ = ε + ε̄` satisfies `τ³ − 3τ = 25`, and
  `v = v²(v² − 1) = (τ + 2)(τ − 1)/9`.
* `triple_x`, `triple_y`: the triple-angle formulas `X(3k) + 3X(k) = 4X(k)³` and
  `Y(3k) + Y(k) = 4X(k)²Y(k)` of the Pell recurrence.
* `pell_root`: for an irreducible `p = 2m + 1 ≠ 3`, the cubic has a root modulo `p`, or `−23` is
  a square modulo `p`. Take the Pell base `b = m + 11`, whose fundamental solution is
  `(b + 2, 1)` with `2(b + 2) = p + 25` and `4·δ(b) = p(p + 50) + 621`; modulo `p` it is the unit
  `ε³` above. Let `n > 0` be the least index with `X(n) ≡ 1`, `Y(n) ≡ 0 (mod p)`
  (`ZRowsPellValuation.strong_index` and the least-number principle).
  * `n ≡ 2 (mod 3)`: `X(n + 1) ≡ b + 2` and `n + 1 = 3k`, so `τ = 2X(k)` has
    `τ³ − 3τ = 2X(3k) ≡ p + 25` (`cubic_of_triple`).
  * `n ≡ 1 (mod 3)`: the same with the index `2n + 1 = 3k`.
  * `n = 3k`: `X(3k) − 1 = (X(k) − 1)(2X(k) + 1)²`. If `p ∣ X(k) − 1`, then
    `Y(3k) ≡ 3Y(k)` makes `k` a smaller index, a contradiction. Otherwise `p ∣ 2X(k) + 1`, and
    `(2X + 1)(2X − 1) = 3 + 4δY²` gives `p ∣ 3(207·Y(k)² + 1)`, so `(69·Y(k))² ≡ −23`
    (`descent_or_square`).
* `bez_g1`: `23 = (18v − 27)·g(v) + (4 + 9v − 6v²)·g'(v)`, so a root of the cubic modulo
  `p ∤ 23` is simple.
* `two_adic`: `(2u + 1)² + 23 = 8·2ᵏ·c` for every `k` (`t² + 23` has no simple root modulo `2`).
* `prime_power_root`: roots modulo `pᵏ` for irreducible `p`: `p = 2` (`two_adic`), `p = 3`
  (simple root `1` of `t² + 23`), `p ∣ 23` (simple root `3` of the cubic), and otherwise
  `pell_root` with `ZRowsIntersective19.hensel`.
* `root_nat`: strong induction on `m`, combining the roots modulo `pᵏ` and modulo `r < m` by
  `ModelBoundedForallArith.crt_step`, as in `ZRowsIntersective19`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsIntersective23

/-! ### Ring identities (before the Foundation opens, whose scoped `≤` would capture `R`) -/
section Generic
variable {R : Type*} [CommRing R]

/-- The two factors, their derivatives and the product. -/
def g1 (t : R) : R := t * t * t - t - 1
def g1' (t : R) : R := 3 * t * t - 1
def g2 (t : R) : R := t * t + 23
def g2' (t : R) : R := 2 * t
def poly23 (t : R) : R := g1 t * g2 t

theorem exp1 : ∀ x H : R, ∃ r, g1 (x + H) = g1 x + H * g1' x + H * H * r :=
  fun x H => ⟨3 * x + H, by unfold g1 g1'; ring⟩
theorem der1 : ∀ x y : R, ∃ r, g1' x - g1' y = (x - y) * r :=
  fun x y => ⟨3 * x + 3 * y, by unfold g1'; ring⟩
theorem exp2 : ∀ x H : R, ∃ r, g2 (x + H) = g2 x + H * g2' x + H * H * r :=
  fun x H => ⟨1, by unfold g2 g2'; ring⟩
theorem der2 : ∀ x y : R, ∃ r, g2' x - g2' y = (x - y) * r :=
  fun x y => ⟨2, by unfold g2'; ring⟩

theorem poly23_sub_dvd (a b : R) : a - b ∣ poly23 a - poly23 b := by
  refine ⟨(a * a + a * b + b * b - 1) * g2 a + g1 b * (a + b), ?_⟩
  unfold poly23 g1 g2
  ring

/-- A factor coprime to `p` can be cancelled. -/
theorem dvd_of_bez_mul {p a X α β : R} (hb : α * p + β * a = 1) (h : p ∣ a * X) : p ∣ X := by
  obtain ⟨c, hc⟩ := h
  exact ⟨α * X + β * c, by linear_combination (-X) * hb + β * hc⟩

/-- **A root of the cubic from a trace of the Pell unit.** -/
theorem cubic_of_tau {p τ α β : R} (hb : α * p + β * 9 = 1)
    (h : p ∣ τ * τ * τ - 3 * τ - 25) : p ∣ g1 (β * ((τ + 2) * (τ - 1))) := by
  obtain ⟨c, hc⟩ := h
  have h729 : p ∣ 9 * (9 * (9 * g1 (β * ((τ + 2) * (τ - 1))))) := by
    refine ⟨(τ * τ * τ + 3 * τ * τ + 23) * c -
      α * (((τ + 2) * (τ - 1)) ^ 3 * (81 * β ^ 2 + 9 * β + 1) -
        81 * ((τ + 2) * (τ - 1))), ?_⟩
    unfold g1
    linear_combination (τ * τ * τ + 3 * τ * τ + 23) * hc +
      (((τ + 2) * (τ - 1)) ^ 3 * (81 * β ^ 2 + 9 * β + 1) - 81 * ((τ + 2) * (τ - 1))) * hb
  exact dvd_of_bez_mul hb (dvd_of_bez_mul hb (dvd_of_bez_mul hb h729))

/-- **A root of the cubic modulo `p ∤ 23` is simple**: the discriminant is `−23`. -/
theorem bez_g1 {p v c α β : R} (hb : α * p + β * 23 = 1) (hc : g1 v = p * c) :
    (α + β * (18 * v - 27) * c) * p + (β * (4 + 9 * v - 6 * v * v)) * g1' v = 1 := by
  unfold g1 at hc
  unfold g1'
  linear_combination hb - (β * (18 * v - 27)) * hc

end Generic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPow ArithmeticGcdNormalization ModelBetaFunction
open ModelBoundedForallArith ModelFermat ZRowsCoprimeSquares ZRowsRootWitness
open ArithmeticPellRecurrence
open ArithmeticPellPeriodicity (double_x double_y)
open ZRowsPellBinomial (odd_of_irred)
open ZRowsPellValuation (strong_index)
open ZRowsIntersective19 (hensel sub_dvd_of_exp dvd_mul_of_bez_ring exists_nat_congr
  ring_bez_of_not_dvd bez_power not_dvd_two not_dvd_three valuation)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] xcoord ycoord

/-! ### Residue forms -/

/-- `t` is a root of `(t³ − t − 1)(t² + 23)` modulo `N`, in residues of natural numbers. -/
def Root (N t : V) : Prop :=
  ((t * t * t) * (t * t + 23)) % N = ((t + 1) * (t * t + 23)) % N
/-- `x` is a root of `t³ − t − 1` modulo `N`. -/
def Q1 (N x : V) : Prop := (x * x * x) % N = (x + 1) % N
/-- `x` is a root of `t² + 23` modulo `N`. -/
def Q2 (N x : V) : Prop := N ∣ x * x + 23

theorem root_iff (N t : V) : Root N t ↔ (ι N : DiffRing V) ∣ poly23 (ι t) := by
  unfold Root poly23 g1 g2
  constructor
  · intro h
    obtain ⟨q, hq⟩ := ringSub_of_mod_eq h
    simp only [map_mul, map_add, map_ofNat, map_one] at hq
    exact ⟨q, by linear_combination hq⟩
  · rintro ⟨q, hq⟩
    apply mod_eq_of_sub_eq (q := q)
    simp only [map_mul, map_add, map_ofNat, map_one]
    linear_combination hq

theorem q1_iff (N x : V) : Q1 N x ↔ (ι N : DiffRing V) ∣ g1 (ι x) := by
  unfold Q1 g1
  constructor
  · intro h
    obtain ⟨q, hq⟩ := ringSub_of_mod_eq h
    simp only [map_mul, map_add, map_one] at hq
    exact ⟨q, by linear_combination hq⟩
  · rintro ⟨q, hq⟩
    apply mod_eq_of_sub_eq (q := q)
    simp only [map_mul, map_add, map_one]
    linear_combination hq

theorem q2_iff (N x : V) : Q2 N x ↔ (ι N : DiffRing V) ∣ g2 (ι x) := by
  unfold Q2 g2
  rw [← ι_dvd_iff]
  simp only [map_mul, map_add, map_ofNat]

theorem root_of_q1 {N x : V} (h : Q1 N x) : Root N x :=
  (root_iff N x).mpr (Dvd.dvd.mul_right ((q1_iff N x).mp h) _)

theorem root_of_q2 {N x : V} (h : Q2 N x) : Root N x :=
  (root_iff N x).mpr (Dvd.dvd.mul_left ((q2_iff N x).mp h) _)

theorem defQ1 (p x0 : V) :
    𝚺₁-Predicate (fun k : V => ∃ x, Q1 (power p (k + 1)) x ∧ x % p = x0 % p) := by
  unfold Q1
  definability

theorem defQ2 (p x0 : V) :
    𝚺₁-Predicate (fun k : V => ∃ x, Q2 (power p (k + 1)) x ∧ x % p = x0 % p) := by
  unfold Q2
  definability

/-! ### Triple-angle formulas of the Pell recurrence -/

theorem triple_x (k b : V) :
    xcoord (3 * k) b + 3 * xcoord k b = 4 * (xcoord k b * xcoord k b * xcoord k b) := by
  have h1 := (addition (2 * k) k b).1
  rw [double_x, double_y] at h1
  rw [show (3 : V) * k = 2 * k + k by ring, h1]
  calc _ = 4 * (xcoord k b * (1 + delta b * ycoord k b * ycoord k b)) := by ring
    _ = _ := by rw [← ArithmeticPellRecurrence.norm k b]; ring

theorem triple_y (k b : V) :
    ycoord (3 * k) b + ycoord k b = 4 * (xcoord k b * xcoord k b) * ycoord k b := by
  have h1 := (addition (2 * k) k b).2
  rw [double_x, double_y] at h1
  rw [show (3 : V) * k = 2 * k + k by ring, h1]
  calc _ = 2 * ycoord k b * (1 + delta b * ycoord k b * ycoord k b) +
        2 * (xcoord k b * xcoord k b) * ycoord k b := by ring
    _ = _ := by rw [← ArithmeticPellRecurrence.norm k b]; ring

/-! ### Unit indices modulo `p` -/

/-- Doubling an index with `p ∣ Y` gives a unit index: `X ≡ 1`, `Y ≡ 0`. -/
theorem good_double {p b t : V} (hy : p ∣ ycoord t b) :
    p ∣ ycoord (2 * t) b ∧ xcoord (2 * t) b % p = 1 % p := by
  refine ⟨?_, ?_⟩
  · rw [double_y]
    exact dvd_mul_of_dvd_right hy _
  · obtain ⟨c, hc⟩ := hy
    have hc' := congrArg (ι (V := V)) hc
    apply mod_eq_of_sub_eq (q := 2 * ι (delta b) * ι (ycoord t b) * ι c)
    rw [double_x]
    simp only [map_add, map_mul, map_ofNat, map_one] at hc' ⊢
    linear_combination (2 * ι (delta b) * ι (ycoord t b)) * hc'

/-- After a unit index, the next `X` is the fundamental one. -/
theorem next_x {p b t : V} (hy : p ∣ ycoord t b) (hx : xcoord t b % p = 1 % p) :
    (ι p : DiffRing V) ∣ ι (xcoord (t + 1) b) - ι (b + 2) := by
  obtain ⟨c, hc⟩ := hy
  obtain ⟨q, hq⟩ := ringSub_of_mod_eq hx
  refine ⟨(ι b + 2) * q + ι (delta b) * ι c, ?_⟩
  rw [x_succ, hc]
  simp only [map_add, map_mul, map_ofNat, map_one] at hq ⊢
  linear_combination (ι b + 2) * hq

/-- **Trisecting the fundamental unit gives a root of the cubic.** -/
theorem cubic_of_triple {p b k : V} (hp : Irred p) (hp9 : ¬ p ∣ 9)
    (hb2 : (2 : DiffRing V) * ι (b + 2) = ι p + 25)
    (h : (ι p : DiffRing V) ∣ ι (xcoord (3 * k) b) - ι (b + 2)) : ∃ v, Q1 p v := by
  obtain ⟨τ, hτ⟩ : ∃ τ : DiffRing V, τ = 2 * ι (xcoord k b) := ⟨_, rfl⟩
  have hdiv : (ι p : DiffRing V) ∣ τ * τ * τ - 3 * τ - 25 := by
    obtain ⟨c, hc⟩ := h
    have h3 := congrArg (ι (V := V)) (triple_x k b)
    simp only [map_add, map_mul, map_ofNat] at h3
    exact ⟨2 * c + 1, by rw [hτ]; linear_combination (-2) * h3 + 2 * hc + hb2⟩
  obtain ⟨α, β, hαβ⟩ := ring_bez_of_not_dvd hp hp9
  rw [map_ofNat ι 9] at hαβ
  obtain ⟨z, hz⟩ := exists_nat_congr p hp.pos (β * ((τ + 2) * (τ - 1)))
  refine ⟨z, (q1_iff p z).mpr ?_⟩
  have h1 := dvd_trans hz (sub_dvd_of_exp exp1 (ι z) (β * ((τ + 2) * (τ - 1))))
  have h2 := dvd_add h1 (cubic_of_tau hαβ hdiv)
  rwa [sub_add_cancel] at h2

/-- **A unit index divisible by three**: its third is a unit index, or `−23` is a square. -/
theorem descent_or_square {p b k : V} (hp : Irred p) (hp3 : ¬ p ∣ 3)
    (hD4 : (4 : DiffRing V) * ι (delta b) = ι p * (ι p + 50) + 621)
    (hy : p ∣ ycoord (3 * k) b) (hx : xcoord (3 * k) b % p = 1 % p) :
    (p ∣ ycoord k b ∧ xcoord k b % p = 1 % p) ∨ ∃ s, Q2 p s := by
  obtain ⟨u, hu⟩ : ∃ u, xcoord k b = u + 1 :=
    ⟨xcoord k b - 1, (tsub_add_cancel_of_le (one_le_x k b)).symm⟩
  have hX3 : xcoord (3 * k) b = 1 + u * ((2 * u + 3) * (2 * u + 3)) := by
    have h3 := triple_x k b
    rw [hu] at h3
    apply add_right_cancel (b := 3 * (u + 1))
    rw [h3]
    ring
  have hdiv : p ∣ u * ((2 * u + 3) * (2 * u + 3)) := by
    obtain ⟨q, hq⟩ := ringSub_of_mod_eq hx
    rw [hX3] at hq
    rw [← ι_dvd_iff]
    refine ⟨q, ?_⟩
    simp only [map_add, map_mul, map_ofNat, map_one] at hq ⊢
    linear_combination hq
  rcases hp.euclid hdiv with h | h
  · -- `p ∣ X(k) − 1`: the index `k` is already a unit index
    left
    refine ⟨?_, ?_⟩
    · have e1 : ycoord (3 * k) b = u * (4 * u + 8) * ycoord k b + 3 * ycoord k b := by
        apply add_right_cancel (b := ycoord k b)
        rw [triple_y k b, hu]
        ring
      rw [e1] at hy
      have h3 : p ∣ 3 * ycoord k b :=
        dvd_of_dvd_add_left' hy (Dvd.dvd.mul_right (Dvd.dvd.mul_right h _) _)
      rcases hp.euclid h3 with h3 | h3
      · exact absurd h3 hp3
      · exact h3
    · obtain ⟨e, he⟩ := h
      rw [hu, he]
      apply mod_eq_of_sub_eq (q := ι e)
      simp only [map_add, map_mul, map_one]
      ring
  · -- `p ∣ 2X(k) + 1`: then `p ∣ 207·Y(k)² + 1`
    right
    have h' : p ∣ 2 * u + 3 := by rcases hp.euclid h with h | h <;> exact h
    obtain ⟨c, hc⟩ := h'
    have hc' := congrArg (ι (V := V)) hc
    have hn := congrArg (ι (V := V)) (ArithmeticPellRecurrence.norm k b)
    rw [hu] at hn
    simp only [map_add, map_mul, map_ofNat, map_one] at hn hc'
    have h3 : p ∣ 3 * (207 * (ycoord k b * ycoord k b) + 1) := by
      rw [← ι_dvd_iff]
      refine ⟨ι c * (2 * ι u + 1) - (ι p + 50) * (ι (ycoord k b) * ι (ycoord k b)), ?_⟩
      simp only [map_add, map_mul, map_ofNat, map_one]
      linear_combination (2 * ι u + 1) * hc' - 4 * hn -
        (ι (ycoord k b) * ι (ycoord k b)) * hD4
    refine ⟨69 * ycoord k b, ?_⟩
    unfold Q2
    rcases hp.euclid h3 with h3 | h3
    · exact absurd h3 hp3
    · have e : 69 * ycoord k b * (69 * ycoord k b) + 23 =
          23 * (207 * (ycoord k b * ycoord k b) + 1) := by ring
      rw [e]
      exact Dvd.dvd.mul_left h3 23

theorem defUnit (p b : V) :
    𝚺₁-Predicate (fun n : V => 0 < n ∧ p ∣ ycoord n b ∧ xcoord n b % p = 1 % p) := by
  definability

/-- **The cubic has a root modulo `p`, or `−23` is a square modulo `p`**, for every irreducible
`p` other than `2` and `3`. -/
theorem pell_root {p : V} (hp : Irred p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    (∃ v, Q1 p v) ∨ ∃ s, Q2 p s := by
  have hp3' : ¬ p ∣ 3 := not_dvd_three hp hp2 hp3
  have hp9 : ¬ p ∣ 9 := by
    intro h
    rw [show (9 : V) = 3 * 3 by ring] at h
    rcases hp.euclid h with h | h <;> exact hp3' h
  obtain ⟨m, hpm⟩ := odd_of_irred hp hp2
  obtain ⟨b, hb⟩ : ∃ b : V, b = m + 11 := ⟨_, rfl⟩
  have hb2 : (2 : DiffRing V) * ι (b + 2) = ι p + 25 := by
    rw [hpm, hb]
    simp only [map_add, map_mul, map_ofNat, map_one]
    ring
  have hD4 : (4 : DiffRing V) * ι (delta b) = ι p * (ι p + 50) + 621 := by
    rw [hpm, hb]
    unfold delta
    simp only [map_add, map_mul, map_ofNat, map_one]
    ring
  have hP := defUnit p b
  obtain ⟨n0, _, _, hn0, hpy, _⟩ := strong_index b p hp.pos
  obtain ⟨n, ⟨hn, hny, hnx⟩, hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hP (x := 2 * n0)
      ⟨mul_pos (by simp) hn0, good_double hpy⟩
  have h3 : (0 : V) < 3 := by simp
  have hlt : n % 3 ≤ 2 := by
    have h : n % 3 < 2 + 1 := by rw [two_add_one_eq_three]; exact mod_lt n h3
    exact LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp h
  have hd := div_add_mod n 3
  obtain ⟨k, hk⟩ : ∃ k : V, k = n / 3 := ⟨_, rfl⟩
  rw [← hk] at hd
  rcases le_two_iff_eq_zero_or_one_or_two.mp hlt with h | h | h
  · -- `n = 3k`
    rw [h, add_zero] at hd
    have hk0 : 0 < k := by
      rcases eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hd
        exact absurd hd.symm hn.ne'
      · exact h0
    have hkn : k < n := by
      rw [← hd]
      calc k < k + (k + k) := lt_add_of_pos_right k (add_pos hk0 hk0)
        _ = 3 * k := by ring
    rw [← hd] at hny hnx
    rcases descent_or_square hp hp3' hD4 hny hnx with ⟨h1, h2⟩ | h
    · exact absurd ⟨hk0, h1, h2⟩ (hmin k hkn)
    · exact Or.inr h
  · -- `n = 3k + 1`: the index `2n + 1 = 3(2k + 1)`
    left
    rw [h] at hd
    obtain ⟨hy2, hx2⟩ := good_double (t := n) hny
    have hnext := next_x hy2 hx2
    rw [show 2 * n + 1 = 3 * (2 * k + 1) by rw [← hd]; ring] at hnext
    exact cubic_of_triple hp hp9 hb2 hnext
  · -- `n = 3k + 2`: the index `n + 1 = 3(k + 1)`
    left
    rw [h] at hd
    have hnext := next_x hny hnx
    rw [show n + 1 = 3 * (k + 1) by rw [← hd]; ring] at hnext
    exact cubic_of_triple hp hp9 hb2 hnext

/-! ### The prime `2` -/

/-- **A `2`-adic square root of `−23`**: `(2u + 1)² + 23 = 8·2ᵏ·c`, lifting by
`u ↦ u + 2·2ᵏ·c` (`t² + 23` has no simple root modulo `2`). -/
theorem two_adic (k : V) :
    ∃ u c : V, (2 * u + 1) * (2 * u + 1) + 23 = 8 * power 2 k * c := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, 3, by rw [power_zero]; ring⟩
  case succ k ih =>
    obtain ⟨u, c, h⟩ := ih
    refine ⟨u + 2 * power 2 k * c, c * (u + 1) + power 2 k * c * c, ?_⟩
    have e : (2 * (u + 2 * power 2 k * c) + 1) * (2 * (u + 2 * power 2 k * c) + 1) + 23 =
        ((2 * u + 1) * (2 * u + 1) + 23) +
          (8 * power 2 k * c * (2 * u + 1) + 16 * power 2 k * power 2 k * c * c) := by ring
    rw [e, h, power_succ]
    ring

/-! ### Roots modulo prime powers -/

/-- **Roots of `(t³ − t − 1)(t² + 23)` modulo every power of an irreducible.** -/
theorem prime_power_root {p : V} (hp : Irred p) (k : V) : ∃ t, Root (power p k) t := by
  rcases eq_or_ne p 2 with rfl | hp2
  · obtain ⟨u, c, h⟩ := two_adic (V := V) k
    refine ⟨2 * u + 1, root_of_q2 ?_⟩
    unfold Q2
    exact ⟨8 * c, by rw [h]; ring⟩
  rcases eq_or_ne p 3 with rfl | hp3
  · -- `t = 1` is a simple root of `t² + 23` modulo `3`
    have hroot : Q2 3 (1 : V) := by
      unfold Q2
      exact ⟨8, by ring⟩
    obtain ⟨x, hx⟩ := hensel exp2 der2 q2_iff hp (defQ2 3 1) hroot
      ⟨1, -1, by unfold g2'; simp only [map_one, map_ofNat]; norm_num⟩ k
    exact ⟨x, root_of_q2 hx⟩
  by_cases h23 : p ∣ 23
  · -- `t = 3` is a simple root of `t³ − t − 1` modulo `p ∣ 23`
    obtain ⟨e, he⟩ := h23
    have he' := congrArg (ι (V := V)) he
    simp only [map_mul, map_ofNat] at he'
    have hroot : Q1 p (3 : V) := by
      unfold Q1
      apply mod_eq_of_sub_eq (q := ι e)
      simp only [map_mul, map_add, map_one, map_ofNat]
      linear_combination he'
    obtain ⟨x, hx⟩ := hensel exp1 der1 q1_iff hp (defQ1 p 3) hroot
      ⟨-9 * ι e, 8, by
        unfold g1'
        simp only [map_ofNat]
        linear_combination 9 * he'⟩ k
    exact ⟨x, root_of_q1 hx⟩
  rcases pell_root hp hp2 hp3 with ⟨v, hv⟩ | ⟨s, hs⟩
  · -- a root of the cubic; it is simple because `p ∤ 23`
    obtain ⟨c, hc⟩ := (q1_iff p v).mp hv
    obtain ⟨α, β, hαβ⟩ := ring_bez_of_not_dvd hp h23
    rw [map_ofNat ι 23] at hαβ
    obtain ⟨x, hx⟩ := hensel exp1 der1 q1_iff hp (defQ1 p v) hv
      ⟨_, _, bez_g1 hαβ hc⟩ k
    exact ⟨x, root_of_q1 hx⟩
  · -- a square root of `−23`; it is simple because `p ∤ 2·23`
    have hs' : p ∣ s * s + 23 := hs
    have hnd : ¬ p ∣ 2 * s := by
      intro h
      rcases hp.euclid h with h | h
      · exact not_dvd_two hp hp2 h
      · exact h23 (dvd_of_dvd_add_left' hs' (dvd_mul_of_dvd_left h s))
    obtain ⟨α, β, hαβ⟩ := ring_bez_of_not_dvd hp hnd
    have e : (ι (2 * s) : DiffRing V) = 2 * ι s := by rw [map_mul, map_ofNat ι 2]
    rw [e] at hαβ
    obtain ⟨y, hy⟩ := hensel exp2 der2 q2_iff hp (defQ2 p s) hs ⟨α, β, hαβ⟩ k
    exact ⟨y, root_of_q2 hy⟩

/-! ### The intersective root -/

/-- **Every `m > 0` divides `(t³ − t − 1)(t² + 23)` for a natural `t`** (residue form). -/
theorem root_nat (m : V) : 0 < m → ∃ t, Root m t := by
  induction m using ISigma1.sigma1_order_induction
  · unfold Root
    definability
  case ind m ih =>
    intro hm
    rcases lt_or_eq_of_le (pos_iff_one_le.mp hm) with hm1 | hm1
    · obtain ⟨p, hp1, hpm, hirr⟩ := exists_irred_dvd m hm1
      have hp : Irred p := ⟨hp1, hirr⟩
      obtain ⟨k, r, hk1, hmr, hpr⟩ := valuation hp hm hpm
      have hP0 : 0 < power p k := power_pos p k hp.pos
      have hr0 : 0 < r := by
        rcases eq_zero_or_pos r with h0 | h0
        · rw [h0, mul_zero] at hmr
          exact absurd hmr hm.ne'
        · exact h0
      have h2P : 2 ≤ power p k := by
        have := power_mono_exponent p 1 k hp.1.le hk1
        rw [power_one] at this
        exact le_trans (one_lt_iff_two_le.mp hp.1) this
      have hrm : r < m := by
        calc r < r + r := lt_add_of_pos_left r hr0
          _ = 2 * r := (two_mul r).symm
          _ ≤ power p k * r := mul_le_mul_of_nonneg_right h2P (Arithmetic.zero_le r)
          _ = m := hmr.symm
      obtain ⟨t2, ht2⟩ := ih r hrm hr0
      obtain ⟨t1, ht1⟩ := prime_power_root hp k
      have hb : Bez (power p k) r 1 := bez_power (bez_of_irred hp.2 hpr) k
      obtain ⟨a, ha, q, hq⟩ := crt_step hP0 hr0 hb t1 t2
      refine ⟨a, (root_iff m a).mpr ?_⟩
      have h1 : (ι (power p k) : DiffRing V) ∣ poly23 (ι a) := by
        have h := dvd_add (dvd_trans ⟨q, hq⟩ (poly23_sub_dvd (ι a) (ι t1)))
          ((root_iff _ t1).mp ht1)
        rwa [sub_add_cancel] at h
      have h2 : (ι r : DiffRing V) ∣ poly23 (ι a) := by
        obtain ⟨q2, hq2⟩ := ringSub_of_mod_eq ha
        have h := dvd_add (dvd_trans ⟨q2, hq2⟩ (poly23_sub_dvd (ι a) (ι t2)))
          ((root_iff _ t2).mp ht2)
        rwa [sub_add_cancel] at h
      obtain ⟨α, β, hαβ⟩ := bez_one_iff_ring.mp hb
      rw [hmr, map_mul]
      exact dvd_mul_of_bez_ring h1 h2 hαβ
    · subst hm1
      exact ⟨0, by simp [Root]⟩

/-- **The intersective root**: every `m > 0` divides `(t³ − t − 1)(t² + 23)` for some `t` in
the ring of differences. -/
theorem root (m : V) (hm : 0 < m) :
    ∃ t : DiffRing V, (ι m : DiffRing V) ∣ (t ^ 3 - t - 1) * (t ^ 2 + 23) := by
  obtain ⟨t, ht⟩ := root_nat m hm
  refine ⟨ι t, ?_⟩
  have e : ((ι t : DiffRing V) ^ 3 - ι t - 1) * (ι t ^ 2 + 23) = poly23 (ι t) := by
    unfold poly23 g1 g2
    ring
  rw [e]
  exact (root_iff m t).mp ht

#print axioms cubic_of_tau
#print axioms pell_root
#print axioms two_adic
#print axioms prime_power_root
#print axioms root_nat
#print axioms root

end DiophantineConsistency.ZRowsIntersective23
