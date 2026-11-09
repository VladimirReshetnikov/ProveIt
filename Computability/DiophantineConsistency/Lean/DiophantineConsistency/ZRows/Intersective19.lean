import DiophantineConsistency.ZRows.ModelRootWitness

/-! # The intersective polynomial `(t² + 3)(t³ − 19)` in models of `𝗜𝚺₁`

In every model `V` of `𝗜𝚺₁`, every `m > 0` divides `(t² + 3)(t³ − 19)` for some `t`
(`root`, and with a natural `t` in residue form, `root_nat`).

* `lift_step` (any commutative ring): one Hensel step for a simple root. If `P ∣ f(x)`,
  `p ∣ P`, `x ≡ x₀ (mod p)` and `α·p + β·f'(x₀) = 1`, then `P·p ∣ f(x − f(x)/P·β·P)`. The
  polynomial is a function with an explicit first-order expansion
  `f(x + H) = f(x) + H·f'(x) + H²·r`; it is used for `t² + 3` and `t³ − 19`.
* `hensel`: iterating the step along `pᵏ` (a `𝚺₁` induction on `k`, with residues of natural
  representatives, `exists_nat_congr`) gives roots modulo every `pᵏ`.
* `three_adic`: `t³ ≡ 19 (mod 9·3ᵏ)` with `t ≡ 1 (mod 3)`, lifting by `t ↦ t − c·3ᵏ⁺¹`, where
  `t³ − 19 = 9·3ᵏ·c` (`t³ − 19` has no simple root modulo `3`).
* `prime_power_root`: roots modulo `pᵏ` for irreducible `p`:
  `p = 2` (simple root `1` of `t³ − 19`), `p = 3` (`three_adic`), `p ∣ 19` (simple root `4` of
  `t² + 3`), `p = 3m + 1` (simple root of `t² + 3` from `ZRowsRootWitness.neg_three_square`),
  `p = 3m + 2` (simple root of `t³ − 19` from `ModelFermat.cube_root_of_two_mod_three`).
  "`p ∣ 19`" replaces "`p = 19`", so no primality of the numeral `19` is needed.
* `valuation`: `m = pᵏ·r` with `k ≥ 1` and `p ∤ r` (least-number principle).
* `root_nat`: strong induction on `m`, combining the roots modulo `pᵏ` and modulo `r < m` by
  `ModelBoundedForallArith.crt_step`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsIntersective19

/-! ### Ring identities (before the Foundation opens, whose scoped `≤` would capture `R`) -/
section Generic
variable {R : Type*} [CommRing R]

/-- **One Hensel step for a simple root.** -/
theorem lift_step {f f' : R → R}
    (hexp : ∀ x H, ∃ r, f (x + H) = f x + H * f' x + H * H * r)
    (hder : ∀ x y, ∃ r, f' x - f' y = (x - y) * r)
    {p P x x0 α β : R} (hpP : p ∣ P) (hroot : P ∣ f x) (hcong : p ∣ x - x0)
    (hbez : α * p + β * f' x0 = 1) : ∃ h, P * p ∣ f (x + h * P) := by
  obtain ⟨c, hc⟩ := hroot
  obtain ⟨e, he⟩ := hpP
  obtain ⟨u, hu⟩ := hcong
  obtain ⟨s, hs⟩ := hder x x0
  refine ⟨-(c * β), ?_⟩
  obtain ⟨r, hf⟩ := hexp x (-(c * β) * P)
  refine ⟨c * (α - β * u * s) + e * (-(c * β)) * (-(c * β)) * r, ?_⟩
  linear_combination hf + hc + (-(c * β) * P) * hs + (-(c * β) * P * s) * hu +
    ((-(c * β)) * (-(c * β)) * P * r) * he - (c * P) * hbez

/-- The expansion makes `a − b` divide `f a − f b`. -/
theorem sub_dvd_of_exp {f f' : R → R}
    (hexp : ∀ x H, ∃ r, f (x + H) = f x + H * f' x + H * H * r) (a b : R) :
    a - b ∣ f a - f b := by
  obtain ⟨r, hr⟩ := hexp b (a - b)
  refine ⟨f' b + (a - b) * r, ?_⟩
  rw [show b + (a - b) = a by ring] at hr
  linear_combination hr

/-- Two coprime divisors divide together. -/
theorem dvd_mul_of_bez_ring {P r X α β : R} (h1 : P ∣ X) (h2 : r ∣ X)
    (h : P * α + r * β = 1) : P * r ∣ X := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  refine ⟨v * α + u * β, ?_⟩
  linear_combination (-X) * h + (P * α) * hv + (r * β) * hu

/-- The two factors, their derivatives and the product. -/
def f1 (t : R) : R := t * t + 3
def f1' (t : R) : R := 2 * t
def f2 (t : R) : R := t * t * t - 19
def f2' (t : R) : R := 3 * t * t
def poly19 (t : R) : R := f1 t * f2 t

theorem exp1 : ∀ x H : R, ∃ r, f1 (x + H) = f1 x + H * f1' x + H * H * r :=
  fun x H => ⟨1, by unfold f1 f1'; ring⟩
theorem der1 : ∀ x y : R, ∃ r, f1' x - f1' y = (x - y) * r :=
  fun x y => ⟨2, by unfold f1'; ring⟩
theorem exp2 : ∀ x H : R, ∃ r, f2 (x + H) = f2 x + H * f2' x + H * H * r :=
  fun x H => ⟨3 * x + H, by unfold f2 f2'; ring⟩
theorem der2 : ∀ x y : R, ∃ r, f2' x - f2' y = (x - y) * r :=
  fun x y => ⟨3 * x + 3 * y, by unfold f2'; ring⟩

theorem poly19_sub_dvd (a b : R) : a - b ∣ poly19 a - poly19 b := by
  refine ⟨(a + b) * f2 a + f1 b * (a * a + a * b + b * b), ?_⟩
  unfold poly19 f1 f2
  ring

end Generic

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPow ArithmeticGcdNormalization ModelBetaFunction
open ModelBoundedForallArith ModelFermat ZRowsCoprimeSquares ZRowsRootWitness

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Residue forms -/

/-- `t` is a root of `(t² + 3)(t³ − 19)` modulo `N`, in residues of natural numbers. -/
def Root (N t : V) : Prop := ((t * t + 3) * (t * t * t)) % N = ((t * t + 3) * 19) % N
/-- `x` is a root of `t² + 3` modulo `N`. -/
def Q1 (N x : V) : Prop := N ∣ x * x + 3
/-- `x` is a root of `t³ − 19` modulo `N`. -/
def Q2 (N x : V) : Prop := (x * x * x) % N = 19 % N

theorem root_iff (N t : V) : Root N t ↔ (ι N : DiffRing V) ∣ poly19 (ι t) := by
  unfold Root poly19 f1 f2
  constructor
  · intro h
    obtain ⟨q, hq⟩ := ringSub_of_mod_eq h
    simp only [map_mul, map_add, map_ofNat] at hq
    exact ⟨q, by linear_combination hq⟩
  · rintro ⟨q, hq⟩
    apply mod_eq_of_sub_eq (q := q)
    simp only [map_mul, map_add, map_ofNat]
    linear_combination hq

theorem q1_iff (N x : V) : Q1 N x ↔ (ι N : DiffRing V) ∣ f1 (ι x) := by
  unfold Q1 f1
  rw [← ι_dvd_iff]
  simp only [map_mul, map_add, map_ofNat]

theorem q2_iff (N x : V) : Q2 N x ↔ (ι N : DiffRing V) ∣ f2 (ι x) := by
  unfold Q2 f2
  constructor
  · intro h
    obtain ⟨q, hq⟩ := ringSub_of_mod_eq h
    simp only [map_mul, map_ofNat] at hq
    exact ⟨q, by linear_combination hq⟩
  · rintro ⟨q, hq⟩
    apply mod_eq_of_sub_eq (q := q)
    simp only [map_mul, map_ofNat]
    linear_combination hq

theorem root_of_q1 {N x : V} (h : Q1 N x) : Root N x :=
  (root_iff N x).mpr (Dvd.dvd.mul_right ((q1_iff N x).mp h) _)

theorem root_of_q2 {N x : V} (h : Q2 N x) : Root N x :=
  (root_iff N x).mpr (Dvd.dvd.mul_left ((q2_iff N x).mp h) _)

/-- Every ring element is congruent to a natural number modulo `N > 0`. -/
theorem exists_nat_congr (N : V) (hN : 0 < N) (y : DiffRing V) :
    ∃ z : V, (ι N : DiffRing V) ∣ ι z - y := by
  obtain ⟨K, hK⟩ := nonneg_iff.mp (abs_nonneg y)
  have hN1 : (1 : DiffRing V) ≤ ι N := by
    rw [← map_one (ι (V := V))]
    exact ι_le_ι.mpr (pos_iff_one_le.mp hN)
  have hK0 : (0 : DiffRing V) ≤ ι K := ι_nonneg K
  have hKle : ι K ≤ ι N * ι K := le_mul_of_one_le_left hK0 hN1
  have hy : -(ι K) ≤ y := by rw [← hK]; exact neg_abs_le y
  obtain ⟨z, hz⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ y + ι N * ι K by linarith)
  exact ⟨z, ι K, by rw [← hz]; ring⟩

/-- A natural coprimality certificate against an irreducible, in ring form. -/
theorem ring_bez_of_not_dvd {p a : V} (hp : Irred p) (h : ¬ p ∣ a) :
    ∃ α β : DiffRing V, α * ι p + β * ι a = 1 := by
  obtain ⟨α, β, hαβ⟩ := bez_one_iff_ring.mp (bez_of_irred hp.2 h)
  exact ⟨α, β, by linear_combination hαβ⟩

theorem bez_power {p r : V} (h : Bez p r 1) (k : V) : Bez (power p k) r 1 := by
  induction k using ISigma1.sigma1_succ_induction
  · simp only [Bez]
    definability
  case zero => exact ⟨0, 0, 1, 0, by simp⟩
  case succ k ih =>
    rw [power_succ]
    exact bez_mul h ih

theorem not_dvd_two {p : V} (hp : Irred p) (hp2 : p ≠ 2) : ¬ p ∣ 2 := by
  intro h
  have hle : p ≤ 2 := LO.FirstOrder.Arithmetic.le_of_dvd (by simp) h
  rcases le_two_iff_eq_zero_or_one_or_two.mp hle with h0 | h0 | h0
  · exact absurd hp.1 (by rw [h0]; simp)
  · exact absurd hp.1 (by rw [h0]; simp)
  · exact hp2 h0

theorem not_dvd_three {p : V} (hp : Irred p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : ¬ p ∣ 3 := by
  intro h
  have hle : p ≤ 3 := LO.FirstOrder.Arithmetic.le_of_dvd (by simp) h
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp hle with h0 | h0 | h0 | h0
  · exact absurd hp.1 (by rw [h0]; simp)
  · exact absurd hp.1 (by rw [h0]; simp)
  · exact hp2 h0
  · exact hp3 h0

/-! ### Hensel lifting along `pᵏ` -/

theorem defQ1 (p x0 : V) :
    𝚺₁-Predicate (fun k : V => ∃ x, Q1 (power p (k + 1)) x ∧ x % p = x0 % p) := by
  unfold Q1
  definability

theorem defQ2 (p x0 : V) :
    𝚺₁-Predicate (fun k : V => ∃ x, Q2 (power p (k + 1)) x ∧ x % p = x0 % p) := by
  unfold Q2
  definability

/-- **Hensel's lemma for a simple root**, at every internal exponent. The residue predicate
`Q` describes `ι N ∣ f (ι x)` on natural numbers; `hdef` is its `𝚺₁`-definability in the form
used by the induction. -/
theorem hensel {f f' : DiffRing V → DiffRing V}
    (hexp : ∀ x H, ∃ r, f (x + H) = f x + H * f' x + H * H * r)
    (hder : ∀ x y, ∃ r, f' x - f' y = (x - y) * r)
    {Q : V → V → Prop} (hQ : ∀ N x, Q N x ↔ (ι N : DiffRing V) ∣ f (ι x))
    {p x0 : V} (hp : Irred p)
    (hdef : 𝚺₁-Predicate (fun k : V => ∃ x, Q (power p (k + 1)) x ∧ x % p = x0 % p))
    (hroot : Q p x0) (hbez : ∃ α β : DiffRing V, α * ι p + β * f' (ι x0) = 1) (k : V) :
    ∃ x, Q (power p k) x := by
  obtain ⟨α, β, hαβ⟩ := hbez
  have main : ∀ k : V, ∃ x, Q (power p (k + 1)) x ∧ x % p = x0 % p := by
    intro k
    induction k using ISigma1.sigma1_succ_induction
    · exact hdef
    case zero => exact ⟨x0, by rw [zero_add, power_one]; exact hroot, rfl⟩
    case succ k ih =>
      obtain ⟨x, hx, hxc⟩ := ih
      have hP0 : 0 < power p (k + 1) := power_pos p _ hp.pos
      have hPdef : (ι (power p (k + 1)) : DiffRing V) = ι p * ι (power p k) := by
        rw [power_succ, map_mul]
      have hpP : (ι p : DiffRing V) ∣ ι (power p (k + 1)) := ⟨ι (power p k), hPdef⟩
      obtain ⟨q, hq⟩ := ringSub_of_mod_eq hxc
      obtain ⟨h, hh⟩ := lift_step hexp hder hpP ((hQ _ x).mp hx) ⟨q, hq⟩ hαβ
      obtain ⟨z, hz⟩ := exists_nat_congr (power p (k + 1) * p) (mul_pos hP0 hp.pos)
        (ι x + h * ι (power p (k + 1)))
      refine ⟨z, ?_, ?_⟩
      · apply (hQ _ z).mpr
        have e : (ι (power p (k + 1 + 1)) : DiffRing V) = ι (power p (k + 1) * p) := by
          rw [power_succ p (k + 1), mul_comm]
        rw [e]
        have h1 := dvd_trans hz (sub_dvd_of_exp hexp (ι z) (ι x + h * ι (power p (k + 1))))
        rw [map_mul] at h1 ⊢
        have h2 := dvd_add h1 hh
        rwa [sub_add_cancel] at h2
      · obtain ⟨w, hw⟩ := hz
        apply mod_eq_of_sub_eq (q := ι (power p k) * ι p * w + h * ι (power p k) + q)
        rw [map_mul] at hw
        linear_combination hw + hq + (h + ι p * w) * hPdef
  rcases zero_or_succ k with rfl | ⟨j, rfl⟩
  · obtain ⟨x, hx, _⟩ := main 0
    refine ⟨x, (hQ _ x).mpr ?_⟩
    rw [power_zero, map_one]
    exact one_dvd _
  · obtain ⟨x, hx, _⟩ := main j
    exact ⟨x, hx⟩

/-! ### The prime `3` -/

/-- **A `3`-adic cube root of `19`**: `t³ ≡ 19 (mod 9·3ᵏ)` with `t ≡ 1 (mod 3)`. -/
theorem three_adic (k : V) : ∃ x, Q2 (9 * power 3 k) x ∧ x % 3 = 1 % 3 := by
  induction k using ISigma1.sigma1_succ_induction
  · unfold Q2
    definability
  case zero =>
    refine ⟨1, ?_, rfl⟩
    unfold Q2
    rw [power_zero, mul_one]
    apply mod_eq_of_sub_eq (q := -2)
    simp only [map_mul, map_one, map_ofNat]
    norm_num
  case succ k ih =>
    obtain ⟨x, hx, hx3⟩ := ih
    obtain ⟨c, hc⟩ := (q2_iff _ x).mp hx
    obtain ⟨u, hu⟩ := ringSub_of_mod_eq hx3
    have hN0 : 0 < 9 * power (3 : V) (k + 1) :=
      mul_pos (by simp) (power_pos 3 _ (by simp))
    obtain ⟨z, hz⟩ := exists_nat_congr (9 * power 3 (k + 1)) hN0
      (ι x - c * (3 * ι (power (3 : V) k)))
    simp only [map_one, map_ofNat] at hu
    have hx' : (ι x : DiffRing V) = 1 + 3 * u := by linear_combination hu
    have hy : f2 (ι x - c * (3 * ι (power (3 : V) k))) =
        ι (9 * power (3 : V) (k + 1)) *
          (-(c * u * (2 + 3 * u)) + ι x * c * c * ι (power (3 : V) k) -
            c * c * c * ι (power (3 : V) k) * ι (power (3 : V) k)) := by
      rw [power_succ]
      unfold f2 at hc ⊢
      simp only [map_mul, map_ofNat] at hc ⊢
      rw [hx'] at hc ⊢
      linear_combination hc
    refine ⟨z, (q2_iff _ z).mpr ?_, ?_⟩
    · have h1 := dvd_trans hz (sub_dvd_of_exp exp2 (ι z) (ι x - c * (3 * ι (power (3 : V) k))))
      have h2 := dvd_add h1 ⟨_, hy⟩
      rwa [sub_add_cancel] at h2
    · obtain ⟨w, hw⟩ := hz
      apply mod_eq_of_sub_eq
        (q := 9 * ι (power (3 : V) k) * w - c * ι (power (3 : V) k) + u)
      rw [power_succ] at hw
      simp only [map_mul, map_one, map_ofNat] at hw ⊢
      linear_combination hw + hu

/-! ### Roots modulo prime powers -/

/-- **Roots of `(t² + 3)(t³ − 19)` modulo every power of an irreducible.** -/
theorem prime_power_root {p : V} (hp : Irred p) (k : V) : ∃ t, Root (power p k) t := by
  rcases eq_or_ne p 2 with rfl | hp2
  · -- `t = 1` is a simple root of `t³ − 19` modulo `2`
    have hroot : Q2 2 (1 : V) := by
      unfold Q2
      apply mod_eq_of_sub_eq (q := -9)
      simp only [map_mul, map_one, map_ofNat]
      norm_num
    obtain ⟨x, hx⟩ := hensel exp2 der2 q2_iff hp (defQ2 2 1) hroot
      ⟨-1, 1, by unfold f2'; simp only [map_one, map_ofNat]; norm_num⟩ k
    exact ⟨x, root_of_q2 hx⟩
  rcases eq_or_ne p 3 with rfl | hp3
  · obtain ⟨x, hx, _⟩ := three_adic k
    refine ⟨x, root_of_q2 ?_⟩
    exact mod_eq_of_dvd_of_mod_eq hx (dvd_mul_left _ _)
  by_cases h19 : p ∣ 19
  · -- `t = 4` is a simple root of `t² + 3` modulo `p ∣ 19`
    have hroot : Q1 p (4 : V) := by
      unfold Q1
      rwa [show (4 : V) * 4 + 3 = 19 by ring]
    have hnd : ¬ p ∣ 2 * 4 := by
      intro h
      rw [show (2 : V) * 4 = 2 * (2 * 2) by ring] at h
      rcases hp.euclid h with h | h
      · exact not_dvd_two hp hp2 h
      · rcases hp.euclid h with h | h <;> exact not_dvd_two hp hp2 h
    obtain ⟨α, β, hαβ⟩ := ring_bez_of_not_dvd hp hnd
    have e : (ι (2 * 4 : V) : DiffRing V) = 2 * ι (4 : V) := by rw [map_mul, map_ofNat ι 2]
    rw [e] at hαβ
    obtain ⟨x, hx⟩ := hensel exp1 der1 q1_iff hp (defQ1 p _) hroot
      ⟨α, β, hαβ⟩ k
    exact ⟨x, root_of_q1 hx⟩
  rcases mod_three_cases hp hp3 with hm | hm
  · -- `p = 3m + 1`: a simple root of `t² + 3`
    obtain ⟨x, hx⟩ := neg_three_square hp _ hm
    have hnd : ¬ p ∣ 2 * x := by
      intro h
      rcases hp.euclid h with h | h
      · exact not_dvd_two hp hp2 h
      · exact not_dvd_three hp hp2 hp3
          (dvd_of_dvd_add_left' hx (dvd_mul_of_dvd_left h x))
    obtain ⟨α, β, hαβ⟩ := ring_bez_of_not_dvd hp hnd
    have e : (ι (2 * x) : DiffRing V) = 2 * ι x := by rw [map_mul, map_ofNat ι 2]
    rw [e] at hαβ
    obtain ⟨y, hy⟩ := hensel exp1 der1 q1_iff hp (defQ1 p _) hx
      ⟨α, β, hαβ⟩ k
    exact ⟨y, root_of_q1 hy⟩
  · -- `p = 3m + 2`: a simple root of `t³ − 19`
    obtain ⟨b, hb⟩ := cube_root_of_two_mod_three hp _ hm 19
    have hnd : ¬ p ∣ 3 * b * b := by
      have hpb : ¬ p ∣ b := by
        intro h
        apply h19
        apply mod_eq_zero_iff_dvd.mp
        rw [← hb]
        exact mod_eq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) b)
      intro h
      rcases hp.euclid h with h | h
      · rcases hp.euclid h with h | h
        · exact not_dvd_three hp hp2 hp3 h
        · exact hpb h
      · exact hpb h
    obtain ⟨α, β, hαβ⟩ := ring_bez_of_not_dvd hp hnd
    have e : (ι (3 * b * b) : DiffRing V) = 3 * ι b * ι b := by
      rw [map_mul, map_mul, map_ofNat ι 3]
    rw [e] at hαβ
    obtain ⟨y, hy⟩ := hensel exp2 der2 q2_iff hp (defQ2 p _) hb
      ⟨α, β, hαβ⟩ k
    exact ⟨y, root_of_q2 hy⟩

/-! ### Splitting off a prime power -/

theorem lt_power_self {p : V} (hp : 1 < p) (n : V) : n < power p n := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    have hP1 : 1 ≤ power p n := one_le_power p n hp.le
    have h1 : n + 1 ≤ power p n := LO.FirstOrder.Arithmetic.lt_iff_succ_le.mp ih
    calc n + 1 < power p n + 1 := lt_of_le_of_lt h1 (lt_add_one _)
      _ ≤ power p n + power p n := add_le_add le_rfl hP1
      _ = 2 * power p n := (two_mul _).symm
      _ ≤ p * power p n :=
        mul_le_mul_of_nonneg_right (one_lt_iff_two_le.mp hp) (Arithmetic.zero_le _)
      _ = power p (n + 1) := (power_succ p n).symm

/-- **The `p`-part of `m`**: `m = pᵏ·r` with `k ≥ 1` and `p ∤ r`. -/
theorem valuation {p m : V} (hp : Irred p) (hm : 0 < m) (hpm : p ∣ m) :
    ∃ k r, 1 ≤ k ∧ m = power p k * r ∧ ¬ p ∣ r := by
  have hP : 𝚺₁-Predicate (fun k : V => ¬ power p (k + 1) ∣ m) := by definability
  have hs : ¬ power p (m + 1) ∣ m := fun h =>
    absurd (LO.FirstOrder.Arithmetic.le_of_dvd hm h)
      (not_le.mpr (lt_trans (lt_add_one m) (lt_power_self hp.1 (m + 1))))
  obtain ⟨k, hk, hmin⟩ := InductionOnHierarchy.least_number 𝚺 1 hP (x := m) hs
  have hdiv : power p k ∣ m := by
    rcases zero_or_succ k with rfl | ⟨j, rfl⟩
    · rw [power_zero]; exact one_dvd m
    · exact not_not.mp (hmin j (lt_add_one j))
  obtain ⟨r, hr⟩ := hdiv
  refine ⟨k, r, ?_, hr, ?_⟩
  · rcases eq_or_ne k 0 with h0 | h0
    · rw [h0, zero_add, power_one] at hk
      exact absurd hpm hk
    · exact pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0)
  · rintro ⟨s, rfl⟩
    exact hk ⟨s, by rw [hr, power_succ]; ring⟩

/-! ### The intersective root -/

/-- **Every `m > 0` divides `(t² + 3)(t³ − 19)` for a natural `t`** (residue form). -/
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
      have h1 : (ι (power p k) : DiffRing V) ∣ poly19 (ι a) := by
        have h := dvd_add (dvd_trans ⟨q, hq⟩ (poly19_sub_dvd (ι a) (ι t1)))
          ((root_iff _ t1).mp ht1)
        rwa [sub_add_cancel] at h
      have h2 : (ι r : DiffRing V) ∣ poly19 (ι a) := by
        obtain ⟨q2, hq2⟩ := ringSub_of_mod_eq ha
        have h := dvd_add (dvd_trans ⟨q2, hq2⟩ (poly19_sub_dvd (ι a) (ι t2)))
          ((root_iff _ t2).mp ht2)
        rwa [sub_add_cancel] at h
      obtain ⟨α, β, hαβ⟩ := bez_one_iff_ring.mp hb
      rw [hmr, map_mul]
      exact dvd_mul_of_bez_ring h1 h2 hαβ
    · subst hm1
      exact ⟨0, by simp [Root]⟩

/-- **The intersective root**: every `m > 0` divides `(t² + 3)(t³ − 19)` for some `t` in the
ring of differences. -/
theorem root (m : V) (hm : 0 < m) :
    ∃ t : DiffRing V, (ι m : DiffRing V) ∣ (t ^ 2 + 3) * (t ^ 3 - 19) := by
  obtain ⟨t, ht⟩ := root_nat m hm
  refine ⟨ι t, ?_⟩
  have e : ((ι t : DiffRing V) ^ 2 + 3) * (ι t ^ 3 - 19) = poly19 (ι t) := by
    unfold poly19 f1 f2
    ring
  rw [e]
  exact (root_iff m t).mp ht

#print axioms lift_step
#print axioms hensel
#print axioms three_adic
#print axioms prime_power_root
#print axioms valuation
#print axioms root_nat
#print axioms root

end DiophantineConsistency.ZRowsIntersective19
