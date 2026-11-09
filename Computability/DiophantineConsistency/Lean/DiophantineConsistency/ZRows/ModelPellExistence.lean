import DiophantineConsistency.ZRows.PellDirichlet

/-! # Existence of Pell solutions in models of `𝗜𝚺₁`

For a non-square `d > 0` in a model `V` of `𝗜𝚺₁`:

* `exists_pos`: `x² = d·y² + 1` for some `x` and `y > 0`;
* `exists_dvd`: for every `N > 0` such a solution with `N ∣ y` (apply `exists_pos` to the
  non-square `d·N²`).

Proof of `exists_pos`. Put `E = 2d + 3`. `ZRowsPellDirichlet.large_pair`, at `Y = Eⁱ`, gives a
pair `(xᵢ, yᵢ)` with `Eⁱ < yᵢ ≤ Eⁱ⁺¹` and `|xᵢ² − d·yᵢ²| < E`; its norm is not zero
(`no_square_ratio`). A coded sequence (`sigmaOne_skolem_seq`) of the base-`E` codes
`(p⁺, p⁻, xᵢ mod m, yᵢ mod m)`, with `p⁺ = xᵢ² ∸ d·yᵢ²`, `p⁻ = d·yᵢ² ∸ xᵢ²`, `m = p⁺ + p⁻`,
has `E⁴ + 1` entries below `E⁴`, so `ArithmeticPellPigeonhole.pigeonhole` gives `i < j` with
equal codes. The two pairs then have the same norm `k = ±m ≠ 0` and congruent coordinates modulo
`m`, and `y_i < y_j`. In the ring of differences, `(xᵢxⱼ − d·yᵢyⱼ)/m` and `(xᵢyⱼ − xⱼyᵢ)/m` are
integral, satisfy the Pell equation with right side `1` (Brahmagupta's identity, cancelling
`m²`), and the second is not zero because `yᵢ² ≠ yⱼ²`. Absolute values give the natural
solution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ModelPellExistence

/-! ### Two pairs with the same norm and congruent coordinates

Generic over a linearly and strictly ordered commutative ring; stated before
`open LO.FirstOrder.Arithmetic`, whose scoped `≤` would otherwise capture `R`. -/
section Combine
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If `(X₁, Y₁)` and `(X₂, Y₂)` have the same norm `K = ε·m` (`ε² = 1`, `m ≠ 0`), are congruent
modulo `m`, and `0 ≤ Y₁ < Y₂`, then `((X₁X₂ − D·Y₁Y₂)/m, (X₁Y₂ − X₂Y₁)/m)` is a solution of
`u² − D·v² = 1` with `v ≠ 0`. -/
theorem combine {X1 X2 Y1 Y2 D m K ε α β : R}
    (hN1 : X1 * X1 - D * Y1 * Y1 = K) (hN2 : X2 * X2 - D * Y2 * Y2 = K)
    (hK : K = ε * m) (hε : ε * ε = 1) (hm : m ≠ 0)
    (hα : X1 - X2 = m * α) (hβ : Y1 - Y2 = m * β) (hY1 : 0 ≤ Y1) (hY : Y1 < Y2) :
    ∃ u v : R, u * u - D * v * v = 1 ∧ v ≠ 0 := by
  have hP : X1 * X2 - D * Y1 * Y2 = m * (ε - (X1 * α - D * Y1 * β)) := by
    linear_combination (-X1) * hα + (D * Y1) * hβ + hN1 + hK
  have hQ : X1 * Y2 - X2 * Y1 = m * (α * Y1 - β * X1) := by
    linear_combination (-X1) * hβ + Y1 * hα
  have hbrahma : (X1 * X2 - D * Y1 * Y2) * (X1 * X2 - D * Y1 * Y2) -
      D * (X1 * Y2 - X2 * Y1) * (X1 * Y2 - X2 * Y1) =
        (X1 * X1 - D * Y1 * Y1) * (X2 * X2 - D * Y2 * Y2) := by ring
  rw [hP, hQ, hN1, hN2, hK] at hbrahma
  refine ⟨ε - (X1 * α - D * Y1 * β), α * Y1 - β * X1, ?_, ?_⟩
  · apply mul_left_cancel₀ (mul_ne_zero hm hm)
    linear_combination hbrahma + m * m * hε
  · intro h0
    have hQ0 : X1 * Y2 - X2 * Y1 = 0 := by rw [hQ, h0, mul_zero]
    have hK0 : K ≠ 0 := by
      rw [hK]
      intro h
      rcases mul_eq_zero.mp h with h | h
      · rw [h, mul_zero] at hε; exact zero_ne_one hε
      · exact hm h
    have hk : K * (Y2 * Y2 - Y1 * Y1) = 0 := by
      linear_combination (-(Y2 * Y2)) * hN1 + (Y1 * Y1) * hN2 + (X1 * Y2 + X2 * Y1) * hQ0
    rcases mul_eq_zero.mp hk with h | h
    · exact hK0 h
    · have : Y1 * Y1 < Y2 * Y2 := mul_self_lt_mul_self hY1 hY
      linarith

end Combine

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPellPigeonhole ArithmeticPow ZRowsPellDirichlet

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The base-`E` code of a pair: positive part, negative part, residues modulo the norm. -/
def code (D x y : V) : V :=
  (x * x - D * y * y) + (2 * D + 3) * ((D * y * y - x * x) + (2 * D + 3) *
    (x % ((x * x - D * y * y) + (D * y * y - x * x)) + (2 * D + 3) *
      (y % ((x * x - D * y * y) + (D * y * y - x * x)))))

/-- The `i`-th entry of the sequence: a large approximation with nonzero norm. -/
def Good (D i x y : V) : Prop :=
  power (2 * D + 3) i < y ∧ y ≤ power (2 * D + 3) (i + 1) ∧
    x * x < D * y * y + (2 * D + 3) ∧ D * y * y < x * x + (2 * D + 3) ∧ x * x ≠ D * y * y

theorem digit_lt {E a b K : V} (ha : a < E) (hb : b < K) : a + E * b < E * K := by
  have hb' : b + 1 ≤ K := lt_iff_succ_le.mp hb
  calc a + E * b < E + E * b := by simpa using ha
    _ = E * (b + 1) := by ring
    _ ≤ E * K := mul_le_mul_of_nonneg_left hb' (Arithmetic.zero_le E)

theorem tsub_lt_of_lt_add {a b E : V} (hE : 0 < E) (h : a < b + E) : a - b < E := by
  rcases le_total b a with hba | hab
  · apply ι_lt_ι.mp
    rw [ι_tsub hba]
    have := ι_lt_ι.mpr h
    rw [map_add] at this
    linarith
  · rw [tsub_eq_zero_of_le hab]
    exact hE

theorem norm_split (D x y : V) :
    (ι x : DiffRing V) * ι x - ι D * ι y * ι y =
      ι (x * x - D * y * y) - ι (D * y * y - x * x) := by
  rcases le_total (D * y * y) (x * x) with h | h
  · rw [ι_tsub h, tsub_eq_zero_of_le h, map_zero]
    simp only [map_mul]
    ring
  · rw [ι_tsub h, tsub_eq_zero_of_le h, map_zero]
    simp only [map_mul]
    ring

/-- The norm is `±m`. -/
theorem norm_sign (D x y : V) :
    ι (x * x - D * y * y) - ι (D * y * y - x * x) =
        (ι ((x * x - D * y * y) + (D * y * y - x * x)) : DiffRing V) ∨
      ι (x * x - D * y * y) - ι (D * y * y - x * x) =
        -(ι ((x * x - D * y * y) + (D * y * y - x * x)) : DiffRing V) := by
  rcases le_total (D * y * y) (x * x) with h | h
  · left
    rw [tsub_eq_zero_of_le h, map_zero, add_zero]
    ring
  · right
    rw [tsub_eq_zero_of_le h, map_zero, zero_add]
    ring

theorem good_exists (D : V) (hD : 1 ≤ D) (hns : ∀ s : V, s * s ≠ D) (i : V) :
    ∃ x y : V, Good D i x y := by
  have hE1 : (1 : V) ≤ 2 * D + 3 := ι_le_ι.mp (by
    rw [map_one]
    simp only [map_add, map_mul, map_ofNat]
    nlinarith [ι_nonneg D])
  obtain ⟨x, y, hY, hy, hb⟩ := large_pair D hD hns (power (2 * D + 3) i)
  have hP1 : (1 : V) ≤ power (2 * D + 3) i := one_le_power _ _ hE1
  refine ⟨x, y, ?_⟩
  unfold Good
  refine ⟨hY, ?_, ?_, ?_, ?_⟩
  · refine le_trans hy ?_
    rw [power_succ]
    apply ι_le_ι.mp
    simp only [map_add, map_mul, map_ofNat]
    have := ι_le_ι.mpr hP1
    rw [map_one] at this
    nlinarith [ι_nonneg D]
  · apply ι_lt_ι.mp
    simp only [map_add, map_mul, map_ofNat]
    have := (abs_lt.mp hb).2
    linarith
  · apply ι_lt_ι.mp
    simp only [map_add, map_mul, map_ofNat]
    have := (abs_lt.mp hb).1
    linarith
  · have hy1 : 1 ≤ y := le_trans hP1 (le_of_lt hY)
    exact no_square_ratio D hns x y hy1

/-- **Pell existence**: a non-square `d > 0` has a solution of `x² = d·y² + 1` with `y > 0`. -/
theorem exists_pos (d : V) (hd : 0 < d) (hns : ∀ s : V, s * s ≠ d) :
    ∃ x y : V, 0 < y ∧ x * x = d * y * y + 1 := by
  have hD : 1 ≤ d := pos_iff_one_le.mp hd
  set E : V := 2 * d + 3 with hEdef
  have hE1 : (1 : V) ≤ E := ι_le_ι.mp (by
    rw [map_one, hEdef]
    simp only [map_add, map_mul, map_ofNat]
    nlinarith [ι_nonneg d])
  have hE0 : 0 < E := pos_iff_one_le.mpr hE1
  have hR : 𝚺₁-Relation (fun i c : V => ∃ x y : V, c = code d x y ∧ Good d i x y) := by
    unfold code Good
    definability
  obtain ⟨s, hs, hsl, hsm⟩ := sigmaOne_skolem_seq hR (l := E * (E * (E * E)) + 1)
    (fun i _ => by
      obtain ⟨x, y, hg⟩ := good_exists d hD hns i
      exact ⟨_, x, y, rfl, hg⟩)
  have sval : ∀ i < E * (E * (E * E)) + 1,
      ∃ x y : V, znth s i = code d x y ∧ Good d i x y := by
    intro i hi
    have hmem := hs.nth_mem (show i < lh s by rw [hsl]; exact hi)
    rw [hs.znth_eq_of_mem hmem]
    exact hsm i _ hmem
  -- digit bounds of a good pair
  have digits : ∀ i x y : V, Good d i x y →
      x * x - d * y * y < E ∧ d * y * y - x * x < E ∧
        0 < (x * x - d * y * y) + (d * y * y - x * x) ∧
        (x * x - d * y * y) + (d * y * y - x * x) < E := by
    intro i x y hg
    obtain ⟨-, -, h1, h2, h3⟩ := hg
    have hp := tsub_lt_of_lt_add hE0 h1
    have hm := tsub_lt_of_lt_add hE0 h2
    refine ⟨hp, hm, ?_, ?_⟩
    · rcases le_total (d * y * y) (x * x) with h | h
      · rw [tsub_eq_zero_of_le h, add_zero]
        exact tsub_pos_of_lt (lt_of_le_of_ne h (Ne.symm h3))
      · rw [tsub_eq_zero_of_le h, zero_add]
        exact tsub_pos_of_lt (lt_of_le_of_ne h h3)
    · rcases le_total (d * y * y) (x * x) with h | h
      · rw [tsub_eq_zero_of_le h, add_zero]; exact hp
      · rw [tsub_eq_zero_of_le h, zero_add]; exact hm
  have code_lt : ∀ i x y : V, Good d i x y → code d x y < E * (E * (E * E)) := by
    intro i x y hg
    obtain ⟨hp, hm, hm0, hmE⟩ := digits i x y hg
    unfold code
    rw [← hEdef]
    exact digit_lt hp (digit_lt hm (digit_lt (lt_trans (mod_lt _ hm0) hmE)
      (lt_trans (mod_lt _ hm0) hmE)))
  obtain ⟨i, hi, j, hj, hij, he⟩ := pigeonhole (E * (E * (E * E))) s hs hsl (fun n hn => by
    obtain ⟨x, y, hc, hg⟩ := sval n hn
    rw [hc]; exact code_lt n x y hg)
  obtain ⟨x1, y1, hc1, hg1⟩ := sval i hi
  obtain ⟨x2, y2, hc2, hg2⟩ := sval j hj
  rw [hc1, hc2] at he
  obtain ⟨hp1, hm1, hm01, hmE1⟩ := digits i x1 y1 hg1
  obtain ⟨hp2, hm2, hm02, hmE2⟩ := digits j x2 y2 hg2
  unfold code at he
  rw [← hEdef] at he
  obtain ⟨hpe, he⟩ := digit_pair_inj hE0 hp1 hp2 he
  obtain ⟨hme, he⟩ := digit_pair_inj hE0 hm1 hm2 he
  rw [hpe, hme] at he
  obtain ⟨hxe, hye⟩ := digit_pair_inj hE0 (lt_trans (mod_lt _ hm02) hmE2)
    (lt_trans (mod_lt _ hm02) hmE2) he
  -- the common modulus and norm
  set m : V := (x2 * x2 - d * y2 * y2) + (d * y2 * y2 - x2 * x2) with hmdef
  set K : DiffRing V := ι (x2 * x2 - d * y2 * y2) - ι (d * y2 * y2 - x2 * x2) with hKdef
  have hN1 : (ι x1 : DiffRing V) * ι x1 - ι d * ι y1 * ι y1 = K := by
    rw [norm_split, hpe, hme]
  have hN2 : (ι x2 : DiffRing V) * ι x2 - ι d * ι y2 * ι y2 = K := norm_split d x2 y2
  obtain ⟨ε, hK, hε⟩ : ∃ ε : DiffRing V, K = ε * ι m ∧ ε * ε = 1 := by
    rcases norm_sign d x2 y2 with h | h
    · exact ⟨1, by rw [hKdef, h, one_mul], one_mul 1⟩
    · exact ⟨-1, by rw [hKdef, h, neg_one_mul], by ring⟩
  obtain ⟨α, hα⟩ := sub_eq_mul_of_mod_eq hxe
  obtain ⟨β, hβ⟩ := sub_eq_mul_of_mod_eq hye
  -- `y1 < y2`
  have hy12 : y1 < y2 := by
    obtain ⟨-, hy1, -⟩ := hg1
    obtain ⟨hy2, -⟩ := hg2
    have hE1' : (1 : V) ≤ E := hE1
    refine lt_of_le_of_lt hy1 (lt_of_le_of_lt ?_ hy2)
    exact power_mono_exponent _ _ _ hE1' (lt_iff_succ_le.mp hij)
  have hY12 : (ι y1 : DiffRing V) < ι y2 := ι_lt_ι.mpr hy12
  have hm0 : (ι m : DiffRing V) ≠ 0 := by
    intro h0
    have : m = 0 := ι_injective (by rw [h0, map_zero])
    exact (ne_of_gt hm02) this
  obtain ⟨u, v, hpell, hv0⟩ := combine hN1 hN2 hK hε hm0 hα hβ (ι_nonneg y1) hY12
  -- natural absolute values
  obtain ⟨a, ha⟩ := nonneg_iff.mp (abs_nonneg u)
  obtain ⟨b, hb⟩ := nonneg_iff.mp (abs_nonneg v)
  refine ⟨a, b, ?_, ?_⟩
  · apply pos_iff_ne_zero.mpr
    rintro rfl
    rw [map_zero, abs_eq_zero] at hb
    exact hv0 hb
  · apply ι_injective
    simp only [map_add, map_mul, map_one]
    rw [← ha, ← hb, abs_mul_abs_self]
    linear_combination hpell - (ι d : DiffRing V) * abs_mul_abs_self v

/-- **Pell existence with a divisible ordinate.** -/
theorem exists_dvd (d : V) (hd : 0 < d) (hns : ∀ s : V, s * s ≠ d) (N : V) (hN : 0 < N) :
    ∃ x y : V, 0 < y ∧ N ∣ y ∧ x * x = d * y * y + 1 := by
  have hns' : ∀ s : V, s * s ≠ d * N * N :=
    fun s => no_square_ratio d hns s N (pos_iff_one_le.mp hN)
  obtain ⟨x, y, hy, hxy⟩ := exists_pos (d * N * N) (mul_pos (mul_pos hd hN) hN) hns'
  refine ⟨x, N * y, mul_pos hN hy, dvd_mul_right N y, ?_⟩
  rw [hxy]
  ring

#print axioms exists_pos
#print axioms exists_dvd

end DiophantineConsistency.ModelPellExistence
