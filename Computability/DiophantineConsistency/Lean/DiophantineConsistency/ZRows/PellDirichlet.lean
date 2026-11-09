import DiophantineConsistency.ArithmeticPellPigeonhole
import DiophantineConsistency.ModelBoundedForallArith

/-! # Internal Dirichlet approximation for `√D` in models of `𝗜𝚺₁`

No real numbers are used: `√D` only enters through the integer square roots
`u = ⌊√(D·(M·i)²)⌋` (Foundation's `√`), and every comparison with `√D` is replaced by a
comparison of squares.

* `approx_upper`, `approx_lower`, `approx_norm` (any linearly and strictly ordered commutative
  ring): if `aᵢ² ≤ D·bᵢ² < (aᵢ+1)²` for `i = 1, 2`, then `A = a₂ − a₁` and `B = b₂ − b₁` satisfy
  `(A−1)² < D·B² < (A+1)²`, hence `|A² − D·B²| < 2·D·B + 3`. The proofs multiply the defining
  inequalities ("Cauchy–Schwarz for square roots") instead of taking roots.
* `no_square_ratio`: if `D` is not a square, `x² ≠ D·y²` for every `y ≥ 1` (descent
  `(x, y) ↦ (D·y − s·x, x − s·y)` with `s = ⌊√D⌋`, through the least-number principle).
* `dirichlet`: for every `M ≥ 1` there are `x` and `1 ≤ y ≤ M` with
  `M²·|x² − D·y²| < 2·D·M·y + 3` (pigeonhole on the residues `uᵢ mod M`, `i ≤ M`).
* `large_pair`: if `D` is not a square, then for every `Y` there are `x, y` with
  `Y < y ≤ 2·D·Y + 3` and `|x² − D·y²| < 2·D + 3`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsPellDirichlet

/-! The generic ordered-ring lemmas come before `open LO.FirstOrder.Arithmetic`: Foundation's
scoped `≤` instance would otherwise capture `R`. -/
section Ordered
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem lt_of_mul_self_lt' {a b : R} (hb : 0 ≤ b) (h : a * a < b * b) : a < b := by
  by_contra hc
  rw [not_lt] at hc
  exact absurd h (not_lt.mpr (mul_self_le_mul_self hb hc))

theorem le_of_mul_self_le' {a b : R} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b := by
  by_contra hc
  rw [not_le] at hc
  exact absurd h (not_le.mpr (mul_self_lt_mul_self hb hc))

/-- `B√D < A + 1`, squared. -/
theorem approx_upper {D a1 a2 b1 b2 : R} (hD : 0 ≤ D) (hb1 : 0 ≤ b1)
    (hB : 0 ≤ b2 - b1) (h1 : a1 * a1 ≤ D * b1 * b1)
    (h2' : D * b2 * b2 < (a2 + 1) * (a2 + 1)) :
    D * (b2 - b1) * (b2 - b1) < (a2 - a1 + 1) * (a2 - a1 + 1) := by
  by_contra hc
  rw [not_lt] at hc
  have h0 : 0 ≤ D * (b2 - b1) * b1 := mul_nonneg (mul_nonneg hD hB) hb1
  have hm := mul_le_mul hc h1 (mul_self_nonneg a1) (mul_nonneg (mul_nonneg hD hB) hB)
  have hprod : (a2 - a1 + 1) * a1 ≤ D * (b2 - b1) * b1 :=
    le_of_mul_self_le' h0 (by linarith [hm])
  linarith [hc, hprod, h1, h2']

/-- `A − 1 < B√D`, squared. -/
theorem approx_lower {D a1 a2 b1 b2 : R} (hD : 0 ≤ D) (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1)
    (hA1 : 1 ≤ a2 - a1) (h1' : D * b1 * b1 < (a1 + 1) * (a1 + 1))
    (h2 : a2 * a2 ≤ D * b2 * b2) :
    (a2 - a1 - 1) * (a2 - a1 - 1) < D * (b2 - b1) * (b2 - b1) := by
  by_contra hc
  rw [not_lt] at hc
  have h0 : 0 ≤ (a2 - a1 - 1) * (a1 + 1) := mul_nonneg (by linarith) (by linarith)
  have hm := mul_le_mul hc h1'.le (mul_nonneg (mul_nonneg hD hb1) hb1)
    (mul_self_nonneg (a2 - a1 - 1))
  have hprod : D * (b2 - b1) * b1 ≤ (a2 - a1 - 1) * (a1 + 1) :=
    le_of_mul_self_le' h0 (by linarith [hm])
  linarith [hc, hprod, h1', h2]

/-- The norm of a difference of two lower approximations. -/
theorem approx_norm {D a1 a2 b1 b2 : R} (hD : 1 ≤ D) (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1)
    (hB : 1 ≤ b2 - b1) (hA : a2 - a1 = 0 ∨ 1 ≤ a2 - a1)
    (h1 : a1 * a1 ≤ D * b1 * b1) (h1' : D * b1 * b1 < (a1 + 1) * (a1 + 1))
    (h2 : a2 * a2 ≤ D * b2 * b2) (h2' : D * b2 * b2 < (a2 + 1) * (a2 + 1)) :
    |(a2 - a1) * (a2 - a1) - D * (b2 - b1) * (b2 - b1)| < 2 * D * (b2 - b1) + 3 := by
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hB0 : 0 ≤ b2 - b1 := le_trans zero_le_one hB
  have hup := approx_upper hD0 hb1 hB0 h1 h2'
  have hDB : 1 ≤ D * (b2 - b1) * (b2 - b1) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hD hB) hB
  rcases hA with h0 | hA1
  · exfalso
    rw [h0] at hup
    linarith
  have hlow := approx_lower hD0 ha1 hb1 hA1 h1' h2
  have hDD : D * (b2 - b1) * (b2 - b1) ≤ D * (b2 - b1) * (D * (b2 - b1)) := by
    have := mul_le_mul_of_nonneg_left hD (mul_nonneg (mul_nonneg hD0 hB0) hB0)
    linarith
  have hlt : a2 - a1 - 1 < D * (b2 - b1) :=
    lt_of_mul_self_lt' (mul_nonneg hD0 hB0) (by linarith)
  rw [abs_lt]
  constructor <;> linarith

end Ordered

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticPellPigeonhole ModelBoundedForallArith

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_tsub {a b : V} (h : b ≤ a) : (ι (a - b) : DiffRing V) = ι a - ι b := by
  have e := congrArg (ι (V := V)) (tsub_add_cancel_of_le h)
  rw [map_add] at e
  linear_combination e

theorem one_le_abs_of_ne {x : DiffRing V} (h : x ≠ 0) : 1 ≤ |x| :=
  one_le_of_pos (fun _ ha => pos_iff_one_le.mp ha) (abs_pos.mpr h)

/-- **No rational square root.** If `D` is not a square, then `x² ≠ D·y²` whenever `y ≥ 1`. -/
theorem no_square_ratio (D : V) (hns : ∀ s : V, s * s ≠ D) :
    ∀ x y : V, 1 ≤ y → x * x ≠ D * y * y := by
  intro x0 y0 hy0 he0
  have hP : 𝚺₁-Predicate (fun y : V => 1 ≤ y ∧ ∃ x, x * x = D * y * y) := by definability
  obtain ⟨y, ⟨hy1, x, he⟩, hmin⟩ :=
    InductionOnHierarchy.least_number 𝚺 1 hP (x := y0) ⟨hy0, x0, he0⟩
  set s := √D with hsdef
  have hs1 : s * s ≤ D := sqrt_spec_le D
  have hs2 : D < (s + 1) * (s + 1) := sqrt_spec_lt D
  have hs3 : s * s < D := lt_of_le_of_ne hs1 (hns s)
  have hS1 : (ι s : DiffRing V) * ι s < ι D := by rw [← map_mul]; exact ι_lt_ι.mpr hs3
  have hS2 : (ι D : DiffRing V) < (ι s + 1) * (ι s + 1) := by
    rw [← map_one (ι (V := V)), ← map_add, ← map_mul]; exact ι_lt_ι.mpr hs2
  have hE : (ι x : DiffRing V) * ι x = ι D * ι y * ι y := by
    rw [← map_mul, ← map_mul, ← map_mul, he]
  have hY : (1 : DiffRing V) ≤ ι y := by rw [← map_one (ι (V := V))]; exact ι_le_ι.mpr hy1
  have hY0 : (0 : DiffRing V) < ι y * ι y := mul_pos (by linarith) (by linarith)
  have hX0 : (0 : DiffRing V) ≤ ι x := ι_nonneg x
  have hS0 : (0 : DiffRing V) ≤ ι s := ι_nonneg s
  -- `s·y < x < (s+1)·y` and `s·x ≤ D·y`
  have hlt1 : (ι s : DiffRing V) * ι y < ι x := by
    apply lt_of_mul_self_lt' hX0
    have := mul_lt_mul_of_pos_right hS1 hY0
    linarith
  have hlt2 : (ι x : DiffRing V) < (ι s + 1) * ι y := by
    apply lt_of_mul_self_lt' (mul_nonneg (by linarith) (ι_nonneg y))
    have := mul_lt_mul_of_pos_right hS2 hY0
    linarith
  have hle3 : (ι s : DiffRing V) * ι x ≤ ι D * ι y := by
    apply le_of_mul_self_le' (mul_nonneg (ι_nonneg D) (ι_nonneg y))
    have := mul_le_mul_of_nonneg_right hS1.le (mul_nonneg (ι_nonneg D) (le_of_lt hY0))
    have hE2 : (ι s : DiffRing V) * ι s * (ι x * ι x) = ι s * ι s * (ι D * ι y * ι y) := by
      rw [hE]
    linarith
  have hsy : s * y < x := ι_lt_ι.mp (by rw [map_mul]; exact hlt1)
  have hsx : s * x ≤ D * y := ι_le_ι.mp (by rw [map_mul, map_mul]; exact hle3)
  have hy'1 : 1 ≤ x - s * y := pos_iff_one_le.mp (tsub_pos_of_lt hsy)
  have hy'lt : x - s * y < y := ι_lt_ι.mp (by
    rw [ι_tsub hsy.le, map_mul]
    linarith)
  apply hmin (x - s * y) hy'lt
  refine ⟨hy'1, D * y - s * x, ι_injective ?_⟩
  simp only [map_mul, ι_tsub hsy.le, ι_tsub hsx]
  linear_combination (ι s * ι s - ι D) * hE

/-- **Internal Dirichlet approximation.** -/
theorem dirichlet (D M : V) (hD : 1 ≤ D) (hM : 1 ≤ M) :
    ∃ x y : V, 1 ≤ y ∧ y ≤ M ∧
      ι M * ι M * |ι x * ι x - ι D * ι y * ι y| < 2 * ι D * ι M * ι y + 3 := by
  have hM0 : 0 < M := pos_iff_one_le.mpr hM
  have hR : 𝚺₁-Relation (fun i c : V => c = √(D * (M * i) * (M * i)) % M) := by
    definability
  obtain ⟨s, hs, hsl, hsm⟩ := sigmaOne_skolem_seq hR (l := M + 1) (fun i _ => ⟨_, rfl⟩)
  have sval : ∀ i < M + 1, znth s i = √(D * (M * i) * (M * i)) % M := by
    intro i hi
    have hmem := hs.nth_mem (show i < lh s by rw [hsl]; exact hi)
    rw [hs.znth_eq_of_mem hmem]
    exact hsm i _ hmem
  obtain ⟨i, hi, j, hj, hij, he⟩ := pigeonhole M s hs hsl (fun n hn => by
    rw [sval n hn]; exact mod_lt _ hM0)
  rw [sval i hi, sval j hj] at he
  set ui := √(D * (M * i) * (M * i)) with hui
  set uj := √(D * (M * j) * (M * j)) with huj
  have hDd : (1 : DiffRing V) ≤ ι D := by rw [← map_one (ι (V := V))]; exact ι_le_ι.mpr hD
  have hMd : (1 : DiffRing V) ≤ ι M := by rw [← map_one (ι (V := V))]; exact ι_le_ι.mpr hM
  have hijd : (ι i : DiffRing V) ≤ ι j := ι_le_ι.mpr hij.le
  -- the square-root bounds in the ring of differences
  have sq_le (u n : V) (h : u * u ≤ n) : (ι u : DiffRing V) * ι u ≤ ι n := by
    rw [← map_mul]; exact ι_le_ι.mpr h
  have sq_lt (u n : V) (h : n < (u + 1) * (u + 1)) :
      (ι n : DiffRing V) < (ι u + 1) * (ι u + 1) := by
    rw [← map_one (ι (V := V)), ← map_add, ← map_mul]; exact ι_lt_ι.mpr h
  have h1 := sq_le ui _ (sqrt_spec_le _)
  have h1' := sq_lt ui _ (sqrt_spec_lt _)
  have h2 := sq_le uj _ (sqrt_spec_le _)
  have h2' := sq_lt uj _ (sqrt_spec_lt _)
  simp only [map_mul] at h1 h1' h2 h2'
  -- monotonicity `ui ≤ uj`
  have hmono : (ι D : DiffRing V) * (ι M * ι i) * (ι M * ι i) ≤
      ι D * (ι M * ι j) * (ι M * ι j) := by
    have hMi : (0 : DiffRing V) ≤ ι M * ι i := mul_nonneg (ι_nonneg M) (ι_nonneg i)
    have := mul_self_le_mul_self hMi (mul_le_mul_of_nonneg_left hijd (ι_nonneg M))
    have := mul_le_mul_of_nonneg_left this (ι_nonneg D)
    linarith
  have hu : ui ≤ uj := by
    have hlt : (ι ui : DiffRing V) < ι uj + 1 :=
      lt_of_mul_self_lt' (by linarith [ι_nonneg uj]) (by linarith)
    rw [← map_one (ι (V := V)), ← map_add, ι_lt_ι] at hlt
    exact LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hlt
  obtain ⟨x, hx⟩ := dvd_tsub_of_mod_eq he.symm
  refine ⟨x, j - i, pos_iff_one_le.mp (tsub_pos_of_lt hij),
    le_trans tsub_le_self (LO.FirstOrder.Arithmetic.lt_succ_iff_le.mp hj), ?_⟩
  have hA : (ι uj : DiffRing V) - ι ui = ι M * ι x := by
    rw [← ι_tsub hu, hx, map_mul]
  have hB : (ι M : DiffRing V) * ι j - ι M * ι i = ι M * ι (j - i) := by
    rw [ι_tsub hij.le]; ring
  have hy1 : (1 : DiffRing V) ≤ ι (j - i) := by
    rw [← map_one (ι (V := V))]; exact ι_le_ι.mpr (pos_iff_one_le.mp (tsub_pos_of_lt hij))
  have hBone : (1 : DiffRing V) ≤ ι M * ι j - ι M * ι i := by
    rw [hB]; exact one_le_mul_of_one_le_of_one_le hMd hy1
  have hAcase : (ι uj : DiffRing V) - ι ui = 0 ∨ 1 ≤ ι uj - ι ui := by
    rw [hA]
    rcases eq_or_ne x 0 with h0 | h0
    · left; rw [h0, map_zero, mul_zero]
    · right
      have : (1 : DiffRing V) ≤ ι x := by
        rw [← map_one (ι (V := V))]; exact ι_le_ι.mpr (pos_iff_one_le.mp (pos_iff_ne_zero.mpr h0))
      exact one_le_mul_of_one_le_of_one_le hMd this
  have key := approx_norm hDd (ι_nonneg ui) (mul_nonneg (ι_nonneg M) (ι_nonneg i)) hBone
    hAcase h1 h1' h2 h2'
  rw [hA, hB] at key
  have hfac : ι M * ι x * (ι M * ι x) - ι D * (ι M * ι (j - i)) * (ι M * ι (j - i)) =
      ι M * ι M * (ι x * ι x - ι D * ι (j - i) * ι (j - i)) := by ring
  rw [hfac, abs_mul, abs_of_nonneg (mul_nonneg (ι_nonneg M) (ι_nonneg M))] at key
  linarith

/-- **Approximations with large ordinates.** -/
theorem large_pair (D : V) (hD : 1 ≤ D) (hns : ∀ s : V, s * s ≠ D) (Y : V) :
    ∃ x y : V, Y < y ∧ y ≤ 2 * D * Y + 3 ∧
      |(ι x : DiffRing V) * ι x - ι D * ι y * ι y| < 2 * ι D + 3 := by
  have hM : (1 : V) ≤ 2 * D * Y + 3 := ι_le_ι.mp (by
    rw [map_one]
    simp only [map_add, map_mul, map_ofNat]
    nlinarith [ι_nonneg D, ι_nonneg Y])
  obtain ⟨x, y, hy1, hyM, hb⟩ := dirichlet D (2 * D * Y + 3) hD hM
  set m : DiffRing V := ι (2 * D * Y + 3) with hmdef
  have hm : m = 2 * ι D * ι Y + 3 := by
    rw [hmdef]; simp only [map_add, map_mul, map_ofNat]
  have hm1 : (1 : DiffRing V) ≤ m := by rw [← map_one (ι (V := V))]; exact ι_le_ι.mpr hM
  have hyd : (ι y : DiffRing V) ≤ m := ι_le_ι.mpr hyM
  have hD0 : (0 : DiffRing V) ≤ ι D := ι_nonneg D
  set N : DiffRing V := ι x * ι x - ι D * ι y * ι y with hN
  have hN0 : 0 ≤ |N| := abs_nonneg N
  have hmm : (1 : DiffRing V) ≤ m * m := one_le_mul_of_one_le_of_one_le hm1 hm1
  refine ⟨x, y, ?_, hyM, ?_⟩
  · by_contra hc
    rw [not_lt] at hc
    have hyY : (ι y : DiffRing V) ≤ ι Y := ι_le_ι.mpr hc
    have hNne : N ≠ 0 := by
      intro h0
      apply no_square_ratio D hns x y hy1
      apply ι_injective
      simp only [map_mul]
      linear_combination h0 - hN
    have hN1 := one_le_abs_of_ne hNne
    have hY0 : (0 : DiffRing V) ≤ ι Y := ι_nonneg Y
    have e1 : m * m ≤ m * m * |N| := le_mul_of_one_le_right (by linarith) hN1
    have e2 : ι D * m * ι y ≤ ι D * m * ι Y :=
      mul_le_mul_of_nonneg_left hyY (mul_nonneg hD0 (by linarith))
    have e3 : m * m = 2 * ι D * ι Y * m + 3 * m := by rw [hm]; ring
    linarith
  · have e1 : ι D * m * ι y ≤ ι D * m * m :=
      mul_le_mul_of_nonneg_left hyd (mul_nonneg hD0 (by linarith))
    have hlt : m * m * |N| < m * m * (2 * ι D + 3) := by linarith
    exact lt_of_mul_lt_mul_left hlt (by linarith)

#print axioms no_square_ratio
#print axioms dirichlet
#print axioms large_pair

end DiophantineConsistency.ZRowsPellDirichlet
