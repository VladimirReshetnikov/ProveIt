import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.ArithmeticPellClassification
import DiophantineConsistency.ArithmeticPellResidueClasses
import DiophantineConsistency.ModelArithmetic
/-! # The signed odd-index Pell residue in every model of `𝗜𝚺₁`

Internal counterpart of `SignedPellResidue`. With `M = 4(b+2)²`:

* `odd_ordinate_pm`: every odd-index ordinate `ycoord (2h+1) b` is `±1` modulo
  `M`, by a two-step internal induction on the recurrence `odd_y_rec`;
* `four_square_dvd_sub_one`: in the ring of differences, if
  `S²V² - (S²-1)y² = 1` with `S ≥ 2` and `y ≡ 1 (mod 4)`, then
  `4S² ∣ y - 1`. Internal classification (`solution_index`) puts `(S|V|, |y|)`
  on the Pell orbit of base `S`, the base divides the abscissa so the index is
  odd (`odd_index_witness`), and the mod-4 homomorphism selects the sign. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ArithmeticOddOrdinateResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ModelDifferenceRing DiscreteOrderedRingFacts ModelArithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- Keep represented coordinates opaque to the definability simplifier.
attribute [local irreducible] xcoord ycoord

/-- `a ≡ c (mod M)` in the ring of differences. -/
def Cong (M a : V) (c : DiffRing V) : Prop := ∃ u : DiffRing V, ι a - c = ι M * u

theorem cong_of_mod {M a r : V} (h : a % M = r) : Cong M a (ι r) := by
  refine ⟨ι (a / M), ?_⟩
  have e := congrArg (ι : V →+* DiffRing V) (div_add_mod a M)
  simp only [map_add, map_mul] at e
  rw [h] at e
  linear_combination -e

theorem mod_of_cong {M a r : V} (hM : 0 < M) (hr : r < M) (h : Cong M a (ι r)) : a % M = r := by
  obtain ⟨u, hu⟩ := h
  have hMpos : (0 : DiffRing V) < ι M := ι_pos hM
  have hrM : ι r < ι M := ι_lt_ι.mpr hr
  have hu0 : 0 ≤ u := by
    by_contra hneg
    push_neg at hneg
    have h1 : u ≤ -1 := by
      have := model_discrete (-u) (by linarith)
      linarith
    have : ι M * u ≤ ι M * (-1) := mul_le_mul_of_nonneg_left h1 hMpos.le
    have ha := ι_nonneg a
    nlinarith
  obtain ⟨u', rfl⟩ := nonneg_iff.mp hu0
  have hv : a = u' * M + r := ι_injective (by simp only [map_add, map_mul]; linear_combination hu)
  rw [hv, mod_mul_add_of_lt u' M hr]

theorem one_lt_M (b : V) : (1 : V) < 4*(b+2)*(b+2) := by
  apply ι_lt_ι.mp
  simp only [map_mul, map_add, map_one, map_ofNat]
  have := ι_nonneg b
  nlinarith

theorem cong_one_iff {M y : V} (hM : 1 < M) : y % M = 1 ↔ Cong M y 1 := by
  constructor
  · intro h; simpa using cong_of_mod h
  · intro h; exact mod_of_cong (lt_trans (by norm_num) hM) hM (by simpa using h)

theorem cong_neg_one_iff {M y : V} (hM : 0 < M) : (y + 1) % M = 0 ↔ Cong M y (-1) := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := cong_of_mod h
    exact ⟨u, by simp only [map_add, map_one, map_zero] at hu; linear_combination hu⟩
  · rintro ⟨u, hu⟩
    exact mod_of_cong hM hM ⟨u, by simp only [map_add, map_one, map_zero]; linear_combination hu⟩

/-- One step of the odd-index recurrence, as a congruence. -/
theorem step {M y1 y3 y5 : V} (c : DiffRing V) (hr : y5 + y1 + 2*y3 = M*y3)
    (h1 : Cong M y1 c) (h3 : Cong M y3 (-c)) : Cong M y5 c := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨w, hw⟩ := h3
  have e := congrArg (ι : V →+* DiffRing V) hr
  simp only [map_add, map_mul, map_ofNat] at e
  exact ⟨ι y3 - 2*w - u, by linear_combination e - hu - 2*hw⟩

/-- A nonnegative ring witness of `y ≡ c (mod M)` with `y - c ≥ 0` lies in the model. -/
theorem cong_witness {M y : V} {c : V} (hM : 0 < M) (h : Cong M y (ι c)) (hcy : c ≤ y) :
    ∃ u ≤ y, y = M*u + c := by
  obtain ⟨u, hu⟩ := h
  have hMpos : (0 : DiffRing V) < ι M := ι_pos hM
  have hu0 : 0 ≤ u := by
    by_contra hneg; push_neg at hneg
    have := mul_neg_of_pos_of_neg hMpos hneg
    have : ι c ≤ ι y := ι_le_ι.mpr hcy
    linarith
  obtain ⟨u', rfl⟩ := nonneg_iff.mp hu0
  have hv : y = M*u' + c := ι_injective (by simp only [map_add, map_mul]; linear_combination hu)
  refine ⟨u', ?_, hv⟩
  have h1 : (1 : V) ≤ M := pos_iff_one_le.mp hM
  calc u' = 1*u' := (one_mul u').symm
    _ ≤ M*u' := mul_le_mul_of_nonneg_right h1 _root_.zero_le
    _ ≤ M*u' + c := le_self_add
    _ = y := hv.symm

theorem cong_of_witness {M y c u : V} (h : y = M*u + c) : Cong M y (ι c) :=
  ⟨ι u, by rw [h]; simp only [map_add, map_mul]; ring⟩

/-- The pair induction, for a modulus variable `M = 4(b+2)²`. -/
theorem pairM (b M : V) (hMdef : M = 4*(b+2)*(b+2)) : ∀ h : V,
    (∃ u ≤ ycoord (2*(2*h)+1) b, ycoord (2*(2*h)+1) b = M*u + 1) ∧
      (∃ w ≤ ycoord (2*(2*h+1)+1) b + 1, ycoord (2*(2*h+1)+1) b + 1 = M*w + 0) := by
  intro h
  induction h using ISigma1.sigma1_succ_induction
  · clear hMdef; definability
  case zero =>
    have hy1 : ycoord 1 b = 1 := by simpa using y_succ (0:V) b
    have hy3 := ArithmeticPellHalfIndex.y_three b
    refine ⟨⟨0, by simp, by rw [show 2*(2*(0:V))+1 = 1 by simp, hy1]; simp⟩,
      ⟨1, ?_, ?_⟩⟩
    · rw [show 2*(2*(0:V)+1)+1 = 3 by norm_num]
      exact le_add_self
    · rw [show 2*(2*(0:V)+1)+1 = 3 by norm_num, hy3, ← hMdef]; simp
  case succ h ih =>
    have hM : 1 < M := hMdef ▸ one_lt_M b
    have hM0 : (0 : V) < M := lt_trans (by norm_num) hM
    obtain ⟨⟨u, _, hu⟩, ⟨w, _, hw⟩⟩ := ih
    have c1 : Cong M (ycoord (2*(2*h)+1) b) 1 := by simpa using cong_of_witness hu
    have c3 : Cong M (ycoord (2*(2*h+1)+1) b) (-1) := by
      obtain ⟨z, hz⟩ := cong_of_witness hw
      exact ⟨z, by simp only [map_add, map_one, map_zero] at hz; linear_combination hz⟩
    have r1 := ArithmeticPellHalfIndex.odd_y_rec (2*h) b
    have r2 := ArithmeticPellHalfIndex.odd_y_rec (2*h+1) b
    rw [← hMdef] at r1 r2
    rw [show 2*h+1+2 = 2*h+3 by ring, show 2*h+1+1 = 2*h+2 by ring] at r2
    have c5 : Cong M (ycoord (2*(2*h+2)+1) b) 1 := step 1 r1 c1 c3
    have c7 : Cong M (ycoord (2*(2*h+3)+1) b) (-1) :=
      step (-1) r2 c3 (by rw [neg_neg]; exact c5)
    rw [show 2*(h+1) = 2*h+2 by ring, show 2*h+2+1 = 2*h+3 by ring]
    have hy5 : 1 ≤ ycoord (2*(2*h+2)+1) b :=
      le_trans (by simp) (time_le_y (2*(2*h+2)+1) b)
    refine ⟨cong_witness hM0 (by simpa using c5) hy5, cong_witness hM0 ?_ _root_.zero_le⟩
    obtain ⟨z, hz⟩ := c7
    exact ⟨z, by simp only [map_add, map_one, map_zero]; linear_combination hz⟩

/-- Ordinates of index `4h+1` are `1` and of index `4h+3` are `-1` modulo `4(b+2)²`. -/
theorem pair (b h : V) :
    ycoord (2*(2*h)+1) b % (4*(b+2)*(b+2)) = 1 ∧
      (ycoord (2*(2*h+1)+1) b + 1) % (4*(b+2)*(b+2)) = 0 := by
  have hM := one_lt_M b
  have hM0 : (0 : V) < 4*(b+2)*(b+2) := lt_trans (by norm_num) hM
  obtain ⟨⟨u, _, hu⟩, ⟨w, _, hw⟩⟩ := pairM b _ rfl h
  refine ⟨mod_of_cong hM0 hM (by simpa using cong_of_witness hu), mod_of_cong hM0 hM0 ?_⟩
  simpa using cong_of_witness hw

/-- Every odd-index ordinate is `±1` modulo `4(b+2)²`. -/
theorem odd_ordinate_pm (b k : V) :
    Cong (4*(b+2)*(b+2)) (ycoord (2*k+1) b) 1 ∨
      Cong (4*(b+2)*(b+2)) (ycoord (2*k+1) b) (-1) := by
  have hM := one_lt_M b
  have hM0 : (0 : V) < 4*(b+2)*(b+2) := lt_trans (by norm_num) hM
  obtain ⟨m, hm, hkm⟩ := exists_nat_of_lt (k % 2) 2 (mod_lt k (by norm_num))
  have hk := div_add_mod k 2
  rw [hkm] at hk
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  · left
    have : k = 2*(k/2) := by simpa using hk.symm
    rw [this]; exact (cong_one_iff hM).mp (pair b (k/2)).1
  · right
    have : k = 2*(k/2)+1 := by simpa using hk.symm
    rw [this]; exact (cong_neg_one_iff hM0).mp (pair b (k/2)).2

/-- **The signed residue of the thirteen-coordinate auxiliary norm.** -/
theorem four_square_dvd_sub_one (S W y : DiffRing V) (hS : 2 ≤ S)
    (hnorm : S ^ 2 * W ^ 2 - (S ^ 2 - 1) * y ^ 2 = 1) (hy : ∃ k, y - 1 = 4 * k) :
    ∃ u, y - 1 = 4 * S ^ 2 * u := by
  obtain ⟨A, hA⟩ := nonneg_iff.mp (show (0 : DiffRing V) ≤ S by linarith)
  have hA2 : 2 ≤ A := two_le_of_ι (hA ▸ hS)
  obtain ⟨b, rfl⟩ : ∃ b, A = b + 2 := by
    obtain ⟨c, hc⟩ := exists_add_of_le hA2
    exact ⟨c, by rw [hc, add_comm]⟩
  obtain ⟨p, hp⟩ := nonneg_iff.mp (abs_nonneg W)
  obtain ⟨q, hq⟩ := nonneg_iff.mp (abs_nonneg y)
  have hn : ((b+2)*p)*((b+2)*p) = 1 + delta b * q * q := by
    have h' := hnorm
    rw [hA, ← sq_abs W, hp, ← sq_abs y, hq] at h'
    apply ι_injective
    simp only [map_mul, map_add, map_one, map_ofNat, delta] at h' ⊢
    linear_combination h'
  obtain ⟨n, _, hx, hyn⟩ := ArithmeticPellClassification.solution_index b _ _ hn
  obtain ⟨k, rfl⟩ := ArithmeticPellResidueClasses.odd_index_witness b n
    (by rw [hx]; exact dvd_mul_right _ _)
  have hM : ι (4*(b+2)*(b+2)) = 4 * S ^ 2 := by
    rw [hA]; simp only [map_mul, map_add, map_ofNat]; ring
  have hmod : Cong (4*(b+2)*(b+2)) q 1 ∨ Cong (4*(b+2)*(b+2)) q (-1) := by
    rw [← hyn]; exact odd_ordinate_pm b k
  obtain ⟨k4, hk4⟩ := hy
  rcases abs_choice y with hya | hya <;> rcases hmod with ⟨u, hu⟩ | ⟨u, hu⟩ <;>
    rw [hM, ← hq, hya] at hu
  · exact ⟨u, by linear_combination hu⟩
  · -- y ≡ -1 (mod 4S²) contradicts y ≡ 1 (mod 4)
    exfalso
    have h2 : (2 : DiffRing V) = 4 * (S ^ 2 * u - k4) := by linear_combination hu - hk4
    have := congrArg mod4 h2
    rw [map_ofNat, map_mul, map_ofNat, show (4 : ZMod 4) = 0 from rfl, zero_mul] at this
    exact absurd this (by decide)
  · exfalso
    have h2 : (2 : DiffRing V) = -4 * (S ^ 2 * u + k4) := by linear_combination -hu - hk4
    have := congrArg mod4 h2
    rw [map_ofNat, map_mul, map_neg, map_ofNat, show (4 : ZMod 4) = 0 from rfl, neg_zero,
      zero_mul] at this
    exact absurd this (by decide)
  · exact ⟨-u, by linear_combination -hu⟩

end DiophantineConsistency.ArithmeticOddOrdinateResidue
