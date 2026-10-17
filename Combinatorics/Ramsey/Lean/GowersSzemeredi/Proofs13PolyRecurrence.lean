import GowersSzemeredi.Proofs13LargeScaleRecurrence
import GowersSzemeredi.Proofs13SingletonRecurrence

/-! Lemma 13.5 with a polynomial exponent (Notes L.7c, P1).

Lemma 13.5 needs a sub-progression `Q` of the Stage 13.4 progression `P` on
which the `q` phases `(a_i h + b_i)·step` are simultaneously small. The
corpus proof (`lemma_13_5_with_scale`) partitions `P` with Section 5's
simultaneous polynomial partition. That partition costs `2^(11q)` in the
exponent, so `|Q| ≥ |P|^(1/2^(12q))`, exponentially small in `q`. This
exponential is what blocks Theorem 18.1 (Notes L.7c).

A Schmidt-type partition is polynomial in `q`. Here it enters as the
hypothesis `ProgressionPhasePartition K p`: cells of length at least `H` with
phases at most `(4/H)·N`, once `K(q+1) ≤ H` and `H^(p(q+1)^8) ≤ |P|`. The
bridge derives it from `CommonDiffPartitionBoundAt 1 K p`.

`IsStage135At S D E eL eP` is the catalogue's `IsStage135Data` with the two
printed exponents `1/2^(12q)` (length) and `1/2^(11q)` (precision) left
free; `isStage135Data_iff_at` records the specialization. The main result,
`lemma_13_5_poly`, gives both exponents equal to
`e_q = (2p(q+1)^8)^(−2)` (`stage135PolyExponent`), which is polynomial in `q`.
There are three cases:
* an empty `P`;
* `|P|^(e_q) ≤ 2`, where one critical height with a Bohr step suffices;
* otherwise, a cell of the phase partition at `H = ⌊|P|^(1/(p(q+1)^8))⌋`
  carrying the average good-height weight. The partition already controls
  the phases on every point of the cell, so no endpoint deletion is needed. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- **A polynomial phase partition of progressions** (a `ModAP` form of
`CommonDiffPartitionBoundAt 1 K p`). -/
def ProgressionPhasePartition (K : Real) (p : Nat) : Prop :=
  ∀ (N : Nat) [NeZero N] (q : Nat) (P : ModAP N), P.IsProper →
    ∀ (a b : Fin q → ZMod N) (H : Nat), 0 < H → K * ((q : Real) + 1) ≤ H →
      (H : Real) ^ (p * (q + 1) ^ 8) ≤ P.length →
      ∃ M : Nat, ∃ Q : Fin M → ModAP N,
        IsPartition (fun j => (Q j).carrier) P.carrier ∧ (∀ j, (Q j).IsProper) ∧
        (∀ j, H ≤ (Q j).length) ∧
        ∀ i j h, h ∈ (Q j).carrier →
          (centeredAbs ((a i * h + b i) * (Q j).step) : Real) ≤ (4 / H) * N

/-- A phase partition persists for every larger exponent constant. -/
theorem ProgressionPhasePartition.mono {K : Real} {p p' : Nat}
    (h : ProgressionPhasePartition K p) (hpp' : p ≤ p') : ProgressionPhasePartition K p' := by
  intro N _ q P hP a b H hH hKH hsize
  refine h N q P hP a b H hH hKH (le_trans ?_ hsize)
  have hH1 : (1 : Real) ≤ H := by exact_mod_cast hH
  exact pow_le_pow_right₀ hH1 (Nat.mul_le_mul_right _ hpp')

/-- The polynomial Stage 13.5 exponent `(2p(q+1)^8)^(−2)`. -/
def stage135PolyExponent (p q : Nat) : Real :=
  (((2 * p * (q + 1) ^ 8 : Nat) : Real) ^ 2)⁻¹

theorem stage135PolyExponent_pos {p q : Nat} (hp : 0 < p) : 0 < stage135PolyExponent p q := by
  unfold stage135PolyExponent
  have : (0 : Nat) < 2 * p * (q + 1) ^ 8 := by positivity
  positivity

theorem two_mul_stage135PolyExponent_le {p q : Nat} (hp : 0 < p) :
    2 * (q : Real) * stage135PolyExponent p q ≤ 1 := by
  have h1 : 2 * q ≤ 2 * p * (q + 1) ^ 8 := by
    have ha : q + 1 ≤ (q + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
    have hb : (q + 1) ^ 8 ≤ p * (q + 1) ^ 8 := Nat.le_mul_of_pos_left _ hp
    calc 2 * q ≤ 2 * (p * (q + 1) ^ 8) := by omega
      _ = 2 * p * (q + 1) ^ 8 := by ring
  have h2 : 2 * p * (q + 1) ^ 8 ≤ (2 * p * (q + 1) ^ 8) ^ 2 := Nat.le_self_pow (by norm_num) _
  unfold stage135PolyExponent
  rw [mul_inv_le_iff₀ (by positivity), one_mul]
  exact_mod_cast h1.trans h2

/-- A proper progression of length at least two has a nonzero step. -/
theorem ModAP.step_ne_zero_of_proper {N : Nat} (P : ModAP N) (hP : P.IsProper)
    (h2 : 2 ≤ P.length) : P.step != 0 := by
  refine bne_iff_ne.mpr fun hs => ?_
  have hsub : P.carrier ⊆ {P.start} := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simp [hs]
  have := Finset.card_le_card hsub
  rw [hP, Finset.card_singleton] at this
  omega

/-- An empty Stage 13.4 progression is its own Stage 13.5 progression. -/
theorem stage135_empty_at {N : Nat} [NeZero N] (S : Section13Context N)
    (D : Stage134Data N) (theta : Real) (h134 : IsStage134Data S theta D)
    (hL : D.P.length = 0) {eL eP : Real} (heL : 0 < eL) :
    ∃ E : Stage135Data N, IsStage135At S D E eL eP := by
  have hempty : D.P.carrier = ∅ := Finset.card_eq_zero.mp (h134.2.2.1.trans hL)
  refine ⟨⟨D.P⟩, h134.2.1, h134.2.2.1, subset_rfl, ?_, ?_, ?_⟩
  · change (D.P.length : Real) ^ eL / 2 ≤ (D.P.length : Real)
    rw [hL, Nat.cast_zero, Real.zero_rpow heL.ne']
    norm_num
  · intro i h hh
    change h ∈ D.P.carrier at hh
    rw [hempty] at hh
    exact absurd hh (Finset.notMem_empty h)
  · change S.alpha ^ 32 * (D.P.length : Real) / 20 ≤ _
    rw [hL, Nat.cast_zero, mul_zero, zero_div]
    exact Nat.cast_nonneg _

/-- The arithmetic of the large case: `2^p·(q+1) + 1 ≤ 2^(4p(q+1)^8)`. -/
theorem stage135_poly_threshold_nat (p q : Nat) (hp : 0 < p) :
    2 ^ p * (q + 1) + 1 ≤ 2 ^ (4 * (p * (q + 1) ^ 8)) := by
  have hq2 : q + 2 ≤ 2 ^ (q + 1) := Nat.lt_two_pow_self
  have hp1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  have hlin : p + q + 1 ≤ 4 * (p * (q + 1) ^ 8) := by
    have ha : q + 1 ≤ (q + 1) ^ 8 := Nat.le_self_pow (by norm_num) _
    have hb : p * (q + 1) ≤ p * (q + 1) ^ 8 := Nat.mul_le_mul_left p ha
    have hc : q ≤ p * q := Nat.le_mul_of_pos_left q hp
    have hd : p * (q + 1) = p * q + p := by ring
    omega
  calc 2 ^ p * (q + 1) + 1 ≤ 2 ^ p * (q + 2) := by nlinarith only [hp1]
    _ ≤ 2 ^ p * 2 ^ (q + 1) := Nat.mul_le_mul_left _ hq2
    _ = 2 ^ (p + q + 1) := by rw [← pow_add]; ring_nf
    _ ≤ 2 ^ (4 * (p * (q + 1) ^ 8)) := Nat.pow_le_pow_right (by norm_num) hlin

/-- **The large case.** When `|P|^(e_q) > 2`, a cell of the phase partition at
`H = ⌊|P|^(1/(p(q+1)^8))⌋` with the average good-height weight is a Stage 13.5
progression at exponent `e_q` for both length and precision. -/
theorem stage135_phase_partition_at {N : Nat} [NeZero N] {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D)
    (hscale : 2 < (D.P.length : Real) ^ stage135PolyExponent p D.q) :
    ∃ E : Stage135Data N, IsStage135At S D E
      (stage135PolyExponent p D.q) (stage135PolyExponent p D.q) := by
  have hP : D.P.IsProper := h134.2.2.1
  obtain ⟨m, hm⟩ : ∃ m : Nat, m = p * (D.q + 1) ^ 8 := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have hmR : (m : Real) ≠ 0 := by exact_mod_cast hm0.ne'
  have he' : stage135PolyExponent p D.q = (((4 * m ^ 2 : Nat) : Real))⁻¹ := by
    unfold stage135PolyExponent
    rw [hm]
    push_cast
    ring
  have hepos : 0 < stage135PolyExponent p D.q := stage135PolyExponent_pos hp
  have hPpos : 0 < D.P.length := by
    by_contra hz
    have hzero : D.P.length = 0 := by omega
    rw [hzero, Nat.cast_zero, Real.zero_rpow hepos.ne'] at hscale
    norm_num at hscale
  have hP0 : (0 : Real) ≤ D.P.length := Nat.cast_nonneg _
  set y := (D.P.length : Real) ^ stage135PolyExponent p D.q with hy_def
  have hypos : 0 < y := by linarith only [hscale]
  have hX : (D.P.length : Real) ^ ((m : Real)⁻¹) = y ^ (4 * m) := by
    rw [hy_def, ← Real.rpow_natCast, ← Real.rpow_mul hP0, he']
    congr 1
    push_cast
    field_simp
  obtain ⟨H, hH⟩ : ∃ H : Nat, H = Nat.floor ((D.P.length : Real) ^ ((m : Real)⁻¹)) := ⟨_, rfl⟩
  have hHle : (H : Real) ≤ (D.P.length : Real) ^ ((m : Real)⁻¹) := by
    rw [hH]
    exact Nat.floor_le (by positivity)
  have hHgt : (D.P.length : Real) ^ ((m : Real)⁻¹) < H + 1 := by
    rw [hH]
    exact Nat.lt_floor_add_one _
  rw [hX] at hHgt
  have hy4 : y ^ 4 ≤ y ^ (4 * m) := pow_le_pow_right₀ (by linarith only [hscale]) (by omega)
  have hy3 : (2 : Real) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hscale.le 3
  have hcube : 8 * y ≤ y ^ 4 := by nlinarith only [hy3, hypos]
  have hH4 : 4 * y ≤ H := by nlinarith only [hy4, hcube, hHgt, hscale]
  have hHposR : (0 : Real) < H := by linarith only [hH4, hypos]
  have hHpos : 0 < H := by exact_mod_cast hHposR
  have hH2 : 2 ≤ H := by
    have : (2 : Real) ≤ H := by linarith only [hH4, hscale]
    exact_mod_cast this
  have hKH : K * ((D.q : Real) + 1) ≤ H := by
    have hnat := stage135_poly_threshold_nat p D.q hp
    rw [← hm] at hnat
    have hreal : (2 : Real) ^ p * ((D.q : Real) + 1) + 1 ≤ (2 : Real) ^ (4 * m) := by
      exact_mod_cast hnat
    have h2y : (2 : Real) ^ (4 * m) ≤ y ^ (4 * m) := pow_le_pow_left₀ (by norm_num) hscale.le _
    have hKq : K * ((D.q : Real) + 1) ≤ (2 : Real) ^ p * ((D.q : Real) + 1) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    linarith only [hreal, h2y, hKq, hHgt]
  have hHP : (H : Real) ^ (p * (D.q + 1) ^ 8) ≤ D.P.length := by
    rw [← hm]
    calc (H : Real) ^ m ≤ ((D.P.length : Real) ^ ((m : Real)⁻¹)) ^ m :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hHle m
      _ = D.P.length := Real.rpow_inv_natCast_pow hP0 hm0.ne'
  obtain ⟨M, Q, hpart, hproper, hlen, hsmall⟩ :=
    hpp N D.q D.P hP D.a D.b H hHpos hKH hHP
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with hM0 | hM
    · subst hM0
      have hsum := hpart.sum_card
      rw [hP] at hsum
      simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsum
      omega
    · exact hM
  obtain ⟨j, hj⟩ := stage135_select_weighted_cell S D Q hM hP h134.2.2.2.1 hpart hproper
    h134.2.2.2.2.2.2.2.1
  have hcount := stage135_critical_count_of_weight S D (Q j) (hproper j) hj
  have hQH : (H : Real) ≤ (Q j).length := by exact_mod_cast hlen j
  refine ⟨⟨Q j⟩, (Q j).step_ne_zero_of_proper (hproper j) (hH2.trans (hlen j)), hproper j,
    hpart.cell_subset j, ?_, ?_, ?_⟩
  · change y / 2 ≤ ((Q j).length : Real)
    linarith only [hH4, hQH, hypos]
  · intro i h hh
    have hneg : (D.P.length : Real) ^ (-stage135PolyExponent p D.q) = y⁻¹ :=
      Real.rpow_neg hP0 _
    rw [hneg]
    refine (hsmall i j h hh).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg N))
    rw [div_le_iff₀ hHposR, inv_mul_eq_div, le_div_iff₀ hypos]
    exact hH4
  · change S.alpha ^ 32 * ((Q j).length : Real) / 20 ≤ _
    have hl0 : 0 ≤ S.alpha ^ 32 * ((Q j).length : Real) :=
      mul_nonneg (pow_nonneg S.alpha_pos.le 32) (Nat.cast_nonneg _)
    linarith only [hcount, hl0]

/-- **Lemma 13.5 with a polynomial exponent.** From a polynomial phase
partition with `K ≤ 2^p`, every Stage 13.4 datum has a Stage 13.5 progression
of length at least `|P|^(e_q)/2` with phases at most `|P|^(−e_q)·N`, where
`e_q = (2p(q+1)^8)^(−2)`. -/
theorem lemma_13_5_poly {N : Nat} [NeZero N] {K : Real} {p : Nat}
    (hpp : ProgressionPhasePartition K p) (hp : 0 < p) (hK : K ≤ 2 ^ p)
    (S : Section13Context N) (D : Stage134Data N) (theta : Real)
    (h134 : IsStage134Data S theta D) :
    ∃ E : Stage135Data N, IsStage135At S D E
      (stage135PolyExponent p D.q) (stage135PolyExponent p D.q) := by
  have hepos := stage135PolyExponent_pos (q := D.q) hp
  by_cases hL : D.P.length = 0
  · exact stage135_empty_at S D theta h134 hL hepos
  by_cases hs : (D.P.length : Real) ^ stage135PolyExponent p D.q ≤ 2
  · exact stage135_singleton_at S D theta h134 (by omega) hepos
      (two_mul_stage135PolyExponent_le hp) hs
  · exact stage135_phase_partition_at hpp hp hK S D theta h134 (lt_of_not_ge hs)

end LeanProofs.GowersSzemeredi
