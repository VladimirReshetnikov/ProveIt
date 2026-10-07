import OAI.Combinatorics.Progressions.Lattices.IntegerFiberCount
import OAI.Combinatorics.Progressions.Lattices.ShortIntegerDifference

namespace OAI

section

namespace Erdos3

theorem short_difference_card_of_density {H Q : ℕ} {ρ : ℝ}
    (hQ : 0 < Q) (hρQ : 4 ≤ ρ * Q) (hρH : 4 ≤ ρ * H)
    (D : Finset ℤ) (hsize : ρ * H ≤ (D.card : ℝ)) :
    2 * H / Q + 1 < D.card := by
  have hQ' : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hdiv : ((2 * H / Q : ℕ) : ℝ) ≤ (2 * H : ℝ) / Q := by
    apply (le_div_iff₀ hQ').mpr
    exact_mod_cast Nat.div_mul_le_self (2 * H) Q
  have hquot : (2 * H : ℝ) / Q ≤ ρ * H / 2 := by
    apply (div_le_iff₀ hQ').mpr
    have h := mul_le_mul_of_nonneg_right hρQ (Nat.cast_nonneg (α := ℝ) H)
    nlinarith only [h]
  have hreal : ((2 * H / Q + 1 : ℕ) : ℝ) < D.card := by
    push_cast
    linarith
  exact_mod_cast hreal

theorem many_multiples_rational_approximation (D : Finset ℤ) (n : ℤ → ℤ)
    {H Q : ℕ} {α ε ρ : ℝ} (hH : 0 < H) (hQ : 0 < Q)
    (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hρQ : 4 ≤ ρ * Q) (hρH : 4 ≤ ρ * H)
    (hsmall : 16 * ((Q : ℝ) * ε) ≤ ρ) (hcap : (Q : ℝ) * ε ≤ 1)
    (hsize : ρ * H ≤ (D.card : ℝ))
    (hD : ∀ h ∈ D, |h| ≤ (H : ℤ))
    (hclose : ∀ h ∈ D, |(h : ℝ) * α - n h| ≤ ε) :
    ∃ q : ℕ, 0 < q ∧ q ≤ Q ∧ ∃ p : ℤ,
      |(q : ℝ) * α - p| ≤ 24 * Q * ε / (ρ * H) := by
  obtain ⟨x, hx, y, hy, hxy, hdiff⟩ := exists_short_integer_difference D hQ hD
    (short_difference_card_of_density hQ hρQ hρH D hsize)
  let q := (y - x).toNat
  let p := n y - n x
  have hqcast : (q : ℤ) = y - x := Int.toNat_of_nonneg (by omega)
  have hq : 0 < q := by omega
  have hqQ : q ≤ Q := by omega
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqQ' : (q : ℝ) ≤ Q := Nat.cast_le.mpr hqQ
  have hqε : (q : ℝ) * ε ≤ Q * ε := mul_le_mul_of_nonneg_right hqQ' hε
  have hfirst : |(q : ℝ) * α - p| ≤ 2 * ε := by
    have hxc := abs_le.mp (hclose x hx)
    have hyc := abs_le.mp (hclose y hy)
    have hqr : (q : ℝ) = (y : ℝ) - x := by exact_mod_cast hqcast
    rw [hqr]
    simp only [p, Int.cast_sub]
    rw [abs_le]
    constructor <;> nlinarith only [hxc.1, hxc.2, hyc.1, hyc.2]
  let m : ℤ → ℤ := fun h => (q : ℤ) * n h - h * p
  have hphase : ∀ h ∈ D,
      |(h : ℝ) * ((q : ℝ) * α - p) - m h| ≤ (q : ℝ) * ε := by
    intro h hh
    have hid : (h : ℝ) * ((q : ℝ) * α - p) - m h =
        (q : ℝ) * ((h : ℝ) * α - n h) := by
      simp only [m, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
      ring
    rw [hid, abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
    exact mul_le_mul_of_nonneg_left (hclose h hh) (Nat.cast_nonneg q)
  have happrox := small_linear_phase_of_many_near_integers D m
    (Nat.cast_pos.mpr hH) hρ (mul_nonneg (Nat.cast_nonneg q) hε)
    (hqε.trans hcap) (by nlinarith only [hsmall, hqε])
    (hfirst.trans (by nlinarith only [mul_le_mul_of_nonneg_right hq' hε]))
    hsize (fun h hh => by exact_mod_cast hD h hh) hphase
  refine ⟨q, hq, hqQ, p, happrox.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (mul_nonneg hρ.le (Nat.cast_nonneg H))
  nlinarith only [hqε]

end Erdos3

end

section

namespace Erdos3

theorem exists_common_denominator_subset (D : Finset ℤ) (q : ℤ → ℕ) {K : ℕ}
    (hK : 0 < K) (hq : ∀ h ∈ D, 0 < q h ∧ q h ≤ K)
    {μ : ℝ} (hsize : (K : ℝ) * μ ≤ D.card) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ q₀ ≤ K ∧ ∃ E : Finset ℤ,
      E ⊆ D ∧ μ ≤ E.card ∧ ∀ h ∈ E, q h = q₀ := by
  have hmap : ∀ h ∈ D, q h ∈ Finset.Icc 1 K := by
    intro h hh
    exact Finset.mem_Icc.mpr ⟨(hq h hh).1, (hq h hh).2⟩
  have hnonempty : (Finset.Icc 1 K).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hK⟩⟩
  have hcard : (Finset.Icc 1 K).card = K := by simp
  obtain ⟨q₀, hq₀, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    hmap hnonempty (by simpa only [hcard, nsmul_eq_mul] using hsize)
  refine ⟨q₀, (Finset.mem_Icc.mp hq₀).1, (Finset.mem_Icc.mp hq₀).2,
    D.filter (fun h => q h = q₀), Finset.filter_subset _ _, hlarge, ?_⟩
  intro h hh
  exact (Finset.mem_filter.mp hh).2

theorem varying_denominator_multiples_approximation (D : Finset ℤ)
    (q : ℤ → ℕ) (p : ℤ → ℤ) {H K Q : ℕ} {α ε ρ : ℝ}
    (hH : 0 < H) (hK : 0 < K) (hQ : 0 < Q) (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (hρQ : 4 ≤ ρ * Q) (hρH : 4 ≤ ρ * H)
    (hsmall : 16 * ((Q : ℝ) * ε) ≤ ρ) (hcap : (Q : ℝ) * ε ≤ 1)
    (hsize : (K : ℝ) * (ρ * H) ≤ D.card)
    (hD : ∀ h ∈ D, |h| ≤ (H : ℤ))
    (hq : ∀ h ∈ D, 0 < q h ∧ q h ≤ K)
    (hclose : ∀ h ∈ D, |(q h : ℝ) * ((h : ℝ) * α) - p h| ≤ ε) :
    ∃ r : ℕ, 0 < r ∧ r ≤ Q * K ∧ ∃ m : ℤ,
      |(r : ℝ) * α - m| ≤ 24 * Q * ε / (ρ * H) := by
  obtain ⟨q₀, hq₀, hq₀K, E, hED, hE, hconstant⟩ :=
    exists_common_denominator_subset D q hK hq hsize
  have hclose' : ∀ h ∈ E, |(h : ℝ) * ((q₀ : ℝ) * α) - p h| ≤ ε := by
    intro h hh
    have he := hclose h (hED hh)
    rw [hconstant h hh] at he
    rw [mul_left_comm]
    exact he
  obtain ⟨r, hr, hrQ, m, hm⟩ := many_multiples_rational_approximation E p
    hH hQ hρ hε hρQ hρH hsmall hcap hE (fun h hh => hD h (hED hh)) hclose'
  refine ⟨r * q₀, Nat.mul_pos hr hq₀, Nat.mul_le_mul hrQ hq₀K, m, ?_⟩
  simpa only [Nat.cast_mul, mul_assoc] using hm

end Erdos3

end

end OAI
