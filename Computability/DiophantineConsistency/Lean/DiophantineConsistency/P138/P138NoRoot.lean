import DiophantineConsistency.P138.P138Bootstrap
import DiophantineConsistency.ZRows.CoprimeSquares

/-! # The quintic has no rational root; `s` and `r` vanish at no zero

`PROOF.md`, "Soundness": the polynomial `π(t) = (t² + 3)(t³ − 19)` has no rational root, and
`Ac = H⁵ π(T + K/H)`. Inside a model of `𝗜𝚺₁` this is stated without denominators:

* `no_cube_19`: `z³ ≠ 19 h³` in `DiffRing V` whenever `h ≠ 0` (divide `|z|, |h|` by their gcd
  certificate; the coprime cofactors give `h' ∣ 1`, then `z'³ = 19`, impossible as `8 < 19 < 27`);
* `Ac_ne`: `Ac = (zc² + 3H²)(zc³ − 19H³) ≠ 0`, since `H` is odd;
* `S_ne`, `s_r_ne`: at a zero of the output, `S = s r H ≠ 0`, because at `S = 0` the identity (4)
  reduces the output to `(Q − 1) Ac²`, and `Q − 1 ≠ 0` (`P138Bootstrap.nonzero`). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.P138NoRoot
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing ArithmeticGcdNormalization ModelBetaFunction ModelBoundedForallArith
open ZRowsCoprimeSquares P138Value P138Ports P138Bootstrap

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- No natural cube equals `19`. -/
theorem cube_ne_19 (a : DiffRing V) (ha : 0 ≤ a) : a ^ 3 ≠ 19 := by
  intro h
  rcases le_or_gt a 2 with h2 | h2
  · have : a ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ ha h2 3
    have e : (2:DiffRing V) ^ 3 = 8 := by norm_num
    linarith
  · have h3 : 3 ≤ a := by have := one_le_of_pos' (sub_pos.mpr h2); linarith
    have : 3 ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ (by norm_num) h3 3
    have e : (3:DiffRing V) ^ 3 = 27 := by norm_num
    linarith

/-- **`19` is not a rational cube**: `z³ ≠ 19 h³` for `h ≠ 0`. -/
theorem no_cube_19 {z h : DiffRing V} (hh : h ≠ 0) : z ^ 3 ≠ 19 * h ^ 3 := by
  intro he
  obtain ⟨a, ha⟩ := abs_eq_ι z
  obtain ⟨b, hb⟩ := abs_eq_ι h
  have hab : (ι a : DiffRing V) ^ 3 = 19 * ι b ^ 3 := by
    rw [← ha, ← hb, ← abs_pow, ← abs_pow, he, abs_mul, abs_of_pos (by norm_num : (0:DiffRing V) < 19)]
  have hb0 : (ι b : DiffRing V) ≠ 0 := by rw [← hb]; exact abs_ne_zero.mpr hh
  obtain ⟨g, ⟨a', rfl⟩, ⟨b', rfl⟩, hbez⟩ := gcd_certificate_exists a b
  have hgR : (ι g : DiffRing V) ≠ 0 := by
    intro h0; apply hb0; rw [map_mul, h0, zero_mul]
  have hcop : Bez a' b' 1 := by
    obtain ⟨u, v, w, z, he⟩ := hbez
    have he' := congrArg (ι (V := V)) he
    simp only [map_add, map_mul] at he'
    apply bez_one_iff_ring.mpr
    refine ⟨ι w - ι u, ι z - ι v, mul_left_cancel₀ hgR ?_⟩
    linear_combination (-1 : DiffRing V) * he'
  have hab' : (ι a' : DiffRing V) ^ 3 = 19 * ι b' ^ 3 := by
    rw [map_mul, map_mul] at hab
    have hg3 : (ι g : DiffRing V) ^ 3 ≠ 0 := pow_ne_zero 3 hgR
    apply mul_left_cancel₀ hg3
    linear_combination hab
  have hdiv : b' ∣ a' * a' * a' * 1 := by
    refine ⟨19 * b' * b', ι_injective ?_⟩
    simp only [map_mul, map_one, map_ofNat]
    linear_combination hab'
  have hc3 : Bez (a' * a' * a') b' 1 := bez_mul (bez_mul hcop hcop) hcop
  have hone : b' ∣ 1 := unit_certificate_cancel hc3 hdiv
  have hb1 : b' = 1 := Arithmetic.dvd_antisymm hone (one_dvd _)
  rw [hb1, map_one, one_pow, mul_one] at hab'
  exact cube_ne_19 _ (ι_nonneg a') hab'

section Regs
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V)
local notation "𝓡" => regs p x

/-- **`Ac ≠ 0`** (`H` is odd, hence nonzero). -/
theorem Ac_ne : (𝓡).Ac ≠ 0 := by
  rw [Ac_eq]
  have hH := H_ne p x
  refine mul_ne_zero ?_ (sub_ne_zero.mpr (no_cube_19 hH))
  have : 0 < 3 * (𝓡).H ^ 2 := by positivity
  have := sq_nonneg (𝓡).zc
  exact (show (0 : DiffRing V) < (𝓡).zc ^ 2 + 3 * (𝓡).H ^ 2 by linarith).ne'

/-- **At a zero, `S = s r H ≠ 0`.** -/
theorem S_ne (hp : PortFacts p) (hz : value p x = 0) : (𝓡).S ≠ 0 := by
  intro hS
  rw [value_eq_product, hS, Z_eq, hS] at hz
  have h : ((𝓡).Q - 1) * (𝓡).Ac ^ 2 = 0 := by linear_combination hz
  rcases mul_eq_zero.mp h with h | h
  · exact (nonzero p x hp).2.2.1 h
  · exact Ac_ne p x (pow_eq_zero_iff (by norm_num) |>.mp h)

/-- **At a zero, `s ≠ 0` and `r ≠ 0`.** -/
theorem s_r_ne (hp : PortFacts p) (hz : value p x = 0) : x 10 ≠ 0 ∧ x 4 ≠ 0 := by
  have h := S_ne p x hp hz
  rw [S_eq] at h
  exact ⟨fun h0 => h (by rw [h0]; ring), fun h0 => h (by rw [h0]; ring)⟩

end Regs

#print axioms cube_ne_19
#print axioms no_cube_19
#print axioms Ac_ne
#print axioms S_ne
#print axioms s_r_ne

end DiophantineConsistency.P138NoRoot
