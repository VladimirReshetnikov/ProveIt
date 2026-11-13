import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ModelArithmetic

/-! # Jones's Lemma 2.22(iii) at base two, in every model of `𝗜𝚺₁`

For the Pell sequence with `A = a + 2` and `J = 4A - 5 = 4a + 3`,

  `3 · 2ᵗ · ψ_A(t) ≡ 2 · ((2ᵗ)² - 1)  (mod J)`

(`Jones1982.Nine` uses it with `t = 2R + 1` in the ratio stage). It follows
from `ArithmeticPellPowerRecovery.projection_quotient`, `xₜ = 2ᵗ + a·yₜ + J·z`,
and the Pell norm: expanding the norm gives the explicit quotient below, so
the congruence holds as an exact divisibility in the model ring of
differences. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.ModelExponentialCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ModelDifferenceRing
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The base-two Pell congruence as an exact divisibility in `DiffRing V`. -/
theorem pow_congruence (a t : V) :
    (4 * ι a + 3 : DiffRing V) ∣
      3 * ι (Exp.exp t) * ι (ycoord t a) - 2 * (ι (Exp.exp t) ^ 2 - 1) := by
  obtain ⟨z, hz⟩ := ArithmeticPellPowerRecovery.projection_quotient a t
  have hn := norm t a
  unfold delta at hn
  have hx : ι (xcoord t a) = ι (Exp.exp t) + ι a * ι (ycoord t a) + (4 * ι a + 3) * ι z := by
    rw [hz]; simp only [map_add, map_mul, map_ofNat]
  have hnorm : ι (xcoord t a) * ι (xcoord t a) =
      1 + (ι a + 1) * (ι a + 3) * ι (ycoord t a) * ι (ycoord t a) := by
    have := congrArg ι hn
    simpa only [map_add, map_mul, map_one, map_ofNat] using this
  set X := ι (Exp.exp t)
  set y := ι (ycoord t a)
  set A := ι a
  set Z := ι z
  refine ⟨X * y + 2 * (2 * Z * (X + A * y) + (4 * A + 3) * Z ^ 2 - y ^ 2), ?_⟩
  rw [hx] at hnorm
  linear_combination (-2 : DiffRing V) * hnorm

end DiophantineConsistency.ModelExponentialCongruence
