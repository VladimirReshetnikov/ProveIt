import DiophantineConsistency.Z10.Z10Squares
import DiophantineConsistency.ArithmeticGcdNormalization

/-! # The quintic carrier of the ten-integer forms: `S ∣ T`

Package 106, integer lane (step S4 of the route). `𝓡 = Z10Regs.regs p x` at a signed assignment in
the ring of differences of a model of `𝗜𝚺₁`; no port fact is used.

At a zero of the polar value, `Sigma = xi S⁵` divides
`Theta = (rho³ − rho S² − S³)(rho² + 23 S²)` (`Z10Squares.Sigma_dvd_Theta`), where
`rho = T + S y`.

* `carrier_core`: `S⁵ ∣ (ρ³ − ρ S² − S³)(ρ² + 23 S²)` and `S ≠ 0` give `S ∣ ρ`. No valuations are
  used: with `g = gcd(|ρ|, |S|)`, `ρ = g ζ`, `S = g μ` and a Bezout identity `ζ α + μ β = 1`,
  cancelling `g⁵` leaves `μ ∣ ζ⁵` (the quintic is `ζ⁵` modulo `μ`), and the fifth power of the
  Bezout identity makes `μ` a unit (`unit_of_quintic`). This is `LCCarrier.carrier_core` with the
  certificate recomputed for the intersective quintic `(t³ − t − 1)(t² + 23)`.
* `S_dvd_rho`, `S_dvd_T`: hence `S ∣ rho` and `S = 2A − 5` divides
  `T = 3 W C − 2 (W² − 1)`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Z10Carrier
open Nine121 Nine121.N105Layout Z10Regs Z10Bootstrap Z10Squares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing
open ArithmeticGcdNormalization (gcd_certificate_exists)
open ZRowsCoprimeSquares (abs_eq_ι eq_or_eq_neg_abs)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The carrier core -/

/-- If `ζ α + μ β = 1` and `μ⁵ ∣ (ζ³ − ζ μ² − μ³)(ζ² + 23 μ²)`, then `μ` is a unit. -/
theorem unit_of_quintic {ζ μ α β d : DiffRing V} (hb : ζ * α + μ * β = 1)
    (hd : (ζ ^ 3 - ζ * μ ^ 2 - μ ^ 3) * (ζ ^ 2 + 23 * μ ^ 2) = μ ^ 5 * d) : μ ∣ 1 := by
  refine ⟨(μ ^ 4 * d - 22 * ζ ^ 3 * μ + ζ ^ 2 * μ ^ 2 + 23 * ζ * μ ^ 3 + 23 * μ ^ 4) * α ^ 5 +
    β * (5 * ζ ^ 4 * α ^ 4 + 10 * ζ ^ 3 * α ^ 3 * μ * β +
      10 * ζ ^ 2 * α ^ 2 * μ ^ 2 * β ^ 2 + 5 * ζ * α * μ ^ 3 * β ^ 3 + μ ^ 4 * β ^ 4), ?_⟩
  linear_combination (-(1 + (ζ * α + μ * β) + (ζ * α + μ * β) ^ 2 + (ζ * α + μ * β) ^ 3 +
    (ζ * α + μ * β) ^ 4)) * hb + α ^ 5 * hd

/-- **The carrier core.** `S⁵ ∣ (ρ³ − ρ S² − S³)(ρ² + 23 S²)` and `S ≠ 0` give `S ∣ ρ`. -/
theorem carrier_core {ρ S : DiffRing V} (hS : S ≠ 0)
    (h : S ^ 5 ∣ (ρ ^ 3 - ρ * S ^ 2 - S ^ 3) * (ρ ^ 2 + 23 * S ^ 2)) : S ∣ ρ := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨zn, hzn⟩ := abs_eq_ι ρ
  obtain ⟨mn, hmn⟩ := abs_eq_ι S
  obtain ⟨g, ⟨z', rfl⟩, ⟨m', rfl⟩, hbez⟩ := gcd_certificate_exists zn mn
  have hgR : (ι g : DiffRing V) ≠ 0 := by
    intro h0
    apply abs_ne_zero.mpr hS
    rw [hmn, map_mul, h0, zero_mul]
  obtain ⟨u, v, w, t, he⟩ := hbez
  have he' := congrArg (ι (V := V)) he
  simp only [map_add, map_mul] at he'
  have hcop : (ι z' : DiffRing V) * (ι w - ι u) + ι m' * (ι t - ι v) = 1 :=
    mul_left_cancel₀ hgR (by linear_combination (-1 : DiffRing V) * he')
  rw [map_mul] at hzn hmn
  obtain ⟨ζ, α, hζ, hα⟩ : ∃ ζ α : DiffRing V, ρ = ι g * ζ ∧ ζ * α = ι z' * (ι w - ι u) := by
    rcases eq_or_eq_neg_abs ρ with h1 | h1
    · exact ⟨ι z', ι w - ι u, by rw [h1, hzn], rfl⟩
    · exact ⟨-ι z', -(ι w - ι u), by rw [h1, hzn]; ring, by ring⟩
  obtain ⟨μ, β, hμ, hβ⟩ : ∃ μ β : DiffRing V, S = ι g * μ ∧ μ * β = ι m' * (ι t - ι v) := by
    rcases eq_or_eq_neg_abs S with h1 | h1
    · exact ⟨ι m', ι t - ι v, by rw [h1, hmn], rfl⟩
    · exact ⟨-ι m', -(ι t - ι v), by rw [h1, hmn]; ring, by ring⟩
  have hb : ζ * α + μ * β = 1 := by rw [hα, hβ]; exact hcop
  have hd' : (ζ ^ 3 - ζ * μ ^ 2 - μ ^ 3) * (ζ ^ 2 + 23 * μ ^ 2) = μ ^ 5 * d := by
    apply mul_left_cancel₀ (pow_ne_zero 5 hgR)
    rw [hζ, hμ] at hd
    linear_combination hd
  obtain ⟨W, hW⟩ := unit_of_quintic hb hd'
  exact ⟨ζ * W, by rw [hζ, hμ]; linear_combination (ι g * ζ) * hW⟩

/-! ## The carrier at a zero -/

section Regs
variable (p : Fin 4 → DiffRing V) (x : Fin 10 → DiffRing V)
local notation "𝓡" => regs p x

/-- **`S ∣ rho` at a zero.** -/
theorem S_dvd_rho (hz : value p x = 0) : (𝓡).S ∣ (𝓡).rho := by
  obtain ⟨c, hc⟩ := Sigma_dvd_Theta p x hz
  apply carrier_core (S_ne p x)
  have e := Theta_def (p := p) (x := x)
  refine ⟨(𝓡).xi * c, ?_⟩
  rw [← e, hc, Sigma_def]; ring

/-- **The carrier congruence**: `S = 2A − 5` divides `T = 3 W C − 2 (W² − 1)` at a zero. -/
theorem S_dvd_T (hz : value p x = 0) : (𝓡).S ∣ (𝓡).T := by
  have h := S_dvd_rho p x hz
  rw [rho_def] at h
  exact (dvd_add_left (dvd_mul_right _ _)).mp h

/-- The quotient form used by the intersective root: `T = S T'`, and then
`Theta = S⁵ · (t³ − t − 1)(t² + 23)` at `t = T' + y`. -/
theorem Theta_quotient {T' : DiffRing V} (hT : (𝓡).T = (𝓡).S * T') :
    (𝓡).Theta = (𝓡).S ^ 5 * (((T' + x 7) ^ 3 - (T' + x 7) - 1) * ((T' + x 7) ^ 2 + 23)) := by
  rw [Theta_def, rho_def, hT]; ring

end Regs

#print axioms carrier_core
#print axioms S_dvd_T
#print axioms Theta_quotient

end DiophantineConsistency.Z10Carrier
