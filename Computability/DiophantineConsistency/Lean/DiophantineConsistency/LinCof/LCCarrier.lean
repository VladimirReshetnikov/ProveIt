import DiophantineConsistency.LinCof.LCAdjacent
import DiophantineConsistency.P138.P138EarlyFold
import DiophantineConsistency.ArithmeticGcdNormalization

/-! # The carrier: `S ∣ Ac`, the scale valuation `M ∣ zc`, and `H ∣ q¹⁵ Kq⁵`

At a zero of the linear-cofactor output `LCValue.valueK p x κ ω Λ ψ wt` with a square even
weight (`LCNorm.Weight wt`, `wt = l²`):

* `Z_eq_S`: the norm relation `delta (Z − S g) = l S w` with `w² = B · Df · Da`
  (`LCNorm.norm`), the roots `B = u²`, `Df = f²`, `Da = e²` (`LCSquares.roots`) and the integral
  auxiliary ordinate `e = delta · y` (`LCAdjacent.aux_integral`) give `w = ±delta · u f y`, so
  `Z = S (g ± l u f y)` after cancelling `delta`;
* `S_dvd_Ac`: hence `S ∣ Ac = S (n + Ψ) − Z`;
* `carrier_core`: in the ring of differences, `M⁵ ∣ (z² + 3(HM)²)(z³ − 19(HM)³)` with `M ≠ 0`
  gives `M ∣ z`. No valuations are used: with `g = gcd(|z|, |M|)`, `z = g ζ`, `M = g μ` and a
  Bezout identity `ζ α + μ β = 1`, cancelling `g⁵` leaves `μ ∣ ζ⁵`, and the fifth power of the
  Bezout identity makes `μ` a unit (`unit_of_quintic`);
* `M_dvd_zc`: `M⁵ ∣ S ∣ Ac` and `Dc = H M` give `M ∣ zc`; since
  `zc = Dc T + M K + H (Y − q³)`, `M ∣ H (Y − q³)` (`M_dvd_H_mul`), and as `M = 2q³` with `q`
  even and `H` odd, `Y` is even (`Y_even`), hence so are `a` and `A`;
* `H_dvd_q15_Kq5`: `H ∣ S ∣ Ac`, `Ac ≡ zc⁵`, `zc ≡ M K` and `K ≡ −2 Kq (mod H)` with
  `Kq = X (X + 2 a c) − 1` give `H ∣ 2¹⁰ q¹⁵ Kq⁵`, and `H` is odd.

Compared with `P138EarlyFold.{Z_eq_S, S_dvd_Ac, H_dvd_Kq5}` the carrier is `Dc = H M` instead of
`H`, so the divisibility by `H` acquires the factor `q¹⁵`; none of this needs the early fold. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCCarrier
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCSquares LCBudget LCAdjacent
open ArithmeticGcdNormalization (gcd_certificate_exists)
open ZRowsCoprimeSquares (abs_eq_ι eq_or_eq_neg_abs)
open P138EarlyFold (odd_dvd_of_dvd_two_mul)
open LCNorm (Weight)

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The carrier core -/

/-- If `ζ α + μ β = 1` and `μ⁵ ∣ (ζ² + 3(Hμ)²)(ζ³ − 19(Hμ)³)`, then `μ` is a unit. -/
theorem unit_of_quintic {ζ μ α β H d : DiffRing V} (hb : ζ * α + μ * β = 1)
    (hd : (ζ ^ 2 + 3 * (H * μ) ^ 2) * (ζ ^ 3 - 19 * (H * μ) ^ 3) = μ ^ 5 * d) : μ ∣ 1 := by
  refine ⟨(μ ^ 4 * d + 19 * H ^ 3 * μ ^ 2 * ζ ^ 2 - 3 * H ^ 2 * μ * ζ ^ 3 + 57 * H ^ 5 * μ ^ 4) *
    α ^ 5 + β * (5 * ζ ^ 4 * α ^ 4 + 10 * ζ ^ 3 * α ^ 3 * μ * β +
      10 * ζ ^ 2 * α ^ 2 * μ ^ 2 * β ^ 2 + 5 * ζ * α * μ ^ 3 * β ^ 3 + μ ^ 4 * β ^ 4), ?_⟩
  linear_combination (-(1 + (ζ * α + μ * β) + (ζ * α + μ * β) ^ 2 + (ζ * α + μ * β) ^ 3 +
    (ζ * α + μ * β) ^ 4)) * hb + α ^ 5 * hd

/-- **The carrier core.** `M⁵ ∣ (z² + 3(HM)²)(z³ − 19(HM)³)` and `M ≠ 0` give `M ∣ z`. -/
theorem carrier_core {z M H : DiffRing V} (hM : M ≠ 0)
    (h : M ^ 5 ∣ (z ^ 2 + 3 * (H * M) ^ 2) * (z ^ 3 - 19 * (H * M) ^ 3)) : M ∣ z := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨zn, hzn⟩ := abs_eq_ι z
  obtain ⟨mn, hmn⟩ := abs_eq_ι M
  obtain ⟨g, ⟨z', rfl⟩, ⟨m', rfl⟩, hbez⟩ := gcd_certificate_exists zn mn
  have hgR : (ι g : DiffRing V) ≠ 0 := by
    intro h0
    apply abs_ne_zero.mpr hM
    rw [hmn, map_mul, h0, zero_mul]
  obtain ⟨u, v, w, t, he⟩ := hbez
  have he' := congrArg (ι (V := V)) he
  simp only [map_add, map_mul] at he'
  have hcop : (ι z' : DiffRing V) * (ι w - ι u) + ι m' * (ι t - ι v) = 1 :=
    mul_left_cancel₀ hgR (by linear_combination (-1 : DiffRing V) * he')
  rw [map_mul] at hzn hmn
  obtain ⟨ζ, α, hζ, hα⟩ : ∃ ζ α : DiffRing V, z = ι g * ζ ∧ ζ * α = ι z' * (ι w - ι u) := by
    rcases eq_or_eq_neg_abs z with h1 | h1
    · exact ⟨ι z', ι w - ι u, by rw [h1, hzn], rfl⟩
    · exact ⟨-ι z', -(ι w - ι u), by rw [h1, hzn]; ring, by ring⟩
  obtain ⟨μ, β, hμ, hβ⟩ : ∃ μ β : DiffRing V, M = ι g * μ ∧ μ * β = ι m' * (ι t - ι v) := by
    rcases eq_or_eq_neg_abs M with h1 | h1
    · exact ⟨ι m', ι t - ι v, by rw [h1, hmn], rfl⟩
    · exact ⟨-ι m', -(ι t - ι v), by rw [h1, hmn]; ring, by ring⟩
  have hb : ζ * α + μ * β = 1 := by rw [hα, hβ]; exact hcop
  have hd' : (ζ ^ 2 + 3 * (H * μ) ^ 2) * (ζ ^ 3 - 19 * (H * μ) ^ 3) = μ ^ 5 * d := by
    apply mul_left_cancel₀ (pow_ne_zero 5 hgR)
    rw [hζ, hμ] at hd
    linear_combination hd
  obtain ⟨W, hW⟩ := unit_of_quintic hb hd'
  exact ⟨ζ * W, by rw [hζ, hμ]; linear_combination (ι g * ζ) * hW⟩

/-! ## The carrier at a zero -/

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- **`Z = S (g ± l u f y)`** with `P = g²`, `wt = l²`. -/
theorem Z_eq_S (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    ∃ (g l : DiffRing V) (u f y : V), (𝓡).P = g * g ∧ wt = l * l ∧
      ((𝓡).Z = (𝓡).S * (g + l * (ι u * ι f * ι y)) ∨
        (𝓡).Z = (𝓡).S * (g - l * (ι u * ι f * ι y))) := by
  obtain ⟨g, l, w, hP, hl, hX, hw⟩ := LCNorm.norm ψ wt hp h hwt hz
  obtain ⟨u, f, e', _, _, he0, hB, hDf, hDa⟩ := roots ψ wt hp h hwt hz
  obtain ⟨y, _, hey, _⟩ := aux_integral ψ wt hp h hwt hz hDa he0
  have hδ : (𝓡).delta ≠ 0 := (nonzero p x κ ω Λ ψ wt).2.1
  have hDa' : (𝓡).delta * (𝓡).Cy = ι e' * ι e' := hDa
  have hey' : (ι e' : DiffRing V) = (𝓡).delta * ι y := by
    rw [hey, delta_eq p x κ ω Λ ψ wt]
  have hsq : w * w = ((𝓡).delta * (ι u * ι f * ι y)) * ((𝓡).delta * (ι u * ι f * ι y)) := by
    rw [hw, hB, hDf, hDa', hey']; ring
  refine ⟨g, l, u, f, y, hP, hl, ?_⟩
  rcases mul_self_eq_mul_self_iff.mp hsq with h1 | h1
  · left
    apply mul_left_cancel₀ hδ
    rw [h1] at hX
    linear_combination hX
  · right
    apply mul_left_cancel₀ hδ
    rw [h1] at hX
    linear_combination hX

/-- **`S ∣ Ac`.** -/
theorem S_dvd_Ac (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) : (𝓡).S ∣ (𝓡).Ac := by
  obtain ⟨g, l, u, f, y, _, _, hZ⟩ := Z_eq_S ψ wt hp h hwt hz
  rcases hZ with hZ | hZ
  · exact ⟨x 9 + (𝓡).Psi - (g + l * (ι u * ι f * ι y)), by
      linear_combination Z_eq p x κ ω Λ ψ wt - hZ⟩
  · exact ⟨x 9 + (𝓡).Psi - (g - l * (ι u * ι f * ι y)), by
      linear_combination Z_eq p x κ ω Λ ψ wt - hZ⟩

/-- **The scale valuation: `M ∣ zc`.** -/
theorem M_dvd_zc (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) : (𝓡).M ∣ (𝓡).zc := by
  have hS : (𝓡).M ^ 5 ∣ (𝓡).S := ⟨x 10 * x 4 * (𝓡).H, by rw [S_eq]; ring⟩
  have hAc := dvd_trans hS (S_dvd_Ac ψ wt hp h hwt hz)
  rw [Ac_eq p x κ ω Λ ψ wt, Dc_eq p x κ ω Λ ψ wt] at hAc
  exact carrier_core (M_ne p x κ ω Λ ψ wt hp) hAc

/-- **`M ∣ H (Y − q³)`.** -/
theorem M_dvd_H_mul (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    (𝓡).M ∣ (𝓡).H * ((𝓡).Y - (𝓡).q ^ 3) := by
  obtain ⟨t, ht⟩ := M_dvd_zc ψ wt hp h hwt hz
  exact ⟨t - (𝓡).H * x 7 - (𝓡).K, by
    linear_combination ht - zc_eq p x κ ω Λ ψ wt - x 7 * Dc_eq p x κ ω Λ ψ wt⟩

/-- **`Y` is even** at a zero. -/
theorem Y_even (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) : ∃ m : DiffRing V, (𝓡).Y = 2 * m := by
  obtain ⟨t, ht⟩ := M_dvd_H_mul ψ wt hp h hwt hz
  obtain ⟨s, hs⟩ := q_even p x κ ω Λ ψ wt hp
  obtain ⟨m, hm⟩ := H_odd p x κ ω Λ ψ wt
  have hM := M_eq p x κ ω Λ ψ wt
  refine ⟨(𝓡).q ^ 3 * t - m * ((𝓡).Y - (𝓡).q ^ 3) + 4 * s ^ 3, ?_⟩
  linear_combination ht - ((𝓡).Y - (𝓡).q ^ 3) * hm + t * hM +
    ((𝓡).q ^ 2 + 2 * (𝓡).q * s + 4 * s ^ 2) * hs

/-- `a` is even at a zero. -/
theorem a_even (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) : ∃ m : DiffRing V, (𝓡).a = 2 * m := by
  obtain ⟨m, hm⟩ := Y_even ψ wt hp h hwt hz
  exact ⟨m * ((𝓡).X + 1), by rw [a_fac, hm]; ring⟩

/-- `A` is even at a zero. -/
theorem A_even (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) : ∃ m : DiffRing V, (𝓡).A = 2 * m := by
  obtain ⟨m, hm⟩ := a_even ψ wt hp h hwt hz
  exact ⟨m + 1, by rw [A_eq, hm]; ring⟩

end Regs

section Projector
variable (p : Fin 6 → DiffRing V) (x : Fin 11 → DiffRing V) (κ ω Λ ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- The projector register `Kq = X (X + 2 a c) − 1`. -/
def Kq : DiffRing V := (𝓡).X * ((𝓡).X + 2 * (𝓡).a * x 8) - 1

theorem K_Kq : (𝓡).K = (𝓡).H * (𝓡).X * x 8 - 2 * Kq p x κ ω Λ ψ wt := by
  unfold Kq; rw [K_eq, H_def]; ring

end Projector

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt

/-- **`H ∣ q¹⁵ Kq⁵`.** -/
theorem H_dvd_q15_Kq5 (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hwt : Weight wt) (hz : valueK p x κ ω Λ ψ wt = 0) :
    (𝓡).H ∣ (𝓡).q ^ 15 * Kq p x κ ω Λ ψ wt ^ 5 := by
  have hHS : (𝓡).H ∣ (𝓡).S := ⟨x 10 * x 4 * (𝓡).M ^ 5, by rw [S_eq]; ring⟩
  have hHAc : (𝓡).H ∣ (𝓡).Ac := dvd_trans hHS (S_dvd_Ac ψ wt hp h hwt hz)
  have h1 : (𝓡).H ∣ (𝓡).Ac - (𝓡).zc ^ 5 :=
    ⟨3 * (𝓡).H * (𝓡).M ^ 2 * (𝓡).zc ^ 3 - 19 * (𝓡).H ^ 2 * (𝓡).M ^ 3 * (𝓡).zc ^ 2 -
      57 * (𝓡).H ^ 4 * (𝓡).M ^ 5, by rw [Ac_eq, Dc_eq]; ring⟩
  have h2 : (𝓡).H ∣ (𝓡).zc ^ 5 - ((𝓡).M * (𝓡).K) ^ 5 :=
    dvd_trans (show (𝓡).H ∣ (𝓡).zc - (𝓡).M * (𝓡).K from
      ⟨(𝓡).M * x 7 + ((𝓡).Y - (𝓡).q ^ 3), by rw [zc_eq, Dc_eq]; ring⟩)
      (sub_dvd_pow_sub_pow _ _ 5)
  have h3 : (𝓡).H ∣ ((𝓡).M * (𝓡).K) ^ 5 - ((𝓡).M * (-2 * Kq p x κ ω Λ ψ wt)) ^ 5 :=
    dvd_trans (show (𝓡).H ∣ (𝓡).M * (𝓡).K - (𝓡).M * (-2 * Kq p x κ ω Λ ψ wt) from
      ⟨(𝓡).M * (𝓡).X * x 8, by rw [K_Kq]; ring⟩)
      (sub_dvd_pow_sub_pow _ _ 5)
  have hM := M_eq p x κ ω Λ ψ wt
  have h4 : (𝓡).H ∣ -(2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
      ((𝓡).q ^ 15 * Kq p x κ ω Λ ψ wt ^ 5))))))))))) := by
    have e1 : -(2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 *
        ((𝓡).q ^ 15 * Kq p x κ ω Λ ψ wt ^ 5))))))))))) =
        ((𝓡).Ac - (((𝓡).Ac - (𝓡).zc ^ 5) + ((𝓡).zc ^ 5 - ((𝓡).M * (𝓡).K) ^ 5))) -
          (((𝓡).M * (𝓡).K) ^ 5 - ((𝓡).M * (-2 * Kq p x κ ω Λ ψ wt)) ^ 5) := by
      rw [hM]; ring
    rw [e1]
    exact dvd_sub (dvd_sub hHAc (dvd_add h1 h2)) h3
  have hodd := H_odd p x κ ω Λ ψ wt
  have o : ∀ Y : DiffRing V, (𝓡).H ∣ 2 * Y → (𝓡).H ∣ Y :=
    fun _ hY => odd_dvd_of_dvd_two_mul hodd hY
  exact o _ (o _ (o _ (o _ (o _ (o _ (o _ (o _ (o _ (o _ (dvd_neg.mp h4))))))))))

end Regs

#print axioms unit_of_quintic
#print axioms carrier_core
#print axioms Z_eq_S
#print axioms S_dvd_Ac
#print axioms M_dvd_zc
#print axioms M_dvd_H_mul
#print axioms Y_even
#print axioms A_even
#print axioms K_Kq
#print axioms H_dvd_q15_Kq5

end DiophantineConsistency.LCCarrier
