import DiophantineConsistency.LinCof.LCNoRoot
import DiophantineConsistency.ZRows.CoprimeSquares

/-! # Norm extraction for the two-radical output

The output of the linear-cofactor family is the norm
`N = (pa + pb − pc)² − 4·pa·pb`, with `pa = δ Z²`, `pb = δ S² P`, `pc = wt S² B Df Cy`, where
the radical weight `wt` is an even nonzero square (`Weight wt`: `wt = ℓ²`, `ℓ ≠ 0`, `wt = 2 m`;
`1024 = 32²` for package 172, and `64`, `4` for its sibling forms).
`PROOF.md` extracts the two square roots by the independence of squarefree radicals and a
case analysis of negative radicands. Inside a model of `𝗜𝚺₁` the following elementary route is
used instead (it needs only "`b² ∣ a²` implies `b ∣ a`",
`ZRowsCoprimeSquares.dvd_of_sq_dvd_sq_ring`):

* `Z_ne`: at a zero `Z ≠ 0`; otherwise `δ P = wt B Df Cy`, and the left side is odd
  (`δ ≡ −1`, `P ≡ 1 (mod 4)`) while the weight is even;
* at a zero `(pa + pb − pc)² = (2 δ Z S)² · P`, so `2 δ Z S ∣ pa + pb − pc` with a quotient `g`,
  and `P = g²`;
* then `pc = δ (Z − S g)²`, so `(δ (Z − S g))² = (ℓ S)² · B · Df · (δ Cy)`; hence
  `ℓ S ∣ δ (Z − S g)` with a quotient `w`, and `B · Df · (δ Cy) = w²`.

`norm_sq` states the result for an explicit root `ℓ`: `P = g²`, `δ (Z − S g) = ℓ S w`,
`w² = B · Df · (δ · Cy)`; `norm` is the same under `Weight wt`, and `norm1024` is the instance
`ℓ = 32` of package 172. The sign of `g` is not normalized. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.LCNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing LCValue P138Ports LCBootstrap LCNoRoot
open ZRowsCoprimeSquares (dvd_of_sq_dvd_sq_ring)
open P138Bootstrap (odd_ne_zero')

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The radical weight is an even nonzero square: `1024 = 32²` for package 172; `64` and `4`
for the sibling forms. -/
def Weight (wt : DiffRing V) : Prop :=
  ∃ l m : DiffRing V, wt = l * l ∧ l ≠ 0 ∧ wt = 2 * m

theorem weight1024 : Weight (1024 : DiffRing V) :=
  ⟨32, 512, by norm_num, by norm_num, by norm_num⟩

theorem weight64 : Weight (64 : DiffRing V) :=
  ⟨8, 32, by norm_num, by norm_num, by norm_num⟩

theorem weight4 : Weight (4 : DiffRing V) :=
  ⟨2, 2, by norm_num, by norm_num, by norm_num⟩

theorem Weight.even {wt : DiffRing V} (h : Weight wt) : ∃ m : DiffRing V, wt = 2 * m := by
  obtain ⟨_, m, _, _, hm⟩ := h; exact ⟨m, hm⟩

section Regs
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ wt : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ wt
set_option quotPrecheck false in
local notation "𝓘" => (𝓡).delta * (𝓡).Z ^ 2 + (𝓡).delta * (𝓡).S ^ 2 * (𝓡).P -
  wt * (𝓡).S ^ 2 * (𝓡).B * (𝓡).Df * (𝓡).Cy
set_option quotPrecheck false in
local notation "𝓣" => 2 * (𝓡).delta * (𝓡).Z * (𝓡).S

/-- **At a zero, `Z ≠ 0`** for an even weight: otherwise `δ P = wt B Df Cy`, odd against even. -/
theorem Z_ne (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (heven : ∃ m : DiffRing V, wt = 2 * m)
    (hz : valueK p x κ ω Λ ψ wt = 0) : (𝓡).Z ≠ 0 := by
  intro hZ
  have hS := S_ne p x κ ω Λ ψ wt hp hz
  rw [value_eq_product, hZ] at hz
  have h1 : ((𝓡).S ^ 2 * ((𝓡).delta * (𝓡).P - wt * (𝓡).B * (𝓡).Df * (𝓡).Cy)) ^ 2 = 0 := by
    linear_combination hz
  have h2 : (𝓡).delta * (𝓡).P - wt * (𝓡).B * (𝓡).Df * (𝓡).Cy = 0 := by
    rcases mul_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1) with h3 | h3
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h3) hS
    · exact h3
  obtain ⟨n, hn⟩ := delta_mod p x κ ω Λ ψ wt
  obtain ⟨m, hm⟩ := P_mod ψ wt hp h
  obtain ⟨m', hm'⟩ := heven
  apply odd_ne_zero' (8 * n * m + 2 * n - 2 * m - 1 - m' * (𝓡).B * (𝓡).Df * (𝓡).Cy)
  linear_combination h2 + ((𝓡).B * (𝓡).Df * (𝓡).Cy) * hm' - (𝓡).P * hn - (4 * n - 1) * hm

/-- **Norm extraction** for a weight `wt = l²`, `l ≠ 0`, `wt` even. At a zero of the output
there are `g`, `w` with `P = g²`, `δ (Z − S g) = l S w` and `w² = B · Df · (δ · Cy)`. -/
theorem norm_sq (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) {l : DiffRing V}
    (hl : wt = l * l) (hl0 : l ≠ 0) (heven : ∃ m : DiffRing V, wt = 2 * m)
    (hz : valueK p x κ ω Λ ψ wt = 0) :
    ∃ g w : DiffRing V, (𝓡).P = g * g ∧
      (𝓡).delta * ((𝓡).Z - (𝓡).S * g) = l * (𝓡).S * w ∧
      w * w = (𝓡).B * (𝓡).Df * ((𝓡).delta * (𝓡).Cy) := by
  have hS := S_ne p x κ ω Λ ψ wt hp hz
  have hZ := Z_ne ψ wt hp h heven hz
  have hδ := (nonzero p x κ ω Λ ψ wt).2.1
  have hT : 𝓣 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hδ) hZ) hS
  have hz' := hz
  rw [value_eq_product] at hz'
  have hdvd : (𝓣) * (𝓣) ∣ (𝓘) * (𝓘) := ⟨(𝓡).P, by linear_combination hz'⟩
  obtain ⟨g, hg⟩ := dvd_of_sq_dvd_sq_ring hdvd
  have hP : (𝓡).P = g * g := by
    apply mul_left_cancel₀ (mul_ne_zero hT hT)
    linear_combination (-1 : DiffRing V) * hz' + ((𝓘) + (𝓣) * g) * hg
  have hX2 : ((𝓡).delta * ((𝓡).Z - (𝓡).S * g)) * ((𝓡).delta * ((𝓡).Z - (𝓡).S * g)) =
      (l * (𝓡).S) * (l * (𝓡).S) * ((𝓡).B * (𝓡).Df * ((𝓡).delta * (𝓡).Cy)) := by
    linear_combination (𝓡).delta * hg - (𝓡).delta ^ 2 * (𝓡).S ^ 2 * hP +
      ((𝓡).S ^ 2 * (𝓡).B * (𝓡).Df * (𝓡).delta * (𝓡).Cy) * hl
  obtain ⟨w, hw⟩ := dvd_of_sq_dvd_sq_ring ⟨_, hX2⟩
  have hlS : l * (𝓡).S ≠ 0 := mul_ne_zero hl0 hS
  refine ⟨g, w, hP, hw, ?_⟩
  apply mul_left_cancel₀ (mul_ne_zero hlS hlS)
  linear_combination hX2 - ((𝓡).delta * ((𝓡).Z - (𝓡).S * g) + l * (𝓡).S * w) * hw

/-- **Norm extraction** under `Weight wt`: `P = g²`, `wt = l²`, `δ (Z − S g) = l S w`,
`w² = B · Df · (δ · Cy)`. -/
theorem norm (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e) (hwt : Weight wt)
    (hz : valueK p x κ ω Λ ψ wt = 0) :
    ∃ g l w : DiffRing V, (𝓡).P = g * g ∧ wt = l * l ∧
      (𝓡).delta * ((𝓡).Z - (𝓡).S * g) = l * (𝓡).S * w ∧
      w * w = (𝓡).B * (𝓡).Df * ((𝓡).delta * (𝓡).Cy) := by
  obtain ⟨l, m, hl, hl0, hm⟩ := hwt
  obtain ⟨g, w, hP, hX, hw⟩ := norm_sq ψ wt hp h hl hl0 ⟨m, hm⟩ hz
  exact ⟨g, l, w, hP, hl, hX, hw⟩

end Regs

section W1024
variable {p : Fin 6 → DiffRing V} {x : Fin 11 → DiffRing V} {κ ω Λ : DiffRing V} {e : ℕ}
variable (ψ : DiffRing V)
local notation "𝓡" => regsK p x κ ω Λ ψ 1024

/-- Norm extraction at the weight `1024 = 32²` of package 172. -/
theorem norm1024 (hp : PortFacts p) (h : SlotLaw p x κ ω Λ e)
    (hz : valueK p x κ ω Λ ψ 1024 = 0) :
    ∃ g w : DiffRing V, (𝓡).P = g * g ∧
      (𝓡).delta * ((𝓡).Z - (𝓡).S * g) = 32 * (𝓡).S * w ∧
      w * w = (𝓡).B * (𝓡).Df * ((𝓡).delta * (𝓡).Cy) :=
  norm_sq ψ 1024 hp h (l := 32) (by norm_num) (by norm_num) ⟨512, by norm_num⟩ hz

end W1024

#print axioms weight1024
#print axioms weight64
#print axioms weight4
#print axioms Z_ne
#print axioms norm_sq
#print axioms norm
#print axioms norm1024

end DiophantineConsistency.LCNorm
