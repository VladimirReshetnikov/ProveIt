import IPRADerivations.Core.LinearAlgebra

/-!
# Hoehn's pentagram identities and the theorems of Pascal and Brianchon

Packet: `eight_geometry_theorems_ipra`, `sections/08_hoehn.tex` and `sections/10_brianchon.tex`.
Coordinates are integer terms (`ZT`).

* `four_point`: for affine points `V = (x, y, 1)` and `Δ_{ijk} = det(V_i, V_j, V_k)`,
  `Δ_{QUP} − Δ_{QUR} + Δ_{PRQ} − Δ_{PRU} = 0`, the identity behind `T_i = −S_{i+1}`;
* `hoehn_cert` (reusable): the quotient-free certificate `∏ A_i T_i = ∏ S_i D_i`,
  `∏ C_i S_i = ∏ T_i B_i` from the cyclic relations `T_i = −S_{i+1}`, `D_i = −A_{i+2}`,
  `C_i = −B_{i−1}`, by rewriting (no expansion of the degree-20 products);
* `hoehn`: Hoehn's two identities for five points, with `A_i = Δ_{i−1,i+1,i}`,
  `B_i = −Δ_{i−1,i+1,i+2}`, `C_i = Δ_{i+1,i+3,i}`, `D_i = −Δ_{i+1,i+3,i+2}`, `S = A + B`, `T = C + D`;
* `pascal_cert`: on the conic `p(t) = (t², t, 1)`, with secants `L(s, t) = (1, −(s + t), st)` and the
  Pascal points `X = L(a,b) × L(d,e)`, `Y = L(b,c) × L(e,f)`, `Z = L(c,d) × L(f,a)`,
  `(c − f) X + (d − a) Y + (e − b) Z = 0`, so `X, Y, Z` are collinear;
* `brianchon`: for six tangents `τ(t) = (1, −2t, t²)` of `xz = y²`, the hexagon vertices
  `V_i = τ_i × τ_{i+1}` and the diagonals `d_i = V_i × V_{i+3}`, the point `P = d₁ × d₂` lies on
  `d₃` (it lies on `d₁` and `d₂` by `on_cross_left`, `on_cross_right`): the three diagonals are
  concurrent.

The reduction of a general conic to `xz = y²` and the cancellation of nonzero factors in the ratio
forms are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.HoehnBrianchon

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn Matrix
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Hoehn -/

/-- `det((x₁, y₁, 1), (x₂, y₂, 1), (x₃, y₃, 1))`. -/
abbrev Δ (x₁ y₁ x₂ y₂ x₃ y₃ : ZT n) : ZT n := x₁ * (y₂ - y₃) - y₁ * (x₂ - x₃) + (x₂ * y₃ - x₃ * y₂)

/-- `Δ_{QUP} − Δ_{QUR} + Δ_{PRQ} − Δ_{PRU} = 0`. -/
theorem four_point (xP yP xQ yQ xR yR xU yU : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (Δ xQ yQ xU yU xP yP - Δ xQ yQ xU yU xR yR + (Δ xP yP xR yR xQ yQ - Δ xP yP xR yR xU yU))
      (ZT.natLit 0) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit]; push_cast; ring)

/-- `Δ_{PQR} = Δ_{QRP}`. -/
theorem delta_cyc (xP yP xQ yQ xR yR : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (Δ xP yP xQ yQ xR yR) (Δ xQ yQ xR yR xP yP) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul]; ring)

/-- The quotient-free Hoehn certificate from the cyclic relations. -/
theorem hoehn_cert {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ C₀ C₁ C₂ C₃ C₄ D₀ D₁ D₂ D₃ D₄
      S₀ S₁ S₂ S₃ S₄ T₀ T₁ T₂ T₃ T₄ : ZT n}
    (t₀ : Γ ⊢[PRAAx] ZT.eq T₀ (-S₁)) (t₁ : Γ ⊢[PRAAx] ZT.eq T₁ (-S₂)) (t₂ : Γ ⊢[PRAAx] ZT.eq T₂ (-S₃))
    (t₃ : Γ ⊢[PRAAx] ZT.eq T₃ (-S₄)) (t₄ : Γ ⊢[PRAAx] ZT.eq T₄ (-S₀))
    (d₀ : Γ ⊢[PRAAx] ZT.eq D₀ (-A₂)) (d₁ : Γ ⊢[PRAAx] ZT.eq D₁ (-A₃)) (d₂ : Γ ⊢[PRAAx] ZT.eq D₂ (-A₄))
    (d₃ : Γ ⊢[PRAAx] ZT.eq D₃ (-A₀)) (d₄ : Γ ⊢[PRAAx] ZT.eq D₄ (-A₁))
    (c₀ : Γ ⊢[PRAAx] ZT.eq C₀ (-B₄)) (c₁ : Γ ⊢[PRAAx] ZT.eq C₁ (-B₀)) (c₂ : Γ ⊢[PRAAx] ZT.eq C₂ (-B₁))
    (c₃ : Γ ⊢[PRAAx] ZT.eq C₃ (-B₂)) (c₄ : Γ ⊢[PRAAx] ZT.eq C₄ (-B₃)) :
    Γ ⊢[PRAAx] ZT.eq (A₀ * T₀ * (A₁ * T₁) * (A₂ * T₂) * (A₃ * T₃) * (A₄ * T₄))
        (S₀ * D₀ * (S₁ * D₁) * (S₂ * D₂) * (S₃ * D₃) * (S₄ * D₄)) ⋏
      ZT.eq (C₀ * S₀ * (C₁ * S₁) * (C₂ * S₂) * (C₃ * S₃) * (C₄ * S₄))
        (T₀ * B₀ * (T₁ * B₁) * (T₂ * B₂) * (T₃ * B₃) * (T₄ * B₄)) := by
  have et₀ := ZT.toZ_eq t₀; have et₁ := ZT.toZ_eq t₁; have et₂ := ZT.toZ_eq t₂
  have et₃ := ZT.toZ_eq t₃; have et₄ := ZT.toZ_eq t₄
  have ed₀ := ZT.toZ_eq d₀; have ed₁ := ZT.toZ_eq d₁; have ed₂ := ZT.toZ_eq d₂
  have ed₃ := ZT.toZ_eq d₃; have ed₄ := ZT.toZ_eq d₄
  have ec₀ := ZT.toZ_eq c₀; have ec₁ := ZT.toZ_eq c₁; have ec₂ := ZT.toZ_eq c₂
  have ec₃ := ZT.toZ_eq c₃; have ec₄ := ZT.toZ_eq c₄
  rw [ZT.toZ_neg] at et₀ et₁ et₂ et₃ et₄ ed₀ ed₁ ed₂ ed₃ ed₄ ec₀ ec₁ ec₂ ec₃ ec₄
  refine .andI (ZT.derive ?_) (ZT.derive ?_)
  · simp only [ZT.toZ_mul]
    rw [et₀, et₁, et₂, et₃, et₄, ed₀, ed₁, ed₂, ed₃, ed₄]; ring
  · simp only [ZT.toZ_mul]
    rw [et₀, et₁, et₂, et₃, et₄, ec₀, ec₁, ec₂, ec₃, ec₄]; ring

section Pentagon

variable (x₀ y₀ x₁ y₁ x₂ y₂ x₃ y₃ x₄ y₄ : ZT n)

/-- `A_i = Δ_{i−1,i+1,i}`. -/
abbrev hA₀ : ZT n := Δ x₄ y₄ x₁ y₁ x₀ y₀
abbrev hA₁ : ZT n := Δ x₀ y₀ x₂ y₂ x₁ y₁
abbrev hA₂ : ZT n := Δ x₁ y₁ x₃ y₃ x₂ y₂
abbrev hA₃ : ZT n := Δ x₂ y₂ x₄ y₄ x₃ y₃
abbrev hA₄ : ZT n := Δ x₃ y₃ x₀ y₀ x₄ y₄
/-- `B_i = −Δ_{i−1,i+1,i+2}`. -/
abbrev hB₀ : ZT n := -Δ x₄ y₄ x₁ y₁ x₂ y₂
abbrev hB₁ : ZT n := -Δ x₀ y₀ x₂ y₂ x₃ y₃
abbrev hB₂ : ZT n := -Δ x₁ y₁ x₃ y₃ x₄ y₄
abbrev hB₃ : ZT n := -Δ x₂ y₂ x₄ y₄ x₀ y₀
abbrev hB₄ : ZT n := -Δ x₃ y₃ x₀ y₀ x₁ y₁
/-- `C_i = Δ_{i+1,i+3,i}`. -/
abbrev hC₀ : ZT n := Δ x₁ y₁ x₃ y₃ x₀ y₀
abbrev hC₁ : ZT n := Δ x₂ y₂ x₄ y₄ x₁ y₁
abbrev hC₂ : ZT n := Δ x₃ y₃ x₀ y₀ x₂ y₂
abbrev hC₃ : ZT n := Δ x₄ y₄ x₁ y₁ x₃ y₃
abbrev hC₄ : ZT n := Δ x₀ y₀ x₂ y₂ x₄ y₄
/-- `D_i = −Δ_{i+1,i+3,i+2}`. -/
abbrev hD₀ : ZT n := -Δ x₁ y₁ x₃ y₃ x₂ y₂
abbrev hD₁ : ZT n := -Δ x₂ y₂ x₄ y₄ x₃ y₃
abbrev hD₂ : ZT n := -Δ x₃ y₃ x₀ y₀ x₄ y₄
abbrev hD₃ : ZT n := -Δ x₄ y₄ x₁ y₁ x₀ y₀
abbrev hD₄ : ZT n := -Δ x₀ y₀ x₂ y₂ x₁ y₁

theorem tS {xP yP xQ yQ xR yR xU yU : ZT n} :
    Γ ⊢[PRAAx] ZT.eq (Δ xQ yQ xU yU xP yP + -Δ xQ yQ xU yU xR yR) (-(Δ xP yP xR yR xQ yQ + -Δ xP yP xR yR xU yU)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg]; ring)

theorem dA {xP yP xQ yQ xR yR : ZT n} : Γ ⊢[PRAAx] ZT.eq (-Δ xP yP xQ yQ xR yR) (-Δ xP yP xQ yQ xR yR) :=
  ZT.derive rfl

theorem cB {xP yP xQ yQ xR yR : ZT n} : Γ ⊢[PRAAx] ZT.eq (Δ xQ yQ xR yR xP yP) (-(-Δ xR yR xP yP xQ yQ)) :=
  ZT.derive (by simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_neg]; ring)

/-- Hoehn's theorem for the pentagram, quotient-free:
`∏ A_i T_i = ∏ S_i D_i` and `∏ C_i S_i = ∏ T_i B_i`, i.e. `∏ a_i/(1 − b_i) = 1` and
`∏ b_i/(1 − a_i) = 1`. -/
theorem hoehn :
    Γ ⊢[PRAAx] ZT.eq
        (hA₀ x₀ y₀ x₁ y₁ x₄ y₄ * (hC₀ x₀ y₀ x₁ y₁ x₃ y₃ + hD₀ x₁ y₁ x₂ y₂ x₃ y₃) *
          (hA₁ x₀ y₀ x₁ y₁ x₂ y₂ * (hC₁ x₁ y₁ x₂ y₂ x₄ y₄ + hD₁ x₂ y₂ x₃ y₃ x₄ y₄)) *
          (hA₂ x₁ y₁ x₂ y₂ x₃ y₃ * (hC₂ x₀ y₀ x₂ y₂ x₃ y₃ + hD₂ x₀ y₀ x₃ y₃ x₄ y₄)) *
          (hA₃ x₂ y₂ x₃ y₃ x₄ y₄ * (hC₃ x₁ y₁ x₃ y₃ x₄ y₄ + hD₃ x₀ y₀ x₁ y₁ x₄ y₄)) *
          (hA₄ x₀ y₀ x₃ y₃ x₄ y₄ * (hC₄ x₀ y₀ x₂ y₂ x₄ y₄ + hD₄ x₀ y₀ x₁ y₁ x₂ y₂)))
        ((hA₀ x₀ y₀ x₁ y₁ x₄ y₄ + hB₀ x₁ y₁ x₂ y₂ x₄ y₄) * hD₀ x₁ y₁ x₂ y₂ x₃ y₃ *
          ((hA₁ x₀ y₀ x₁ y₁ x₂ y₂ + hB₁ x₀ y₀ x₂ y₂ x₃ y₃) * hD₁ x₂ y₂ x₃ y₃ x₄ y₄) *
          ((hA₂ x₁ y₁ x₂ y₂ x₃ y₃ + hB₂ x₁ y₁ x₃ y₃ x₄ y₄) * hD₂ x₀ y₀ x₃ y₃ x₄ y₄) *
          ((hA₃ x₂ y₂ x₃ y₃ x₄ y₄ + hB₃ x₀ y₀ x₂ y₂ x₄ y₄) * hD₃ x₀ y₀ x₁ y₁ x₄ y₄) *
          ((hA₄ x₀ y₀ x₃ y₃ x₄ y₄ + hB₄ x₀ y₀ x₁ y₁ x₃ y₃) * hD₄ x₀ y₀ x₁ y₁ x₂ y₂)) ⋏
      ZT.eq
        (hC₀ x₀ y₀ x₁ y₁ x₃ y₃ * (hA₀ x₀ y₀ x₁ y₁ x₄ y₄ + hB₀ x₁ y₁ x₂ y₂ x₄ y₄) *
          (hC₁ x₁ y₁ x₂ y₂ x₄ y₄ * (hA₁ x₀ y₀ x₁ y₁ x₂ y₂ + hB₁ x₀ y₀ x₂ y₂ x₃ y₃)) *
          (hC₂ x₀ y₀ x₂ y₂ x₃ y₃ * (hA₂ x₁ y₁ x₂ y₂ x₃ y₃ + hB₂ x₁ y₁ x₃ y₃ x₄ y₄)) *
          (hC₃ x₁ y₁ x₃ y₃ x₄ y₄ * (hA₃ x₂ y₂ x₃ y₃ x₄ y₄ + hB₃ x₀ y₀ x₂ y₂ x₄ y₄)) *
          (hC₄ x₀ y₀ x₂ y₂ x₄ y₄ * (hA₄ x₀ y₀ x₃ y₃ x₄ y₄ + hB₄ x₀ y₀ x₁ y₁ x₃ y₃)))
        ((hC₀ x₀ y₀ x₁ y₁ x₃ y₃ + hD₀ x₁ y₁ x₂ y₂ x₃ y₃) * hB₀ x₁ y₁ x₂ y₂ x₄ y₄ *
          ((hC₁ x₁ y₁ x₂ y₂ x₄ y₄ + hD₁ x₂ y₂ x₃ y₃ x₄ y₄) * hB₁ x₀ y₀ x₂ y₂ x₃ y₃) *
          ((hC₂ x₀ y₀ x₂ y₂ x₃ y₃ + hD₂ x₀ y₀ x₃ y₃ x₄ y₄) * hB₂ x₁ y₁ x₃ y₃ x₄ y₄) *
          ((hC₃ x₁ y₁ x₃ y₃ x₄ y₄ + hD₃ x₀ y₀ x₁ y₁ x₄ y₄) * hB₃ x₀ y₀ x₂ y₂ x₄ y₄) *
          ((hC₄ x₀ y₀ x₂ y₂ x₄ y₄ + hD₄ x₀ y₀ x₁ y₁ x₂ y₂) * hB₄ x₀ y₀ x₁ y₁ x₃ y₃)) :=
  hoehn_cert tS tS tS tS tS dA dA dA dA dA cB cB cB cB cB

end Pentagon

/-! ## Pascal and Brianchon over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R]

/-- The secant `L(s, t) = (1, −(s + t), st)` of `xz = y²`. -/
def secR (s t : R) : Fin 3 → R := ![1, -(s + t), s * t]

/-- The tangent `τ(t) = (1, −2t, t²)` of `xz = y²`. -/
def tauR (t : R) : Fin 3 → R := ![1, -(t + t), t * t]

theorem pascalR (a b c d e f : R) :
    (c - f) • (secR a b ⨯₃ secR d e) + (d - a) • (secR b c ⨯₃ secR e f) + (e - b) • (secR c d ⨯₃ secR f a) = 0 := by
  ext i
  fin_cases i <;> simp [secR, crossProduct] <;> ring

set_option maxHeartbeats 4000000 in
theorem brianchonR (a b c d e f : R) :
    ((tauR c ⨯₃ tauR d) ⨯₃ (tauR f ⨯₃ tauR a)) ⬝ᵥ
      (((tauR a ⨯₃ tauR b) ⨯₃ (tauR d ⨯₃ tauR e)) ⨯₃ ((tauR b ⨯₃ tauR c) ⨯₃ (tauR e ⨯₃ tauR f))) = 0 := by
  simp only [tauR, crossProduct, dotProduct, Fin.sum_univ_three]
  simp
  ring

theorem on_cross_left (u v : Fin 3 → R) : u ⬝ᵥ (u ⨯₃ v) = 0 := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

theorem on_cross_right (u v : Fin 3 → R) : v ⬝ᵥ (u ⨯₃ v) = 0 := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]; ring

end Ring

/-! ## The iPRA statements -/

/-- `L(s, t)` as an integer vector. -/
def sec (s t : ZT n) : Vec 3 n := ![ZT.natLit 1, -(s + t), s * t]

/-- `τ(t)` as an integer vector. -/
def tau (t : ZT n) : Vec 3 n := ![ZT.natLit 1, -(t + t), t * t]

theorem toZ_sec (s t : ZT n) : Vec.toZ Γ (sec s t) = secR (ZT.toZ Γ s) (ZT.toZ Γ t) := by
  funext i; fin_cases i <;> simp [sec, secR, Vec.toZ]

theorem toZ_tau (t : ZT n) : Vec.toZ Γ (tau t) = tauR (ZT.toZ Γ t) := by
  funext i; fin_cases i <;> simp [tau, tauR, Vec.toZ]

/-- Pascal on `xz = y²`: `(c − f) X + (d − a) Y + (e − b) Z = 0`. -/
theorem pascal_cert (a b c d e f : ZT n) :
    Γ ⊢[PRAAx] Vec.eqFm (Vec.add (Vec.add (Vec.smul (c - f) (Vec.cross (sec a b) (sec d e)))
      (Vec.smul (d - a) (Vec.cross (sec b c) (sec e f)))) (Vec.smul (e - b) (Vec.cross (sec c d) (sec f a))))
      (fun _ => ZT.natLit 0) := by
  refine Vec.derive ?_
  funext i
  fin_cases i <;> simp [Vec.toZ, Vec.add, Vec.smul, Vec.cross, sec] <;> ring

/-- Brianchon on `xz = y²`: for the tangent hexagon with vertices `V_i = τ_i × τ_{i+1}` and
diagonals `d_i = V_i × V_{i+3}`, the point `P = d₁ × d₂` lies on all three diagonals. -/
theorem brianchon (a b c d e f : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (Vec.dot (Vec.cross (Vec.cross (tau c) (tau d)) (Vec.cross (tau f) (tau a)))
        (Vec.cross (Vec.cross (Vec.cross (tau a) (tau b)) (Vec.cross (tau d) (tau e)))
          (Vec.cross (Vec.cross (tau b) (tau c)) (Vec.cross (tau e) (tau f))))) (ZT.natLit 0) := by
  refine ZT.derive ?_
  simp only [Vec.toZ_dot, Vec.toZ_cross, toZ_tau, ZT.toZ_natLit, Nat.cast_zero]
  exact brianchonR _ _ _ _ _ _

end LeanProofs.IPRA.Geometry.HoehnBrianchon
