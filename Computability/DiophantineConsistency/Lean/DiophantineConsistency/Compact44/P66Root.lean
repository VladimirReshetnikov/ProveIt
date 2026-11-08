import DiophantineConsistency.Compact44.P66Vals
import DiophantineConsistency.Mixed121.Short15Root
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011
import DiophantineConsistency.Compact44.P72Mu

/-! # Package 66's integral-root carriers in a model of `𝗜𝚺₁`

* `first_int`: `(Q(ℓ + r) + Y)² = Q²(ℓ(ℓ + k) + 1)` with `Q, Y > 0` forces
  `Y = sQ` with `s > 0`: the root of `Q²n` is `Qt`, and `Qt > Q(ℓ + r)`.
  At `Q = q³` this recovers package 58's `q³ ∣ Y`.
* `second_int`: `(qD₀ + XH)² = q²n` and a Bézout certificate for `H` and `q`
  force `q ∣ X`. With `q ≡ 2 (mod 3)` and `q ∣ Y`, `H = 4(XY + Y) + 3 ≡ 3`
  (mod `q`) gives the certificate (`P72Mu.bez_q_H`).
* `c_regs`: the registers of `P66Vals.vals` at a model valuation are the
  images of the corresponding model terms. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P66Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticGcdNormalization
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem first_int (Q Y ell r k : V) (hQ : 0 < Q) (hY : 0 < Y)
    (h : (Q * (ell + r) + Y) * (Q * (ell + r) + Y) = Q * Q * (ell * (ell + k) + 1)) :
    ∃ s : V, 0 < s ∧ Y = s * Q := by
  obtain ⟨t, ht, -⟩ :=
    ArithmeticAdaptiveQuotients2011.scaled_quotient Q (Q * (ell + r) + Y) _ hQ h
  have hle : ell + r ≤ t := by
    have : Q * (ell + r) ≤ Q * t := by rw [← ht]; exact le_self_add
    exact le_of_mul_le_mul_left this hQ
  have e : Q * t = Q * (ell + r) + Q * (t - (ell + r)) := by
    rw [← mul_add, add_tsub_cancel_of_le hle]
  rw [e] at ht
  have hYs : Y = Q * (t - (ell + r)) := add_left_cancel ht
  refine ⟨t - (ell + r), ?_, by rw [hYs, mul_comm]⟩
  rcases (Arithmetic.zero_le (t - (ell + r))).lt_or_eq with h0 | h0
  · exact h0
  · exfalso
    rw [← h0, mul_zero] at hYs
    exact absurd hYs (ne_of_gt hY)

theorem second_int (q D0 X H n : V) (hq : 0 < q) (hqH : Bez H q 1)
    (h : (q * D0 + X * H) * (q * D0 + X * H) = q * q * n) : q ∣ X := by
  obtain ⟨t, ht, -⟩ := ArithmeticAdaptiveQuotients2011.scaled_quotient q (q * D0 + X * H) n hq h
  apply ArithmeticGcdNormalization.unit_certificate_cancel hqH
  apply mod_eq_zero_iff_dvd.mp
  have h1 : (H * X + q * D0) % q = (H * X) % q := mod_add_mul' _ _ hq
  have h2 : (H * X + q * D0) % q = 0 := by
    rw [show H * X + q * D0 = q * D0 + X * H by ring, ht]
    exact mod_eq_zero_iff_dvd.mpr ⟨t, rfl⟩
  rw [← h1, h2]

section Casts
variable (p : Fin 4 → ℕ) (v : Fin 15 → V)

/-- The registers of `P66Vals.vals` at `ι ∘ v`, from `J` and `X`. -/
theorem c_regs (J X : V) (Jr : DiffRing V) (Xf : DiffRing V → DiffRing V) (hJ : Jr = ι J)
    (hX : Xf (ι ((p 0 : V) * J + 1)) = ι X) :
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).q = ι ((p 0 : V) * J + 1) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).q2 =
      ι (((p 0 : V) * J + 1) * ((p 0 : V) * J + 1)) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).q3 =
      ι ((((p 0 : V) * J + 1) * ((p 0 : V) * J + 1)) * ((p 0 : V) * J + 1)) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).X = ι X ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).Y = ι (v 9) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).k = ι (v 11 + v 12) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).c =
      ι ((v 11 + v 12) * v 9 + v 11) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).a = ι (X * v 9 + v 9) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).H =
      ι (4 * (X * v 9 + v 9) + 3) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).Delta =
      ι ((X * v 9 + v 9) * (X * v 9 + v 9) + (4 * (X * v 9 + v 9) + 3)) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).D0 =
      ι ((X * v 9 + v 9) * ((v 11 + v 12) * v 9 + v 11) + (X + v 14 * (4 * (X * v 9 + v 9) + 3))) ∧
    (P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j))).ell =
      ι ((X * v 9) * ((v 11 + v 12) * v 9)) := by
  set vv := P66Vals.vals (fun j => (p j : ℤ)) Jr Xf (fun j => ι (v j)) with hvv
  have cq : vv.q = ι ((p 0 : V) * J + 1) := by
    rw [show vv.q = (((p 0 : ℕ) : ℤ) : DiffRing V) * Jr + 1 from rfl, hJ, Short15Root.cast_nat]
    simp only [map_add, map_mul, map_one]
  have cX : vv.X = ι X := by rw [show vv.X = Xf vv.q from rfl, cq, hX]
  have cY : vv.Y = ι (v 9) := rfl
  have ck : vv.k = ι (v 11 + v 12) := by rw [show vv.k = ι (v 11) + ι (v 12) from rfl, map_add]
  have cc : vv.c = ι ((v 11 + v 12) * v 9 + v 11) := by
    rw [show vv.c = vv.k * vv.Y + ι (v 11) from rfl, ck, cY, ← map_mul, ← map_add]
  have ca : vv.a = ι (X * v 9 + v 9) := by
    rw [show vv.a = vv.X * vv.Y + vv.Y from rfl, cX, cY, ← map_mul, ← map_add]
  have cH : vv.H = ι (4 * (X * v 9 + v 9) + 3) := by
    rw [show vv.H = 4 * vv.a + 3 from rfl, ca]; simp only [map_add, map_mul, map_ofNat]
  refine ⟨cq, ?_, ?_, cX, cY, ck, cc, ca, cH, ?_, ?_, ?_⟩
  · rw [show vv.q2 = vv.q * vv.q from rfl, cq, map_mul]
  · rw [show vv.q3 = (vv.q * vv.q) * vv.q from rfl, cq, map_mul, map_mul]
  · rw [show vv.Delta = vv.a * vv.a + vv.H from rfl, ca, cH, ← map_mul, ← map_add]
  · rw [show vv.D0 = vv.a * vv.c + (vv.X + ι (v 14) * vv.H) from rfl, ca, cc, cX, cH]
    simp only [map_add, map_mul]
  · rw [show vv.ell = (vv.X * vv.Y) * (vv.k * vv.Y) from rfl, cX, cY, ck]
    simp only [map_mul]

end Casts

end P66Root

#print axioms P66Root.first_int
#print axioms P66Root.second_int
#print axioms P66Root.c_regs
