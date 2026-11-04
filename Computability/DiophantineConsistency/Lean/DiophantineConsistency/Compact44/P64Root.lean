import DiophantineConsistency.Compact44.P64Graph
import DiophantineConsistency.Compact44.P72Aux

/-! # Package 64's degree-30 equation: the residuals in a model

Write `q = βJ + 1`, `X = wq`, `k = η + ζ`, `c = kY + η`, `a = XY + Y`,
`Δ = a² + (4a + 3)` and `U = Y²`. In every model of `𝗜𝚺₁`, at a positive
valuation:

* `first_root`: `A0 = 0` gives `q³ ∣ Y` and a first Pell norm
  `τ² = ℓ(ℓ + k) + 1`;
* `transport`: `Lt = 0` gives `F + α < q` and `(K0 + w)C = F + z(q−1)`, where
  `C = q − (F + α)`;
* `strong`: `W = 0` is the ordinary strong norm `(ic²)² = Δ(f²−1)`;
* `aux_norm`: `Na = 1` is the auxiliary norm in the absolute-difference form
  of `P72Exact`;
* `main_root`: `M = 0` gives the main Pell root `g`, with
  `U·g + H·k = U(X + ac) + H(Uγ + R + 1)`. `D*` is positive because
  `U·a·c ≥ H·k` once `Y ≥ 2`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P64Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveQuotients2011 P64Graph
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem ι_pos' {x : V} (h : 0 < x) : (0 : DiffRing V) < ι x := by
  simpa using (ι_lt_ι (V := V)).mpr h

private theorem ι_one_le {x : V} (h : 0 < x) : (1 : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)

theorem cast_nat (n : ℕ) : (((n : ℤ)) : DiffRing V) = ι (n : V) := by
  rw [Int.cast_natCast, map_natCast]

section Casts
variable (p : Fin 4 → ℕ) (v : Fin 14 → V)

theorem c_qm : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qm = ι ((p 0 : V) * v 0) := by
  simp only [vals, map_mul, cast_nat]

theorem c_q : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q = ι ((p 0 : V) * v 0 + 1) := by
  simp only [vals, map_add, map_mul, map_one, cast_nat]

theorem c_q3 : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q3 =
    ι (((p 0 : V) * v 0 + 1) * ((p 0 : V) * v 0 + 1) * ((p 0 : V) * v 0 + 1)) := by
  simp only [vals, map_add, map_mul, map_one, cast_nat]

theorem c_U : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U = ι (v 7 * v 7) := by
  simp only [vals, map_mul]

theorem c_X : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).X = ι (v 8 * ((p 0 : V) * v 0 + 1)) := by
  simp only [vals, map_add, map_mul, map_one, cast_nat]

theorem c_k : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).k = ι (v 10 + v 11) := by
  simp only [vals, map_add]

theorem c_ell : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).ell =
    ι ((v 8 * ((p 0 : V) * v 0 + 1)) * v 7 * ((v 10 + v 11) * v 7)) := by
  simp only [vals, map_add, map_mul, map_one, cast_nat]

theorem c_c : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c = ι ((v 10 + v 11) * v 7 + v 10) := by
  simp only [vals, map_add, map_mul]

theorem c_a : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).a =
    ι ((v 8 * ((p 0 : V) * v 0 + 1)) * v 7 + v 7) := by
  simp only [vals, map_add, map_mul, map_one, cast_nat]

theorem c_H : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).H =
    ι (4 * ((v 8 * ((p 0 : V) * v 0 + 1)) * v 7 + v 7) + 3) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_Delta : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta =
    ι (((v 8 * ((p 0 : V) * v 0 + 1)) * v 7 + v 7) * ((v 8 * ((p 0 : V) * v 0 + 1)) * v 7 + v 7) +
      (4 * ((v 8 * ((p 0 : V) * v 0 + 1)) * v 7 + v 7) + 3)) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_C : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).C =
    ι ((p 0 : V) * v 0 + 1) - ι (v 1) - ι (v 2) := by
  rw [← c_q]; rfl

theorem c_Aaux : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta * (ι (v 4) * ι (v 4) - 1) := rfl

theorem c_y : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).y =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).V + ι (v 12) := rfl

theorem c_V : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).V =
    (ι (v 4) * ι (v 4)) * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c * ι (v 6) -
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR) - (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c := rfl

theorem c_Dstar : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Dstar =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).X +
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).a * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c) +
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).H * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U * ι (v 13) -
      (((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).k - (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR) - 1)) :=
  rfl

/-- The rank `R`, once `F ≤ q`. -/
theorem c_RR (hF : v 1 ≤ (p 0 : V) * v 0 + 1) :
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR =
      ι (((p 0 : V) * v 0 * (((p 0 : V) * v 0 + 1) - v 1) + v 2) *
        (((p 0 : V) * v 0 + 1) * ((p 0 : V) * v 0 + 1) - 1) +
          ((p 2 : V) + ((p 0 : V) * v 0 + 1) * (p 3 : V)) * v 0) := by
  have hq1 : 1 ≤ ((p 0 : V) * v 0 + 1) * ((p 0 : V) * v 0 + 1) :=
    one_le_mul_of_one_le_of_one_le le_add_self le_add_self
  simp only [vals, map_add, map_mul, map_one, cast_nat, ι_tsub hF, ι_tsub hq1]

end Casts

/-- `A0 = 0`: `q³ ∣ Y` and the first Pell norm. -/
theorem first_root (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).A0 v) :
    let q : V := (p 0 : V) * v 0 + 1
    let k : V := v 10 + v 11
    let ell : V := (v 8 * q) * v 7 * (k * v 7)
    (q * q * q) ∣ v 7 ∧ ∃ τ : V, τ * τ = ell * (ell + k) + 1 := by
  intro q k ell
  let Q3 : V := q * q * q
  have hQ3 : 0 < Q3 := by
    have hq : 0 < q := lt_of_lt_of_le (by simp) le_add_self
    exact mul_pos (mul_pos hq hq) hq
  let P : V := Q3 * (ell + v 9) + v 7
  rw [internalZero_iff, A0_eval, c_q3, c_ell, c_k] at hz
  have hP : P * P = Q3 * Q3 * (ell * (ell + k) + 1) := by
    apply ι_injective
    simp only [P, Q3, ell, k, q, map_add, map_mul, map_one] at hz ⊢
    linear_combination hz
  obtain ⟨τ, hτ, hττ⟩ := scaled_quotient Q3 P _ hQ3 hP
  refine ⟨?_, τ, hττ⟩
  apply mod_eq_zero_iff_dvd.mp
  have h1 : P % Q3 = v 7 % Q3 := by
    simp only [P]; rw [add_comm]; exact mod_add_mul' _ _ hQ3
  have h2 : P % Q3 = 0 := by rw [hτ]; exact mod_eq_zero_iff_dvd.mpr ⟨τ, rfl⟩
  rw [← h1, h2]

/-- `Lt = 0`: the positive gap and the transport. -/
theorem transport (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).Lt v) :
    let q : V := (p 0 : V) * v 0 + 1
    v 1 + v 2 < q ∧ ((p 1 : V) + v 8) * (q - (v 1 + v 2)) = v 1 + v 3 * ((p 0 : V) * v 0) := by
  intro q
  rw [internalZero_iff, Lt_eval, c_C, c_qm] at hz
  simp only [cast_nat] at hz
  have hF : (1 : DiffRing V) ≤ ι (v 1) := ι_one_le (hv 1)
  have hKw : (0 : DiffRing V) ≤ ι (p 1 : V) + ι (v 8) := add_nonneg (ι_nonneg _) (ι_nonneg _)
  have hzq : (0 : DiffRing V) ≤ ι (v 3) * ι ((p 0 : V) * v 0) := mul_nonneg (ι_nonneg _) (ι_nonneg _)
  set Cr : DiffRing V := ι q - ι (v 1) - ι (v 2) with hCr
  have hC : 0 < Cr := by
    by_contra hneg
    have hle : Cr ≤ 0 := le_of_not_gt hneg
    have h1 : (ι (p 1 : V) + ι (v 8)) * Cr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKw hle
    linarith
  have hlt : v 1 + v 2 < q := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_add]; linarith
  refine ⟨hlt, ?_⟩
  apply ι_injective
  rw [map_mul, ι_tsub (le_of_lt hlt)]
  simp only [q, Cr, map_add, map_mul, map_one] at hz ⊢
  linear_combination hz

/-- `W = 0`: the ordinary strong norm. -/
theorem strong (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).W v) :
    let q : V := (p 0 : V) * v 0 + 1
    let c : V := (v 10 + v 11) * v 7 + v 10
    let a : V := (v 8 * q) * v 7 + v 7
    let Δ : V := a * a + (4 * a + 3)
    (v 5 * (c * c)) * (v 5 * (c * c)) + Δ = Δ * (v 4 * v 4) := by
  intro q c a Δ
  rw [internalZero_iff, W_eval, c_Aaux, c_Delta, c_c] at hz
  apply ι_injective
  simp only [map_add, map_mul]
  linear_combination hz

/-- `Na = 1`: the auxiliary norm, in the absolute-difference form of `P72Exact`. -/
theorem aux_norm (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hF : v 1 ≤ (p 0 : V) * v 0 + 1) (hf : 0 < v 4)
    (hz : (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) = 1) :
    let q : V := (p 0 : V) * v 0 + 1
    let c : V := (v 10 + v 11) * v 7 + v 10
    let a : V := (v 8 * q) * v 7 + v 7
    let R : V := ((p 0 : V) * v 0 * (q - v 1) + v 2) * (q * q - 1) + ((p 2 : V) + q * (p 3 : V)) * v 0
    let f : V := v 4
    let T : V := v 6
    let u : V := v 12
    ((3 + 4 * a) + a * a) * (f * f - 1) *
        (absdiff (f * f * (T * c)) (f * f * R + c) * absdiff (f * f * (T * c)) (f * f * R + c)) +
        absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c) =
      1 + ((3 + 4 * a) + a * a) * (f * f - 1) *
        (absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c)) := by
  intro q c a R f T u
  rw [Na_eval, c_y, c_V, c_Aaux, c_RR p v hF, c_Delta, c_c] at hz
  have hf1 : 1 ≤ f * f := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  apply ι_injective
  simp only [map_add, map_mul, map_one, ι_tsub hf1, map_one]
  rw [ι_absdiff_sq, ι_absdiff_sq]
  simp only [q, c, a, R, f, T, u] at hz ⊢
  simp only [map_add, map_mul, map_ofNat, map_one] at hz ⊢
  linear_combination hz

section Bounds

private theorem hk_bound {H U a c k Y : DiffRing V} (hH : H = 4 * a + 3) (hU : U = Y * Y)
    (hc : k * Y ≤ c) (ha : 1 ≤ a) (hY : 2 ≤ Y) (hk : 0 < k) : H * k ≤ U * (a * c) := by
  have ha0 : 0 ≤ a := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have h1 : (Y * Y) * (a * (k * Y)) ≤ U * (a * c) := by
    rw [hU]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc ha0) (by positivity)
  have hY3 : (8 : DiffRing V) ≤ Y * Y * Y := by nlinarith
  have hak : 0 ≤ a * k := by positivity
  have h2 : (Y * Y) * (a * (k * Y)) = (a * k) * (Y * Y * Y) := by ring
  rw [hH]
  nlinarith

private theorem D0_bound {H k U a c X G R : DiffRing V} (h : H * k ≤ U * (a * c))
    (hU : 0 ≤ U) (hX : 0 ≤ X) (hH : 0 ≤ H) (hG : 0 ≤ G) (hR : 0 ≤ R) :
    H * k ≤ U * (X + a * c) + H * (U * G + R + 1) := by
  have h1 : 0 ≤ U * X := mul_nonneg hU hX
  have h2 : 0 ≤ H * (U * G + R + 1) := by positivity
  nlinarith

end Bounds

/-- `M = 0`: the main Pell root and the carrier relation. -/
theorem main_root (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (hF : v 1 ≤ (p 0 : V) * v 0 + 1)
    (hY : ((p 0 : V) * v 0 + 1) * ((p 0 : V) * v 0 + 1) * ((p 0 : V) * v 0 + 1) ∣ v 7)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).M v) :
    let q : V := (p 0 : V) * v 0 + 1
    let X : V := v 8 * q
    let k : V := v 10 + v 11
    let c : V := k * v 7 + v 10
    let a : V := X * v 7 + v 7
    let H : V := 4 * a + 3
    let Δ : V := a * a + H
    let R : V := ((p 0 : V) * v 0 * (q - v 1) + v 2) * (q * q - 1) + ((p 2 : V) + q * (p 3 : V)) * v 0
    let U : V := v 7 * v 7
    ∃ g : V, g * g = Δ * (c * c) + 1 ∧
      U * g + H * k = U * (X + a * c) + H * (U * v 13 + R + 1) := by
  intro q X k c a H Δ R U
  rw [internalZero_iff, M_eval, c_Dstar, c_U, c_c, c_a, c_X, c_H, c_k, c_RR p v hF, c_Delta] at hz
  let Dr : DiffRing V := ι U * (ι X + ι a * ι c) + ι H * (ι U * ι (v 13) + ι R + 1) - ι H * ι k
  have hDr : Dr * Dr = (ι U * ι U) * (ι Δ * (ι c * ι c) + 1) := by
    simp only [Dr]
    linear_combination hz
  -- positivity of D*
  have hk : (0 : DiffRing V) < ι k := ι_pos' (add_pos (hv 10) (hv 11))
  have hY2 : (2 : DiffRing V) ≤ ι (v 7) := by
    obtain ⟨s, hs⟩ := hY
    have hs0 : 1 ≤ s := by
      rcases (Arithmetic.zero_le s).lt_or_eq with h | h
      · exact pos_iff_one_le.mp h
      · exfalso; rw [← h, mul_zero] at hs; exact (ne_of_gt (hv 7)) hs
    have hq2 : (2 : V) ≤ q := by
      have h1 : 1 ≤ (p 0 : V) * v 0 :=
        one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
      simpa [q, one_add_one_eq_two] using (add_le_add_iff_right (1 : V)).mpr h1
    have h2 : (2 : V) ≤ v 7 := by
      rw [hs]
      calc (2 : V) ≤ q := hq2
        _ ≤ q * q * q := le_mul_of_one_le_left (Arithmetic.zero_le _)
            (one_le_mul_of_one_le_of_one_le (le_trans (by norm_num) hq2) (le_trans (by norm_num) hq2))
        _ ≤ q * q * q * s := le_mul_of_one_le_right (Arithmetic.zero_le _) hs0
    have h := (ι_le_ι (V := V)).mpr h2
    rwa [map_ofNat] at h
  have ha1 : (1 : DiffRing V) ≤ ι a := by
    have : ι a = ι X * ι (v 7) + ι (v 7) := by simp [a, map_add, map_mul]
    rw [this]; exact le_trans (by linarith) (le_add_of_nonneg_left (mul_nonneg (ι_nonneg _) (ι_nonneg _)))
  have hc' : ι k * ι (v 7) ≤ ι c := by
    have : ι c = ι k * ι (v 7) + ι (v 10) := by simp [c, map_add, map_mul]
    rw [this]; exact le_add_of_nonneg_right (ι_nonneg _)
  have hHk : ι H * ι k ≤ ι U * (ι a * ι c) :=
    hk_bound (by simp [H, map_add, map_mul, map_ofNat]) (by simp [U, map_mul]) hc' ha1 hY2 hk
  let D0 : V := U * (X + a * c) + H * (U * v 13 + R + 1)
  have hle : H * k ≤ D0 := by
    apply (ι_le_ι (V := V)).mp
    have : ι D0 = ι U * (ι X + ι a * ι c) + ι H * (ι U * ι (v 13) + ι R + 1) := by
      simp [D0, map_add, map_mul]
    rw [this, map_mul]
    exact D0_bound hHk (ι_nonneg U) (ι_nonneg X) (ι_nonneg H) (ι_nonneg (v 13)) (ι_nonneg R)
  let Ds : V := D0 - H * k
  have cDs : ι Ds = Dr := by
    rw [ι_tsub hle]; simp [D0, Dr, map_add, map_mul]
  have hDsV : Ds * Ds = U * U * (Δ * (c * c) + 1) := by
    apply ι_injective
    simp only [map_mul, map_add, map_one, cDs]
    rw [hDr]
  have hUpos : 0 < U := mul_pos (hv 7) (hv 7)
  obtain ⟨g, hg, hgg⟩ := scaled_quotient U Ds (Δ * (c * c) + 1) hUpos hDsV
  refine ⟨g, hgg, ?_⟩
  rw [← hg]
  exact tsub_add_cancel_of_le hle

end P64Root

#print axioms P64Root.first_root
#print axioms P64Root.transport
#print axioms P64Root.strong
#print axioms P64Root.aux_norm
#print axioms P64Root.main_root
