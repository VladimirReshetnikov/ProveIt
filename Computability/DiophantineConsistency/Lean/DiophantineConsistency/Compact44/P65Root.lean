import DiophantineConsistency.Compact44.P65Graph
import DiophantineConsistency.Compact44.P72Aux

/-! # Package 65's degree-26 equation: the five residuals in a model

Write `J = 1 + 3j`, `q = 1 + βJ`, `X = q + x`, `k = η + ζ`, `c = η + Yk`,
`a = Y + YX` and `Δ = (3 + 4a) + a²`. In every model of `𝗜𝚺₁`, a positive zero
gives:

* `strong`: the ordinary strong norm `(ic²)² + Δ = Δf²`;
* `first_root`: `q³ ∣ Y` and a first Pell norm `τ² = 1 + ℓ(ℓ + k)`, because
  `(Y + q³(r + ℓ))² = q⁶(1 + ℓ(ℓ+k))` has an integral root;
* `transport`: `F + α < q`, and with `C = q − (F + α)` and `A = X + K0·q`,
  `qA = ((F + α)A + Fq) + (q − 1)(qz)`. The gap is positive because otherwise
  every summand of `At` other than `−qF` is nonpositive;
* `aux_norm`: the auxiliary norm in the absolute-difference form that
  `P72Exact` consumes;
* `main_root`: the main Pell root `g`, with `M·g + H·k = M(X+ac) +
  H(Mγ + SX + R + 1)`. As for P13, `D*` is positive because `M·a·c ≥ H·k`
  once `q³ ∣ Y`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P65Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveQuotients2011 P65Graph
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem ι_pos' {x : V} (h : 0 < x) : (0 : DiffRing V) < ι x := by
  simpa using (ι_lt_ι (V := V)).mpr h

private theorem ι_one_le {x : V} (h : 0 < x) : (1 : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)

private theorem cast_nat (n : ℕ) : (((n : ℤ)) : DiffRing V) = ι (n : V) := by
  rw [Int.cast_natCast, map_natCast]

section Casts
variable (p : Fin 4 → ℕ) (v : Fin 14 → V)

theorem c_bJ : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).bJ = ι ((p 0 : V) * (1 + 3 * v 0)) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_q : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q = ι (1 + (p 0 : V) * (1 + 3 * v 0)) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_X : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).X = ι ((1 + (p 0 : V) * (1 + 3 * v 0)) + v 7) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_k : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).k = ι (v 10 + v 11) := by
  simp only [vals, map_add]

theorem c_c : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c = ι (v 10 + v 8 * (v 10 + v 11)) := by
  simp only [vals, map_add, map_mul]

theorem c_a : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).a = ι (v 8 + v 8 * ((1 + (p 0 : V) * (1 + 3 * v 0)) + v 7)) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_H : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).H = ι (3 + 4 * (v 8 + v 8 * ((1 + (p 0 : V) * (1 + 3 * v 0)) + v 7))) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_Delta : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta = ι ((3 + 4 * (v 8 + v 8 * ((1 + (p 0 : V) * (1 + 3 * v 0)) + v 7))) +
    (v 8 + v 8 * ((1 + (p 0 : V) * (1 + 3 * v 0)) + v 7)) *
      (v 8 + v 8 * ((1 + (p 0 : V) * (1 + 3 * v 0)) + v 7))) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_ell : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).ell = ι ((v 8 * (v 10 + v 11)) * (v 8 * ((1 + (p 0 : V) * (1 + 3 * v 0)) + v 7))) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_q3 : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q3 = ι ((1 + (p 0 : V) * (1 + 3 * v 0)) *
    ((1 + (p 0 : V) * (1 + 3 * v 0)) * (1 + (p 0 : V) * (1 + 3 * v 0)))) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_S : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).S = ι (4 * (v 8 * (1 + (p 0 : V) * (1 + 3 * v 0)))) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_M : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).M = ι (4 * (v 8 * (1 + (p 0 : V) * (1 + 3 * v 0))) * (1 + (p 0 : V) * (1 + 3 * v 0))) := by
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_C : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).C = ι (1 + (p 0 : V) * (1 + 3 * v 0)) - ι (v 1) - ι (v 2) := by
  rw [← c_q]; rfl

theorem c_U : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U = (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta * (ι (v 4) * ι (v 4) - 1) := rfl

theorem c_V : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).V = (ι (v 4) * ι (v 4)) * (ι (v 6) * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c - (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR) - (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c := rfl

theorem c_Dstar : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Dstar = (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).M * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).a + (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).X) +
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).H * ((ι (v 13) * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).M - (((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).k - (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR) - 1)) + (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).S * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).X) := rfl

/-- The rank `R`, once `F ≤ q`. -/
theorem c_RR (hF : v 1 ≤ 1 + (p 0 : V) * (1 + 3 * v 0)) :
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR = ι ((v 2 + ((p 0 : V) * (1 + 3 * v 0)) * ((1 + (p 0 : V) * (1 + 3 * v 0)) - v 1)) *
      ((1 + (p 0 : V) * (1 + 3 * v 0)) * (1 + (p 0 : V) * (1 + 3 * v 0)) - 1) +
        (1 + 3 * v 0) * ((p 2 : V) + (p 3 : V) * (1 + (p 0 : V) * (1 + 3 * v 0)))) := by
  have hq1 : 1 ≤ (1 + (p 0 : V) * (1 + 3 * v 0)) * (1 + (p 0 : V) * (1 + 3 * v 0)) :=
    one_le_mul_of_one_le_of_one_le le_self_add le_self_add
  simp only [vals, map_add, map_mul, map_one, map_ofNat, cast_nat, ι_tsub hF, ι_tsub hq1]

end Casts

/-- `As = 0`: the ordinary strong norm. -/
theorem strong (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).As v) :
    let q : V := 1 + (p 0 : V) * (1 + 3 * v 0)
    let c : V := v 10 + v 8 * (v 10 + v 11)
    let a : V := v 8 + v 8 * (q + v 7)
    let Δ : V := (3 + 4 * a) + a * a
    (v 5 * (c * c)) * (v 5 * (c * c)) + Δ = Δ * (v 4 * v 4) := by
  intro q c a Δ
  rw [internalZero_iff, As_eval, c_U, c_Delta, c_c] at hz
  apply ι_injective
  simp only [map_add, map_mul]
  linear_combination hz

/-- `A0 = 0`: `q³ ∣ Y` and the first Pell norm. -/
theorem first_root (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).A0 v) :
    let q : V := 1 + (p 0 : V) * (1 + 3 * v 0)
    let k : V := v 10 + v 11
    let ell : V := (v 8 * k) * (v 8 * (q + v 7))
    (q * (q * q)) ∣ v 8 ∧ ∃ τ : V, τ * τ = 1 + ell * (ell + k) := by
  intro q k ell
  let Q3 : V := q * (q * q)
  have hQ3 : 0 < Q3 := by
    have hq : 0 < q := lt_of_lt_of_le (by simp) le_self_add
    exact mul_pos hq (mul_pos hq hq)
  let P : V := v 8 + Q3 * (v 9 + ell)
  rw [internalZero_iff, A0_eval, c_q3, c_ell, c_k] at hz
  have hP : P * P = Q3 * Q3 * (1 + ell * (ell + k)) := by
    apply ι_injective
    simp only [P, Q3, ell, k, q, map_add, map_mul, map_one] at hz ⊢
    linear_combination hz
  obtain ⟨τ, hτ, hττ⟩ := scaled_quotient Q3 P _ hQ3 hP
  refine ⟨?_, τ, hττ⟩
  apply mod_eq_zero_iff_dvd.mp
  have h1 : P % Q3 = v 8 % Q3 := by simp only [P]; exact mod_add_mul' _ _ hQ3
  have h2 : P % Q3 = 0 := by rw [hτ]; exact mod_eq_zero_iff_dvd.mpr ⟨τ, rfl⟩
  rw [← h1, h2]

/-- `At = 0`: the positive gap and the transport identity. -/
theorem transport (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).At v) :
    let q : V := 1 + (p 0 : V) * (1 + 3 * v 0)
    let A : V := (q + v 7) + (p 1 : V) * q
    v 1 + v 2 < q ∧
      q * A = ((v 1 + v 2) * A + v 1 * q) + ((p 0 : V) * (1 + 3 * v 0)) * (q * v 3) := by
  intro q A
  rw [internalZero_iff, At_eval, c_C, c_X, c_q, c_bJ] at hz
  simp only [cast_nat] at hz
  have hq0 : (0 : DiffRing V) < ι q := ι_pos' (lt_of_lt_of_le (by simp) le_self_add)
  have hF : (1 : DiffRing V) ≤ ι (v 1) := ι_one_le (hv 1)
  have hX : (0 : DiffRing V) ≤ ι (q + v 7) := ι_nonneg _
  have hK : (0 : DiffRing V) ≤ ι (p 1 : V) := ι_nonneg _
  have hbz : (0 : DiffRing V) ≤ ι ((p 0 : V) * (1 + 3 * v 0)) * ι (v 3) :=
    mul_nonneg (ι_nonneg _) (ι_nonneg _)
  set Cr : DiffRing V := ι q - ι (v 1) - ι (v 2) with hCr
  have hC : 0 < Cr := by
    by_contra hneg
    have hle : Cr ≤ 0 := le_of_not_gt hneg
    have h1 : Cr * ι (q + v 7) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hle hX
    have h2 : ι (p 1 : V) * Cr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hK hle
    have h3 : ι q * ((ι (p 1 : V) * Cr - ι (v 1)) - ι ((p 0 : V) * (1 + 3 * v 0)) * ι (v 3)) < 0 :=
      mul_neg_of_pos_of_neg hq0 (by linarith)
    linarith
  have hlt : v 1 + v 2 < q := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_add]; linarith
  refine ⟨hlt, ?_⟩
  apply ι_injective
  simp only [A, q, Cr, map_add, map_mul, map_one, map_ofNat] at hz ⊢
  linear_combination hz

/-- `Aa = 0`, in the absolute-difference form of `P72Exact`. -/
theorem aux_norm (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hF : v 1 ≤ 1 + (p 0 : V) * (1 + 3 * v 0)) (hf : 0 < v 4)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).Aa v) :
    let q : V := 1 + (p 0 : V) * (1 + 3 * v 0)
    let c : V := v 10 + v 8 * (v 10 + v 11)
    let a : V := v 8 + v 8 * (q + v 7)
    let Δ : V := (3 + 4 * a) + a * a
    let R : V := (v 2 + ((p 0 : V) * (1 + 3 * v 0)) * (q - v 1)) * (q * q - 1) +
      (1 + 3 * v 0) * ((p 2 : V) + (p 3 : V) * q)
    let f : V := v 4
    let T : V := v 6
    let u : V := v 12
    Δ * (f * f - 1) *
        (absdiff (f * f * (T * c)) (f * f * R + c) * absdiff (f * f * (T * c)) (f * f * R + c)) +
        absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c) =
      1 + Δ * (f * f - 1) *
        (absdiff (f * f * (T * c) + u) (f * f * R + c) * absdiff (f * f * (T * c) + u) (f * f * R + c)) := by
  intro q c a Δ R f T u
  rw [internalZero_iff, Aa_eval, c_V, c_U, c_RR p v hF, c_Delta, c_c] at hz
  have hf1 : 1 ≤ f * f := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  apply ι_injective
  simp only [map_add, map_mul, map_one, ι_tsub hf1, map_one]
  rw [ι_absdiff_sq, ι_absdiff_sq]
  simp only [map_add, map_mul]
  linear_combination hz

section Bounds

private theorem cube_bound {q s : DiffRing V} (hq : 2 ≤ q) (hs : 1 ≤ s) : (3 : DiffRing V) ≤ q * (q * q) * s := by
  have h4 : (4 : DiffRing V) ≤ q * q := by nlinarith
  have h8 : (8 : DiffRing V) ≤ q * (q * q) := by nlinarith
  nlinarith

private theorem scale_bound {Y q : DiffRing V} (hY : 0 ≤ Y) (hq : 1 ≤ q) : 4 * Y ≤ 4 * (Y * q) * q := by
  have h1 : Y ≤ Y * q := le_mul_of_one_le_right hY hq
  have h2 : Y * q ≤ Y * q * q := le_mul_of_one_le_right (le_trans hY h1) hq
  nlinarith

private theorem hk_bound {H M a c k Y : DiffRing V} (hH : H = 3 + 4 * a) (hM : 4 * Y ≤ M)
    (hc : k * Y ≤ c) (ha : 3 ≤ a) (hY : 3 ≤ Y) (hk : 0 < k) : H * k ≤ M * (a * c) := by
  have ha0 : 0 ≤ a := by linarith
  have hY0 : 0 ≤ Y := by linarith
  have h1 : (4 * Y) * (a * (k * Y)) ≤ M * (a * c) :=
    mul_le_mul hM (mul_le_mul_of_nonneg_left hc ha0) (by positivity) (by linarith)
  have hYY : (9 : DiffRing V) ≤ Y * Y := by nlinarith
  have hak : 0 ≤ a * k := by positivity
  have h2 : (4 * Y) * (a * (k * Y)) = 4 * (a * k) * (Y * Y) := by ring
  rw [hH]
  nlinarith

private theorem D0_bound {H k M a c X G S R : DiffRing V} (h : H * k ≤ M * (a * c))
    (hM : 0 ≤ M) (hX : 0 ≤ X) (hH : 0 ≤ H) (hG : 0 ≤ G) (hS : 0 ≤ S) (hR : 0 ≤ R) :
    H * k ≤ M * (X + a * c) + H * (M * G + S * X + R + 1) := by
  have h1 : 0 ≤ M * X := mul_nonneg hM hX
  have h2 : 0 ≤ H * (M * G + S * X + R + 1) := by positivity
  nlinarith

end Bounds

/-- `Nm = 0`: the main Pell root and the carrier relation. -/
theorem main_root (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (hF : v 1 ≤ 1 + (p 0 : V) * (1 + 3 * v 0))
    (hY : (1 + (p 0 : V) * (1 + 3 * v 0)) *
      ((1 + (p 0 : V) * (1 + 3 * v 0)) * (1 + (p 0 : V) * (1 + 3 * v 0))) ∣ v 8)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).Nm v) :
    let q : V := 1 + (p 0 : V) * (1 + 3 * v 0)
    let X : V := q + v 7
    let k : V := v 10 + v 11
    let c : V := v 10 + v 8 * k
    let a : V := v 8 + v 8 * X
    let H : V := 3 + 4 * a
    let Δ : V := H + a * a
    let R : V := (v 2 + ((p 0 : V) * (1 + 3 * v 0)) * (q - v 1)) * (q * q - 1) +
      (1 + 3 * v 0) * ((p 2 : V) + (p 3 : V) * q)
    let S : V := 4 * (v 8 * q)
    let M : V := S * q
    ∃ g : V, g * g = 1 + Δ * (c * c) ∧
      M * g + H * k = M * (X + a * c) + H * (M * v 13 + S * X + R + 1) := by
  intro q X k c a H Δ R S M
  rw [internalZero_iff, Nm_eval, c_Dstar, c_M, c_c, c_a, c_X, c_H, c_k, c_RR p v hF, c_S,
    c_Delta] at hz
  let Dr : DiffRing V := ι M * (ι X + ι a * ι c) +
    ι H * (ι M * ι (v 13) + ι S * ι X + ι R + 1) - ι H * ι k
  have hDr : Dr * Dr = (ι M * ι M) * (1 + ι Δ * (ι c * ι c)) := by
    simp only [Dr]
    linear_combination hz
  -- positivity of D*
  have hq1 : 1 ≤ q := le_self_add
  have hk : (0 : DiffRing V) < ι k := ι_pos' (add_pos (hv 10) (hv 11))
  have hY0 : (0 : DiffRing V) ≤ ι (v 8) := ι_nonneg _
  have hY3 : (3 : DiffRing V) ≤ ι (v 8) := by
    obtain ⟨s, hs⟩ := hY
    have hs0 : 1 ≤ s := by
      rcases (Arithmetic.zero_le s).lt_or_eq with h | h
      · exact pos_iff_one_le.mp h
      · exfalso; rw [← h, mul_zero] at hs; exact (ne_of_gt (hv 8)) hs
    have hq2 : (2 : DiffRing V) ≤ ι q := by
      have h2 : (2 : V) ≤ q := by
        have h1 : 1 ≤ (p 0 : V) * (1 + 3 * v 0) :=
          one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) le_self_add
        simpa [q, one_add_one_eq_two] using (add_le_add_iff_left (1 : V)).mpr h1
      have h := (ι_le_ι (V := V)).mpr h2
      rwa [map_ofNat] at h
    have hs1 : (1 : DiffRing V) ≤ ι s := by simpa using (ι_le_ι (V := V)).mpr hs0
    have he : ι (v 8) = ι q * (ι q * ι q) * ι s := by rw [hs]; simp only [map_mul]; rfl
    rw [he]
    exact cube_bound hq2 hs1
  have ha3 : (3 : DiffRing V) ≤ ι a := by
    have : ι a = ι (v 8) + ι (v 8) * ι X := by simp [a, map_add, map_mul]
    rw [this]; exact le_trans hY3 (le_add_of_nonneg_right (mul_nonneg hY0 (ι_nonneg _)))
  have hc' : ι k * ι (v 8) ≤ ι c := by
    have : ι c = ι (v 10) + ι (v 8) * ι k := by simp [c, k, map_add, map_mul]
    rw [this, mul_comm (ι k)]; exact le_add_of_nonneg_left (ι_nonneg _)
  have hM : 4 * ι (v 8) ≤ ι M := by
    have : ι M = 4 * (ι (v 8) * ι q) * ι q := by simp [M, S, map_mul, map_ofNat]
    have hq1' : (1 : DiffRing V) ≤ ι q := by simpa using (ι_le_ι (V := V)).mpr hq1
    rw [this]; exact scale_bound hY0 hq1'
  have hHk : ι H * ι k ≤ ι M * (ι a * ι c) :=
    hk_bound (by simp [H, map_add, map_mul, map_ofNat]) hM hc' ha3 hY3 hk
  let D0 : V := M * (X + a * c) + H * (M * v 13 + S * X + R + 1)
  have hle : H * k ≤ D0 := by
    apply (ι_le_ι (V := V)).mp
    have : ι D0 = ι M * (ι X + ι a * ι c) + ι H * (ι M * ι (v 13) + ι S * ι X + ι R + 1) := by
      simp [D0, map_add, map_mul]
    rw [this, map_mul]
    exact D0_bound hHk (ι_nonneg M) (ι_nonneg X) (ι_nonneg H) (ι_nonneg (v 13)) (ι_nonneg S) (ι_nonneg R)
  let Ds : V := D0 - H * k
  have cDs : ι Ds = Dr := by
    rw [ι_tsub hle]; simp [D0, Dr, map_add, map_mul]
  have hDsV : Ds * Ds = M * M * (1 + Δ * (c * c)) := by
    apply ι_injective
    simp only [map_mul, map_add, map_one, cDs]
    rw [hDr]
  have hMpos : 0 < M := by
    apply (ι_lt_ι (V := V)).mp; simp only [map_zero]
    exact lt_of_lt_of_le (by linarith) hM
  obtain ⟨g, hg, hgg⟩ := scaled_quotient M Ds (1 + Δ * (c * c)) hMpos hDsV
  refine ⟨g, hgg, ?_⟩
  rw [← hg]
  exact tsub_add_cancel_of_le hle

end P65Root

#print axioms P65Root.strong
#print axioms P65Root.first_root
#print axioms P65Root.transport
#print axioms P65Root.aux_norm
#print axioms P65Root.main_root
