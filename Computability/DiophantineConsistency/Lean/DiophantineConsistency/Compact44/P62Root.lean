import DiophantineConsistency.Compact44.P62Units
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011

/-! # Package 62: the factors in a model

After the unit guard (`P62Units.units`), at a positive valuation of a model of
`𝗜𝚺₁`:

* `transport`: `Nt = 1` gives `F + α < q` and `(K0 + w)C + q = 1 + F + z(q−1)`.
  If `C ≤ 0`, then `Nt ≤ (q − F) − z(q−1) ≤ 0`;
* `strong`: `Ns = 1` is `I² = Δ(f²−1)`, the ordinary strong norm;
* `main_root`: `Nmain = 0` gives the main Pell root `g` with
  `U·g + H·k = U(X + ac) + H(Uγ + R + 1)` for `U = 4q⁴`;
* `two_root`: `N = 0` restores both roots. The identity
  `N = (d(x²+A) − E)² − 4d²x²A` makes `(d(x²+A) − E)/(2dx)` a rational square
  root of `A`, hence an integer `±τ`. Then `E = d(x ∓ τ)²`, which is the
  auxiliary norm `QV² + y² = 1 + Qy²` with `y = |x ∓ τ| > 0`, and `τ²` is the
  first Pell norm. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P62Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticAdaptiveQuotients2011 P62Graph P62Units
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem ι_pos' {x : V} (h : 0 < x) : (0 : DiffRing V) < ι x := by
  simpa using (ι_lt_ι (V := V)).mpr h

private theorem ι_one_le {x : V} (h : 0 < x) : (1 : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)

section Values
variable (p : Fin 4 → ℕ) (v : Fin 13 → V)

def RV : V := ((p 0 : V) * v 0 * (qV p v - v 1) + v 2) * (qV p v * qV p v - 1) +
  ((p 2 : V) + qV p v * (p 3 : V)) * v 0

theorem c_qm : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qm = ι ((p 0 : V) * v 0) := by
  simp only [vals, map_mul, cast_nat]

theorem c_RR (hF : v 1 ≤ qV p v) :
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR = ι (RV p v) := by
  have hq1 : 1 ≤ qV p v * qV p v := one_le_mul_of_one_le_of_one_le le_add_self le_add_self
  have e1 : ι (qV p v - v 1) = ι (qV p v) - ι (v 1) := ι_tsub hF
  have e2 : ι (qV p v * qV p v - 1) = ι (qV p v) * ι (qV p v) - 1 := by
    rw [ι_tsub hq1, map_mul, map_one]
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR =
      ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qm *
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1)) + ι (v 2)) *
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - 1) +
      (((p 2 : ℕ) : ℤ) + (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q * (((p 3 : ℕ) : ℤ) : DiffRing V)) * ι (v 0)
    from rfl, c_qm, c_q]
  simp only [RV, map_add, map_mul, e1, e2, cast_nat]

end Values

/-- `Nt = 1`: the positive gap and the transport identity. -/
theorem transport (p : Fin 4 → ℕ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hNt : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nt = 1) :
    v 1 + v 2 < qV p v ∧
      ((p 1 : V) + v 8) * (qV p v - (v 1 + v 2)) + qV p v = 1 + v 1 + v 3 * ((p 0 : V) * v 0) := by
  have e : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nt =
      (((((p 1 : ℕ) : ℤ) : DiffRing V) + ι (v 8)) *
          (((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1)) - ι (v 2)) +
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1))) -
      ι (v 3) * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qm := rfl
  rw [e, c_q, c_qm, cast_nat] at hNt
  have hqq : ι (qV p v) = ι ((p 0 : V) * v 0) + 1 := by simp [qV, map_add]
  have hF : (1 : DiffRing V) ≤ ι (v 1) := ι_one_le (hv 1)
  have hz : (1 : DiffRing V) ≤ ι (v 3) := ι_one_le (hv 3)
  have hb : (0 : DiffRing V) ≤ ι ((p 0 : V) * v 0) := ι_nonneg _
  have hKw : (0 : DiffRing V) ≤ ι (p 1 : V) + ι (v 8) := add_nonneg (ι_nonneg _) (ι_nonneg _)
  set Cr : DiffRing V := ι (qV p v) - ι (v 1) - ι (v 2) with hCr
  have hC : 0 < Cr := by
    by_contra hneg
    have hle : Cr ≤ 0 := le_of_not_gt hneg
    have h1 : (ι (p 1 : V) + ι (v 8)) * Cr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKw hle
    have h2 : ι ((p 0 : V) * v 0) ≤ ι (v 3) * ι ((p 0 : V) * v 0) := le_mul_of_one_le_left hb hz
    linarith
  have hlt : v 1 + v 2 < qV p v := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_add]; linarith
  refine ⟨hlt, ?_⟩
  apply ι_injective
  rw [map_add, map_mul, ι_tsub (le_of_lt hlt)]
  simp only [Cr, map_add, map_mul, map_one] at hNt ⊢
  linear_combination hNt

/-- `Ns = 1`: the ordinary strong norm, in the form `(ic²)² + Δ = Δf²`. -/
theorem strong (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hNs : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Ns = 1) :
    (v 5 * (cV p v * cV p v)) * (v 5 * (cV p v * cV p v)) + ΔV p v = ΔV p v * (v 4 * v 4) := by
  have e : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Ns =
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I -
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Q - 1) := rfl
  have eQ : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Q =
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta * (ι (v 4) * ι (v 4) - 1) := rfl
  rw [e, eQ, c_I, c_Delta] at hNs
  apply ι_injective
  simp only [IV, map_add, map_mul] at hNs ⊢
  linear_combination hNs

section Bounds

private theorem hk_bound {H U a c k : DiffRing V} (hH : H = 4 * a + 3) (hU : 64 ≤ U)
    (hc : k ≤ c) (ha : 1 ≤ a) (hk : 0 < k) : H * k ≤ U * (a * c) := by
  have ha0 : 0 ≤ a := by linarith
  have h1 : 64 * (a * k) ≤ U * (a * c) :=
    mul_le_mul hU (mul_le_mul_of_nonneg_left hc ha0) (by positivity) (by linarith)
  have hak : 0 ≤ a * k := by positivity
  rw [hH]
  nlinarith

private theorem D0_bound {H k U a c X G R : DiffRing V} (h : H * k ≤ U * (a * c))
    (hU : 0 ≤ U) (hX : 0 ≤ X) (hH : 0 ≤ H) (hG : 0 ≤ G) (hR : 0 ≤ R) :
    H * k ≤ U * (X + a * c) + H * (U * G + R + 1) := by
  have h1 : 0 ≤ U * X := mul_nonneg hU hX
  have h2 : 0 ≤ H * (U * G + R + 1) := by positivity
  nlinarith

end Bounds

/-- `Nmain = 0`: the main Pell root and the carrier relation, for `U = 4q⁴`. -/
theorem main_root (p : Fin 4 → ℕ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (hF : v 1 ≤ qV p v)
    (hz : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nmain = 0) :
    ∃ g : V, g * g = ΔV p v * (cV p v * cV p v) + 1 ∧
      UV p v * g + HV p v * kV v =
        UV p v * (XV p v + aV p v * cV p v) + HV p v * (UV p v * v 11 + RV p v + 1) := by
  have eN : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nmain =
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Dstar * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Dstar -
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U) *
        ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta *
          ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c) + 1) := rfl
  have eD : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Dstar =
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U *
          ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).X +
            (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).a * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c) +
        (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).H *
          ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U * ι (v 11) -
            (((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).k - (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR) - 1)) := rfl
  rw [eN, eD, c_U, c_X, c_a, c_c, c_H, c_k, c_RR p v hF, c_Delta] at hz
  set U := UV p v
  set X := XV p v
  set a := aV p v
  set c := cV p v
  set H := HV p v
  set k := kV v
  set R := RV p v
  set Δ := ΔV p v
  let Dr : DiffRing V := ι U * (ι X + ι a * ι c) + ι H * (ι U * ι (v 11) + ι R + 1) - ι H * ι k
  have hDr : Dr * Dr = (ι U * ι U) * (ι Δ * (ι c * ι c) + 1) := by
    simp only [Dr]; linear_combination hz
  -- positivity of D*
  have hk : (0 : DiffRing V) < ι k := ι_pos' (add_pos (hv 9) (hv 10))
  have hq2 : (2 : V) ≤ qV p v := by
    have h1 : 1 ≤ (p 0 : V) * v 0 :=
      one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
    simpa [qV, one_add_one_eq_two] using (add_le_add_iff_right (1 : V)).mpr h1
  have hU64 : (64 : DiffRing V) ≤ ι U := by
    have h4 : (4 : V) ≤ qV p v * qV p v := by
      calc (4 : V) = 2 * 2 := by norm_num
        _ ≤ qV p v * qV p v := mul_le_mul hq2 hq2 (by norm_num) (Arithmetic.zero_le _)
    have h64 : (64 : V) ≤ U := by
      show (64 : V) ≤ 4 * ((qV p v * qV p v) * (qV p v * qV p v))
      calc (64 : V) = 4 * (4 * 4) := by norm_num
        _ ≤ 4 * ((qV p v * qV p v) * (qV p v * qV p v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h4 h4 (by norm_num) (Arithmetic.zero_le _)) (by norm_num)
    have h := (ι_le_ι (V := V)).mpr h64; rwa [map_ofNat] at h
  have ha1 : (1 : DiffRing V) ≤ ι a := by
    have : (1 : V) ≤ a := by
      show 1 ≤ EV p v + YV p v
      exact le_trans (pos_iff_one_le.mp (mul_pos (hv 7) (mul_pos (mul_pos (lt_of_lt_of_le (by norm_num) hq2)
        (lt_of_lt_of_le (by norm_num) hq2)) (lt_of_lt_of_le (by norm_num) hq2)))) le_add_self
    simpa using (ι_le_ι (V := V)).mpr this
  have hkc : ι k ≤ ι c := by
    apply (ι_le_ι (V := V)).mpr
    show kV v ≤ kV v * YV p v + v 9
    exact le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _)
      (pos_iff_one_le.mp (mul_pos (hv 7) (mul_pos (mul_pos (lt_of_lt_of_le (by norm_num) hq2)
        (lt_of_lt_of_le (by norm_num) hq2)) (lt_of_lt_of_le (by norm_num) hq2))))) le_self_add
  have hHk : ι H * ι k ≤ ι U * (ι a * ι c) :=
    hk_bound (by simp only [H, HV, map_add, map_mul, map_ofNat]; rfl) hU64 hkc ha1 hk
  let D0 : V := U * (X + a * c) + H * (U * v 11 + R + 1)
  have hle : H * k ≤ D0 := by
    apply (ι_le_ι (V := V)).mp
    have : ι D0 = ι U * (ι X + ι a * ι c) + ι H * (ι U * ι (v 11) + ι R + 1) := by
      simp [D0, map_add, map_mul]
    rw [this, map_mul]
    exact D0_bound hHk (ι_nonneg U) (ι_nonneg X) (ι_nonneg H) (ι_nonneg (v 11)) (ι_nonneg R)
  let Ds : V := D0 - H * k
  have cDs : ι Ds = Dr := by
    rw [ι_tsub hle]; simp [D0, Dr, map_add, map_mul]
  have hDsV : Ds * Ds = U * U * (Δ * (c * c) + 1) := by
    apply ι_injective
    simp only [map_mul, map_add, map_one, cDs]
    rw [hDr]
  have hUpos : 0 < U := (ι_lt_ι (V := V)).mp (by simpa using lt_of_lt_of_le (by norm_num) hU64)
  obtain ⟨g, hg, hgg⟩ := scaled_quotient U Ds (Δ * (c * c) + 1) hUpos hDsV
  refine ⟨g, hgg, ?_⟩
  rw [← hg]
  exact tsub_add_cancel_of_le hle

/-- `Ns = 1` and `N = 0` restore the first root `τ` and the auxiliary ordinate `y`. -/
theorem two_root (p : Fin 4 → ℕ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j) (hF : v 1 ≤ qV p v)
    (hNs : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Ns = 1)
    (hN : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).N = 0) :
    ∃ τ y : V, τ * τ = ellV p v * (ellV p v + kV v) + 1 ∧ 0 < y ∧
      (IV p v * IV p v) * absdiff (cV p v * v 6 * v 4) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (cV p v * v 6 * v 4) (v 4 * v 4 * RV p v + cV p v) + y * y =
        1 + (IV p v * IV p v) * y * y := by
  set W := vals (fun j => (p j : ℤ)) (fun j => ι (v j)) with hW
  -- Q = I²
  have eNs : W.Ns = W.I * W.I - (W.Q - 1) := rfl
  have hQ : W.Q = ι (IV p v) * ι (IV p v) := by rw [← c_I]; linear_combination -(eNs.symm.trans hNs)
  -- the registers as model values
  set I := IV p v
  have hc9 : 9 ≤ cV p v * cV p v := by
    have hc3 : (3 : V) ≤ cV p v := by
      show 3 ≤ kV v * YV p v + v 9
      have hk2 : 2 ≤ kV v := by
        simpa [kV, one_add_one_eq_two] using add_le_add (pos_iff_one_le.mp (hv 9)) (pos_iff_one_le.mp (hv 10))
      calc (3 : V) = 2 * 1 + 1 := by norm_num
        _ ≤ kV v * YV p v + v 9 := add_le_add (mul_le_mul hk2
            (pos_iff_one_le.mp (mul_pos (hv 7) (mul_pos (mul_pos (lt_of_lt_of_le (by simp) le_add_self)
              (lt_of_lt_of_le (by simp) le_add_self)) (lt_of_lt_of_le (by simp) le_add_self))))
            (by norm_num) (Arithmetic.zero_le _)) (pos_iff_one_le.mp (hv 9))
    calc (9 : V) = 3 * 3 := by norm_num
      _ ≤ cV p v * cV p v := mul_le_mul hc3 hc3 (by norm_num) (Arithmetic.zero_le _)
  have hI9 : 9 ≤ I := by
    show 9 ≤ v 5 * (cV p v * cV p v)
    exact le_trans hc9 (le_mul_of_one_le_left (Arithmetic.zero_le _) (pos_iff_one_le.mp (hv 5)))
  have hII : 1 ≤ I * I := one_le_mul_of_one_le_of_one_le (le_trans (by norm_num) hI9) (le_trans (by norm_num) hI9)
  set dV : V := I * I - 1 with hdV
  have hd : W.d = ι dV := by
    rw [show W.d = W.Q - 1 from rfl, hQ, hdV, ι_tsub hII, map_mul, map_one]
  have hd0 : 0 < dV := by
    apply tsub_pos_of_lt
    calc (1 : V) < 9 := by norm_num
      _ ≤ I := hI9
      _ ≤ I * I := le_mul_of_one_le_left (Arithmetic.zero_le _) (le_trans (by norm_num) hI9)
  set xV : V := v 12 + ellV p v with hxV
  have hx : W.x = ι xV := by
    rw [show W.x = ι (v 12) + W.ell from rfl, c_ell, hxV, map_add]
  have hA : W.A1 = ι (A1V p v) := c_A1 p v
  set Lv : V := cV p v * v 6 * v 4
  set Nv : V := v 4 * v 4 * RV p v + cV p v
  have hVv : W.V = ι Lv - ι Nv := by
    rw [show W.V = W.c * (ι (v 6) * ι (v 4) - 1) - W.RR * (ι (v 4) * ι (v 4)) from rfl, c_c, c_RR p v hF]
    simp only [Lv, Nv, map_add, map_mul]; ring
  set zV : V := absdiff Lv Nv with hzV
  have hzsq : W.V * W.V = ι zV * ι zV := by rw [hVv, ι_absdiff_sq]
  have hE : W.Eaux = ι (I * I) * (ι zV * ι zV) - 1 := by
    rw [show W.Eaux = W.Q * (W.V * W.V) - 1 from rfl, hQ, hzsq, map_mul]
  -- the centered identity
  have eN : W.N = (W.d * (W.x * W.x - W.A1) - W.Eaux) * (W.d * (W.x * W.x - W.A1) - W.Eaux) -
      4 * ((W.d * W.A1) * W.Eaux) := rfl
  set Ar : DiffRing V := ι (A1V p v)
  have hid : (W.d * (W.x * W.x + W.A1) - W.Eaux) * (W.d * (W.x * W.x + W.A1) - W.Eaux) =
      (2 * W.d * W.x) * (2 * W.d * W.x) * W.A1 := by
    rw [eN] at hN; linear_combination hN
  rw [hd, hx, hA] at hid
  -- the rational root
  obtain ⟨P1, P2, hP⟩ := exists_mk (ι dV * (ι xV * ι xV + Ar) - W.Eaux)
  rw [mk_eq_sub] at hP
  have hPsq : absdiff P1 P2 * absdiff P1 P2 = (2 * dV * xV) * (2 * dV * xV) * A1V p v := by
    apply ι_injective
    rw [map_mul, ι_absdiff_sq, ← hP]
    simp only [map_mul, map_ofNat]
    linear_combination hid
  have hx0 : 0 < xV := add_pos_of_pos_of_nonneg (hv 12) (Arithmetic.zero_le _)
  have hm0 : 0 < 2 * dV * xV := mul_pos (mul_pos (by norm_num) hd0) hx0
  obtain ⟨τ, hτ, hττ⟩ := scaled_quotient (2 * dV * xV) (absdiff P1 P2) (A1V p v) hm0 hPsq
  have hA1 : A1V p v = ellV p v * (ellV p v + kV v) + 1 := rfl
  -- E = d·y²
  have hyE : ∃ y : V, W.Eaux = ι dV * (ι y * ι y) := by
    have hAt : Ar = ι τ * ι τ := by rw [← map_mul, hττ]
    rcases le_total P2 P1 with hle | hle
    · refine ⟨absdiff xV τ, ?_⟩
      have hpos : ι (absdiff P1 P2) = ι P1 - ι P2 := by
        rw [show absdiff P1 P2 = P1 - P2 by simp [absdiff, tsub_eq_zero_of_le hle], ι_tsub hle]
      have h' : ι dV * (ι xV * ι xV + Ar) - W.Eaux = ι (2 * dV * xV * τ) :=
        hP.trans (hpos.symm.trans (congrArg ι hτ))
      simp only [map_mul, map_ofNat] at h'
      rw [hAt] at h'
      rw [ι_absdiff_sq]
      linear_combination -h'
    · refine ⟨xV + τ, ?_⟩
      have hneg : ι (absdiff P1 P2) = ι P2 - ι P1 := by
        rw [show absdiff P1 P2 = P2 - P1 by simp [absdiff, tsub_eq_zero_of_le hle], ι_tsub hle]
      have h0 : ι P2 - ι P1 = ι (2 * dV * xV * τ) := hneg.symm.trans (congrArg ι hτ)
      have h' : ι dV * (ι xV * ι xV + Ar) - W.Eaux = -ι (2 * dV * xV * τ) := by
        rw [hP]; linear_combination -h0
      simp only [map_mul, map_ofNat] at h'
      rw [hAt] at h'
      simp only [map_add]
      linear_combination -h'
  obtain ⟨y, hy⟩ := hyE
  -- the auxiliary norm
  have haux : (I * I) * zV * zV + y * y = 1 + (I * I) * y * y := by
    apply ι_injective
    rw [hE, hdV, ι_tsub hII, map_mul, map_one] at hy
    simp only [map_add, map_mul, map_one]
    linear_combination hy
  have hy0 : 0 < y := by
    rcases (Arithmetic.zero_le y).lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 : (I * I) * zV * zV = 1 := by
        have h2 := haux
        rw [← h] at h2
        simp only [mul_zero, add_zero] at h2
        exact h2
      have hd1 : I * I ∣ (1 : V) := ⟨zV * zV, by rw [← h1]; ring⟩
      have hle : I * I ≤ 1 := Arithmetic.le_of_dvd (by simp) hd1
      exact absurd hle (not_le_of_gt (lt_of_lt_of_le (by norm_num) (le_trans hI9
        (le_mul_of_one_le_left (Arithmetic.zero_le _) (le_trans (by norm_num) hI9)))))
  exact ⟨τ, y, hττ.trans hA1, hy0, by simpa only [mul_assoc] using haux⟩

end P62Root

#print axioms P62Root.transport
#print axioms P62Root.strong
#print axioms P62Root.main_root
#print axioms P62Root.two_root
