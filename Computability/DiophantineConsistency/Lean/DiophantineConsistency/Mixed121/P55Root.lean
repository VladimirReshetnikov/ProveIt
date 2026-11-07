import DiophantineConsistency.Mixed121.P55Graph
import DiophantineConsistency.Compact44.P72Aux
import DiophantineConsistency.ArithmeticAdaptiveQuotients2011

/-! # Package 55's degree-52 equation: the residuals in a model

Write `q = βJ + 1`, `X = wq`, `Y = sq³`, `k = η + ζ`, `c = kY + η`,
`a = XY + Y`, `H = 4a + 3`, `Δ = a² + H`, `ℓ = XY·kY` and `U = 4q⁴`. In every
model of `𝗜𝚺₁`, at a positive valuation:

* `transport`: `Nt = 1` gives `F + α < q` and `(K0 + w)C + q = 1 + F + z(q−1)`,
  where `C = q − (F + α)`. This is `P62Root.transport`;
* `first`: `N0 = 1` is the first Pell norm `τ² = ℓ(ℓ + k) + 1`;
* `strong`: `W = 0` is the ordinary strong norm `(ic²)² + Δ = Δf²`;
* `aux_norm`: `Na = 1` is the auxiliary norm in the absolute-difference form
  of `P72Exact`. This is `P64Root.aux_norm`;
* `main_root`: `M = 0` gives the main Pell root `g`, with
  `U·g + H·k = U(X + ac) + H(Uγ + R + 1)` for `U = 4q⁴`. This is
  `P62Root.main_root`.

The ports enter only through `p : Fin 4 → ℕ` and `0 < β`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P55Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveQuotients2011 P55Graph
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem ι_pos' {x : V} (h : 0 < x) : (0 : DiffRing V) < ι x := by
  simpa using (ι_lt_ι (V := V)).mpr h

private theorem ι_one_le {x : V} (h : 0 < x) : (1 : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)

section Values
variable (p : Fin 4 → ℕ) (v : Fin 14 → V)

def qV : V := (p 0 : V) * v 0 + 1
def XV : V := v 8 * qV p v
def YV : V := v 7 * ((qV p v * qV p v) * qV p v)
def EV : V := XV p v * YV p v
def kV : V := v 10 + v 11
def cV : V := kV v * YV p v + v 10
def aV : V := EV p v + YV p v
def HV : V := 4 * aV p v + 3
def ΔV : V := aV p v * aV p v + HV p v
def ellV : V := EV p v * (kV v * YV p v)
def UV : V := 4 * ((qV p v * qV p v) * (qV p v * qV p v))
def RV : V := ((p 0 : V) * v 0 * (qV p v - v 1) + v 2) * (qV p v * qV p v - 1) +
  ((p 2 : V) + qV p v * (p 3 : V)) * v 0

theorem cast_nat (n : ℕ) : (((n : ℤ)) : DiffRing V) = ι (n : V) := by
  rw [Int.cast_natCast, map_natCast]

theorem c_qm : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qm = ι ((p 0 : V) * v 0) := by
  simp only [vals, map_mul, cast_nat]
theorem c_q : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q = ι (qV p v) := by
  simp only [vals, qV, map_add, map_mul, map_one, cast_nat]
theorem c_X : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).X = ι (XV p v) := by
  simp only [vals, XV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_Y : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Y = ι (YV p v) := by
  simp only [vals, YV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_k : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).k = ι (kV v) := by
  simp only [vals, kV, map_add]
theorem c_c : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c = ι (cV p v) := by
  simp only [vals, cV, kV, YV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_a : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).a = ι (aV p v) := by
  simp only [vals, aV, EV, XV, YV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_H : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).H = ι (HV p v) := by
  simp only [vals, HV, aV, EV, XV, YV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]
theorem c_Delta : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta = ι (ΔV p v) := by
  simp only [vals, ΔV, HV, aV, EV, XV, YV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]
theorem c_ell : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).ell = ι (ellV p v) := by
  simp only [vals, ellV, EV, XV, YV, kV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_U : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U = ι (UV p v) := by
  simp only [vals, UV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_C : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).C =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1) - ι (v 2) := rfl
theorem c_qF : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qF =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1) := rfl
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
theorem transport (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hNt : (graph (fun j => (p j : ℤ))).Nt.evalRing (fun j => ι (v j)) = 1) :
    v 1 + v 2 < qV p v ∧
      ((p 1 : V) + v 8) * (qV p v - (v 1 + v 2)) + qV p v = 1 + v 1 + v 3 * ((p 0 : V) * v 0) := by
  rw [Nt_eval, c_C, c_qF, c_q, c_qm, cast_nat] at hNt
  have hF : (1 : DiffRing V) ≤ ι (v 1) := ι_one_le (hv 1)
  have hz : (1 : DiffRing V) ≤ ι (v 3) := ι_one_le (hv 3)
  have hb : (0 : DiffRing V) ≤ ι ((p 0 : V) * v 0) := ι_nonneg _
  have hKw : (0 : DiffRing V) ≤ ι (p 1 : V) + ι (v 8) := add_nonneg (ι_nonneg _) (ι_nonneg _)
  have hqq : ι (qV p v) = ι ((p 0 : V) * v 0) + 1 := by simp [qV, map_add]
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

/-- `N0 = 1`: the first Pell norm. -/
theorem first (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hN0 : (graph (fun j => (p j : ℤ))).N0.evalRing (fun j => ι (v j)) = 1) :
    v 9 * v 9 = ellV p v * (ellV p v + kV v) + 1 := by
  rw [N0_eval, c_ell, c_k] at hN0
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  linear_combination hN0

/-- `W = 0`: the ordinary strong norm. -/
theorem strong (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).W v) :
    (v 5 * (cV p v * cV p v)) * (v 5 * (cV p v * cV p v)) + ΔV p v = ΔV p v * (v 4 * v 4) := by
  rw [internalZero_iff, W_eval, c_Aaux, c_Delta, c_c] at hz
  apply ι_injective
  simp only [map_add, map_mul]
  linear_combination hz

/-- `Na = 1`: the auxiliary norm, in the absolute-difference form of `P72Exact`. -/
theorem aux_norm (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hF : v 1 ≤ qV p v) (hf : 0 < v 4)
    (hz : (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) = 1) :
    ((3 + 4 * aV p v) + aV p v * aV p v) * (v 4 * v 4 - 1) *
        (absdiff (v 4 * v 4 * (v 6 * cV p v)) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (v 4 * v 4 * (v 6 * cV p v)) (v 4 * v 4 * RV p v + cV p v)) +
        absdiff (v 4 * v 4 * (v 6 * cV p v) + v 12) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (v 4 * v 4 * (v 6 * cV p v) + v 12) (v 4 * v 4 * RV p v + cV p v) =
      1 + ((3 + 4 * aV p v) + aV p v * aV p v) * (v 4 * v 4 - 1) *
        (absdiff (v 4 * v 4 * (v 6 * cV p v) + v 12) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (v 4 * v 4 * (v 6 * cV p v) + v 12) (v 4 * v 4 * RV p v + cV p v)) := by
  rw [Na_eval, c_y, c_V, c_Aaux, c_RR p v hF, c_Delta, c_c] at hz
  have hf1 : 1 ≤ v 4 * v 4 :=
    one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  apply ι_injective
  simp only [map_add, map_mul, map_one, ι_tsub hf1, map_one]
  rw [ι_absdiff_sq, ι_absdiff_sq]
  simp only [ΔV, HV] at hz
  simp only [map_add, map_mul, map_ofNat, map_one] at hz ⊢
  linear_combination hz

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

/-- `M = 0`: the main Pell root and the carrier relation, for `U = 4q⁴`. -/
theorem main_root (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j) (hb : 0 < (p 0 : V))
    (hF : v 1 ≤ qV p v)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).M v) :
    ∃ g : V, g * g = ΔV p v * (cV p v * cV p v) + 1 ∧
      UV p v * g + HV p v * kV v =
        UV p v * (XV p v + aV p v * cV p v) + HV p v * (UV p v * v 13 + RV p v + 1) := by
  rw [internalZero_iff, M_eval, c_Dstar, c_U, c_X, c_a, c_c, c_H, c_k, c_RR p v hF, c_Delta] at hz
  set U := UV p v
  set X := XV p v
  set a := aV p v
  set c := cV p v
  set H := HV p v
  set k := kV v
  set R := RV p v
  set Δ := ΔV p v
  let Dr : DiffRing V := ι U * (ι X + ι a * ι c) + ι H * (ι U * ι (v 13) + ι R + 1) - ι H * ι k
  have hDr : Dr * Dr = (ι U * ι U) * (ι Δ * (ι c * ι c) + 1) := by
    simp only [Dr]; linear_combination hz
  -- positivity of D*
  have hk : (0 : DiffRing V) < ι k := ι_pos' (add_pos (hv 10) (hv 11))
  have hq2 : (2 : V) ≤ qV p v := by
    have h1 : 1 ≤ (p 0 : V) * v 0 :=
      one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hb) (pos_iff_one_le.mp (hv 0))
    simpa [qV, one_add_one_eq_two] using (add_le_add_iff_right (1 : V)).mpr h1
  have hq0 : 0 < qV p v := lt_of_lt_of_le (by norm_num) hq2
  have hY0 : 0 < YV p v := mul_pos (hv 7) (mul_pos (mul_pos hq0 hq0) hq0)
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
      exact le_trans (pos_iff_one_le.mp hY0) le_add_self
    simpa using (ι_le_ι (V := V)).mpr this
  have hkc : ι k ≤ ι c := by
    apply (ι_le_ι (V := V)).mpr
    show kV v ≤ kV v * YV p v + v 10
    exact le_trans (le_mul_of_one_le_right (Arithmetic.zero_le _) (pos_iff_one_le.mp hY0)) le_self_add
  have hHk : ι H * ι k ≤ ι U * (ι a * ι c) :=
    hk_bound (by simp only [H, HV, map_add, map_mul, map_ofNat]; rfl) hU64 hkc ha1 hk
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
  have hUpos : 0 < U := (ι_lt_ι (V := V)).mp (by simpa using lt_of_lt_of_le (by norm_num) hU64)
  obtain ⟨g, hg, hgg⟩ := scaled_quotient U Ds (Δ * (c * c) + 1) hUpos hDsV
  refine ⟨g, hgg, ?_⟩
  rw [← hg]
  exact tsub_add_cancel_of_le hle

end P55Root

#print axioms P55Root.transport
#print axioms P55Root.first
#print axioms P55Root.strong
#print axioms P55Root.aux_norm
#print axioms P55Root.main_root
