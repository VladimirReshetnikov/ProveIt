import DiophantineConsistency.Mixed121.Short15Graph
import DiophantineConsistency.Mixed121.P55Root
import DiophantineConsistency.ModelArithmetic

/-! # The fifteen-positive residuals in a model of `𝗜𝚺₁`

The registers of `Short15Graph`, read at a positive valuation `v : Fin 15 → V`
of a model of `𝗜𝚺₁` and the natural ports `p`, are the model values `qV`, `XV`,
`YV`, `EV`, `kV`, `cV`, `aV`, `HV`, `ΔV`, `ellV`, `RV` and `DV` (the rank `RV`
once `F ≤ q`). Each residual condition is then a model relation:

* `transport_pos`: `Nt = 1` gives `F + α < q` and the transport identity
  (as `P55Root.transport`); `transport_neg`: `Nt = −1` gives `F + α ≤ q`
  once `0 < K0`;
* `first`: `N0 = 1` is `τ² = ℓ(ℓ + k) + 1`; `main`: `N1 = 1` is
  `D² = ΔC² + 1`, so the main Pell root is `D` itself;
* `strong`: `S = 0` is the ordinary strong norm; `normalized`: the normalized
  strong norm gives the ordinary one at index `Δi`;
* `aux_free`, `aux_gap`, `aux_old`: `Na = 1` in the absolute-difference forms,
  for a free partner, for `y = V + e`, and for the old ordinate;
* `index_pos` / `index_neg`: `Nk = ±1` is `k = R + 1 + hE` / `k + 1 = R + hE`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Short15Root
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs ArithmeticPellRecurrence
open Short15Graph
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem ι_pos' {x : V} (h : 0 < x) : (0 : DiffRing V) < ι x := by
  simpa using (ι_lt_ι (V := V)).mpr h

theorem ι_one_le {x : V} (h : 0 < x) : (1 : DiffRing V) ≤ ι x := by
  simpa using (ι_le_ι (V := V)).mpr (pos_iff_one_le.mp h)

section Values
variable (p : Fin 4 → ℕ) (v : Fin 15 → V)

def qV : V := (p 0 : V) * v 0 + 1
def XV : V := v 9 * qV p v
def YV : V := v 8 * ((qV p v * qV p v) * qV p v)
def EV : V := XV p v * YV p v
def kV : V := v 11 + v 12
def cV : V := kV v * YV p v + v 11
def aV : V := EV p v + YV p v
def HV : V := 4 * aV p v + 3
def ΔV : V := aV p v * aV p v + HV p v
def ellV : V := EV p v * (kV v * YV p v)
def RV : V := ((p 0 : V) * v 0 * (qV p v - v 1) + v 2) * (qV p v * qV p v - 1) +
  ((p 2 : V) + qV p v * (p 3 : V)) * v 0
def DV : V := XV p v + aV p v * cV p v + v 14 * HV p v

theorem ΔV_eq : ΔV p v = delta (aV p v) := by unfold ΔV HV delta; ring

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
theorem c_E : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).E = ι (EV p v) := by
  simp only [vals, EV, XV, YV, qV, map_add, map_mul, map_one, cast_nat]
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
theorem c_D : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).D = ι (DV p v) := by
  simp only [vals, DV, XV, aV, cV, HV, EV, YV, kV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]

theorem c_C : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).C =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1) - ι (v 2) := rfl
theorem c_qF : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).qF =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).q - ι (v 1) := rfl
theorem c_Aaux : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta * (ι (v 4) * ι (v 4) - 1) := rfl
theorem c_Vn : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Vn =
    (ι (v 4) * ι (v 4)) * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c * ι (v 7) -
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR) - (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c :=
  rfl
theorem c_Vo : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Vo =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c * (ι (v 7) * ι (v 4) - 1) -
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).RR * (ι (v 4) * ι (v 4)) := rfl

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
theorem transport_pos (p : Fin 4 → ℕ) (v : Fin 15 → V) (hv : ∀ j, 0 < v j)
    (hNt : rNt (fun j => (p j : ℤ)) (fun j => ι (v j)) = 1) :
    v 1 + v 2 < qV p v ∧
      ((p 1 : V) + v 9) * (qV p v - (v 1 + v 2)) + qV p v = 1 + v 1 + v 3 * ((p 0 : V) * v 0) := by
  rw [rNt, c_C, c_qF, c_q, c_qm, cast_nat] at hNt
  have hz : (1 : DiffRing V) ≤ ι (v 3) := ι_one_le (hv 3)
  have hb : (0 : DiffRing V) ≤ ι ((p 0 : V) * v 0) := ι_nonneg _
  have hKw : (0 : DiffRing V) ≤ ι (p 1 : V) + ι (v 9) := add_nonneg (ι_nonneg _) (ι_nonneg _)
  have hqq : ι (qV p v) = ι ((p 0 : V) * v 0) + 1 := by simp [qV, map_add]
  set Cr : DiffRing V := ι (qV p v) - ι (v 1) - ι (v 2) with hCr
  have hC : 0 < Cr := by
    by_contra hneg
    have hle : Cr ≤ 0 := le_of_not_gt hneg
    have h1 : (ι (p 1 : V) + ι (v 9)) * Cr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hKw hle
    have h2 : ι ((p 0 : V) * v 0) ≤ ι (v 3) * ι ((p 0 : V) * v 0) := le_mul_of_one_le_left hb hz
    have hF : (1 : DiffRing V) ≤ ι (v 1) := ι_one_le (hv 1)
    linarith
  have hlt : v 1 + v 2 < qV p v := by
    apply (ι_lt_ι (V := V)).mp
    rw [map_add]; linarith
  refine ⟨hlt, ?_⟩
  apply ι_injective
  rw [map_add, map_mul, ι_tsub (le_of_lt hlt)]
  simp only [Cr, map_add, map_mul, map_one] at hNt ⊢
  linear_combination hNt

/-- `Nt = −1` with `0 < K0`: still `F + α ≤ q`. -/
theorem transport_neg (p : Fin 4 → ℕ) (v : Fin 15 → V) (hv : ∀ j, 0 < v j) (hK : 0 < (p 1 : V))
    (hNt : rNt (fun j => (p j : ℤ)) (fun j => ι (v j)) = -1) :
    v 1 + v 2 ≤ qV p v := by
  rw [rNt, c_C, c_qF, c_q, c_qm, cast_nat] at hNt
  have hz : (1 : DiffRing V) ≤ ι (v 3) := ι_one_le (hv 3)
  have hb : (0 : DiffRing V) ≤ ι ((p 0 : V) * v 0) := ι_nonneg _
  have hK1 : (1 : DiffRing V) ≤ ι (p 1 : V) := ι_one_le hK
  have hw1 : (1 : DiffRing V) ≤ ι (v 9) := ι_one_le (hv 9)
  have hF : (1 : DiffRing V) ≤ ι (v 1) := ι_one_le (hv 1)
  have hqq : ι (qV p v) = ι ((p 0 : V) * v 0) + 1 := by simp [qV, map_add]
  set Cr : DiffRing V := ι (qV p v) - ι (v 1) - ι (v 2) with hCr
  have hC : 0 ≤ Cr := by
    by_contra hneg
    have hlt : Cr < 0 := lt_of_not_ge hneg
    have hC1 : 1 ≤ -Cr := ModelArithmetic.model_discrete _ (by linarith)
    have h1 : (ι (p 1 : V) + ι (v 9)) * Cr ≤ (ι (p 1 : V) + ι (v 9)) * (-1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : ι ((p 0 : V) * v 0) ≤ ι (v 3) * ι ((p 0 : V) * v 0) := le_mul_of_one_le_left hb hz
    linarith
  apply (ι_le_ι (V := V)).mp
  rw [map_add]; linarith

/-- `N0 = 1` at a root `τ`: the first Pell norm. -/
theorem first (p : Fin 4 → ℕ) (v : Fin 15 → V) (τ : V)
    (hN0 : rN0 (fun j => (p j : ℤ)) (fun j => ι (v j)) (ι τ) = 1) :
    τ * τ = ellV p v * (ellV p v + kV v) + 1 := by
  rw [rN0, c_ell, c_k] at hN0
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  linear_combination hN0

/-- `N1 = 1`: the main Pell norm with root `D`. -/
theorem main (p : Fin 4 → ℕ) (v : Fin 15 → V)
    (hN1 : rN1 (fun j => (p j : ℤ)) (fun j => ι (v j)) = 1) :
    DV p v * DV p v = 1 + delta (aV p v) * cV p v * cV p v := by
  rw [rN1, c_D, c_Delta, c_c] at hN1
  rw [← ΔV_eq]
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  linear_combination hN1

/-- `S = 0` at index `i`: the ordinary strong norm. -/
theorem strong (p : Fin 4 → ℕ) (v : Fin 15 → V) (i : V)
    (hS : rS (fun j => (p j : ℤ)) (fun j => ι (v j)) (ι i) = 0) :
    (i * cV p v * cV p v) * (i * cV p v * cV p v) + delta (aV p v) = delta (aV p v) * (v 4 * v 4) := by
  rw [rS, c_Aaux, c_Delta, c_c] at hS
  rw [← ΔV_eq]
  apply ι_injective
  simp only [map_add, map_mul]
  linear_combination hS

/-- The normalized strong norm `f² − Δ(ic²)² = 1` is the ordinary one at index `Δi`. -/
theorem normalized (p : Fin 4 → ℕ) (v : Fin 15 → V) (i : V)
    (h : ι (v 4) * ι (v 4) - (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta *
      ((ι i * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c)) *
        (ι i * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c * (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c))) = 1) :
    (delta (aV p v) * i * cV p v * cV p v) * (delta (aV p v) * i * cV p v * cV p v) + delta (aV p v) =
      delta (aV p v) * (v 4 * v 4) := by
  rw [c_Delta, c_c] at h
  rw [← ΔV_eq]
  apply ι_injective
  simp only [map_add, map_mul]
  linear_combination (-(ι (ΔV p v))) * h

/-- `Na = 1` with a free partner `y = v 13`. -/
theorem aux_free (p : Fin 4 → ℕ) (v : Fin 15 → V) (hF : v 1 ≤ qV p v) (hf : 0 < v 4)
    (hz : rNa (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Vn (ι (v 13)) = 1) :
    delta (aV p v) * (v 4 * v 4 - 1) *
        (absdiff (v 4 * v 4 * (v 7 * cV p v)) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (v 4 * v 4 * (v 7 * cV p v)) (v 4 * v 4 * RV p v + cV p v)) + v 13 * v 13 =
      1 + delta (aV p v) * (v 4 * v 4 - 1) * (v 13 * v 13) := by
  rw [rNa, c_Vn, c_Aaux, c_RR p v hF, c_Delta, c_c] at hz
  rw [← ΔV_eq]
  have hf1 : 1 ≤ v 4 * v 4 :=
    one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  apply ι_injective
  simp only [map_add, map_mul, map_one, ι_tsub hf1]
  rw [ι_absdiff_sq]
  simp only [map_add, map_mul]
  linear_combination hz

/-- `Na = 1` with `y = V + e`, `e = v 13`. -/
theorem aux_gap (p : Fin 4 → ℕ) (v : Fin 15 → V) (hF : v 1 ≤ qV p v) (hf : 0 < v 4)
    (hz : rNa (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Vn
      ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Vn + ι (v 13)) = 1) :
    delta (aV p v) * (v 4 * v 4 - 1) *
        (absdiff (v 4 * v 4 * (v 7 * cV p v)) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (v 4 * v 4 * (v 7 * cV p v)) (v 4 * v 4 * RV p v + cV p v)) +
        absdiff (v 4 * v 4 * (v 7 * cV p v) + v 13) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (v 4 * v 4 * (v 7 * cV p v) + v 13) (v 4 * v 4 * RV p v + cV p v) =
      1 + delta (aV p v) * (v 4 * v 4 - 1) *
        (absdiff (v 4 * v 4 * (v 7 * cV p v) + v 13) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (v 4 * v 4 * (v 7 * cV p v) + v 13) (v 4 * v 4 * RV p v + cV p v)) := by
  rw [rNa, c_Vn, c_Aaux, c_RR p v hF, c_Delta, c_c] at hz
  rw [← ΔV_eq]
  have hf1 : 1 ≤ v 4 * v 4 :=
    one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  apply ι_injective
  simp only [map_add, map_mul, map_one, ι_tsub hf1]
  rw [ι_absdiff_sq, ι_absdiff_sq]
  simp only [map_add, map_mul]
  linear_combination hz

/-- `Na = 1` at the old ordinate `V = c(Tf − 1) − Rf²` with `y = V + e`. -/
theorem aux_old (p : Fin 4 → ℕ) (v : Fin 15 → V) (hF : v 1 ≤ qV p v) (hf : 0 < v 4)
    (hz : rNa (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Vo
      ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Vo + ι (v 13)) = 1) :
    delta (aV p v) * (v 4 * v 4 - 1) *
        (absdiff (cV p v * v 7 * v 4) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (cV p v * v 7 * v 4) (v 4 * v 4 * RV p v + cV p v)) +
        absdiff (cV p v * v 7 * v 4 + v 13) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (cV p v * v 7 * v 4 + v 13) (v 4 * v 4 * RV p v + cV p v) =
      1 + delta (aV p v) * (v 4 * v 4 - 1) *
        (absdiff (cV p v * v 7 * v 4 + v 13) (v 4 * v 4 * RV p v + cV p v) *
          absdiff (cV p v * v 7 * v 4 + v 13) (v 4 * v 4 * RV p v + cV p v)) := by
  rw [rNa, c_Vo, c_Aaux, c_RR p v hF, c_Delta, c_c] at hz
  rw [← ΔV_eq]
  have hf1 : 1 ≤ v 4 * v 4 :=
    one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  apply ι_injective
  simp only [map_add, map_mul, map_one, ι_tsub hf1]
  rw [ι_absdiff_sq, ι_absdiff_sq]
  simp only [map_add, map_mul]
  linear_combination hz

/-- `Nk = 1`: `k = R + 1 + hE`. -/
theorem index_pos (p : Fin 4 → ℕ) (v : Fin 15 → V) (hF : v 1 ≤ qV p v)
    (hNk : rNk (fun j => (p j : ℤ)) (fun j => ι (v j)) = 1) :
    kV v = RV p v + 1 + v 5 * EV p v := by
  rw [rNk, c_k, c_E, c_RR p v hF] at hNk
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  linear_combination hNk

/-- `Nk = −1`: `k + 1 = R + hE`. -/
theorem index_neg (p : Fin 4 → ℕ) (v : Fin 15 → V) (hF : v 1 ≤ qV p v)
    (hNk : rNk (fun j => (p j : ℤ)) (fun j => ι (v j)) = -1) :
    kV v + 1 = RV p v + v 5 * EV p v := by
  rw [rNk, c_k, c_E, c_RR p v hF] at hNk
  apply ι_injective
  simp only [map_add, map_mul, map_one]
  linear_combination hNk

end Short15Root

#print axioms Short15Root.transport_pos
#print axioms Short15Root.transport_neg
#print axioms Short15Root.first
#print axioms Short15Root.main
#print axioms Short15Root.strong
#print axioms Short15Root.normalized
#print axioms Short15Root.aux_free
#print axioms Short15Root.aux_gap
#print axioms Short15Root.aux_old
#print axioms Short15Root.index_pos
#print axioms Short15Root.index_neg
