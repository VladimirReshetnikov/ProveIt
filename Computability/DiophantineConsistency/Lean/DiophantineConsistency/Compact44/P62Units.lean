import DiophantineConsistency.Compact44.P62Graph
import DiophantineConsistency.Compact44.P72Aux
import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011

/-! # Package 62: the product-unit guard

At a positive zero, `Nt·(1 + Nmain)·Ns·(1 + N) = 1` in the ring of differences
of a model of `𝗜𝚺₁`, so every factor is `±1`. None of the three negative cases
can occur:

* `1 + Nmain = −1` would give `D*² + 2 = (4q⁴)²G`, impossible modulo 4;
* `Ns = −1` would give `I² + 2 = Δ(f²−1)`. But `Δ(f²−1)` is `0` or `1`
  modulo 4, and `I² + 2` is `2` or `3`;
* `1 + N = −1` would give `core² + 2 = 4·dA·E`, impossible modulo 4.

Hence `Nt = 1`, `Nmain = 0`, `Ns = 1` and `N = 0`. Signed registers enter only
through some representation `ι P − ι N`. This module also fixes the model
values `qV … QV` of the nonnegative registers and their casts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace P62Units
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing P62Graph
open ArithmeticAdaptiveFactorUnits2011 (residue residue_add residue_mul residue_nat)
open P72Root (ι_tsub)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Values
variable (p : Fin 4 → ℕ) (v : Fin 13 → V)

def qV : V := (p 0 : V) * v 0 + 1
def XV : V := v 8 * qV p v
def YV : V := v 7 * ((qV p v * qV p v) * qV p v)
def EV : V := XV p v * YV p v
def kV : V := v 9 + v 10
def cV : V := kV v * YV p v + v 9
def aV : V := EV p v + YV p v
def HV : V := 4 * aV p v + 3
def ΔV : V := aV p v * aV p v + HV p v
def ellV : V := EV p v * (kV v * YV p v)
def A1V : V := ellV p v * (ellV p v + kV v) + 1
def UV : V := 4 * ((qV p v * qV p v) * (qV p v * qV p v))
def IV : V := v 5 * (cV p v * cV p v)
def QV : V := ΔV p v * (v 4 * v 4 - 1)

theorem cast_nat (n : ℕ) : (((n : ℤ)) : DiffRing V) = ι (n : V) := by
  rw [Int.cast_natCast, map_natCast]

local notation "W" => vals (fun j => (p j : ℤ)) (fun j => ι (v j))

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
theorem c_A1 : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).A1 = ι (A1V p v) := by
  simp only [vals, A1V, ellV, EV, XV, YV, kV, qV, map_add, map_mul, map_one, cast_nat]
theorem c_U : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).U = ι (UV p v) := by
  simp only [vals, UV, qV, map_add, map_mul, map_one, map_ofNat, cast_nat]
theorem c_I : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I = ι (IV p v) := by
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).I =
    ι (v 5) * ((vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c *
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).c) from rfl, c_c]
  simp only [IV, map_mul]
theorem c_Q (hf : 0 < v 4) : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Q = ι (QV p v) := by
  have hf1 : 1 ≤ v 4 * v 4 := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp hf) (pos_iff_one_le.mp hf)
  rw [show (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Q =
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Delta * (ι (v 4) * ι (v 4) - 1) from rfl, c_Delta]
  simp only [QV, map_mul, ι_tsub hf1, map_one]

end Values

private theorem r1 : residue (V := V) 1 = 1 := by simpa using residue_nat (V := V) 1
private theorem r2 : residue (V := V) 2 = 2 := by simpa using residue_nat (V := V) 2
private theorem r3 : residue (V := V) 3 = 3 := by simpa using residue_nat (V := V) 3
private theorem r4 : residue (V := V) 4 = 4 := by simpa using residue_nat (V := V) 4

private theorem main_bad : ∀ x m g : ZMod 4, x * x + 2 ≠ (4 * m) * (4 * m) * g := by decide
private theorem strong_bad : ∀ i a f g : ZMod 4, g + 1 = f * f →
    i * i + 2 ≠ (a * a + (4 * a + 3)) * g := by decide
private theorem norm_bad : ∀ x w : ZMod 4, x * x + 2 ≠ 4 * w := by decide

/-- A positive zero makes the four factors `1, 0, 1, 0`. -/
theorem units (p : Fin 4 → ℕ) (v : Fin 13 → V) (hv : ∀ j, 0 < v j)
    (hz : InternalZero (graph (fun j => (p j : ℤ))).output v) :
    (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nt = 1 ∧
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Nmain = 0 ∧
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Ns = 1 ∧
      (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).N = 0 := by
  rw [internalZero_iff, output_eval] at hz
  set W := vals (fun j => (p j : ℤ)) (fun j => ι (v j)) with hW
  have hprod : W.Nt * (W.Nmain + 1) * W.Ns * (W.N + 1) = 1 := by linear_combination hz
  have hd := ModelArithmetic.model_discrete (V := V)
  have u2 := DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one hd
    (x := W.Nmain + 1) (y := W.Nt * W.Ns * (W.N + 1)) (by linear_combination hprod)
  have u3 := DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one hd
    (x := W.Ns) (y := W.Nt * (W.Nmain + 1) * (W.N + 1)) (by linear_combination hprod)
  have u4 := DiscreteOrderedRingFacts.eq_one_or_neg_one_of_mul_eq_one hd
    (x := W.N + 1) (y := W.Nt * (W.Nmain + 1) * W.Ns) (by linear_combination hprod)
  -- 1 + Nmain ≠ −1
  have h2 : W.Nmain + 1 = 1 := by
    rcases u2 with h | h
    · exact h
    · exfalso
      have hNm : W.Nmain = W.Dstar * W.Dstar - (W.U * W.U) * (W.Delta * (W.c * W.c) + 1) := rfl
      obtain ⟨P0, N0, hPN⟩ := exists_mk W.Dstar
      rw [mk_eq_sub] at hPN
      have hsq : W.Dstar * W.Dstar = ι (absdiff P0 N0) * ι (absdiff P0 N0) := by
        rw [P72Aux.ι_absdiff_sq, hPN]
      rw [hNm, hsq, c_U, c_Delta, c_c] at h
      have hV : absdiff P0 N0 * absdiff P0 N0 + 2 =
          UV p v * UV p v * (ΔV p v * (cV p v * cV p v) + 1) := by
        apply ι_injective
        simp only [map_add, map_mul, map_one, map_ofNat]
        linear_combination h
      have hr := congrArg (residue (V := V)) hV
      simp only [UV, residue_add, residue_mul, r1, r2, r4] at hr
      exact main_bad _ _ _ hr
  -- Ns ≠ −1
  have h3 : W.Ns = 1 := by
    rcases u3 with h | h
    · exact h
    · exfalso
      have hNs : W.Ns = W.I * W.I - (W.Q - 1) := rfl
      rw [hNs, c_I, c_Q p v (hv 4)] at h
      have hV : IV p v * IV p v + 2 = QV p v := by
        apply ι_injective
        simp only [map_add, map_mul, map_ofNat]
        linear_combination h
      have hf1 : 1 ≤ v 4 * v 4 :=
        one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp (hv 4)) (pos_iff_one_le.mp (hv 4))
      have hg : residue (v 4 * v 4 - 1) + 1 = residue (v 4) * residue (v 4) := by
        rw [← r1 (V := V), ← residue_add, tsub_add_cancel_of_le hf1, residue_mul]
      have hr := congrArg (residue (V := V)) hV
      simp only [QV, ΔV, HV, residue_add, residue_mul, r2, r3, r4] at hr
      exact strong_bad _ _ _ _ hg hr
  -- 1 + N ≠ −1
  have h4 : W.N + 1 = 1 := by
    rcases u4 with h | h
    · exact h
    · exfalso
      have hN : W.N = W.core * W.core - 4 * ((W.d * W.A1) * W.Eaux) := rfl
      rw [hN] at h
      obtain ⟨P0, N0, hPN⟩ := exists_mk W.core
      rw [mk_eq_sub] at hPN
      have hsq : W.core * W.core = ι (absdiff P0 N0) * ι (absdiff P0 N0) := by
        rw [P72Aux.ι_absdiff_sq, hPN]
      rw [hsq] at h
      have hpos : 0 ≤ (W.d * W.A1) * W.Eaux := by
        have := mul_self_nonneg (ι (absdiff P0 N0))
        linarith
      obtain ⟨w0, hw0⟩ := nonneg_iff.mp hpos
      rw [hw0] at h
      have hV : absdiff P0 N0 * absdiff P0 N0 + 2 = 4 * w0 := by
        apply ι_injective
        simp only [map_add, map_mul, map_ofNat]
        linear_combination h
      have hr := congrArg (residue (V := V)) hV
      simp only [residue_add, residue_mul, r2, r4] at hr
      exact norm_bad _ _ hr
  have h1 : W.Nt = 1 := by
    rw [h2, h3, h4] at hprod; linear_combination hprod
  refine ⟨h1, by linear_combination h2, h3, by linear_combination h4⟩

end P62Units

#print axioms P62Units.units
