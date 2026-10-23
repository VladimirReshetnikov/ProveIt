import DiophantineConsistency.NativeNineSource52
import DiophantineConsistency.NativeNinePolynomial52

/-!
# The literal package-52 equation over exactly nine natural coordinates

The polynomial recipe has integer coefficients and shifts precisely b, g,
h, s, w and i by one. Its zero set is proved equivalent to that of the
literal 31-coordinate source, under the explicit coefficient-height bound.
The four coefficient ports remain supplied data in this module.
-/

namespace DiophantineConsistency.NativeNineEquation52

open NativeQuadraticParent

set_option maxRecDepth 16000
set_option maxHeartbeats 200000

theorem sourceBase_cast (a b : ℕ) :
    (NativeNineSource52.sourceBase a b : ℤ) =
      NativeNinePolynomial52.sourceBase ((2 : ℤ) ^ a) (b : ℤ) := by
  simp only [NativeNineSource52.sourceBase, NativeBaseBounds52.base,
    NativeNinePolynomial52.sourceBase, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem sourceN_cast (a b : ℕ) :
    (NativeNineSource52.sourceN a b : ℤ) =
      NativeNinePolynomial52.sourceN
        (NativeNinePolynomial52.sourceBase ((2 : ℤ) ^ a) (b : ℤ)) := by
  rw [← sourceBase_cast]
  simp only [NativeNineSource52.sourceN, NativeQuadraticSource52.N,
    NativeQuadraticSource52.N0, NativeQuadraticSource52.N1,
    NativeNinePolynomial52.sourceN, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem sourceCap_cast (a b : ℕ) :
    (NativeNineSource52.sourceCap a b : ℤ) =
      NativeNinePolynomial52.sourceCap
        (NativeNinePolynomial52.sourceBase ((2 : ℤ) ^ a) (b : ℤ)) (b : ℤ) := by
  rw [← sourceBase_cast]
  simp only [NativeNineSource52.sourceCap, NativeBaseBounds52.cap,
    NativeNinePolynomial52.sourceCap, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem highInt_eq_sourceHigh (ports : Fin 4 → ℤ) (B g : ℕ) :
    NativeQuadraticSource52.highInt ports B g =
      NativeNinePolynomial52.sourceHigh ports (B : ℤ) (g : ℤ) := rfl

/-- The cast of the natural central rank agrees with the literal polynomial
for every natural g. No upper bound or digit decoding is required. -/
theorem sourceRank_cast (ports : Fin 4 → ℤ) (a : ℕ)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ (2 : ℤ) ^ a)
    {b : ℕ} (hb : 0 < b) (g : ℕ) :
    (NativeNineSource52.sourceRank ports a b g : ℤ) =
      NativeNinePolynomial52.sourceRank ports
        (NativeNinePolynomial52.sourceBase ((2 : ℤ) ^ a) (b : ℤ)) (b : ℤ) (g : ℤ) := by
  let B := NativeNineSource52.sourceBase a b
  have hH : (0 : ℤ) < 2 ^ a := by positivity
  have hscale : (B : ℤ) = 4096 * (2 : ℤ) ^ a * (b : ℤ) ^ 2 := sourceBase_cast a b
  obtain ⟨hB, hbB⟩ := NativeBaseBounds52.base_bounds
    (by positivity : 0 < (2 : ℕ) ^ a) hb
  change 2 ≤ B at hB
  change b < B at hbB
  have hN : 1 ≤ NativeQuadraticSource52.N B := by
    have h := (NativeNineSource52.ratio_size_bounds ports (a := a) (g := g) hb).1
    change 8 ≤ NativeQuadraticSource52.N B at h
    omega
  have hR := NativeQuadraticSource52.rank_cast ports B b g hN
  rw [NativeQuadraticSource52.S_cast_of_scale ports hH hc (by omega) hscale g,
    NativeQuadraticSource52.T_cast hB (by omega) hbB.le,
    highInt_eq_sourceHigh] at hR
  change (NativeQuadraticSource52.rank ports B b g : ℤ) = _
  rw [hR]
  have hbase : (B : ℤ) =
      NativeNinePolynomial52.sourceBase ((2 : ℤ) ^ a) (b : ℤ) := sourceBase_cast a b
  have hNcast : (NativeQuadraticSource52.N B : ℤ) =
      NativeNinePolynomial52.sourceN (B : ℤ) := by
    simpa only [NativeNineSource52.sourceN, ← hbase] using sourceN_cast a b
  rw [hNcast, ← hbase]
  simp only [NativeNinePolynomial52.sourceRank, NativeNinePolynomial52.sourceMask,
    NativeNinePolynomial52.sourceHighMask, NativeQuadraticSource52.inputWeights]
  ring

/-- The exact six successor shifts used to express positivity over naturals. -/
def successorShift {A : Type*} [CommRing A] (x : Fin 9 → A) (i : Fin 9) : A :=
  x i + if i.val ≤ 4 ∨ i.val = 6 then 1 else 0

theorem successorShift_witness (x : Fin 9 → ℕ) :
    successorShift (fun i => (x i : ℤ)) =
      fun i => (NativeNinePolynomial52.witnessVector (x 0 + 1) (x 1 + 1)
        (NativeNineSource52.varsOfTuple x) (x 8) i : ℤ) := by
  funext i
  fin_cases i <;>
    simp [successorShift, NativeNinePolynomial52.witnessVector, NativeNineSource52.varsOfTuple]

theorem value_eq_naturalValue (ports : Fin 4 → ℤ) (a : ℕ)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ (2 : ℤ) ^ a)
    (x : Fin 9 → ℕ) :
    NativeNinePolynomial52.value ports ((2 : ℤ) ^ a)
      (successorShift (fun i => (x i : ℤ))) = NativeNineSource52.naturalValue ports a x := by
  rw [successorShift_witness]
  exact NativeNinePolynomial52.value_eq_finalValue ports ((2 : ℤ) ^ a)
    (x 0 + 1) (x 1 + 1) (NativeNineSource52.varsOfTuple x) (x 8)
    (NativeNineSource52.sourceRank ports a (x 0 + 1) (x 1 + 1))
    (NativeNineSource52.sourceN a (x 0 + 1)) (NativeNineSource52.sourceCap a (x 0 + 1))
    (sourceRank_cast ports a hc (by omega) (x 1 + 1)).symm
    (sourceN_cast a (x 0 + 1)).symm (sourceCap_cast a (x 0 + 1)).symm

/-- A supplied finite arithmetic recipe for an ordinary integer polynomial.
Finite-support polynomial operations are the only noncomputable data here. -/
noncomputable def polynomial (ports : Fin 4 → ℤ) (a : ℕ) : MvPolynomial (Fin 9) ℤ :=
  NativeNinePolynomial52.value (fun i => MvPolynomial.C (ports i))
    (MvPolynomial.C ((2 : ℤ) ^ a)) (successorShift MvPolynomial.X)

theorem eval_polynomial (ports : Fin 4 → ℤ) (a : ℕ) (x : Fin 9 → ℤ) :
    MvPolynomial.eval x (polynomial ports a) =
      NativeNinePolynomial52.value ports ((2 : ℤ) ^ a) (successorShift x) := by
  unfold polynomial
  rw [NativeNinePolynomial52.map_value]
  simp only [successorShift, map_add, apply_ite, map_one, map_zero,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  congr 1
  funext i
  by_cases hi : i.val ≤ 4 ∨ i.val = 6 <;> simp [successorShift, hi]

theorem eval_polynomial_nat (ports : Fin 4 → ℤ) (a : ℕ)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ (2 : ℤ) ^ a)
    (x : Fin 9 → ℕ) :
    MvPolynomial.eval (fun i => (x i : ℤ)) (polynomial ports a) =
      NativeNineSource52.naturalValue ports a x := by
  rw [eval_polynomial, value_eq_naturalValue ports a hc]

theorem exists_zero_iff_source (ports : Fin 4 → ℤ) (a : ℕ)
    (hc : ∀ k p, p ∈ rowSupport k →
      |QuadraticCoding.correction p * rowCoefficient ports k p| ≤ (2 : ℤ) ^ a) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i : ℤ)) (polynomial ports a) = 0) ↔
      ∃ x : Fin 31 → ℕ, ∀ k, sourceRows ports (fun i => (x i : ℤ) + 1) k = 0 := by
  simp only [eval_polynomial_nat ports a hc]
  exact NativeNineSource52.natural_zero_iff_source ports a hc

/-- The published bit bounds discharge every coefficient-height premise.
The four port values themselves are still explicit supplied data. -/
theorem exists_zero_iff_source_published (ports : Fin 4 → ℤ)
    (hbeta : 0 ≤ ports 0 ∧ ports 0 < 2 ^ 590069)
    (htransport : 0 ≤ ports 1 ∧ ports 1 < 2 ^ 592884)
    (hMC : 0 ≤ ports 2 ∧ ports 2 < 2 ^ 590069)
    (hMF : 0 ≤ ports 3 ∧ ports 3 < 2 * 2 ^ 590069) :
    (∃ x : Fin 9 → ℕ, MvPolynomial.eval (fun i => (x i : ℤ)) (polynomial ports 1182955) = 0) ↔
      ∃ x : Fin 31 → ℕ, ∀ k, sourceRows ports (fun i => (x i : ℤ) + 1) k = 0 :=
  exists_zero_iff_source ports 1182955 (fun k p _ =>
    (NativeCoefficientBounds.weighted_rowCoefficient_lt_published ports
      hbeta htransport hMC hMF k p).le)

end DiophantineConsistency.NativeNineEquation52
