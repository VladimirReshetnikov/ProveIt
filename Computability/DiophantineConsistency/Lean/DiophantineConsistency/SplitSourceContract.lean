import DiophantineConsistency.SplitSourceWords
import DiophantineConsistency.SplitSourceCarry

/-! # The split source, calibrated binomial test and finalizer

Source residuals here are the literal target coefficients of the three
supplied kernel polynomials. Their identification with a particular
native source system is a separate binding theorem.
-/

namespace DiophantineConsistency.SplitSourceContract

open Polynomial Finset Jones1982 SplitSourceWords
open scoped BigOperators

noncomputable def sourcePolynomial (d : Parameters) (z : Fin 31 → ℕ) : ℤ[X] :=
  SplitCoefficientBounds.product d.w (fun i => (z i : ℤ) + 1) d.D0 d.D1 d.D2

/-- The actual source masks calibrate the binomial threshold; all degree,
coefficient, positivity and word-range premises have been discharged. -/
theorem binomial_iff_source {d : Parameters} {a b k g : ℕ} (hd : Valid d a)
    (hb : b = 2 ^ k) (hg : g < 4 * b * (SplitNineRatio.base a b) ^ 116) :
    (SplitNineRatio.threshold a b) ^ 2 ∣
      (2 * SplitNineRatio.rank a b (word d a b g) (mask d a b)).choose
        (SplitNineRatio.rank a b (word d a b g) (mask d a b)) ↔
      ∃ z : Fin 31 → ℕ, (∀ i, z i < b) ∧
        g = LowMaskCoding.indexedCode (SplitNineRatio.base a b) d.w z ∧
        ∀ j, (sourcePolynomial d z).coeff (d.q j) = 0 := by
  have hb0 : 0 < b := by rw [hb]; positivity
  have h31 : (lowPositions d).card = 31 := by
    unfold lowPositions LowMaskCoding.positions
    rw [Finset.card_image_of_injective _ hd.weights_injective]
    simp
  have h22 : (targetPositions d).card = 22 := by
    unfold targetPositions LowMaskCoding.positions
    rw [Finset.card_image_of_injective _ hd.targets_injective]
    simp
  have hlo : lowPositions d ⊆ range 117 :=
    LowMaskCoding.positions_subset (fun i => by have h := hd.weights_le i; omega)
  have hhi : targetPositions d ⊆ range 2162 :=
    LowMaskCoding.positions_subset (fun i => by have h := hd.targets_le i; omega)
  obtain ⟨hgblock, hS⟩ := weak_cap_bounds hd hb0 hg
  have hbin : (SplitNineRatio.threshold a b) ^ 2 ∣
      (2 * SplitNineRatio.rank a b (word d a b g) (mask d a b)).choose
        (SplitNineRatio.rank a b (word d a b g) (mask d a b)) ↔
        τ 2 (word d a b g) (mask d a b) = 0 := by
    rw [mask_eq_population]
    exact SplitNineRatio.binomial_iff hb (lowPositions d) (targetPositions d)
      hlo hhi h31 h22 hS
  apply hbin.trans
  have hB := SplitNineRatio.base_power (a := a) hb
  have hBI : (SplitNineRatio.base a b : ℤ) = (2 : ℤ) ^ (a + 12 + 2 * k) := by
    exact_mod_cast hB
  have hbase : 4096 * (2 : ℤ) ^ a * (b : ℤ) ^ 2 ≤ (2 : ℤ) ^ (a + 12 + 2 * k) := by
    rw [← hBI, scale]
  have hcarry := SplitSourceCarry.tau_targets_iff d.w hd.weights_injective hd.weights_le
    hb hB (by omega : 2 ≤ a + 12 + 2 * k)
    (show b ≤ SplitNineRatio.base a b by have h := (SplitNineRatio.base_bounds a hb0).2; omega)
    hgblock d.q (fun j => by have h := hd.targets_le j; omega)
    d.D0 d.D1 d.D2 (by positivity : 0 < (2 : ℤ) ^ a) hd.kernels hbase
    (highInt_pos hd hb0 g).le
  simpa only [word, mask, highInt, targetPositions, LowMaskCoding.positions, sourcePolynomial] using hcarry

/-- A positive final-equation zero recovers bounded positive source digits.
The weak cap is obtained from ratio soundness before decoding is invoked. -/
theorem source_of_zero {d : Parameters} {a b g : ℕ} (hd : Valid d a)
    (v : FreeCarrierRatio.FreeVars) (hb : 0 < b)
    (hh : 0 < v.h) (hs : 0 < v.s) (hw : 0 < v.w) (hC : 0 < v.C) (hi : 0 < v.i)
    (hz : ∃ n : ℕ, 0 < n ∧
      SplitNineRatio.value a b g (word d a b g) (mask d a b) v n = 0) :
    ∃ k, b = 2 ^ k ∧ ∃ z : Fin 31 → ℕ, (∀ i, z i < b) ∧
      g = LowMaskCoding.indexedCode (SplitNineRatio.base a b) d.w z ∧
      ∀ j, (sourcePolynomial d z).coeff (d.q j) = 0 := by
  obtain ⟨hdvd, ⟨k, hpow⟩, hg⟩ :=
    SplitNineRatio.sound a b g (word d a b g) (mask d a b) v hb hh hs hw hC hi hz
  exact ⟨k, hpow, (binomial_iff_source hd hpow hg).mp hdvd⟩

/-- A sufficiently small encoded source witness supplies the positive
free-carrier and final coordinates, with no supplied calibration premise. -/
theorem zero_of_source {d : Parameters} {a b k : ℕ} (hd : Valid d a)
    (hb : b = 2 ^ k) (z : Fin 31 → ℕ) (hz : ∀ i, z i < b)
    (hcoeff : ∀ j, (sourcePolynomial d z).coeff (d.q j) = 0)
    (hcap : LowMaskCoding.indexedCode (SplitNineRatio.base a b) d.w z <
      b * (SplitNineRatio.base a b) ^ 116) :
    let g := LowMaskCoding.indexedCode (SplitNineRatio.base a b) d.w z
    ∃ v : FreeCarrierRatio.FreeVars, 0 < v.h ∧ 0 < v.s ∧ 0 < v.w ∧ 0 < v.C ∧ 0 < v.i ∧
      ∃ n : ℕ, 0 < n ∧ SplitNineRatio.value a b g (word d a b g) (mask d a b) v n = 0 := by
  dsimp only
  have hb0 : 0 < b := by rw [hb]; positivity
  have hweak : LowMaskCoding.indexedCode (SplitNineRatio.base a b) d.w z <
      4 * b * (SplitNineRatio.base a b) ^ 116 := by nlinarith only [hcap]
  have hdvd := (binomial_iff_source hd hb hweak).mpr ⟨z, hz, rfl, hcoeff⟩
  exact SplitNineRatio.complete a b _ _ _ hb0 hcap hdvd ⟨k, hb⟩

end DiophantineConsistency.SplitSourceContract
