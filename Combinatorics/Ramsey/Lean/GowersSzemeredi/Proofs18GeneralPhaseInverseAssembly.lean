import GowersSzemeredi.Proofs18GeneralLocalInverseAssembly
import GowersSzemeredi.Proofs05VariablePhaseRefinement
import GowersSzemeredi.Proofs13ExplicitGeometricThreshold
import GowersSzemeredi.Proofs18QuantitativeSzemeredi

/-! Remove polynomial phases of arbitrary degree from a discrepancy
partition, with an explicit threshold absorbing the refinement constant. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Convert a common-cell-length count into a power of the original modulus. -/
theorem partition_count_power_of_length {N l J : Nat} [NeZero N]
    {e t D c : Real} (ht : 0 ≤ t) (hD : 0 ≤ D) (hc : 0 < c)
    (hl : (N : Real) ^ e / c ≤ l)
    (hcount : (J : Real) ≤ D * N / (l : Real) ^ t) :
    (J : Real) ≤ (D * c ^ t) * (N : Real) ^ (1 - e * t) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hbase : 0 < (N : Real) ^ e / c := by positivity
  have hpow := Real.rpow_le_rpow hbase.le hl ht
  calc
    (J : Real) ≤ D * N / (l : Real) ^ t := hcount
    _ ≤ D * N / ((N : Real) ^ e / c) ^ t :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hbase t) hpow
    _ = _ := by
      rw [Real.div_rpow (Real.rpow_nonneg hN.le _) hc.le,
        ← Real.rpow_mul hN.le, Real.rpow_sub hN, Real.rpow_one]
      field_simp

/-- The exponent retained after refining polynomial phases of degree k. -/
def phaseInverseExponent (k : Nat) (e : Real) : Real :=
  e / (2 * (polynomialPartitionConstant k : Real))

/-- The fixed factor in the refined partition count. -/
def phaseInverseConstant (k : Nat) (beta D : Real) : Real :=
  section5LocalRefinementConstant k beta * D ^ (polynomialPartitionConstant k : Real)⁻¹

/-- A polynomial twist may vary from cell to cell. A full power-saving
count and twisted discrepancy yield an untwisted proper partition with
explicit average-size exponent and a finite modulus threshold. -/
theorem polynomial_phase_inverse_partition {N K k : Nat} [NeZero N]
    {e beta D : Real} (hk : 1 ≤ k) (he : 0 < e) (hβ : 0 < beta) (hD : 0 < D)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (Q : Fin K → ModAP N) (phi : Fin K → ZMod N → ZMod N)
    (hpoly : ∀ i, PolynomialOn k Finset.univ (phi i))
    (hQ : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hcount : (K : Real) ≤ D * (N : Real) ^ (1 - e))
    (hdis : beta * N ≤ ∑ i, ‖∑ x ∈ (Q i).carrier, phaseTwist f (phi i) x‖)
    (hN : positivePowerThreshold (phaseInverseConstant k beta D) 1
      (phaseInverseExponent k e) ≤ (N : Real)) :
    ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      (∀ j, (R j).IsProper) ∧
      (N : Real) ^ phaseInverseExponent k e ≤ averageCellSize (fun j => (R j).carrier) ∧
      (beta / 2) * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  let q : Real := (polynomialPartitionConstant k : Real)⁻¹
  let C := phaseInverseConstant k beta D
  let s := phaseInverseExponent k e
  have hK : 0 < (polynomialPartitionConstant k : Real) := by
    unfold polynomialPartitionConstant
    positivity
  have hs : 0 < s := by dsimp [s, phaseInverseExponent]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have heq : s = e * q / 2 := by dsimp [s, q, phaseInverseExponent]; ring
  obtain ⟨J, R, hR, _, hRproper, hJ, hdisR⟩ := variable_polynomial_phase_refinement
    Q phi f beta hk hβ hpoly hf hQ hdis
  have hNr : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hJ' : (J : Real) ≤ C * (N : Real) ^ (1 - e * q) := by
    calc
      _ ≤ section5LocalRefinementConstant k beta * (K : Real) ^ q * (N : Real) ^ (1 - q) := hJ
      _ ≤ section5LocalRefinementConstant k beta * (D * (N : Real) ^ (1 - e)) ^ q * (N : Real) ^ (1 - q) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hcount hq.le)
            (section5LocalRefinementConstant_pos _ _).le) (Real.rpow_nonneg hNr.le _)
      _ = _ := by
        rw [Real.mul_rpow hD.le (Real.rpow_nonneg hNr.le _), ← Real.rpow_mul hNr.le]
        have hp : (N : Real) ^ ((1 - e) * q) * (N : Real) ^ (1 - q) = (N : Real) ^ (1 - e * q) := by
          rw [← Real.rpow_add hNr]
          congr 1
          ring
        change (section5LocalRefinementConstant k beta * (D ^ q * (N : Real) ^ ((1 - e) * q))) *
          (N : Real) ^ (1 - q) = (section5LocalRefinementConstant k beta * D ^ q) * (N : Real) ^ (1 - e * q)
        rw [← hp]
        ring
  have hCbound : C ≤ (N : Real) ^ s := by
    simpa only [one_mul] using positivePowerThreshold_spec (C := C) zero_lt_one hs hN
  have hJbound : (J : Real) ≤ (N : Real) ^ (1 - s) := by
    calc
      _ ≤ C * (N : Real) ^ (1 - e * q) := hJ'
      _ ≤ (N : Real) ^ s * (N : Real) ^ (1 - e * q) :=
        mul_le_mul_of_nonneg_right hCbound (Real.rpow_nonneg hNr.le _)
      _ = _ := by rw [← Real.rpow_add hNr]; congr 1; linarith only [heq]
  have hJpos := section18_partition_index_nonempty (fun j => (R j).carrier) hR
  refine ⟨J, R, hR, hRproper, ?_, hdisR⟩
  rw [hR.averageCellSize_univ]
  apply (le_div_iff₀ (show (0 : Real) < J by exact_mod_cast hJpos)).2
  calc
    _ ≤ (N : Real) ^ s * (N : Real) ^ (1 - s) :=
      mul_le_mul_of_nonneg_left hJbound (Real.rpow_nonneg hNr.le _)
    _ = N := by rw [← Real.rpow_add hNr, show s + (1 - s) = 1 by ring, Real.rpow_one]

end LeanProofs.GowersSzemeredi
