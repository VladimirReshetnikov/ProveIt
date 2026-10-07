import GowersSzemeredi.Proofs18GeneralPhaseInverseAssembly

/-! The full inverse induction step after polynomial localization, in every
degree. Prime selection, transport, assembly, phase removal, and their
quantitative losses are proved here. The structural localization input
remains explicit and is not asserted for the unresolved higher degrees. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- The average-size exponent after one inverse induction step. -/
def inverseStepExponent (degree : Nat) (e sigma : Real) : Real :=
  phaseInverseExponent (degree + 1) (e * (sigma / 16))

/-- The complete count constant before polynomial phase refinement. -/
def inverseStepCountConstant (degree : Nat) (c sigma : Real) : Real :=
  localInverseAssemblyConstant (2 * (degree + 2 : Nat)) sigma * c ^ (sigma / 16)

/-- A finite threshold absorbing the complete polynomial phase-refinement cost. -/
def inverseStepThreshold (degree : Nat) (eta beta e c sigma : Real) : Real :=
  positivePowerThreshold
    (phaseInverseConstant (degree + 1) (eta * beta / 2) (inverseStepCountConstant degree c sigma))
    1 (inverseStepExponent degree e sigma)

/-- From an actual localized obstruction and the lower-degree inverse
bound, construct the full untwisted discrepancy partition. This theorem
applies in every degree, with no ambient inverse hypothesis. -/
theorem FunctionDiscrepancyBound.inverse_step
    {degree N K l m : Nat} [NeZero N] [Fact N.Prime]
    {eta beta sigma T e c : Real}
    (hbound : FunctionDiscrepancyBound degree
      ((eta / 2) / (2 * (degree + 2 : Nat) : Real) ^ (degree + 2)) beta sigma T)
    (hη : 0 < eta) (hβ : 0 < beta) (hσ : 0 < sigma) (hσ16 : sigma ≤ 16)
    (he : 0 < e) (hc : 0 < c)
    (f : ZMod N → Complex) (hf : DiscValued f)
    (phi : ZMod N → ZMod N) (hpoly : PolynomialOn (degree + 1) Finset.univ phi)
    (Q : Fin K → ModAP N)
    (hQ : IsPartition (fun i => (Q i).carrier) Finset.univ)
    (hproper : ∀ i, (Q i).IsProper) (hl : 2 ≤ l) (hT : T ≤ (l : Real)) (hm : 0 < m)
    (hlength : ∀ i, l ≤ (Q i).length ∧ (Q i).length ≤ m ∧ (degree + 2) * (Q i).length ≤ N)
    (hscale : (N : Real) ^ e / c ≤ l)
    (hfail : ¬ UniformOnPartition (phaseTwist f phi) degree eta Q m)
    (hN : inverseStepThreshold degree eta beta e c sigma ≤ (N : Real)) :
    ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      (∀ j, (R j).IsProper) ∧
      (N : Real) ^ inverseStepExponent degree e sigma ≤ averageCellSize (fun j => (R j).carrier) ∧
      (eta * beta / 4) * N ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  obtain ⟨J, R, hR, _, hcount, hdis⟩ := hbound.localized_partition hη.le hβ.le hσ.le hσ16
    (phaseTwist f phi) (phaseTwist_discValued hf phi) Q hQ hproper hl hT hm hlength hfail
  have hD : 0 < localInverseAssemblyConstant (2 * (degree + 2 : Nat)) sigma :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hpower : (J : Real) ≤ inverseStepCountConstant degree c sigma *
      (N : Real) ^ (1 - e * (sigma / 16)) :=
    partition_count_power_of_length (by positivity) hD.le hc hscale hcount
  have hD' : 0 < inverseStepCountConstant degree c sigma := by
    unfold inverseStepCountConstant
    positivity
  have hex := polynomial_phase_inverse_partition (by omega : 1 ≤ degree + 1)
    (by positivity : 0 < e * (sigma / 16)) (by positivity : 0 < eta * beta / 2) hD'
    f hf R (fun _ => phi) (fun _ => hpoly) hR hpower hdis hN
  simpa only [inverseStepExponent, show eta * beta / 2 / 2 = eta * beta / 4 by ring] using hex

/-- An explicit localization theorem and a lower-degree function inverse
bound suffice for the next function inverse bound. The maximum accounts
for both the localization and phase-removal thresholds. -/
theorem FunctionDiscrepancyBound.of_polynomial_localization
    {degree : Nat} {alpha eta beta sigma T e c Tloc : Real}
    (hbound : FunctionDiscrepancyBound degree
      ((eta / 2) / (2 * (degree + 2 : Nat) : Real) ^ (degree + 2)) beta sigma T)
    (hη : 0 < eta) (hβ : 0 < beta) (hσ : 0 < sigma) (hσ16 : sigma ≤ 16)
    (he : 0 < e) (hc : 0 < c)
    (hlocal : ∀ (N : Nat) [NeZero N] [Fact N.Prime], Tloc ≤ (N : Real) →
      ∀ f : ZMod N → Complex, DiscValued f → ¬ UniformOfDegree f alpha (degree + 1) →
      ∃ phi : ZMod N → ZMod N, ∃ K l m : Nat, ∃ Q : Fin K → ModAP N,
        PolynomialOn (degree + 1) Finset.univ phi ∧
        IsPartition (fun i => (Q i).carrier) Finset.univ ∧
        (∀ i, (Q i).IsProper) ∧ 2 ≤ l ∧ T ≤ (l : Real) ∧ 0 < m ∧
        (∀ i, l ≤ (Q i).length ∧ (Q i).length ≤ m ∧ (degree + 2) * (Q i).length ≤ N) ∧
        (N : Real) ^ e / c ≤ l ∧
        ¬ UniformOnPartition (phaseTwist f phi) degree eta Q m) :
    FunctionDiscrepancyBound (degree + 1) alpha (eta * beta / 4)
      (inverseStepExponent degree e sigma)
      (max Tloc (inverseStepThreshold degree eta beta e c sigma)) := by
  intro N _ _ hN f hf hnot
  obtain ⟨phi, K, l, m, Q, hpoly, hQ, hp, hl, hT, hm, hlen, hscale, hfail⟩ :=
    hlocal N ((le_max_left _ _).trans hN) f hf hnot
  exact hbound.inverse_step hη hβ hσ hσ16 he hc f hf phi hpoly Q hQ hp hl hT hm hlen hscale hfail
    ((le_max_right _ _).trans hN)

end LeanProofs.GowersSzemeredi
