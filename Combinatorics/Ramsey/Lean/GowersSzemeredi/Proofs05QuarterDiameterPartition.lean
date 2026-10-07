import GowersSzemeredi.Proofs05FullPartition
import GowersSzemeredi.Proofs05QuarterDiameterBudget

/-! Simultaneous polynomial partitions with a factor-four diameter reserve.
The existing recurrence threshold supplies the necessary ideal-root bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem lemma_5_9_quarter_diameter (N k q r v : Nat) [NeZero N]
    (phi : Fin q → ZMod N → ZMod N)
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hphi : ∀ i, PolynomialOn k Finset.univ (phi i))
    (hthreshold : simultaneousPolynomialThreshold k q < r) (hrN : r ≤ N)
    (hv : 1 ≤ v) (hvupper : (v : Real) ≤
      (r : Real) ^ (2 * (polynomialPartitionConstant k : Real) ^ q)⁻¹) :
    ∃ M : Nat, ∃ P : Fin M → NatAP,
      0 < M ∧ IsNatAPPartition P (Finset.range r) ∧
      (∀ j, (P j).IsProper ∧ 0 < (P j).length ∧
        ((P j).length = v - 1 ∨ (P j).length = v)) ∧
      ∀ i j, diameterAtMostReal ((P j).carrier.image fun x : Nat => phi i (x : ZMod N))
        (((r : Real) ^ (-((polynomialPartitionConstant k : Real) ^ q)⁻¹) / 4) * N) := by
  have hboost := simultaneous_partition_final_root hk hq hthreshold
  let targets := section5MaximalTargets (polynomialPartitionConstant k) q r v
  have htargetsLength : targets.length = q := section5MaximalTargets_length _ _ _ _
  have htargetsLast : targets.getLast? = some v := section5MaximalTargets_getLast? _ _ _ _ hq
  have htargetsSchedule := lemma_5_9_quarter_scale_schedule k q r v hk hq hthreshold hv hvupper hboost
  let functions : List (ZMod N -> ZMod N) := List.ofFn phi
  have hfunctionsLength : functions.length = targets.length := by
    simpa only [functions, List.length_ofFn] using htargetsLength.symm
  have hfunctionsNonempty : functions ≠ [] := by
    intro hnil
    have hzero : functions.length = 0 := by simp [hnil]
    have hlengthQ : functions.length = q := by
      simp only [functions, List.length_ofFn]
    omega
  have hfunctionsPolynomial :
      forall psi, psi ∈ functions -> PolynomialOn k Finset.univ psi := by
    intro psi hpsi
    change psi ∈ List.ofFn phi at hpsi
    rw [List.mem_ofFn'] at hpsi
    obtain ⟨i, rfl⟩ := hpsi
    exact hphi i
  obtain ⟨M, P, hM, hpartition, hcells, hsubset, hdiameter⟩ :=
    section5_iterated_strong_nat_refinement corollary_5_6_strong_diameter_holds hk
      ((r : Real) ^ (-((polynomialPartitionConstant k : Real) ^ q)⁻¹) / 4)
      functions targets hfunctionsLength hfunctionsNonempty
      (section5RangeNatAP r) (section5RangeNatAP_isProper r)
      (by
        simpa only [section5RangeNatAP_length] using
          (lt_of_le_of_lt (Nat.zero_le _) hthreshold))
      hrN hfunctionsPolynomial htargetsSchedule v htargetsLast
  refine ⟨M, P, hM, ?_, hcells, ?_⟩
  · simpa only [section5RangeNatAP_carrier] using hpartition
  · intro i j
    have hmem : phi i ∈ functions := by
      change phi i ∈ List.ofFn phi
      rw [List.mem_ofFn']
      exact ⟨i, rfl⟩
    exact hdiameter (phi i) hmem j


end LeanProofs.GowersSzemeredi
