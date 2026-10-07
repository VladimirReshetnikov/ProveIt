/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import OAI.Combinatorics.Progressions.Dynamics.PhysicalBoundaryBudget
import OAI.Combinatorics.Progressions.Lattices.BoundedPrimeGridCorrelation
import OAI.Combinatorics.Progressions.Probability.CylinderUniformMass

namespace OAI

section

namespace Erdos3

theorem residualPointAccuracy_inverse_le_exp {M S F mesh epsilon P : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hF : 0 ≤ F) (hmesh : 0 ≤ mesh)
    (heps : 0 < epsilon) (hP : 0 ≤ P)
    (hcoef : 6 * M * S * F ≤ Real.exp P) (hmeshcoef : 2 * mesh ≤ Real.exp P)
    (hepsinv : epsilon⁻¹ ≤ Real.exp P) :
    (residualPointAccuracy M S F mesh epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  unfold residualPointAccuracy
  apply inv_min_le_of_inv_le
  · exact replacementAccuracy_inverse_le_exp (by positivity) heps hP hcoef hepsinv
  · exact replacementAccuracy_inverse_le_exp (by positivity) (by norm_num) hP hmeshcoef
      (by simpa only [inv_one] using Real.one_le_exp_iff.mpr hP)

theorem residualGridAccuracy_inverse_le_exp {M S K epsilon P : ℝ}
    (hM : 0 ≤ M) (hS : 0 ≤ S) (hK : 0 ≤ K) (heps : 0 < epsilon) (hP : 0 ≤ P)
    (hcoef : 6 * M * S * K ≤ Real.exp P) (hepsinv : epsilon⁻¹ ≤ Real.exp P) :
    (residualGridAccuracy M S K epsilon)⁻¹ ≤ Real.exp (2 * P + 2) :=
  replacementAccuracy_inverse_le_exp (by positivity) heps hP hcoef hepsinv

theorem residualMeanAccuracy_inverse_le_exp {M K V epsilon P : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (heps : 0 < epsilon) (hP : 0 ≤ P)
    (hcoef : V ^ 2 * (1 + 3 * M * K) ≤ Real.exp P) (hepsinv : epsilon⁻¹ ≤ Real.exp P) :
    (residualMeanAccuracy M K V epsilon)⁻¹ ≤ Real.exp (2 * P + 2) := by
  apply replacementAccuracy_inverse_le_exp (by positivity) (lt_min zero_lt_one heps) hP hcoef
  exact inv_min_le_of_inv_le (by simpa only [inv_one] using Real.one_le_exp_iff.mpr hP) hepsinv

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem partial_assignment_card_le_exp {ι : Type*} [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {V : ℝ} (hV : 0 ≤ V)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) (S : Finset ι) {j : ℕ} (hS : S.card ≤ j) :
    (Fintype.card (∀ i : S, X i.val) : ℝ) ≤ Real.exp ((j : ℝ) * V) := by
  classical
  rw [Fintype.card_pi, Nat.cast_prod]
  calc
    _ ≤ ∏ _i : S, Real.exp V := Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun i _ => hX i.val)
    _ = Real.exp ((S.card : ℝ) * V) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, ← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hV)

theorem lowDegreeCoordinateSets_card_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : ℝ} (hP : 0 ≤ P) (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) (j : ℕ) :
    ((lowDegreeCoordinateSets ι j).card : ℝ) ≤ Real.exp ((j : ℝ) * (P + 1)) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (j + 1)) :
      ((Fintype.card ι).choose k : ℝ) ≤ Real.exp ((j : ℝ) * P) := by
    have hkj : k ≤ j := by have := Finset.mem_range.mp hk; omega
    calc
      _ ≤ (Fintype.card ι : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow (Fintype.card ι) k
      _ ≤ (Real.exp P) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount k
      _ = Real.exp ((k : ℝ) * P) := (Real.exp_nat_mul P k).symm
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast hkj) hP)
  rw [lowDegreeCoordinateSets_card, Nat.cast_sum]
  calc
    _ ≤ ∑ _k ∈ Finset.range (j + 1), Real.exp ((j : ℝ) * P) := Finset.sum_le_sum hterm
    _ = ((j : ℝ) + 1) * Real.exp ((j : ℝ) * P) := by simp
    _ ≤ Real.exp j * Real.exp ((j : ℝ) * P) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem ProductCylinder.bounded_card_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] {P V : ℝ} (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) (j : ℕ) :
    ((ProductCylinder.bounded (X := X) j).card : ℝ) ≤ Real.exp ((j : ℝ) * (P + V + 1)) := by
  classical
  have he : ((ProductCylinder.bounded (X := X) j).card : ℝ) =
      ∑ S ∈ lowDegreeCoordinateSets ι j, (Fintype.card (∀ i : S, X i.val) : ℝ) := by
    simp only [ProductCylinder.bounded_card, Nat.cast_sum, Fintype.card_pi, Nat.cast_prod]
  rw [he]
  calc
    _ ≤ ∑ _S ∈ lowDegreeCoordinateSets ι j, Real.exp ((j : ℝ) * V) := by
      apply Finset.sum_le_sum
      intro S hS
      exact partial_assignment_card_le_exp hV hX S ((mem_lowDegreeCoordinateSets ι j S).mp hS)
    _ = ((lowDegreeCoordinateSets ι j).card : ℝ) * Real.exp ((j : ℝ) * V) := by simp
    _ ≤ Real.exp ((j : ℝ) * (P + 1)) * Real.exp ((j : ℝ) * V) :=
      mul_le_mul_of_nonneg_right (lowDegreeCoordinateSets_card_le_exp hP hcount j) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem CylinderRemovalChain.length_le_exp {Ω ι : Type*}
    [Fintype Ω] [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]
    {μ : ∀ i, FiniteProbabilityWeights (X i)} {base : ∀ i, X i}
    {p : FiniteProbabilityWeights Ω} {F : Ω → ∀ i, X i}
    {K τ P V : ℝ} {j r : ℕ} {w rem : Ω → ℝ} {cs : List (ProductCylinder X)}
    (hchain : CylinderRemovalChain μ base p F K τ j r w rem cs)
    (hτ : 0 ≤ τ) (hw : ∀ z, 0 ≤ w z) (hP : 0 ≤ P) (hV : 0 ≤ V)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P)
    (hX : ∀ i, (Fintype.card (X i) : ℝ) ≤ Real.exp V) :
    (cs.length : ℝ) ≤ Real.exp ((j : ℝ) * (P + V + 1)) := by
  classical
  have hsub : cs.toFinset ⊆ ProductCylinder.bounded (X := X) j := by
    intro d hd
    exact (ProductCylinder.mem_bounded j d).mpr (hchain.size_le d (List.mem_toFinset.mp hd))
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (hchain.nodup hτ hw)] at hc
  exact (Nat.cast_le.mpr hc).trans (ProductCylinder.bounded_card_le_exp hP hV hcount hX j)

end Erdos3

end

section

namespace Erdos3

noncomputable def scalarTransferBaseAccuracy (targetLog : ℝ) : ℝ := Real.exp (-(targetLog + 10))

noncomputable def scalarTransferMarginalAccuracy (targetLog capLog : ℝ) : ℝ :=
  Real.exp (-(targetLog + capLog + 10))

noncomputable def scalarTransferTail (targetLog : ℝ) : ℝ := 2 * (targetLog + 10)

theorem residueTruncationCap_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℕ) {P eta : ℝ} (hP : 0 ≤ P) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    residueTruncationCap ι b eta ≤ Real.exp ((b : ℝ) * (P + 2) + 1) := by
  have hc := lowDegreeCoordinateSets_card_le_exp hP hcount b
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ b ≤ Real.exp b := by
    calc
      _ ≤ (Real.exp 1) ^ b := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo b
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  unfold residueTruncationCap
  calc
    _ ≤ Real.exp ((b : ℝ) * (P + 1)) * Real.exp b * Real.exp 1 :=
      mul_le_mul (mul_le_mul hc hp (by positivity) (Real.exp_nonneg _))
        (by linarith : 1 + eta ≤ Real.exp 1) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem scalarTransferAccuracy_spec {targetLog capLog : ℝ}
    (htarget : 0 ≤ targetLog) (hcapLog : 0 ≤ capLog) :
    0 < scalarTransferBaseAccuracy targetLog ∧ scalarTransferBaseAccuracy targetLog ≤ 1 ∧
      0 < scalarTransferMarginalAccuracy targetLog capLog ∧
      scalarTransferMarginalAccuracy targetLog capLog ≤ scalarTransferBaseAccuracy targetLog ∧
      (scalarTransferBaseAccuracy targetLog)⁻¹ = Real.exp (targetLog + 10) ∧
      (scalarTransferMarginalAccuracy targetLog capLog)⁻¹ = Real.exp (targetLog + capLog + 10) := by
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), Real.exp_pos _, ?_, ?_, ?_⟩
  · exact Real.exp_le_exp.mpr (by linarith)
  · simp only [scalarTransferBaseAccuracy, Real.exp_neg, inv_inv]
  · simp only [scalarTransferMarginalAccuracy, Real.exp_neg, inv_inv]

theorem scalarTransferMarginalAccuracy_cost {targetLog capLog cap : ℝ}
    (hcap : cap ≤ Real.exp capLog) :
    scalarTransferMarginalAccuracy targetLog capLog * cap ≤ scalarTransferBaseAccuracy targetLog := by
  calc
    _ ≤ Real.exp (-(targetLog + capLog + 10)) * Real.exp capLog :=
      mul_le_mul_of_nonneg_left hcap (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem scalarTransfer_combined_error_le {epsilon level targetLog capLog cap : ℝ}
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (_hlevel : 0 ≤ level) (hlevel2 : level ≤ 2) (hcap0 : 0 ≤ cap)
    (hcap : cap ≤ Real.exp capLog) :
    100 * (1 + epsilon) * Real.exp (-scalarTransferTail targetLog / 2) +
      (1 + epsilon) * scalarTransferBaseAccuracy targetLog +
      (1 + (1 + epsilon) * level) *
        ((scalarTransferMarginalAccuracy targetLog capLog + scalarTransferMarginalAccuracy targetLog capLog) * cap +
          scalarTransferBaseAccuracy targetLog) ≤ Real.exp (-targetLog) / 2 := by
  let a := scalarTransferBaseAccuracy targetLog
  have ha : 0 < a := Real.exp_pos _
  have ht : Real.exp (-scalarTransferTail targetLog / 2) = a := by
    congr 1
    unfold scalarTransferTail
    ring
  have hm := scalarTransferMarginalAccuracy_cost (targetLog := targetLog) hcap
  have hsmall : (scalarTransferMarginalAccuracy targetLog capLog + scalarTransferMarginalAccuracy targetLog capLog) * cap + a ≤ 3 * a := by
    change scalarTransferMarginalAccuracy targetLog capLog * cap ≤ a at hm
    nlinarith
  have hsmall0 : 0 ≤ (scalarTransferMarginalAccuracy targetLog capLog + scalarTransferMarginalAccuracy targetLog capLog) * cap + a := by
    unfold scalarTransferMarginalAccuracy
    positivity
  have hcoeff : 1 + (1 + epsilon) * level ≤ 5 := by nlinarith
  have hprod := mul_le_mul hcoeff hsmall hsmall0 (by norm_num : (0 : ℝ) ≤ 5)
  have h512 : (512 : ℝ) ≤ Real.exp 10 := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      512 ≤ (2 : ℝ) ^ 10 := by norm_num
      _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) htwo 10
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hpaid : 512 * a ≤ Real.exp (-targetLog) := by
    calc
      _ ≤ Real.exp 10 * a := mul_le_mul_of_nonneg_right h512 ha.le
      _ = _ := by dsimp only [a, scalarTransferBaseAccuracy]; rw [← Real.exp_add]; congr 1; ring
  rw [ht]
  change 100 * (1 + epsilon) * a + (1 + epsilon) * a + _ ≤ _
  have hc := mul_le_mul_of_nonneg_right hepsilon1 ha.le
  nlinarith

end Erdos3

end

section

namespace Erdos3

noncomputable def residualCapEnvelope (ι : Type*) [Fintype ι] [DecidableEq ι] (degree : ℕ) : ℝ :=
  1 + 2 * ((lowDegreeCoordinateSets ι degree).card : ℝ) * 2 ^ degree

theorem residualCapEnvelope_one_le (ι : Type*) [Fintype ι] [DecidableEq ι] (degree : ℕ) :
    1 ≤ residualCapEnvelope ι degree := by
  unfold residualCapEnvelope
  exact le_add_of_nonneg_right (by positivity)

theorem residueTruncationCap_le_envelope (ι : Type*) [Fintype ι] [DecidableEq ι]
    (degree : ℕ) {eta : ℝ} (heta : eta ≤ 1) :
    residueTruncationCap ι degree eta ≤ residualCapEnvelope ι degree := by
  have h := mul_le_mul_of_nonneg_left (show 1 + eta ≤ 2 by linarith)
    (show 0 ≤ ((lowDegreeCoordinateSets ι degree).card : ℝ) * 2 ^ degree by positivity)
  unfold residueTruncationCap residualCapEnvelope
  nlinarith

theorem residualCapEnvelope_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (degree : ℕ) {P : ℝ} (hP : 0 ≤ P) (hcount : (Fintype.card ι : ℝ) ≤ Real.exp P) :
    residualCapEnvelope ι degree ≤ Real.exp ((degree : ℝ) * (P + 2) + 2) := by
  have hs := lowDegreeCoordinateSets_card_le_exp hP hcount degree
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ degree ≤ Real.exp (degree : ℝ) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo degree
    simpa only [← Real.exp_nat_mul, mul_one] using h
  have hprod : ((lowDegreeCoordinateSets ι degree).card : ℝ) * 2 ^ degree ≤
      Real.exp ((degree : ℝ) * (P + 2)) := by
    apply (mul_le_mul hs hp (by positivity) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : 1 ≤ Real.exp ((degree : ℝ) * (P + 2)) := Real.one_le_exp_iff.mpr (by positivity)
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  unfold residualCapEnvelope
  calc
    _ ≤ 3 * Real.exp ((degree : ℝ) * (P + 2)) := by nlinarith
    _ ≤ Real.exp 2 * Real.exp ((degree : ℝ) * (P + 2)) := mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def physicalResidualPairBudget {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (k : J) (Q : ℕ)
    (C κ δ : ℝ) (degree : ℕ) (eta ρ : ℝ) : ℝ :=
  ((translatedIntegerBox lo N).card : ℝ) ^ 2 / (∏ i, H i ^ 2) *
    ((smoothPairKernelCap (Fintype.card I) k C κ : ℝ) * (eta * residueTruncationCap (BoundedPrime Q) degree eta) ^ 2 +
      (fullSmoothPairError (Fintype.card I) k Q C κ δ + (smoothPairKernelLip (Fintype.card I) k C κ : ℝ) * ρ) *
        (2 : ℝ) ^ Fintype.card I * (1 + eta * residueTruncationCap (BoundedPrime Q) degree eta ^ 2))

theorem physicalResidualPairBudget_nonneg {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (k : J) (Q : ℕ)
    (C κ δ : ℝ) (degree : ℕ) (eta ρ : ℝ) (hδ : 0 ≤ δ) (heta : 0 ≤ eta) (hρ : 0 ≤ ρ) :
    0 ≤ physicalResidualPairBudget lo N H k Q C κ δ degree eta ρ := by
  have he := fullSmoothPairError_nonneg (Fintype.card I) k Q C κ δ hδ
  unfold physicalResidualPairBudget
  positivity

theorem uniform_physical_residual_correlation {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (t u : J → ℤ) (k0 : J)
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : ∀ j, |(t j : ℝ) / L| ≤ C) (hu : ∀ j, |(u j : ℝ) / L| ≤ C)
    (hgap : ∃ k : J, u k - t k ≠ 0 ∧ κ ≤ |((u k - t k : ℤ) : ℝ) / L|)
    (hQ : affinePairModulus t u ≤ Q)
    (hmesh : ∀ i, 2 * C * L ^ 2 / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k0}) * smoothPairRowLipschitz k0 * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f (smoothAffineSample t z.val) *
        physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree g (smoothAffineSample u z.val))| ≤
      physicalResidualPairBudget lo N H k0 Q C κ δ degree eta ρ := by
  obtain ⟨k, hne, hk⟩ := hgap
  have hsmallk : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k * δ ≤ 1 / 2 := by
    simpa only [smoothPair_pivot_card, smoothPairRowLipschitz_pivot k k0] using hsmall
  have h := bounded_prime_physical_residual_correlation t u k hne H Q hH hL hC hκ hδ hδ1 ht hu hk hQ
    (fun i => normalized_pair_mesh_bound (t k) (u k) (zero_lt_one.trans_le hL) (hH i) (ht k) (hu k) (hmesh i))
    hsmallk origin hZ lo N hside degree f g hf hg eta ρ modLog dimLog accLog hρ heta hmodLog hacc hQlog hdim
    hlarge hwhole hlength hQdegree
  simpa only [physicalResidualPairBudget, smoothPairKernelCap_pivot (Fintype.card I) k k0,
    smoothPairKernelLip_pivot (Fintype.card I) k k0, fullSmoothPairError_pivot (Fintype.card I) k k0] using h

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalPairPointAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A epsilon : ℝ) : ℝ :=
  residualPointAccuracy (A ^ (2 * n)) (2 ^ n) (smoothPairErrorCoefficient n k Q C κ)
    ((4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k) epsilon

noncomputable def physicalPairGridAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ A epsilon : ℝ) : ℝ :=
  residualGridAccuracy (A ^ (2 * n)) (2 ^ n) (smoothPairKernelLip n k C κ) epsilon

noncomputable def physicalPairMeanAccuracy {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ A : ℝ) (degree : ℕ) (epsilon : ℝ) : ℝ :=
  residualMeanAccuracy (A ^ (2 * n)) (smoothPairKernelCap n k C κ)
    (residualCapEnvelope (BoundedPrime Q) degree) epsilon

theorem physicalPairPointAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let delta := physicalPairPointAccuracy n k Q C κ A epsilon
    0 < delta ∧ delta ≤ 1 ∧
      6 * A ^ (2 * n) * (2 : ℝ) ^ n * smoothPairErrorCoefficient n k Q C κ * delta ≤ epsilon ∧
      ((4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k}) * smoothPairRowLipschitz k) * delta ≤ 1 / 2 :=
  residualPointAccuracy_spec (by positivity) (by positivity) (smoothPairErrorCoefficient_nonneg n k Q C κ)
    (by positivity) heps

theorem physicalPairGridAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (C κ : ℝ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let rho := physicalPairGridAccuracy n k C κ A epsilon
    0 < rho ∧ rho ≤ 1 ∧
      6 * A ^ (2 * n) * (2 : ℝ) ^ n * (smoothPairKernelLip n k C κ : ℝ) * rho ≤ epsilon :=
  residualGridAccuracy_spec (by positivity) (by positivity) (NNReal.coe_nonneg _) heps

theorem physicalPairMeanAccuracy_spec {J : Type*} [Fintype J] [DecidableEq J]
    (n : ℕ) (k : J) (Q : ℕ) (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon) :
    let eta := physicalPairMeanAccuracy n k Q C κ A degree epsilon
    let V := residualCapEnvelope (BoundedPrime Q) degree
    0 < eta ∧ eta ≤ 1 ∧ eta * V ^ 2 ≤ 1 ∧
      3 * A ^ (2 * n) * (smoothPairKernelCap n k C κ : ℝ) * eta * V ^ 2 ≤ epsilon :=
  residualMeanAccuracy_spec (by positivity) (NNReal.coe_nonneg _) heps

theorem physicalResidualPairBudget_of_accuracies {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ) (hH : ∀ i, 0 < H i) (k : J) (Q : ℕ)
    (C κ : ℝ) (degree : ℕ) {A epsilon : ℝ} (hA : 0 ≤ A) (heps : 0 < epsilon)
    (hside : ∀ i, (N i : ℝ) ≤ A * H i) :
    let delta := physicalPairPointAccuracy (Fintype.card I) k Q C κ A epsilon
    let rho := physicalPairGridAccuracy (Fintype.card I) k C κ A epsilon
    let eta := physicalPairMeanAccuracy (Fintype.card I) k Q C κ A degree epsilon
    physicalResidualPairBudget lo N H k Q C κ delta degree eta rho ≤ epsilon := by
  let delta := physicalPairPointAccuracy (Fintype.card I) k Q C κ A epsilon
  let rho := physicalPairGridAccuracy (Fintype.card I) k C κ A epsilon
  let eta := physicalPairMeanAccuracy (Fintype.card I) k Q C κ A degree epsilon
  have hd := physicalPairPointAccuracy_spec (Fintype.card I) k Q C κ hA heps
  have hr := physicalPairGridAccuracy_spec (Fintype.card I) k C κ hA heps
  have he := physicalPairMeanAccuracy_spec (Fintype.card I) k Q C κ degree hA heps
  have hd0 : 0 ≤ delta := hd.1.le
  have hr0 : 0 ≤ rho := hr.1.le
  have he0 : 0 ≤ eta := he.1.le
  have hfull := fullSmoothPairError_nonneg (Fintype.card I) k Q C κ delta hd0
  have hcap0 := residueTruncationCap_nonneg (BoundedPrime Q) degree he.1.le
  have hcap := residueTruncationCap_le_envelope (BoundedPrime Q) degree he.2.1
  have hM : 0 ≤ A ^ (2 * Fintype.card I) := by positivity
  have halloc := residual_three_term_budget hM (NNReal.coe_nonneg (smoothPairKernelCap (Fintype.card I) k C κ))
    (smoothPairErrorCoefficient_nonneg (Fintype.card I) k Q C κ)
    (NNReal.coe_nonneg (smoothPairKernelLip (Fintype.card I) k C κ))
    (by positivity : (0 : ℝ) ≤ 2 ^ Fintype.card I)
    hcap0 hcap he.1.le he.2.1 hd.1.le hr.1.le he.2.2.1 he.2.2.2 hd.2.2.1 hr.2.2
  have hpoint := fullSmoothPairError_le_linear (Fintype.card I) k Q C κ hd.1.le hd.2.1
  dsimp only
  unfold physicalResidualPairBudget
  apply le_trans _ halloc
  apply mul_le_mul (translated_box_pair_volume_le lo N H hH hside) _ (by positivity) hM
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact add_le_add hpoint le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem retained_physical_residual_correlation {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (k0 : J) (D r : ℕ) (anchor parLo parHi : J → ℤ)
    (x y : ∀ j, Finset.Ico (parLo j) (parHi j))
    (H : I → ℝ) {L C κ δ : ℝ} (Q : ℕ) (hH : ∀ i, 0 < H i)
    (hL : 1 ≤ L) (hC : 1 ≤ C) (hκ : 0 < κ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hleft : ∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C)
    (hright : ∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C)
    (hgap : κ * L ≤ (D : ℝ) * (r + 1 : ℕ))
    (hgood : ¬ affineParameterBadPair D Q r anchor (fun j => (x j).val) (fun j => (y j).val))
    (hmesh : ∀ i, 2 * C * L ^ 2 / H i ≤ δ)
    (hsmall : (4 : ℝ) ^ (2 + Fintype.card {j : J // j ≠ k0}) * smoothPairRowLipschitz k0 * δ ≤ 1 / 2)
    (origin : Option J × I → ℤ)
    (hZ : 0 < shiftedSmoothProductMass (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1))
    (lo : I → ℤ) (N : I → ℕ) (hside : ∀ i, (Q : ℝ) ≤ (N i : ℝ))
    (degree : ℕ) (f g : (I → ℤ) → ℝ)
    (hf : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x ∈ translatedIntegerBox lo N, 0 ≤ g x ∧ g x ≤ 1)
    (eta ρ modLog dimLog accLog : ℝ) (hρ : 0 ≤ ρ) (heta : eta ≤ 1)
    (hmodLog : 0 ≤ modLog) (hacc : Real.exp (-accLog) ≤ eta)
    (hQlog : (Q : ℝ) ≤ Real.exp modLog)
    (hdim : (Fintype.card I : ℝ) ≤ Real.exp dimLog)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (hlength : ∀ i, Real.exp (modLog * (2 * degree : ℕ) + accLog + dimLog + 1) ≤ ρ * H i / 4)
    (hQdegree : Q ≤ 2 ^ degree) :
    let P := normalizedBoxPartitions N H ρ hlarge hwhole
    let hpos := normalizedBoxPartitions_positive N H ρ hlarge hwhole
    |(smoothSourceFiniteWeights (fun z => (origin z : ℝ))
      (fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1)
      (fun z => smoothPairCoefficientScale_pos (hH z.2) (zero_lt_one.trans_le hL) z.1) hZ).mean
      (fun z => physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree f (smoothAffineSample (fun j => anchor j + (D : ℤ) * (x j).val) z.val) *
        physicalBoxResidual lo N P hpos (boundedPrimePower Q) degree g (smoothAffineSample (fun j => anchor j + (D : ℤ) * (y j).val) z.val))| ≤
      physicalResidualPairBudget lo N H k0 Q C κ δ degree eta ρ := by
  obtain ⟨hQ, hpivot⟩ := retained_affine_pair_geometry D Q r anchor (fun j => (x j).val) (fun j => (y j).val)
    (zero_lt_one.trans_le hL) hκ hgap hgood
  exact uniform_physical_residual_correlation
    (fun j => anchor j + (D : ℤ) * (x j).val) (fun j => anchor j + (D : ℤ) * (y j).val)
    k0 H Q hH hL hC hκ hδ hδ1
    (fun j => affineInterval_normalized_cap D (anchor j) (parLo j) (parHi j) (x j).val
      (zero_lt_one.trans_le hL) (x j).property (hleft j) (hright j))
    (fun j => affineInterval_normalized_cap D (anchor j) (parLo j) (parHi j) (y j).val
      (zero_lt_one.trans_le hL) (y j).property (hleft j) (hright j))
    hpivot hQ hmesh hsmall origin hZ lo N hside degree f g hf hg eta ρ modLog dimLog accLog hρ heta hmodLog
    hacc hQlog hdim hlarge hwhole hlength hQdegree

end Erdos3

end

section

namespace Erdos3

variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def physicalPairCoefficientLog (n d : ℕ) (P : ℝ) : ℝ :=
  30 + 2 * n * P + 2 * n + smoothPairErrorLog n d P +
    n * (5 * P + 11) + 10 * P + 4 * (2 + d)

theorem physicalPairCoefficientLog_bounds (n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalPairCoefficientLog n d P ∧
    P ≤ physicalPairCoefficientLog n d P ∧
    6 + 2 * n * P + 2 * n + smoothPairErrorLog n d P ≤ physicalPairCoefficientLog n d P ∧
    2 + 4 * (2 + d) + P ≤ physicalPairCoefficientLog n d P ∧
    20 + 2 * n * P + 2 * n + n * (5 * P + 11) + 9 * P ≤ physicalPairCoefficientLog n d P := by
  have hF := smoothPairErrorLog_nonneg n d hP
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hnp := mul_nonneg hn hP
  unfold physicalPairCoefficientLog
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem physicalPairPowerBounds (n : ℕ) {A P : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ Real.exp P) :
    A ^ (2 * n) ≤ Real.exp (2 * n * P) ∧ (2 : ℝ) ^ n ≤ Real.exp (2 * n) := by
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  constructor
  · apply (pow_le_pow_left₀ hA0 hA (2 * n)).trans_eq
    rw [← Real.exp_nat_mul]
    push_cast
    rfl
  · apply (pow_le_pow_left₀ (by norm_num) h2 n).trans_eq
    rw [← Real.exp_nat_mul]
    congr 1
    ring

theorem physicalPairPointGridAccuracy_inverse_le_exp (n : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon)
    (hn : (n : ℝ) ≤ Real.exp P) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P) (hcard : (Fintype.card J : ℝ) ≤ Real.exp P)
    (hrow : (smoothPairRowLipschitz k : ℝ) ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (physicalPairPointAccuracy n k Q C κ A epsilon)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) P + 2) ∧
    (physicalPairGridAccuracy n k C κ A epsilon)⁻¹ ≤
      Real.exp (2 * physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k}) P + 2) := by
  let d := Fintype.card {j : J // j ≠ k}
  have hlogs := physicalPairCoefficientLog_bounds n d hP
  obtain ⟨hM, hS⟩ := physicalPairPowerBounds n hA0 hA
  have hF := smoothPairErrorCoefficient_le_exp n k Q hP hC0 hκ0 hn hQ hC hκ hcard hrow hpow
  have hK := smoothPairKernelLip_le_exp n k hP hC0 hκ0 hn hC hκ hrow hpow
  have hm := smoothPairMeshCoefficient_le_exp k hrow
  have h6 : (6 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hF0 := smoothPairErrorCoefficient_nonneg n k Q C κ
  have heps' : epsilon⁻¹ ≤ Real.exp (physicalPairCoefficientLog n d P) :=
    heps.trans (Real.exp_le_exp.mpr hlogs.2.1)
  constructor
  · apply residualPointAccuracy_inverse_le_exp (by positivity) (by positivity) hF0 (by positivity)
      heps0 hlogs.1
    · calc
        _ ≤ Real.exp 6 * Real.exp (2 * n * P) * Real.exp (2 * n) *
            Real.exp (smoothPairErrorLog n d P) := by gcongr
        _ = Real.exp (6 + 2 * n * P + 2 * n + smoothPairErrorLog n d P) := by
          simp only [← Real.exp_add]
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.1
    · calc
        _ ≤ Real.exp 2 * Real.exp (4 * (2 + (d : ℝ)) + P) := by gcongr
        _ = Real.exp (2 + 4 * (2 + (d : ℝ)) + P) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.2.1
    · exact heps'
  · apply residualGridAccuracy_inverse_le_exp (by positivity) (by positivity) (by positivity)
      heps0 hlogs.1
    · calc
        _ ≤ Real.exp 6 * Real.exp (2 * n * P) * Real.exp (2 * n) *
            Real.exp ((n : ℝ) * (5 * P + 11) + 9 * P + 14) := by gcongr
        _ = Real.exp (20 + 2 * n * P + 2 * n + n * (5 * P + 11) + 9 * P) := by
          simp only [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := Real.exp_le_exp.mpr hlogs.2.2.2.2
    · exact heps'

noncomputable def physicalPairMeanLog (n degree : ℕ) (P : ℝ) : ℝ :=
  2 * ((degree : ℝ) * (P + 2) + 2) + 4 + 2 * n * P + n * (5 * P + 11) + P

theorem physicalPairMeanLog_bounds (n degree : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ physicalPairMeanLog n degree P ∧ P ≤ physicalPairMeanLog n degree P := by
  unfold physicalPairMeanLog
  constructor
  · positivity
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ degree := Nat.cast_nonneg _
    nlinarith [mul_nonneg hn hP, mul_nonneg hd hP]

theorem physicalPairMeanAccuracy_inverse_le_exp (n degree : ℕ) (k : J) (Q : ℕ)
    {C κ A epsilon P : ℝ} (hP : 0 ≤ P) (hC0 : 0 ≤ C) (hκ0 : 0 < κ)
    (hA0 : 0 ≤ A) (heps0 : 0 < epsilon) (hQ : (Q : ℝ) ≤ Real.exp P)
    (hC : C ≤ Real.exp P) (hκ : κ⁻¹ ≤ Real.exp P) (hA : A ≤ Real.exp P)
    (heps : epsilon⁻¹ ≤ Real.exp P)
    (hpow : (2 : ℝ) ^ Fintype.card {j : J // j ≠ k} ≤ Real.exp P) :
    (physicalPairMeanAccuracy n k Q C κ A degree epsilon)⁻¹ ≤
      Real.exp (2 * physicalPairMeanLog n degree P + 2) := by
  have hlogs := physicalPairMeanLog_bounds n degree hP
  have hpower := (physicalPairPowerBounds n hA0 hA).1
  have hK := smoothPairKernelCap_le_exp n k hP hC0 hκ0 hC hκ hpow
  have hcount : (Fintype.card (BoundedPrime Q) : ℝ) ≤ Real.exp P :=
    (Nat.cast_le.mpr (boundedPrime_card_le Q)).trans hQ
  have hV := residualCapEnvelope_le_exp degree hP hcount
  have hV0 := zero_le_one.trans (residualCapEnvelope_one_le (BoundedPrime Q) degree)
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hprod : 3 * A ^ (2 * n) * (smoothPairKernelCap n k C κ : ℝ) ≤
      Real.exp (3 + 2 * n * P + n * (5 * P + 11)) := by
    calc
      _ ≤ Real.exp 3 * Real.exp (2 * n * P) * Real.exp ((n : ℝ) * (5 * P + 11)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]
  have hsum := one_add_le_exp_succ (by positivity : 0 ≤ 3 + 2 * n * P + n * (5 * P + 11)) hprod
  apply residualMeanAccuracy_inverse_le_exp (by positivity) (by positivity) heps0 hlogs.1
  · calc
      _ ≤ (Real.exp ((degree : ℝ) * (P + 2) + 2)) ^ 2 *
          Real.exp ((3 + 2 * n * P + n * (5 * P + 11)) + 1) := by gcongr
      _ = Real.exp (2 * ((degree : ℝ) * (P + 2) + 2) + 4 + 2 * n * P + n * (5 * P + 11)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold physicalPairMeanLog; linarith)
  · exact heps.trans (Real.exp_le_exp.mpr hlogs.2)

end Erdos3

end

end OAI
