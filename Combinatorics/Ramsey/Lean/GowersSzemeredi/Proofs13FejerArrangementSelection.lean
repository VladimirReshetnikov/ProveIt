import GowersSzemeredi.Proofs13FejerArrangementRegularity
import GowersSzemeredi.Proofs13FejerSelection

/-! Arrangement-specific Fejer purification with an explicit score
budget. All structural and counting hypotheses are discharged; the remaining
input is the displayed scalar inequality selecting the kernel length. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_purification_score {N L M : Nat} [NeZero N] [Fact N.Prime]
    (hL : 2 ≤ L) (hML : 2 * M ≤ L) (hLN : L ≤ N)
    (U : Finset (Pair N)) (phi : Pair N → ZMod N)
    (eta mass : Real) (heta : 0 < eta) (hmass : 0 < mass)
    (hbudget : eta * mass ≤
      eta * (respectedArrangementCount 8 U phi : Real) *
        ((((L : Real) ^ 2)⁻¹) ^ 32 * (M : Real) ^ 33) -
      (arrangementCount 8 U : Real) * ((L : Real)⁻¹) ^ 32 -
      (2 * (L : Real)) ^ 32 * (2 * (N : Real) ^ 31)) :
    ∃ S ⊆ U, mass ≤ (respectedArrangementCount 8 S phi : Real) ∧
      (arrangementCount 8 S : Real) ≤ (1 + eta) * (respectedArrangementCount 8 S phi : Real) := by
  classical
  let good := fejerArrangementEdges U (fun R => R.IsRespected phi)
  let bad := fejerArrangementEdges U (fun R => ¬ R.IsRespected phi)
  let exceptional := fejerExceptionalArrangements (N := N) (L := L)
  let vertex := fun R : FejerBalancedArrangement N => fejerArrangementVertex R.1
  have hg : good.card = respectedArrangementCount 8 U phi := fejerArrangementEdges_good_card U phi
  have hb : (bad.card : Real) ≤ (arrangementCount 8 U : Real) := by
    have hp := fejerArrangementEdges_partition_card U (fun R => R.IsRespected phi)
    have hn : bad.card ≤ arrangementCount 8 U := by dsimp [bad]; omega
    exact_mod_cast hn
  have he : (exceptional.card : Real) ≤ (2 * (L : Real)) ^ 32 * (2 * (N : Real) ^ 31) := by
    exact_mod_cast fejerExceptionalArrangements_card (N := N) (L := L)
  have hbase : (0 : Real) ≤ ((L : Real)⁻¹) ^ 32 := by positivity
  have hbudget' : eta * mass ≤ eta * (good.card : Real) *
      ((((L : Real) ^ 2)⁻¹) ^ 32 * (M : Real) ^ 33) -
      (bad.card : Real) * ((L : Real)⁻¹) ^ 32 - exceptional.card := by
    rw [hg]
    have hbb := mul_le_mul_of_nonneg_right hb hbase
    linarith only [hbudget, hbb, he]
  have hgood : ∀ R ∈ good, Finset.univ.image (vertex R) ⊆ U :=
    fun R hR => fejerArrangementEdges_carrier U _ R hR
  have hbad : ∀ R ∈ bad, Finset.univ.image (vertex R) ⊆ U :=
    fun R hR => fejerArrangementEdges_carrier U _ R hR
  have hphi : ∀ R ∈ good,
      ∑ j, (if fejerArrangementPositive j then 1 else -1) * phi (vertex R j) = 0 := by
    intro R hR
    simp_rw [fejerArrangementPositive_coefficient]
    exact (fejerArrangement_respected_iff R.1 phi).mp (Finset.mem_filter.mp hR).2.2
  have hfeature : ∀ R ∈ good, ∑ j, (if fejerArrangementPositive j then 1 else -1) *
      ((vertex R j).1 * (vertex R j).2) = 0 := by
    intro R _
    simp_rw [fejerArrangementPositive_coefficient]
    exact fejerArrangement_feature_sum R.1 R.2
  have hinj : ∀ R ∈ bad, R ∉ exceptional → Function.Injective (vertex R) :=
    fun R _ hr => fejerArrangement_regular_injective hL R hr
  have hdiag : ∀ R ∈ bad, R ∉ exceptional →
      ∀ v : (Option (Fin 15) × Bool) → Fin L × Fin L,
        (fejerPairRelation v (phi ∘ vertex R) = 0 ∧
          fejerPairRelation v ((fun z => z.1 * z.2) ∘ vertex R) = 0) ↔
          ∀ j, (v j).1 = (v j).2 := by
    intro R hR hr
    have hbR : R.1.IsIn U ∧ ¬ R.1.IsRespected phi := by
      simpa [bad, fejerArrangementEdges] using hR
    exact fejerArrangement_regular_diagonal hLN R phi hr hbR.2
  have hcard : Fintype.card (Option (Fin 15) × Bool) = 32 := by decide
  obtain ⟨S, hS, hmassS, hbadS⟩ := exists_subset_fejer_purification (by omega : 0 < L) hML
    U good bad exceptional vertex phi (fun z => z.1 * z.2) (fun _ => fejerArrangementPositive)
    hgood hbad hphi hfeature hinj hdiag eta mass heta hmass (by simpa only [hcard] using hbudget')
  change mass ≤ (((fejerArrangementEdges U (fun R => R.IsRespected phi)).filter
    fun R => Finset.univ.image (fejerArrangementVertex R.1) ⊆ S).card : Real) at hmassS
  rw [fejerArrangementEdges_restrict U S hS, fejerArrangementEdges_good_card] at hmassS
  change (((fejerArrangementEdges U (fun R => ¬ R.IsRespected phi)).filter
    fun R => Finset.univ.image (fejerArrangementVertex R.1) ⊆ S).card : Real) ≤
    eta * (((fejerArrangementEdges U (fun R => R.IsRespected phi)).filter
      fun R => Finset.univ.image (fejerArrangementVertex R.1) ⊆ S).card : Real) at hbadS
  rw [fejerArrangementEdges_restrict U S hS, fejerArrangementEdges_restrict U S hS,
    fejerArrangementEdges_good_card] at hbadS
  have hpart : (respectedArrangementCount 8 S phi : Real) +
      (fejerArrangementEdges S (fun R => ¬ R.IsRespected phi)).card = arrangementCount 8 S := by
    have hp := fejerArrangementEdges_partition_card S (fun R => R.IsRespected phi)
    rw [fejerArrangementEdges_good_card] at hp
    exact_mod_cast hp
  refine ⟨S, hS, hmassS, ?_⟩
  nlinarith only [hpart, hbadS]

end LeanProofs.GowersSzemeredi
