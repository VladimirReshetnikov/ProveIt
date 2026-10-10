import GowersSzemeredi.Proofs16IndependentChoiceSelection

/-! Exact replacement-coordinate counts. A bad configuration is counted
once for every possible old value at the replaced coordinate; all other
coordinates remain unchanged. This controls heavy alternative failures. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def alternativeCoordinateChoices {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (B : Finset (I → V)) (i : I) (b : I → V) : Finset V :=
  (F i).filter fun v => Function.update b i v ∈ B

def heavyAlternativeConfigurations {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (B : Finset (I → V)) (i : I) (tau : Real) : Finset (I → V) :=
  (Fintype.piFinset F).filter fun b => tau < ((alternativeCoordinateChoices F B i b).card : Real)

theorem coordinate_update_restore {I V : Type*} [DecidableEq I] (b : I → V) (i : I) (v : V) :
    Function.update (Function.update b i v) i (b i) = b := by
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hj]

/-- Exact double counting, with no loss from the unused coordinates. -/
theorem alternative_coordinate_total {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (B : Finset (I → V)) (i : I)
    (hB : ∀ b ∈ B, ∀ j, b j ∈ F j) :
    (∑ b ∈ Fintype.piFinset F, (alternativeCoordinateChoices F B i b).card) = (F i).card*B.card := by
  classical
  let S := (Fintype.piFinset F).sigma fun b => alternativeCoordinateChoices F B i b
  let P := B ×ˢ F i
  have hforward : S.card ≤ P.card := by
    apply Finset.card_le_card_of_injOn (fun p => (Function.update p.1 i p.2,p.1 i))
    · intro p hp
      obtain ⟨hpF,hpAlt⟩ := Finset.mem_sigma.mp hp
      exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp hpAlt).2,Fintype.mem_piFinset.mp hpF i⟩
    · intro p hp q hq he
      have hup := congrArg Prod.fst he
      have hold := congrArg Prod.snd he
      have hbase : p.1 = q.1 := by
        funext j
        by_cases hj : j = i
        · subst j
          exact hold
        · simpa only [Function.update_of_ne hj] using congrFun hup j
      have hnew : p.2 = q.2 := by simpa using congrFun hup i
      cases p with | mk p1 p2 =>
        cases q with | mk q1 q2 =>
          dsimp only at hbase hnew
          subst q1
          exact Sigma.ext rfl (heq_of_eq hnew)
  have hbackward : P.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun p => (⟨Function.update p.1 i p.2,p.1 i⟩ : Sigma fun _ : I → V => V))
    · intro p hp
      obtain ⟨hpB,hpF⟩ := Finset.mem_product.mp hp
      refine Finset.mem_sigma.mpr ⟨Fintype.mem_piFinset.mpr ?_, Finset.mem_filter.mpr ⟨hB _ hpB i, ?_⟩⟩
      · intro j
        by_cases hj : j = i
        · subst j
          simpa using hpF
        · simpa only [Function.update_of_ne hj] using hB _ hpB j
      · simpa only [coordinate_update_restore] using hpB
    · intro p hp q hq he
      have hup := congrArg Sigma.fst he
      have hold := congrArg (fun z : Sigma fun _ : I → V => V => z.2) he
      have hbase : p.1 = q.1 := by
        funext j
        by_cases hj : j = i
        · subst j
          exact hold
        · simpa only [Function.update_of_ne hj] using congrFun hup j
      have hnew : p.2 = q.2 := by simpa using congrFun hup i
      exact Prod.ext hbase hnew
  have heq := Nat.le_antisymm hforward hbackward
  simpa only [S,P,Finset.card_sigma,Finset.card_product,Nat.mul_comm] using heq

/-- The heavy replacement configurations are charged to the original bad
configurations, with one factor for the unused old coordinate. -/
theorem heavy_alternative_configurations_scaled {I V : Type*}
    [Fintype I] [DecidableEq I] [DecidableEq V]
    (F : I → Finset V) (B : Finset (I → V)) (i : I) (tau : Real)
    (hB : ∀ b ∈ B, ∀ j, b j ∈ F j) :
    tau*((heavyAlternativeConfigurations F B i tau).card : Real) ≤ (F i).card*(B.card : Real) := by
  classical
  let H := heavyAlternativeConfigurations F B i tau
  have htotal : (∑ b ∈ Fintype.piFinset F, ((alternativeCoordinateChoices F B i b).card : Real)) =
      (F i).card*(B.card : Real) := by exact_mod_cast alternative_coordinate_total F B i hB
  calc tau*(H.card : Real) = ∑ _b ∈ H, tau := by simp [mul_comm]
    _ ≤ ∑ b ∈ H, ((alternativeCoordinateChoices F B i b).card : Real) :=
      Finset.sum_le_sum fun b hb => (Finset.mem_filter.mp hb).2.le
    _ ≤ ∑ b ∈ Fintype.piFinset F, ((alternativeCoordinateChoices F B i b).card : Real) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := htotal

end LeanProofs.GowersSzemeredi
