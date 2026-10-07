import GowersSzemeredi.Proofs13FejerArrangementVertices

/-! Transport subset-selection counts and the exceptional parameter bound
to the catalogue arrangement counts without losing degenerate arrangements. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

private theorem fejer_countWhere_card {X : Type*} [Fintype X] (P : X → Prop) :
    countWhere P = @Fintype.card {x // P x} (by
      classical
      infer_instance) := by
  classical
  simp only [countWhere, Fintype.card_subtype]

private theorem fejer_countWhere_subtype {X : Type*} [Fintype X] (P Q : X → Prop)
    [Fintype {x // P x}] (h : ∀ x, Q x → P x) :
    countWhere (fun x : {x // P x} => Q x.1) = countWhere Q := by
  classical
  rw [fejer_countWhere_card, fejer_countWhere_card]
  apply Fintype.card_congr
  exact
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun x => ⟨⟨x.1, h x.1 x.2⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem fejer_countWhere_sum {X : Type*} [Fintype X] (P : X → Prop) :
    countWhere P = ∑ x : X, @ite Nat (P x) (Classical.propDecidable _) 1 0 := by
  classical
  simp [countWhere]

private theorem fejer_countWhere_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) : countWhere P = countWhere (fun x => P (e x)) := by
  classical
  simp_rw [fejer_countWhere_sum]
  exact (e.sum_comp (fun x => if P x then 1 else 0)).symm

def fejerArrangementEdges {N : Nat} [NeZero N] (U : Finset (Pair N))
    (P : DArrangement N 8 → Prop) : Finset (FejerBalancedArrangement N) := by
  classical
  exact Finset.univ.filter (fun R => R.1.IsIn U ∧ P R.1)

theorem fejerArrangementEdges_card {N : Nat} [NeZero N] (U : Finset (Pair N))
    (P : DArrangement N 8 → Prop) :
    (fejerArrangementEdges U P).card = countWhere (fun R => R.IsIn U ∧ P R) := by
  classical
  have ht := fejer_countWhere_subtype (fun R : DArrangement N 8 => IsAdditiveTuple R.x)
    (fun R => R.IsIn U ∧ P R) (fun _ h => h.1.1)
  convert ht using 1
  unfold fejerArrangementEdges countWhere
  congr 1
  ext R
  simp

theorem fejerArrangementEdges_good_card {N : Nat} [NeZero N] (U : Finset (Pair N))
    (phi : Pair N → ZMod N) :
    (fejerArrangementEdges U (fun R => R.IsRespected phi)).card = respectedArrangementCount 8 U phi :=
  fejerArrangementEdges_card U _

theorem fejerArrangementEdges_partition_card {N : Nat} [NeZero N] (U : Finset (Pair N))
    (P : DArrangement N 8 → Prop) :
    (fejerArrangementEdges U P).card + (fejerArrangementEdges U (fun R => ¬ P R)).card =
      arrangementCount 8 U := by
  classical
  rw [fejerArrangementEdges_card, fejerArrangementEdges_card]
  unfold arrangementCount
  simp_rw [fejer_countWhere_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _
  by_cases hu : R.IsIn U <;> by_cases hp : P R <;> simp [hu, hp]

theorem fejerArrangementEdges_carrier {N : Nat} [NeZero N] (U : Finset (Pair N))
    (P : DArrangement N 8 → Prop) (R : FejerBalancedArrangement N)
    (hR : R ∈ fejerArrangementEdges U P) :
    Finset.univ.image (fejerArrangementVertex R.1) ⊆ U := by
  classical
  apply (fejerArrangement_carrier_iff R.1 R.2 U).mpr
  exact (Finset.mem_filter.mp hR).2.1

theorem fejerArrangementEdges_restrict {N : Nat} [NeZero N] (U S : Finset (Pair N))
    (hS : S ⊆ U) (P : DArrangement N 8 → Prop) :
    ((fejerArrangementEdges U P).filter fun R => Finset.univ.image (fejerArrangementVertex R.1) ⊆ S) =
      fejerArrangementEdges S P := by
  classical
  ext R
  have hmono : R.1.IsIn S → R.1.IsIn U := by
    rintro ⟨hx, hv⟩
    exact ⟨hx, fun i => ⟨hS (hv i).1, hS (hv i).2⟩⟩
  simp only [fejerArrangementEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    fejerArrangement_carrier_iff R.1 R.2 S]
  tauto

def fejerExceptionalArrangements {N L : Nat} [NeZero N] : Finset (FejerBalancedArrangement N) := by
  classical
  exact Finset.univ.filter (fun R => fejerFeatureExceptional (L := L) fejerArrangementFreeSign
    (fejerArrangementEncode R.1))

theorem fejerExceptionalArrangements_card {N L : Nat} [NeZero N] [Fact N.Prime] :
    (fejerExceptionalArrangements (N := N) (L := L)).card ≤ (2 * L) ^ 32 * (2 * N ^ 31) := by
  change countWhere (fun R : FejerBalancedArrangement N =>
    fejerFeatureExceptional (L := L) fejerArrangementFreeSign (fejerArrangementEncode R.1)) ≤ _
  rw [fejer_countWhere_equiv fejerArrangementParametersEquiv]
  change countWhere (fun z : FejerArrangementParameters N =>
    fejerFeatureExceptional (L := L) fejerArrangementFreeSign
      (fejerArrangementEncode (fejerArrangementDecode z))) ≤ _
  simp_rw [fejerArrangementEncode_decode]
  exact fejerFeatureExceptional_count_32 fejerArrangementFreeSign fejerArrangementFreeSign_ne_zero

end LeanProofs.GowersSzemeredi
