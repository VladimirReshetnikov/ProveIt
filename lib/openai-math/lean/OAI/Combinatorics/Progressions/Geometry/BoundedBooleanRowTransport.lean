import OAI.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues

namespace OAI

section

namespace Erdos3

open scoped Classical

theorem boundedBooleanJetRows_family_transport
    {ι α : Type*} [Fintype α] (h : ι → ℕ)
    (P : (O : ι → Type _) → [∀ i, Fintype (O i)] →
      (∀ i, O i → Finset α) → Prop)
    (hyp : P (fun i => BoundedBooleanJet α (h i)) (fun _ => Subtype.val))
    (inst : ∀ i, Fintype {s : Finset α // s ∈ boundedBooleanJetRows α (h i)}) :
    @P (fun i => {s : Finset α // s ∈ boundedBooleanJetRows α (h i)}) inst
      (fun _ => Subtype.val) := by
  let inst0 : ∀ i, Fintype (BoundedBooleanJet α (h i)) := inferInstance
  let Q (O : ι → Type _) (v : ∀ i, O i → Finset α) : Prop :=
    ∀ inst : ∀ i, Fintype (O i), @P O inst v
  have hq : Q (fun i => BoundedBooleanJet α (h i)) (fun _ => Subtype.val) := by
    intro inst
    exact (congrArg (fun ft : ∀ i, Fintype (BoundedBooleanJet α (h i)) =>
      @P (fun i => BoundedBooleanJet α (h i)) ft (fun _ => Subtype.val))
      (Subsingleton.elim inst0 inst)).mp hyp
  have he : (fun i (s : Finset α) => s.card ≤ h i) =
      (fun i s => s ∈ boundedBooleanJetRows α (h i)) := by
    funext i s
    exact propext (mem_boundedBooleanJetRows (h i) s).symm
  have hnew := (congrArg (fun R : ι → Finset α → Prop =>
    Q (fun i => {s // R i s}) (fun _ => Subtype.val)) he).mp hq
  exact hnew inst

end Erdos3

end

end OAI
