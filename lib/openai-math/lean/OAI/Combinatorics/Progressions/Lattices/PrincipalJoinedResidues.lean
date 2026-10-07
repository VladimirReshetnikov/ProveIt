import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3

variable {D α : Type*} {B : D → Type*} {h : D → ℕ}

def principalAxisResidueJoin (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (u : PrincipalAxisTuples (α := α) P L) (m : ℕ)
    (r : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) → Option α → ZMod m) :
    PrincipalTupleIndex B h → Option α → ZMod m :=
  fun j i => if hp : P j.1 then ((u ⟨⟨j.1, hp⟩, j.2⟩ i : ℤ) : ZMod m)
    else r ⟨⟨j.1, hp⟩, j.2⟩ i

theorem principalResidueLabel_join (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (u : PrincipalAxisTuples (α := α) P L)
    (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) (m : ℕ) :
    principalResidueLabel m (principalAxisJoin P u v) =
      principalAxisResidueJoin P u m (principalResidueLabel m v) := by
  funext j i
  by_cases hp : P j.1 <;>
    simp only [principalResidueLabel, principalAxisJoin, principalAxisResidueJoin, hp, ↓reduceDIte]

theorem principalSpatialColumns_join_residue {N : Type*} (P : D → Prop) [DecidablePred P]
    {L : PrincipalTupleIndex B h → ℕ} (u : PrincipalAxisTuples (α := α) P L)
    (v : PrincipalAxisTuples (α := α) (fun d => ¬P d) L) (m : ℕ)
    (c : N → ℤ) (index : N → PrincipalTupleIndex B h) :
    integerResidueMatrix (principalSpatialColumns c index (principalAxisJoin P u v)) m =
      principalSpatialResidueColumns m c index (principalAxisResidueJoin P u m (principalResidueLabel m v)) := by
  rw [principalSpatialColumns_residue, principalResidueLabel_join]

end Erdos3

end

end OAI
