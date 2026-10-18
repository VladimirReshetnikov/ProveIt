import GowersSzemeredi.Proofs18IntervalTransfer

/-!
# Affine transport for the density-increment iteration

Index a proper modular progression by an ordinary integer interval.  Pulling
back a set preserves its relative cardinality, and a progression found in a
sufficiently large new cyclic model transports back to the original set.
The old modulus need not be prime: properness of the original progression
already prevents the transported common difference from vanishing.

`ModAP.card_cyclic_pullback`, `ModAP.card_pullback`,
`ModAP.hasModAP_of_cyclic_pullback`, `ModAP.hasModAP_of_hasNatAP_pullback` and
`ModAP.image_pullback` are in `Proofs18AffineTransferSide`, outside the final
route. -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Parametrization of a modular progression by natural indices. -/
def ModAP.index {N : Nat} (P : ModAP N) (i : Nat) : ZMod N :=
  P.start + (i : ZMod N) * P.step

/-- A proper modular progression has an injective index parametrization. -/
theorem ModAP.index_injOn {N : Nat} (P : ModAP N) (hP : P.IsProper) :
    Set.InjOn P.index (Finset.range P.length) := by
  have hcard : (Finset.univ.image
      (fun i : Fin P.length => P.start + (i : Nat) * P.step)).card =
      (Finset.univ : Finset (Fin P.length)).card := by
    simpa only [ModAP.IsProper, ModAP.carrier, Finset.card_univ, Fintype.card_fin] using hP
  have hinj := Finset.card_image_iff.mp hcard
  intro i hi j hj hij
  have h := hinj (Finset.mem_univ (⟨i, Finset.mem_range.mp hi⟩ : Fin P.length))
    (Finset.mem_univ (⟨j, Finset.mem_range.mp hj⟩ : Fin P.length)) hij
  exact congrArg Fin.val h

/-- The index set of `A` on `P`. -/
def ModAP.pullback {N : Nat} (P : ModAP N) (A : Finset (ZMod N)) : Finset Nat :=
  (Finset.range P.length).filter fun i => P.index i ∈ A

@[simp] theorem ModAP.mem_pullback {N : Nat} (P : ModAP N)
    (A : Finset (ZMod N)) (i : Nat) :
    i ∈ P.pullback A ↔ i < P.length ∧ P.index i ∈ A := by
  simp [ModAP.pullback]

end LeanProofs.GowersSzemeredi
