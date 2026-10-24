import DiophantineConsistency.ObjectPairingInjective

/-! # Internal unpairing and its unique quartic graph -/
noncomputable section
namespace DiophantineConsistency.ObjectUnpair
set_option maxRecDepth 16000
attribute [local irreducible] ObjectPairingSyntax.expression
open SetTheory SetTheory.Form ObjectOmegaSemiring
open LeanProofs.BoundedZFCConsistency
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private theorem exists_pair (z : N H) :
    ∃ p : N H × N H,z=ObjectNatPairing.pair H p.1 p.2 := by
  obtain ⟨a,b,h⟩ := ObjectPairingSurjective.pair_surjective H z
  exact ⟨(a,b),h⟩

/-- A semantic operation selected from the total, unique definable graph.
The literal quartic itself contains no selected representation data. -/
def unpair (z : N H) : N H × N H := Classical.choose (exists_pair H z)

theorem pair_unpair (z : N H) :
    ObjectNatPairing.pair H (unpair H z).1 (unpair H z).2=z :=
  (Classical.choose_spec (exists_pair H z)).symm

theorem unpair_pair (a b : N H) : unpair H (ObjectNatPairing.pair H a b)=(a,b) := by
  apply Prod.ext
  · exact ((ObjectPairingInjective.pair_eq_pair_iff H _ _ _ _).mp
      (pair_unpair H (ObjectNatPairing.pair H a b))).1
  · exact ((ObjectPairingInjective.pair_eq_pair_iff H _ _ _ _).mp
      (pair_unpair H (ObjectNatPairing.pair H a b))).2

theorem unpair_eq_iff (z a b : N H) :
    unpair H z=(a,b) ↔ z=ObjectNatPairing.pair H a b := by
  constructor
  · intro h
    simpa only [h] using (pair_unpair H z).symm
  · rintro rfl
    exact unpair_pair H a b

/-- The graph agrees with the actual external checker's `Nat.unpair` on
all numeral inputs, while remaining total on nonstandard inputs. -/
theorem unpair_cast (n : ℕ) :
    unpair H (n : N H)=((n.unpair.1 : N H),(n.unpair.2 : N H)) := by
  apply (unpair_eq_iff H _ _ _).mpr
  rw [ObjectNatPairing.pair_cast,Nat.pair_unpair]

def pairEquiv : N H × N H ≃ N H where
  toFun p := ObjectNatPairing.pair H p.1 p.2
  invFun := unpair H
  left_inv p := unpair_pair H p.1 p.2
  right_inv := pair_unpair H

/-- Two full quartic graph certificates for one code have the same pair
of decoded values, including both graph's own natural guards. -/
def inverseUniqueForm : Form := sealF
  (fImp (fAnd (ObjectPairingGraph.graphForm 4 3 2) (ObjectPairingGraph.graphForm 4 1 0))
    (fAnd (fEq 3 1) (fEq 2 0)))

theorem sentence_inverseUniqueForm : Sentence inverseUniqueForm := Sentence_seal _

theorem zfc_proves_inverse_unique : BProv ZFCax_s [] inverseUniqueForm := by
  refine completeness_inf_context ZFCax_s [] inverseUniqueForm Sentences_ZFC ?_
  intro Dom relation env hmodel _
  let HH := ObjectMultiplication.axioms_of_zfc_model env hmodel
  apply (seal_valid (mem := relation) _).mpr ?_ env
  intro ee h
  obtain ⟨hz,ha,hb⟩ := ObjectPairingGraph.graphForm_naturals HH ee 4 3 2 h.1
  obtain ⟨_,hc,hd⟩ := ObjectPairingGraph.graphForm_naturals HH ee 4 1 0 h.2
  have he1 := (ObjectPairingGraph.graphForm_spec HH ee 4 3 2 hz ha hb).mp h.1
  have he2 := (ObjectPairingGraph.graphForm_spec HH ee 4 1 0 hz hc hd).mp h.2
  have he := (ObjectPairingInjective.pair_eq_pair_iff HH _ _ _ _).mp (he1.symm.trans he2)
  exact ⟨congrArg Subtype.val he.1,congrArg Subtype.val he.2⟩

end DiophantineConsistency.ObjectUnpair
