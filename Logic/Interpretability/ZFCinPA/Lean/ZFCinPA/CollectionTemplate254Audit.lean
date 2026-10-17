import ZFCinPA.CollectionTemplate254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.SetTheory
open _root_.SetTheory
open _root_.SetTheory.BusyBeaver.ZFC
open _root_.SetTheory.BusyBeaver.ZFC.InternalOrd
open _root_.SetTheory.BusyBeaver.ZFC.InternalRank
open LeanProofs.ZFCinPA.CollectionResources254
open LeanProofs.ZFCinPA.CollectionTemplate254
#print axioms LeanProofs.ZFCinPA.CollectionResources254.leastRank_exists
#print axioms LeanProofs.ZFCinPA.CollectionResources254.totalRank_total
#print axioms LeanProofs.ZFCinPA.CollectionResources254.totalRank_ordinal
#print axioms LeanProofs.ZFCinPA.CollectionResources254.collection
#print axioms LeanProofs.ZFCinPA.CollectionTemplate254.eval_toFormula
#print axioms LeanProofs.ZFCinPA.CollectionTemplate254.models_collection
#print axioms LeanProofs.ZFCinPA.CollectionTemplate254.collection_provable

example {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) (hR : Regular mem)
    (R : V → V → Prop) (hSep : ∀ x a, ∃ s, ∀ c,
      mem c s ↔ mem c a ∧ WitnessRank H R x c)
    {x a : V} (ha : Ord mem a) (hWa : WitnessRank H R x a) :
    ∃ c, LeastRank H R x c := leastRank_exists H hR R hSep ha hWa
example {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
    (R : V → V → Prop) (hSep : ∀ x a, ∃ s, ∀ c,
      mem c s ↔ mem c a ∧ WitnessRank H R x c) :
    ∀ x, ∃! c, TotalRank H R x c := totalRank_total H hR hP R hSep
example {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem)
    (R : V → V → Prop) {x c : V} (hc : TotalRank H R x c) :
    Ord mem c := totalRank_ordinal H R hc
example {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
    (R : V → V → Prop) (h : Resources H R) (a : V) :
    ∃ b, (∀ y, mem y b → ∃ x, R x y) ∧
      ∀ x, mem x a → (∃ y, R x y) → ∃ y, mem y b ∧ R x y :=
  LeanProofs.ZFCinPA.CollectionResources254.collection H hR hP R h a
example {V : Type*} {mem : V → V → Prop} (H : ZFAxioms mem) (hR : Regular mem)
    (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
    (R : V → V → Prop) (h : Resources H R) (a : V) :
    ∃ b, ∀ x, mem x a → ∀ y, R x y → ∃ z, mem z b ∧ R x z := by
  obtain ⟨b,-,hb⟩ := LeanProofs.ZFCinPA.CollectionResources254.collection H hR hP R h a
  exact ⟨b,fun x hx y hxy => hb x hx ⟨y,hxy⟩⟩

section SourceModel
local instance : Language.Mem Lang := ⟨Sum.inl Language.Set.Rel.mem⟩
variable {M : Type*} [Nonempty M] [SetStructure M]
variable [s : Structure Lang M] [Structure.Eq Lang M] [Structure.Mem Lang M]
example (p : Named) {n : Nat} (slots : Nat → SyntacticSemiterm Lang n)
    (b : Fin n → M) (f : Nat → M) :
    (toFormula slots p).Eval b f ↔ NamedSat (fun i => (slots i).val b f) p :=
  eval_toFormula p slots b f
example [M↓[Lang] ⊧* collectionTheory] : M↓[Lang] ⊧ collectionSentence := models_collection
end SourceModel

example : collectionTheory ⊢ collectionSentence := collection_provable
example : witnessSeparation ∈ collectionTheory := Or.inr (Or.inr (Or.inl rfl))
example : rankReplacement ∈ collectionTheory := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
example : outputSeparation ∈ collectionTheory := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
example : predicateCongruence ∈ collectionTheory :=
  Or.inr (Or.inl (LO.FirstOrder.Theory.eqAxiom.relExt _))
