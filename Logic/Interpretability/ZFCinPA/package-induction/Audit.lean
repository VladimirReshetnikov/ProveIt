import ZFCinPA.PackageInduction

set_option autoImplicit false

noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LeanProofs.ZFCinPA

namespace LeanProofs.ZFCinPA.PackageInductionTypedAudit

variable {V : Type*} [ORingStructure V]

example (Package : V → V → Prop) (x : V) :
    HasZFCConsistencyProofPackage Package x ↔ ∃ z : V, Package x z := Iff.rfl

example {Package : V → V → Prop}
    (hPackage : HierarchySymbol.sigmaOne.DefinableRel Package) :
    HierarchySymbol.sigmaOne.DefinablePred
      (HasZFCConsistencyProofPackage Package) :=
  hasZFCConsistencyProofPackage_definable hPackage

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {Package : V → V → Prop}
    (hPackage : HierarchySymbol.sigmaOne.DefinableRel Package)
    (hzero : ∃ z : V, Package 0 z)
    (hsucc : ∀ x z : V, Package x z → ∃ z' : V, Package (x + 1) z')
    (hfinal : ∀ x z : V, Package x z →
      ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c) :
    ZFCProofSelectorIn V :=
  zfcProofSelectorIn_of_package hPackage hzero hsucc hfinal

example (masterCode : V → V) (x d : V) :
    DirectZFCMasterProofPackage masterCode x d ↔
      Proof 𝗭𝗙𝗖 d (masterCode x) := Iff.rfl

example {masterCode : V → V}
    (hmaster : HierarchySymbol.sigmaOne.DefinableFunction₁ masterCode) :
    HierarchySymbol.sigmaOne.DefinableRel
      (DirectZFCMasterProofPackage (V := V) masterCode) :=
  directZFCMasterProofPackage_definable hmaster

example {masterCode : V → V}
    (hmaster : HierarchySymbol.sigmaOne.DefinableFunction₁ masterCode)
    (hbase : ∃ d : V, Proof 𝗭𝗙𝗖 d (masterCode 0))
    (hsucc : ∀ x d : V, Proof 𝗭𝗙𝗖 d (masterCode x) →
      ∃ d' : V, Proof 𝗭𝗙𝗖 d' (masterCode (x + 1)))
    (hfinal : ∀ x d : V, Proof 𝗭𝗙𝗖 d (masterCode x) →
      ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c) :
    ZFCProofSelectorIn V :=
  zfcProofSelectorIn_of_directMasterProofs hmaster hbase hsucc hfinal

example {Package : V → V → Prop}
    (hPackage : HierarchySymbol.sigmaOne.DefinableRel Package)
    (hzero : ∃ z : V, Package 0 z)
    (hsucc : ∀ x z : V, Package x z → ∃ z' : V, Package (x + 1) z')
    (hfinal : ∀ x z : V, Package x z →
      ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c)
    (x : V) : ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c :=
  zfcProofSelectorIn_of_package hPackage hzero hsucc hfinal x

example {masterCode : V → V}
    (hmaster : HierarchySymbol.sigmaOne.DefinableFunction₁ masterCode)
    (hbase : ∃ d : V, Proof 𝗭𝗙𝗖 d (masterCode 0))
    (hsucc : ∀ x d : V, Proof 𝗭𝗙𝗖 d (masterCode x) →
      ∃ d' : V, Proof 𝗭𝗙𝗖 d' (masterCode (x + 1)))
    (hfinal : ∀ x d : V, Proof 𝗭𝗙𝗖 d (masterCode x) →
      ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c)
    (x : V) : ∃ c : V, ConZFCSetCode c x ∧ Provable 𝗭𝗙𝗖 c :=
  zfcProofSelectorIn_of_directMasterProofs hmaster hbase hsucc hfinal x

end LeanProofs.ZFCinPA.PackageInductionTypedAudit

#print axioms LeanProofs.ZFCinPA.HasZFCConsistencyProofPackage
#print axioms LeanProofs.ZFCinPA.hasZFCConsistencyProofPackage_definable
#print axioms LeanProofs.ZFCinPA.zfcProofSelectorIn_of_package
#print axioms LeanProofs.ZFCinPA.DirectZFCMasterProofPackage
#print axioms LeanProofs.ZFCinPA.directZFCMasterProofPackage_definable
#print axioms LeanProofs.ZFCinPA.zfcProofSelectorIn_of_directMasterProofs
