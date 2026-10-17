import ZFCinPA.ModelCodedProofRenaming
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedFreeRenaming
open LeanProofs.ZFCinPA.ModelCodedRenamingSets
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
variable {T : Theory L} [T.Δ₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedProofRenaming.derivable_rename_bounded
#print axioms LeanProofs.ZFCinPA.ModelCodedProofRenaming.derivable_rename
#print axioms LeanProofs.ZFCinPA.ModelCodedProofRenaming.provable_rename
#print axioms LeanProofs.ZFCinPA.ModelCodedProofRenaming.zf_provable_rename
#print axioms LeanProofs.ZFCinPA.ModelCodedProofRenaming.zfc_provable_rename
#print axioms LeanProofs.ZFCinPA.ModelCodedProofRenaming.zf_provable_namedAll
#print axioms LeanProofs.ZFCinPA.ModelCodedProofRenaming.zfc_provable_namedAll
example (a n d k s : V)
    (hAx : ∀ k s p : V, IsFormula L p → p ∈ T.Δ₁Class → rename L a k s p ∈ T.Δ₁Class)
    (hd : Derivation T d) (hk : k ≤ n) (hs : s ≤ n) (hb : d+k+s ≤ n) :
    Derivable T (setRename L a k s (fstIdx d)) := derivable_rename_bounded a n hAx d hd k hk s hs hb
example (a d : V)
    (hAx : ∀ k s p : V, IsFormula L p → p ∈ T.Δ₁Class → rename L a k s p ∈ T.Δ₁Class)
    (hd : Derivation T d) : Derivable T (setRename L a 0 0 (fstIdx d)) :=
  derivable_rename a hAx hd
example (a p : V)
    (hAx : ∀ k s p : V, IsFormula L p → p ∈ T.Δ₁Class → rename L a k s p ∈ T.Δ₁Class)
    (hp : Provable T p) : Provable T (rename L a 0 0 p) := provable_rename a hAx hp
example (a p : V) (hp : Provable (𝗭𝗙 : SetTheory) p) :
    Provable (𝗭𝗙 : SetTheory) (rename ℒₛₑₜ a 0 0 p) := zf_provable_rename a hp
example (a p : V) (hp : Provable (𝗭𝗙𝗖 : SetTheory) p) :
    Provable (𝗭𝗙𝗖 : SetTheory) (rename ℒₛₑₜ a 0 0 p) := zfc_provable_rename a hp
example (a p : V) (hp : Provable (𝗭𝗙 : SetTheory) p) :
    Provable (𝗭𝗙 : SetTheory) (namedAll ℒₛₑₜ a p) := zf_provable_namedAll a hp
example (a p : V) (hp : Provable (𝗭𝗙𝗖 : SetTheory) p) :
    Provable (𝗭𝗙𝗖 : SetTheory) (namedAll ℒₛₑₜ a p) := zfc_provable_namedAll a hp
example (p : V) (hp : Provable (𝗭𝗙 : SetTheory) p) :
    Provable (𝗭𝗙 : SetTheory) (namedAll ℒₛₑₜ 0 p) := zf_provable_namedAll 0 hp
