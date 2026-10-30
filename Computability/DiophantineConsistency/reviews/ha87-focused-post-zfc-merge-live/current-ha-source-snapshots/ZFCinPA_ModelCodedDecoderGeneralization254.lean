import ZFCinPA.ModelCodedProofRenaming
import ZFCinPA.ModelCodedDecoderConstructors254
import BusyBeaver.ZFC.ArithmeticCode254

set_option autoImplicit false

/-!
Actual numerical GEN transport for the all-internal C254 decoder. The numerical
constructor is ArithmeticCode254.wal; the target is the checked named binder,
including arbitrary free labels and literal truth's free zero. The conclusion
is existence of an internal target proof, with no represented proof selector.
This module does not translate the eight logical rows or the gated bundle.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderGeneralization254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The live numerical universal constructor decodes to the actual named binder. -/
theorem decode_wal (chosen matrix : V) :
    decode (ArithmeticCode254.wal chosen matrix) =
      namedAll ℒₛₑₜ chosen (decode matrix) := by
  simpa only [ArithmeticCode254.wal,ArithmeticCode254.tagged] using
    decode_all chosen matrix

/-- GEN in actual ZF, uniformly over arbitrary internal variable and matrix codes. -/
theorem zf_decodedProvable_gen (chosen : V) {matrix : V}
    (hp : Provable (𝗭𝗙 : SetTheory) (decode matrix)) :
    Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticCode254.wal chosen matrix)) := by
  rw [decode_wal]
  exact zf_provable_namedAll chosen hp

/-- The corresponding actual ZFC instance, with no axiom-closure premise. -/
theorem zfc_decodedProvable_gen (chosen : V) {matrix : V}
    (hp : Provable (𝗭𝗙𝗖 : SetTheory) (decode matrix)) :
    Provable (𝗭𝗙𝗖 : SetTheory) (decode (ArithmeticCode254.wal chosen matrix)) := by
  rw [decode_wal]
  exact zfc_provable_namedAll chosen hp

end LeanProofs.ZFCinPA.ModelCodedDecoderGeneralization254
