import ZFCinPA.ModelCodedDecoderGeneralization254

set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoderGeneralization254
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedBindOne
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderGeneralization254.decode_wal
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderGeneralization254.zf_decodedProvable_gen
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderGeneralization254.zfc_decodedProvable_gen
example (a p : V) : decode (ArithmeticCode254.wal a p) =
    namedAll ℒₛₑₜ a (decode p) := decode_wal a p
example (a p : V) (h : Provable (𝗭𝗙 : SetTheory) (decode p)) :
    Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticCode254.wal a p)) :=
  zf_decodedProvable_gen a h
example (a p : V) (h : Provable (𝗭𝗙𝗖 : SetTheory) (decode p)) :
    Provable (𝗭𝗙𝗖 : SetTheory) (decode (ArithmeticCode254.wal a p)) :=
  zfc_decodedProvable_gen a h
example (h : Provable (𝗭𝗙 : SetTheory) (decode (0 : V))) :
    Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticCode254.wal 0 0 : V)) :=
  zf_decodedProvable_gen 0 h
example (a p : V) (h : Provable (𝗭𝗙 : SetTheory) (decode p)) :
    Provable (𝗭𝗙 : SetTheory)
      (decode (ArithmeticCode254.wal a (ArithmeticCode254.wal a p))) :=
  zf_decodedProvable_gen a (zf_decodedProvable_gen a h)
example (a p d : V) (h : Proof (𝗭𝗙 : SetTheory) d (decode p)) :
    ∃ e : V, Proof (𝗭𝗙 : SetTheory) e (decode (ArithmeticCode254.wal a p)) :=
  zf_decodedProvable_gen a ⟨d,h⟩
