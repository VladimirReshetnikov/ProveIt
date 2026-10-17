import ZFCinPA.ModelCodedDecoderAccepted254
set_option autoImplicit false
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticRow254 ArithmeticHistory254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254.rowKernel_sound
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254.rejected_or_decoded_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254.accepted_decoded_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254.accepted_conclusion_provable
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderAccepted254.accepted_falsity_provable_bottom
example (k p u v : V)
    (hu : u ≠ 0 → Provable (𝗭𝗙 : SetTheory) (decode (u-1)))
    (hv : v ≠ 0 → Provable (𝗭𝗙 : SetTheory) (decode (v-1))) :
    rowKernel k p u v = 0 ∨ Provable (𝗭𝗙 : SetTheory) (decode (rowKernel k p u v-1)) :=
  rowKernel_sound k p u v hu hv
example (code : V) : value code = 0 ∨ Provable (𝗭𝗙 : SetTheory) (decode (value code-1)) :=
  rejected_or_decoded_provable code
example (code : V) (hv : value code ≠ 0) :
    Provable (𝗭𝗙 : SetTheory) (decode (value code-1)) := accepted_decoded_provable code hv
example (code conclusion : V) (hv : value code = conclusion+1) :
    Provable (𝗭𝗙 : SetTheory) (decode conclusion) := accepted_conclusion_provable code conclusion hv
example (code : V) (hv : value code = 2) : Provable (𝗭𝗙 : SetTheory) (^⊥ : V) :=
  accepted_falsity_provable_bottom code hv
example (code conclusion : V) (hv : value code = conclusion+1) :
    ∃ d : V, Proof (𝗭𝗙 : SetTheory) d (decode conclusion) :=
  accepted_conclusion_provable code conclusion hv
example (code : V) (hv : value code = 2) :
    ∃ d : V, Proof (𝗭𝗙 : SetTheory) d (^⊥ : V) := accepted_falsity_provable_bottom code hv
example (h : ∃ code : V, value code = 2) : Provable (𝗭𝗙 : SetTheory) (^⊥ : V) := by
  obtain ⟨code,hv⟩ := h
  exact accepted_falsity_provable_bottom code hv
example (n : V) (h : ∃ code : V, value code = n+1) :
    Provable (𝗭𝗙 : SetTheory) (decode n) := by
  obtain ⟨code,hv⟩ := h
  exact accepted_conclusion_provable code n hv
example (code : V) (hn : ¬ Provable (𝗭𝗙 : SetTheory) (^⊥ : V)) : value code ≠ 2 := by
  intro h
  exact hn (accepted_falsity_provable_bottom code h)
