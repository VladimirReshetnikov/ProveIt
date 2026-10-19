import ZFCinPA.R2Ctx

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.R2Ctx
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.R2Ctx.der_mp
#print axioms LeanProofs.ZFCinPA.R2Ctx.der_hyp
#print axioms LeanProofs.ZFCinPA.R2Ctx.der_ded
#print axioms LeanProofs.ZFCinPA.R2Ctx.der_sub
#print axioms LeanProofs.ZFCinPA.R2Ctx.negEnc_shiftList
#print axioms LeanProofs.ZFCinPA.R2Ctx.exists_enum

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example {G a b : V} (hab : Der G (wim a b)) (ha : Der G a) : Der G b :=
  der_mp hab ha

example (G i : V) (hi : i < len G) : Der G G.[i] := der_hyp G i hi

example {G x : V} (hx : x ∈ᵥ G) : Der G x := der_mem hx

example {G a g : V} (h : Der (a ∷ G) g) : Der G (wim a g) := der_ded h

example {G a g : V} (h : Der G (wim a g)) : Der (a ∷ G) g := der_undeduct h

example {G G' g : V} (hsub : ∀ x, x ∈ᵥ G' → x ∈ᵥ G) (h : Der G' g) :
    Der G g := der_sub hsub h

example (F s L : V) (hL : ∀ p, p ∈ᵥ L → IsUFormula ℒₛₑₜ p) :
    negEnc F s (shiftList L) = negEnc (tail F) s L := negEnc_shiftList F s L hL

example (F s L : V) (hL : ∀ p, p ∈ᵥ L → IsUFormula ℒₛₑₜ p) :
    seqC F s (shiftList L) = seqC (tail F) s L := by
  unfold seqC
  rw [negEnc_shiftList F s L hL]

example (s : V) : ∃ L, Enum L s := exists_enum s

example {L s y : V} (hL : Enum L s) : y ∈ᵥ L ↔ y ∈ s := hL.mem
