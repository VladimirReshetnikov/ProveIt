import ZFCinPA.R2Main

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Neg
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.R2Main.oddEnv_nil
#print axioms LeanProofs.ZFCinPA.R2Main.oddEnv_cons
#print axioms LeanProofs.ZFCinPA.R2Main.oddEnv_tail
#print axioms LeanProofs.ZFCinPA.R2Main.oddEnv_definable
#print axioms LeanProofs.ZFCinPA.R2Main.or_lemma
#print axioms LeanProofs.ZFCinPA.R2Main.enum_cons
#print axioms LeanProofs.ZFCinPA.R2Main.seqC_cons
#print axioms LeanProofs.ZFCinPA.R2Main.translate
#print axioms LeanProofs.ZFCinPA.R2Main.cProv_falsum_of_provable

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : OddEnv (0 : V) := LeanProofs.ZFCinPA.R2Main.oddEnv_nil
example {x F : V} (hx : x % 2 = 1) (hF : OddEnv F) : OddEnv (x ∷ F) :=
  LeanProofs.ZFCinPA.R2Main.oddEnv_cons hx hF
example {F : V} (hF : OddEnv F) : OddEnv (tail F) :=
  LeanProofs.ZFCinPA.R2Main.oddEnv_tail hF
example : 𝚫₁-Predicate[V] OddEnv := LeanProofs.ZFCinPA.R2Main.oddEnv_definable
example (a b : V) :
    CProv (wim (wim (vneg b) (wim (vneg a) 1)) (wim (vneg a) b)) :=
  LeanProofs.ZFCinPA.R2Main.or_lemma a b

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]
variable {T : SetTheory} [T.Δ₁]

example {L s p : V} (hL : Enum L s) : Enum (p ∷ L) (insert p s) :=
  LeanProofs.ZFCinPA.R2Main.enum_cons hL
example (F s p L : V) :
    seqC F s (p ∷ L) = imps (vneg (encode F 0 s p) ∷ negEnc F s L) 1 :=
  LeanProofs.ZFCinPA.R2Main.seqC_cons F s p L
example (hAx : LeanProofs.ZFCinPA.R2Main.AxOK T V) :
    ∀ d : V, LeanProofs.ZFCinPA.R2Main.Inv T d :=
  LeanProofs.ZFCinPA.R2Main.translate hAx
example (hAx : LeanProofs.ZFCinPA.R2Main.AxOK T V)
    (h : Provable T (^⊥ : V)) : CProv (1 : V) :=
  LeanProofs.ZFCinPA.R2Main.cProv_falsum_of_provable hAx h

-- Arbitrary internal derivation and an explicit listing of its concluding sequent.
example (hAx : LeanProofs.ZFCinPA.R2Main.AxOK T V) (d : V) (hd : Derivation T d)
    (F s L : V) (hF : OddEnv F) (hs : s % 2 = 0) (hL : Enum L (fstIdx d)) :
    CProv (seqC F s L) :=
  LeanProofs.ZFCinPA.R2Main.translate hAx d hd F s L hF hs hL
example (hAx : LeanProofs.ZFCinPA.R2Main.AxOK T V) (d : V) (hd : Derivation T d)
    (L : V) (hL : Enum L (fstIdx d)) : CProv (seqC (0 : V) 2 L) :=
  LeanProofs.ZFCinPA.R2Main.translate hAx d hd 0 2 L
    LeanProofs.ZFCinPA.R2Main.oddEnv_nil (by simp) hL
example (hAx : LeanProofs.ZFCinPA.R2Main.AxOK T V) (h : ¬ CProv (1 : V)) :
    ¬ Provable T (^⊥ : V) :=
  fun hp => h (LeanProofs.ZFCinPA.R2Main.cProv_falsum_of_provable hAx hp)
