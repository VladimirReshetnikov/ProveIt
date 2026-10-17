import ZFCinPA.ModelCodedDecoderFreshness254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254.bindOneAt_isUFormula
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254.termBindOneAt_commute
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254.termBindOneVecAt_commute
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254.bindOneAt_commute
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254.atomCode_binder_fresh
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254.decode_binder_fresh
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254.positive_code_fresh
#print axioms LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254.decoded_positive_vacuity
example {p : V} (h : IsUFormula L p) (a d : V) :
    IsUFormula L (bindOneAt L a d p) := bindOneAt_isUFormula h a d
example {t : V} (h : IsUTerm L t) (a b d e : V) (hab : a ≠ b) :
    termBindOneAt L a d (termBindOneAt L b e t) =
      termBindOneAt L b e (termBindOneAt L a d t) := termBindOneAt_commute h a b d e hab
example {k ts : V} (h : IsUTermVec L k ts) (a b d e : V) (hab : a ≠ b) :
    termBindOneVecAt L a d k (termBindOneVecAt L b e k ts) =
      termBindOneVecAt L b e k (termBindOneVecAt L a d k ts) := termBindOneVecAt_commute h a b d e hab
example {p : V} (h : IsUFormula L p) (a b d e : V) (hab : a ≠ b) :
    bindOneAt L a d (bindOneAt L b e p) =
      bindOneAt L b e (bindOneAt L a d p) := bindOneAt_commute h a b d e hab
example (r a b c d : V) (hr : (ℒₛₑₜ).IsRel 2 r) (ha : a ≠ c) (hb : b ≠ c) :
    bindOneAt ℒₛₑₜ c d (atomCode r a b) = atomCode r a b :=
  atomCode_binder_fresh r a b c d hr ha hb
example (n c d : V) (hc : 0 < c) (h : n ≤ c) :
    bindOneAt ℒₛₑₜ c d (decode n) = decode n := decode_binder_fresh n c d hc h
example (n d : V) (hn : 0 < n) : bindOneAt ℒₛₑₜ n d (decode n) = decode n :=
  positive_code_fresh n hn d
example (T : SetTheory) [T.Δ₁] (n : V) (hn : 0 < n) :
    Provable T (decode (_root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wim n
      (_root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wal n n))) :=
  decoded_positive_vacuity T n hn
example (d : V) : bindOneAt ℒₛₑₜ 1 d (decode (0 : V)) = decode (0 : V) :=
  decode_binder_fresh 0 1 d (by simp) (by simp)
example (d : V) : bindOneAt ℒₛₑₜ 1 d (decode (1 : V)) = decode (1 : V) :=
  positive_code_fresh 1 (by simp) d
example (n : V) : bindOneAt ℒₛₑₜ (n+1) 0 (decode n) = decode n :=
  decode_binder_fresh n (n+1) 0 (by simp) (by simp)
example (n : V) (hn : 0 < n) :
    Provable (𝗭𝗙 : SetTheory) (decode (_root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wim n
      (_root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wal n n))) :=
  decoded_positive_vacuity 𝗭𝗙 n hn
