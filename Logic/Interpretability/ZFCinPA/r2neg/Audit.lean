import ZFCinPA.R2Neg

set_option autoImplicit false
noncomputable section

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254
open LeanProofs.ZFCinPA.R2Neg
open scoped LO.FirstOrder.Arithmetic

#print axioms LeanProofs.ZFCinPA.R2Neg.taut
#print axioms LeanProofs.ZFCinPA.R2Neg.and_case
#print axioms LeanProofs.ZFCinPA.R2Neg.or_case
#print axioms LeanProofs.ZFCinPA.R2Neg.dneg_right
#print axioms LeanProofs.ZFCinPA.R2Neg.iff2_symm
#print axioms LeanProofs.ZFCinPA.R2Neg.all_iff2
#print axioms LeanProofs.ZFCinPA.R2Neg.neg_swap
#print axioms LeanProofs.ZFCinPA.R2Neg.neg_iff2
#print axioms LeanProofs.ZFCinPA.R2Neg.encode_neg

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (f : Kalmar.PF) (n : ℕ) (hb : f.Bounded n) (ht : f.Tautology)
    (σ : ℕ → V) : CProv (f.eval wim 1 σ) := taut f n hb ht σ

example {a b p q : V} (ha : Iff2 a (vneg p)) (hb : Iff2 b (vneg q)) :
    Iff2 (wim (vneg a) b) (vneg (vneg (wim p (vneg q)))) := and_case ha hb

example {a b p q : V} (ha : Iff2 a (vneg p)) (hb : Iff2 b (vneg q)) :
    Iff2 (vneg (wim a (vneg b))) (vneg (wim (vneg p) q)) := or_case ha hb

example {a b : V} (h : Iff2 a b) : Iff2 a (vneg (vneg b)) := dneg_right h

example {a b : V} (h : Iff2 a b) : Iff2 b a := iff2_symm h

example (i : V) {a b : V} (h : Iff2 a b) :
    Iff2 (wal i a) (wal i b) := all_iff2 i h

example {a b : V} (h : Iff2 a (vneg b)) : Iff2 (vneg a) b := neg_swap h

example {a b : V} (h : Iff2 a b) : Iff2 (vneg a) (vneg b) := neg_iff2 h

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

example {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    NegEq F B s p := encode_neg hp F B s

example {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    CProv (wim (encode F B s (Bootstrapping.neg ℒₛₑₜ p))
      (wim (encode F B s p) 1)) := (encode_neg hp F B s).1

example {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) (F B s : V) :
    CProv (wim (wim (encode F B s p) 1)
      (encode F B s (Bootstrapping.neg ℒₛₑₜ p))) := (encode_neg hp F B s).2

example {n p : V} (hp : IsSemiformula ℒₛₑₜ n p) (F B s i : V) :
    Iff2 (wal i (encode F B s (Bootstrapping.neg ℒₛₑₜ p)))
      (wal i (wim (encode F B s p) 1)) := all_iff2 i (encode_neg hp F B s)
