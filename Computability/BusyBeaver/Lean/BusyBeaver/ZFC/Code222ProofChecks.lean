import BusyBeaver.ZFC.Code222Proof

set_option autoImplicit false
set_option Elab.async false

open SetTheory.BusyBeaver.ZFC
open Code254
open Code254Proof (RawProof)
open Code222Proof

-- The parser's old constructor name is retained; its semantics is new.
example (a b c : Nat) : (RawProof.r7 a b c).quote =
    Code254Proof.node 9 (P a (P b c)) := rfl
example (a b c : Nat) : conclusion222 (.r7 a b c) =
    wim (weq c a) (wim (weq c b) (wal (wel a b) (weq a b))) := rfl
example (a b c : Nat) : conclusion222 (.bundle a b c) =
    wn (wim (KCode222.vrel a b c) (KCode222.nks a b c)) := rfl

-- MP checks both children and their actual new conclusions, not old rho7.
example (b : Nat) (p q : RawProof) : valid222 (.mp b p q) = true ↔
    valid222 p = true ∧ valid222 q = true ∧
      conclusion222 q = wim (conclusion222 p) b := by
  simp only [valid222, Bool.and_eq_true, decide_eq_true_eq]

example (n : Nat) : check222 0 n = false := reject_zero n
example : check222 1 0 = true := accept_truth
example (a b c : Nat) : check222 (RawProof.r7 a b c).quote
    (KCode222.growG a b c) = true := accept_growG a b c
example : check222 (RawProof.bundle 1 1 0).quote (KCode222.bundle222 1 1 0) = true :=
  accept_bundle 1 1 0 (by decide) (by decide)

example (a b : Nat) : check222 (RawProof.bundle a b a).quote
    (KCode222.bundle222 a b a) = false := by
  simpa only [conclusion222, valid222, ne_eq, not_true_eq_false,
    decide_false, Bool.false_and] using check_quote (.bundle a b a)
example (a b : Nat) : check222 (RawProof.bundle a b b).quote
    (KCode222.bundle222 a b b) = false := by
  simpa only [conclusion222, valid222, ne_eq, not_true_eq_false,
    decide_false, Bool.and_false] using check_quote (.bundle a b b)

example (n : Nat) : KCode222.C222 n ↔ ∃ code, check222 code n = true := c222_iff_checked n

#print axioms sound
#print axioms rawProof_exists
#print axioms check_sound
#print axioms check_quote
#print axioms c222_iff_checked
#print axioms reject_zero
#print axioms accept_truth
#print axioms accept_growG
#print axioms accept_bundle
