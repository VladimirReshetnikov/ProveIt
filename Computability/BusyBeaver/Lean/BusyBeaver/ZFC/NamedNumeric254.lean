import BusyBeaver.ZFC.Numeric254

/-!
Exact derivation transport from the named calculus into the original
four-tag numerical calculus. Falsity and `rel 0 0` intentionally encode to1;
the encoder is not injective and no semantic interpretation is asserted.

For the precisely defined theory `Q f := NumThm (encode f)`, numerical
refutability at1 is equivalent to `Tarski.Thm Q bot`. This is a proof-adapter
theorem, not a calibration of Q with SIR, ZFC or a new closure theory.
No decoder, enumerator, compiler or binary-machine endpoint is proved.
-/

namespace SetTheory.BusyBeaver.ZFC.NamedNumeric254

open Tarski (NF)
open Numeric254

def encode : NF → Nat
  | .bot => F
  | .rel i j => wel i j
  | .eq i j => weq i j
  | .imp a b => wim (encode a) (encode b)
  | .all i a => wal i (encode a)

@[simp] theorem encode_neg (f : NF) : encode (NF.neg f) = wn (encode f) := rfl
@[simp] theorem encode_ex (i : Nat) (f : NF) : encode (NF.ex i f) = wex i (encode f) := rfl

/-- The intentional alias rules out an injective interpretation of this encoder. -/
theorem falsity_collision : encode NF.bot = encode (.rel 0 0) := rfl

/-- The named truth formula has code16, distinct from the separate truth code0. -/
theorem named_truth_code : encode (.imp .bot .bot) = 16 := rfl

/-- All thirteen named-calculus constructors transport to actual numeric proofs.
Only the axiom case needs the explicitly stated translation of its theory. -/
theorem transport {Ax : NF → Prop}
    (hAx : ∀ f, Ax f → NumThm (encode f)) {f : NF}
    (h : Tarski.Thm Ax f) : NumThm (encode f) := by
  induction h with
  | ax h => exact hAx _ h
  | mp _ _ ihImp ihA => exact NumThm.mp ihA ihImp
  | gen i _ ih => exact NumThm.gen i ih
  | rho8 c u a b => exact NumThm.rho8 (encode a) (encode b) (encode c) (encode u)
  | rho2 i b c => exact NumThm.rho2 i (encode b) (encode c)
  | rho4 i j c => exact NumThm.rho4 i j (encode c)
  | rho6 i b => exact NumThm.rho6 i (encode b)
  | rho1 i j => exact NumThm.rho1 i j
  | rho7 a b c => exact NumThm.rho7 a b c
  | rho5 a b c => exact NumThm.rho5 a b c
  | rho3 a b c => exact NumThm.rho3 a b c
  | vacRel a b c hca hcb => exact vacuity_rel a b c hca hcb
  | vacEq a b c hca hcb => exact vacuity_eq a b c hca hcb

/-- The actual theory of encoded numerical theorems; no calibration is built in. -/
def Q (f : NF) : Prop := NumThm (encode f)

theorem transport_Q {f : NF} (h : Tarski.Thm Q f) : Q f :=
  transport (fun _ hf => hf) h

/-- Exact refutation equivalence for Q, with no decoder or semantic assumptions. -/
theorem refutation_iff : Tarski.Thm Q NF.bot ↔ NumThm 1 :=
  ⟨fun h => transport_Q h, fun h => .ax h⟩

/-- The original irreflexivity sentence, expressed with genuine named falsity. -/
def ir : NF := .all 0 (.imp (.rel 0 0) .bot)

theorem ir_code : encode ir = 610 := rfl

/-- IR belongs to Q because its numerical image is GEN of relative-F identity. -/
theorem ir_in_Q : Q ir := NumThm.gen 0 (self_imp 1)

theorem named_ir : Tarski.Thm Q ir := .ax ir_in_Q

end SetTheory.BusyBeaver.ZFC.NamedNumeric254
