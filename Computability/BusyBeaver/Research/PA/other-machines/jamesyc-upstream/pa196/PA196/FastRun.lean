module
public import M6.Zip

/-!
A bounded certificate evaluator with delayed tape normalization.

The reference semantics trims both tape lists after every step. This evaluator
keeps harmless trailing zeros during a bounded block and normalizes once at its
end. `run_normalize` proves that the result is exactly the reference run, for
all machines, tapes, and lengths. All generated certificates are checked by
kernel reduction through this theorem; there is no trusted external evaluator.
-/
@[expose] public section
namespace PA196.FastRun
open M6.Zip

def normalize (c : Conf) : Conf := zc c.q c.l c.r

def step (M : TMN) (c : Conf) : Option Conf :=
  match M c.q (c.r.headD false) with
  | none => none
  | some (w, true, q') => some ⟨q',w :: c.l,c.r.tail⟩
  | some (w, false, q') => some ⟨q',c.l.tail,c.l.headD false :: w :: c.r.tail⟩

def run (M : TMN) : Nat → Conf → Option Conf
  | 0, c => some c
  | n + 1, c => match step M c with
    | none => none
    | some c' => run M n c'

theorem step_normalize (M : TMN) (c : Conf) :
    M6.Zip.step M (normalize c) = (step M c).map normalize := by
  rcases c with ⟨q,l,r⟩
  rw [normalize, M6.Zip.step_zc]
  simp only [step]
  cases h : M q (r.headD false) with
  | none => rfl
  | some a =>
    rcases a with ⟨w,d,q'⟩
    cases d <;> rfl

theorem run_normalize (M : TMN) (n : Nat) (c : Conf) :
    M6.Zip.run M n (normalize c) = (run M n c).map normalize := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [M6.Zip.run,step_normalize,run]
    cases h : step M c with
    | none => rfl
    | some c' => exact ih c'

/-- A reflected finite-run equality implies the exact tape-semantics equality. -/
theorem checked {M : TMN} {n : Nat} {a b : Conf}
    (ha : normalize a = a)
    (h : (run M n a).map normalize = some b) :
    M6.Zip.run M n a = some b := by
  have e := run_normalize M n a
  rw [ha] at e
  exact e.trans h

#print axioms run_normalize
end PA196.FastRun
