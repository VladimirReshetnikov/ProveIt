import BusyBeaver.ZFC.KCode222
import BusyBeaver.ZFC.DomRho8

/-!
The dominated calculus of the 217-state machine (Source 149) and its equivalence with `C222`.

`CDom` is `C222` with rho8 restricted to the instances whose fourth argument is at most its
first, `rho8 a b c u` with `u ≤ a`: those are the only rho8 instances the 217's AX command
emits. Every other row, the gated seed bundle, modus ponens and generalization are `C222`'s.

The two calculi derive the same codes (`cdom_iff_c222`): a restricted row is a row, and every
row is derivable from the restricted ones (`DomRho8.rho8_all`, Source 149's certificate).
-/

namespace SetTheory.BusyBeaver.ZFC.KCodeDom

open Code254 KCode222

inductive CDom : Nat → Prop
  | truth : CDom 0
  | mp {t b : Nat} : CDom t → CDom (wim t b) → CDom b
  | gen (a : Nat) {h : Nat} : CDom h → CDom (wal a h)
  | r1 (a b : Nat) : CDom (rho1 a b)
  | r2 (a b c : Nat) : CDom (rho2 a b c)
  | r3 (a b c : Nat) : CDom (rho3 a b c)
  | r4 (a b c : Nat) : CDom (rho4 a b c)
  | r5 (a b c : Nat) : CDom (rho5 a b c)
  | r6 (a b : Nat) : CDom (rho6 a b)
  | rG (a b c : Nat) : CDom (growG a b c)
  | r8 (a b c u : Nat) : u ≤ a → CDom (rho8 a b c u)
  | bundle (a b c : Nat) : c ≠ a → c ≠ b → CDom (bundle222 a b c)

theorem c222_of_cdom {n : Nat} (h : CDom n) : C222 n := by
  induction h with
  | truth => exact .truth
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | gen a _ ih => exact .gen a ih
  | r1 a b => exact .r1 a b
  | r2 a b c => exact .r2 a b c
  | r3 a b c => exact .r3 a b c
  | r4 a b c => exact .r4 a b c
  | r5 a b c => exact .r5 a b c
  | r6 a b => exact .r6 a b
  | rG a b c => exact .rG a b c
  | r8 a b c u _ => exact .r8 a b c u
  | bundle a b c h1 h2 => exact .bundle a b c h1 h2

theorem domImp : DomRho8.DomImp CDom where
  truth := .truth
  mp := fun hab ha => .mp ha hab
  rho8 := fun a b c u h => .r8 a b c u h

theorem cdom_of_c222 {n : Nat} (h : C222 n) : CDom n := by
  induction h with
  | truth => exact .truth
  | mp _ _ ih1 ih2 => exact .mp ih1 ih2
  | gen a _ ih => exact .gen a ih
  | r1 a b => exact .r1 a b
  | r2 a b c => exact .r2 a b c
  | r3 a b c => exact .r3 a b c
  | r4 a b c => exact .r4 a b c
  | r5 a b c => exact .r5 a b c
  | r6 a b => exact .r6 a b
  | rG a b c => exact .rG a b c
  | r8 a b c u => exact DomRho8.rho8_all domImp a b c u
  | bundle a b c h1 h2 => exact .bundle a b c h1 h2

/-- **The dominated calculus derives exactly `C222`'s codes.** -/
theorem cdom_iff_c222 {n : Nat} : CDom n ↔ C222 n := ⟨c222_of_cdom, cdom_of_c222⟩

#print axioms cdom_iff_c222

end SetTheory.BusyBeaver.ZFC.KCodeDom
