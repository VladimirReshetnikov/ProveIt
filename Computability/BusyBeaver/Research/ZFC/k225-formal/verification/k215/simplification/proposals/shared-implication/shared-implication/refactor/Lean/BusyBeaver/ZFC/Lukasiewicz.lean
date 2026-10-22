import BusyBeaver.ZFC.TarskiComplete
import BusyBeaver.ZFC.DominatedImplication

/-!
The shared implicational basis and unconditional Tarski logic bridge.

The generic K, S, Peirce and composition theorems now instantiate the
representation-independent DominatedImplication core with the always-true
side condition. The old 107-certificate port from Jeff's CD254.v is replaced
by four adapters; the shared core's 58-step derivation gains five MP steps
for S. This preserves the public interface and the Tarski bridge below.

Historical attribution: the replaced certificates ported Jeff's ZF/m254/coq/logic/CD254.v
at busy-beaver commit 297ab8df7e5de329605c3875b4934643b371a5e3 (Mira-Cult's
machine; Jeff's verification). See the pinned parent for the complete historical source.
The replacement core is regenerated from k225-formal/rho8cd/derivation_core.txt;
every inference is checked by the Lean kernel, without assumptions about decoding,
implication injectivity, truth, falsity, or the search program.

Ex falso additionally uses rho6 with the original NF.bot-relative existential.
This file concerns named syntax; it does not assert a machine consistency endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.Lukasiewicz

universe u
variable {α : Type u}

/-- Only the actual implicational row and its inference rule. -/
structure Implicational (imp : α → α → α) (T : α → Prop) : Prop where
  mp : ∀ {a b}, T (imp a b) → T a → T b
  rho8 : ∀ c u a b, T (imp (imp (imp c u) a) (imp (imp a c) (imp b c)))

variable {imp : α → α → α} {T : α → Prop}

/-- Unrestricted rows instantiate the shared core with the always-true guard. -/
private def fullLanguage (imp : α → α → α) : DominatedImplication.Language α where
  imp := imp
  below := fun _ _ => True
  refl := fun _ => True.intro
  grow_left := fun _ _ => True.intro
  grow_right := fun _ _ => True.intro

private theorem restricted (h : Implicational imp T) :
    DominatedImplication.Restricted (fullLanguage imp) T where
  mp := h.mp
  rho8 := fun a b c u _ => h.rho8 c u a b

/-- K follows from rho8 alone, through the shared core. -/
theorem k (h : Implicational imp T) (a b : α) : T (imp a (imp b a)) :=
  DominatedImplication.k (restricted h) a b

/-- Peirce follows from rho8 alone, through the shared core. -/
theorem peirce (h : Implicational imp T) (a b : α) :
    T (imp (imp (imp a b) a) a) :=
  DominatedImplication.peirce (restricted h) a b

/-- Implication composition, through the shared core. -/
theorem composition (h : Implicational imp T) (a b c : α) :
    T (imp (imp a b) (imp (imp b c) (imp a c))) :=
  DominatedImplication.composition (restricted h) a b c

/-- S follows from rho8 alone, through the shared core. -/
theorem s (h : Implicational imp T) (a b c : α) :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) :=
  DominatedImplication.s (restricted h) a b c

end SetTheory.BusyBeaver.ZFC.Lukasiewicz

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF

private theorem implicational (Ax : NF → Prop) :
    Lukasiewicz.Implicational NF.imp (Thm Ax) where
  mp := Thm.mp
  rho8 := Thm.rho8

/-- Ex falso uses K, S and the original rho6, not rho8 alone. -/
theorem ex_falso {Ax : NF → Prop} (a : NF) : Thm Ax (imp bot a) := by
  let x := all 0 (neg (all 0 a))
  let e := ex 0 (all 0 a)
  have hk := Lukasiewicz.k (implicational Ax)
  have hs := Lukasiewicz.s (implicational Ax)
  have hbe : Thm Ax (imp bot e) := hk bot x
  have hbea : Thm Ax (imp bot (imp e a)) :=
    .mp (hk (imp e a) bot) (.rho6 0 a)
  exact .mp (.mp (hs bot e a) hbea) hbe

/-- The required classical basis is derived from the actual Tarski rows. -/
theorem classical (Ax : NF → Prop) : Kalmar.Classical NF.imp NF.bot (Thm Ax) where
  mp := Thm.mp
  k := Lukasiewicz.k (implicational Ax)
  s := Lukasiewicz.s (implicational Ax)
  peirce := Lukasiewicz.peirce (implicational Ax)
  efq := ex_falso

/-- Unconditional completeness for named formulas with primitive falsity. -/
theorem complete {Ax : NF → Prop} (f : NF)
    (hval : ∀ (D : Type) (mem : D → D → Prop),
      (∀ a, Ax a → ∀ e : Nat → D, Sat mem e a) → ∀ e : Nat → D, Sat mem e f) :
    Thm Ax f :=
  completeness (classical Ax) (classical (fun _ => False)) f hval

end SetTheory.BusyBeaver.ZFC.Tarski
