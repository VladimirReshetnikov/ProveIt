import BusyBeaver.ZFC.TarskiComplete
import BusyBeaver.ZFC.DominatedImplication

/-!
The classical implicational basis and the unconditional Tarski logic bridge.

K, S, Peirce and composition follow from modus ponens and Lukasiewicz's single
axiom rho8 ((c → u) → a) → ((a → c) → (b → c)) alone. They are the dominated
core's theorems (`DominatedImplication`) for the domination relation that holds
everywhere: then every row is a restricted row. The one condensed-detachment
derivation behind them (`Research/ZFC/k225-formal/rho8cd/`) therefore serves both
the dominated calculus and this unrestricted one. No implication injectivity or
assumption about falsity is used.

Ex falso additionally uses the original rho6, whose existential is defined
relative to `NF.bot`. Thus `Tarski.classical` supplies both explicit hypotheses
of the previously conditional `Tarski.completeness`, for any theory predicate `Ax`.

This concerns the named syntax with primitive falsity. It does not identify
that syntax with numerical machine codes, justify the runtime falsity
alias, verify a theory bundle, or prove a binary machine consistency endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.Lukasiewicz

universe u
variable {α : Type u}

/-- Only the actual implicational row and its inference rule. -/
structure Implicational (imp : α → α → α) (T : α → Prop) : Prop where
  mp : ∀ {a b}, T (imp a b) → T a → T b
  rho8 : ∀ c u a b, T (imp (imp (imp c u) a) (imp (imp a c) (imp b c)))

variable {imp : α → α → α} {T : α → Prop}

/-- Domination that always holds: every row is a restricted row. -/
private def everywhere (imp : α → α → α) : DominatedImplication.Language α where
  imp := imp
  below _ _ := True
  refl _ := trivial
  grow_left _ _ := trivial
  grow_right _ _ := trivial

private theorem restricted (h : Implicational imp T) :
    DominatedImplication.Restricted (everywhere imp) T :=
  ⟨h.mp, fun a b c u _ => h.rho8 c u a b⟩

/-- K follows from rho8 alone. -/
theorem k (h : Implicational imp T) (a b : α) : T (imp a (imp b a)) :=
  DominatedImplication.k (restricted h) a b

/-- Peirce follows from rho8 alone. -/
theorem peirce (h : Implicational imp T) (a b : α) :
    T (imp (imp (imp a b) a) a) := DominatedImplication.peirce (restricted h) a b

/-- Implication composition. -/
theorem composition (h : Implicational imp T) (a b c : α) :
    T (imp (imp a b) (imp (imp b c) (imp a c))) := DominatedImplication.composition (restricted h) a b c

/-- S follows from rho8 alone. -/
theorem s (h : Implicational imp T) (a b c : α) :
    T (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := DominatedImplication.s (restricted h) a b c

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
