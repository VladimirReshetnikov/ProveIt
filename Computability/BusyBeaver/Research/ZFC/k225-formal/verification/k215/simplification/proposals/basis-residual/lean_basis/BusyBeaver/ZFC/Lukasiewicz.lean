import BusyBeaver.ZFC.TarskiComplete
import BusyBeaver.ZFC.ImplicationalBasis

/-!
The named-formula bridge uses the shared pure implication basis.
The Tarski declarations below are byte-for-byte unchanged from the pinned source.
The historic 107-node certificate remains available in repository history.
-/

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
