import BusyBeaver.ZFC.KCode222
import BusyBeaver.ZFC.FourShapeImplication

/-!
A new finite-shape presentation of the existing code calculus.

Only rho8 changes: its unrestricted four-argument row is replaced by four
explicit families. All other rows, including the existing truth axiom and
the two bundle guards, are kept exactly. The four-shape implication theorem
proves equality of derivability for every natural-number code, including
codes with no intended formula interpretation.

This is a formalism-level result, not a claim about any compiled TM size.
-/
namespace SetTheory.BusyBeaver.ZFC.KCodeFourShape

open Code254 KCode222

inductive CFour : Nat → Prop
  | truth : CFour 0
  | mp {t b : Nat} : CFour t → CFour (wim t b) → CFour b
  | gen (a : Nat) {h : Nat} : CFour h → CFour (wal a h)
  | r1 (a b : Nat) : CFour (rho1 a b)
  | r2 (a b c : Nat) : CFour (rho2 a b c)
  | r3 (a b c : Nat) : CFour (rho3 a b c)
  | r4 (a b c : Nat) : CFour (rho4 a b c)
  | r5 (a b c : Nat) : CFour (rho5 a b c)
  | r6 (a b : Nat) : CFour (rho6 a b)
  | rG (a b c : Nat) : CFour (growG a b c)
  | r8same (a b c : Nat) : CFour (rho8 a b c a)
  | r8right (x u b c : Nat) : CFour (rho8 (wim x u) b c u)
  | r8ll (u x y b c : Nat) : CFour (rho8 (wim (wim u x) y) b c u)
  | r8llr (x u y z b c : Nat) : CFour (rho8 (wim (wim (wim x u) y) z) b c u)
  | bundle (a b c : Nat) : c ≠ a → c ≠ b → CFour (bundle222 a b c)

private def language : FourShapeImplication.Language Nat := ⟨wim⟩

private theorem four : FourShapeImplication.FourAxioms language CFour where
  mp := fun hab ha => .mp ha hab
  same := CFour.r8same
  right := CFour.r8right
  ll := CFour.r8ll
  llr := CFour.r8llr

/-- The four explicit families derive every numerical rho8 row. -/
theorem rho8_all (a b c u : Nat) : CFour (rho8 a b c u) :=
  FourShapeImplication.all_of_four four a b c u

theorem c222_of_cfour {n : Nat} (h : CFour n) : C222 n := by
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
  | r8same a b c => exact .r8 a b c a
  | r8right x u b c => exact .r8 (wim x u) b c u
  | r8ll u x y b c => exact .r8 (wim (wim u x) y) b c u
  | r8llr x u y z b c => exact .r8 (wim (wim (wim x u) y) z) b c u
  | bundle a b c h1 h2 => exact .bundle a b c h1 h2

theorem cfour_of_c222 {n : Nat} (h : C222 n) : CFour n := by
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
  | r8 a b c u => exact rho8_all a b c u
  | bundle a b c h1 h2 => exact .bundle a b c h1 h2

/-- Equal derivability for every code, without a well-formedness premise. -/
theorem cfour_iff_c222 {n : Nat} : CFour n ↔ C222 n :=
  ⟨c222_of_cfour, cfour_of_c222⟩

/-- In particular the two code calculi have the same consistency statement. -/
theorem consistent_iff : (¬ CFour F) ↔ (¬ C222 F) :=
  ⟨fun h hn => h (cfour_of_c222 hn), fun h hn => h (c222_of_cfour hn)⟩

#print axioms rho8_all
#print axioms cfour_iff_c222
#print axioms consistent_iff
end SetTheory.BusyBeaver.ZFC.KCodeFourShape
