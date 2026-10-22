import BusyBeaver.ZFC.NamedDerived
import BusyBeaver.ZFC.Kalmar
import BusyBeaver.ZFC.TarskiCalculus

/-!
Derived rules of the machines' Tarski calculus.

Everything here is relative to a hypothesis `hC` that the theorem predicate
`Thm Ax` is classical for `imp`/`bot` (K, S, Peirce and ex falso under MP).
`Lukasiewicz.lean` and `Tarski.classical` discharge that hypothesis from the
row `rho8` alone; keeping it abstract here separates the propositional search
certificates from the quantifier argument.

Main results:

* `vac_of_not_occurs`: `φ → ∀i φ` for every formula in which the label `i`
  does not occur. The calculus only has this for atoms (gated by `c ≠ a, b`);
  the general schema follows from distribution, commutation and `rho6`.
* `ex_elim_of_vac`: `∃i φ → φ` whenever `φ → ∀i φ` is a theorem.
* `eq_refl`, `eq_symm`, `eq_trans`: equality is an equivalence relation,
  obtained from `rho1`, `rho7` and atomic vacuity.
-/

namespace SetTheory.BusyBeaver.ZFC.Tarski

open NF Kalmar

variable {Ax : NF → Prop}

/-- Hypothesis `k` of a list, as a derivation. -/
abbrev h0 := @NamedDerived.h0 (Thm Ax)

abbrev h1 := @NamedDerived.h1 (Thm Ax)

abbrev h2 := @NamedDerived.h2 (Thm Ax)

section PropLayer

variable (hC : Classical NF.imp NF.bot (Thm Ax))
include hC

/-- Derivations from hypotheses discharge into theorems. -/
abbrev of_der := @NamedDerived.of_der (Thm Ax) hC

abbrev thm_of_der0 := @NamedDerived.thm_of_der0 (Thm Ax) hC

/-- Two-hypothesis deduction. -/
abbrev ded2 := @NamedDerived.ded2 (Thm Ax) hC

abbrev ded1 := @NamedDerived.ded1 (Thm Ax) hC

abbrev ded3 := @NamedDerived.ded3 (Thm Ax) hC

abbrev syl := @NamedDerived.syl (Thm Ax) hC

/-- `(a → b) → (¬b → ¬a)` -/
abbrev contra_thm := @NamedDerived.contra_thm (Thm Ax) hC

abbrev contra := @NamedDerived.contra (Thm Ax) hC

abbrev dne := @NamedDerived.dne (Thm Ax) hC

abbrev dni := @NamedDerived.dni (Thm Ax) hC

/-- Classical contraposition in the reverse direction. -/
abbrev contra_rev := @NamedDerived.contra_rev (Thm Ax) hC

/-- Case split: `(¬a → c) → ((b → c) → ((a → b) → c))`. -/
abbrev imp_cases := @NamedDerived.imp_cases (Thm Ax) hC

end PropLayer

/-! ## Quantifier basics -/

section Quant

private theorem quantifierRules : NamedDerived.QuantifierRules (Thm Ax) where
  gen := Thm.gen
  distribute := Thm.rho2
  commute := Thm.rho4
  eliminate := Thm.rho6


variable (hC : Classical NF.imp NF.bot (Thm Ax))
include hC

abbrev all_mono := @NamedDerived.all_mono (Thm Ax) hC quantifierRules

abbrev ex_mono := @NamedDerived.ex_mono (Thm Ax) hC quantifierRules

/-- The B axiom of each quantifier: `a → ∀i ∃i a`. -/
abbrev b_axiom := @NamedDerived.b_axiom (Thm Ax) hC quantifierRules

/-- If `a → ∀i a` then `∃i a → a`. -/
abbrev ex_elim_of_vac := @NamedDerived.ex_elim_of_vac (Thm Ax) hC quantifierRules

/-- If `a → ∀i a` then `¬a → ∀i ¬a`. -/
abbrev vac_neg := @NamedDerived.vac_neg (Thm Ax) hC quantifierRules

abbrev vac_bot := @NamedDerived.vac_bot (Thm Ax) hC

/-- Vacuity for every formula not containing the label. -/
theorem vac_of_not_occurs (i : Nat) (f : NF) (h : ¬ Occurs i f) :
    Thm Ax (imp f (all i f)) :=
  NamedDerived.vac_of_not_occurs hC quantifierRules i (fun _ _ => True)
    (fun a b => Thm.vacRel a b i) (fun a b _ => Thm.vacEq a b i)
    f (NamedDerived.admissible_all f) h

/-- `∃i a → a` when `i` does not occur in `a`. -/
theorem ex_elim (i : Nat) {a : NF} (h : ¬ Occurs i a) : Thm Ax (imp (ex i a) a) :=
  ex_elim_of_vac hC (vac_of_not_occurs hC i a h)

/-! ## Equality is an equivalence relation -/

theorem eq_refl (x : Nat) : Thm Ax (NF.eq x x) := by
  -- Choose a label `c` different from `x`; `rho1` gives `∃c (c = x)`.
  have h7 : Thm Ax (imp (NF.eq (x + 1) x) (NF.eq x x)) := by
    have r : Thm Ax (imp (NF.eq (x + 1) x) (imp (NF.eq (x + 1) x) (NF.eq x x))) := .rho7 x x (x + 1)
    exact ded1 hC (.mp (.mp (.ax r) h0) h0)
  have hex : Thm Ax (ex (x + 1) (NF.eq x x)) := hC.mp (ex_mono hC (x + 1) h7) (.rho1 (x + 1) x)
  have hno : ¬ Occurs (x + 1) (NF.eq x x) := by
    simp only [Occurs]; omega
  exact hC.mp (ex_elim hC (x + 1) hno) hex

theorem eq_symm (x y : Nat) : Thm Ax (imp (NF.eq x y) (NF.eq y x)) :=
  -- rho7: x = y → (x = x → y = x)
  ded1 hC (.mp (.mp (.ax (.rho7 y x x)) h0) (.ax (eq_refl hC x)))

theorem eq_trans (x y z : Nat) : Thm Ax (imp (NF.eq x y) (imp (NF.eq y z) (NF.eq x z))) := by
  -- y = x and y = z give x = z by rho7.
  apply ded2 hC
  exact .mp (.mp (.ax (.rho7 x z y)) (.mp (.ax (eq_symm hC x y)) h1)) h0

end Quant

end SetTheory.BusyBeaver.ZFC.Tarski
