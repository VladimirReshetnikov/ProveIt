import BusyBeaver.ZFC.Kalmar
import BusyBeaver.ZFC.TarskiCalculus

/-!
Derived rules of the machines' Tarski calculus.

The propositional and quantifier rules below hold for any theorem predicate `T`
that is classical for `imp`/`bot` (`hC`: K, S, Peirce and ex falso under MP) and,
for the quantifier rules, has the rows of `Rows` (generalization, rho1–rho7 and
atomic membership vacuity). Both the Tarski calculus `Thm` and the restricted
calculus `KThmK.ThmK` are instances, so these proofs are shared. `Lukasiewicz.lean`
and `Tarski.classical` discharge `hC` from the row `rho8` alone; keeping it
abstract here separates the propositional search certificates from the
quantifier argument.

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

/-- The quantifier and atomic rows shared by `Thm` and the restricted calculus `ThmK`
(everything but equality vacuity, which the two calculi grant at different binders). -/
class Rows (T : NF → Prop) : Prop where
  gen (i : Nat) {a : NF} : T a → T (all i a)
  rho2 (i : Nat) (b c : NF) : T (imp (all i (imp b c)) (imp (all i b) (all i c)))
  rho4 (i j : Nat) (c : NF) : T (imp (all i (all j c)) (all j (all i c)))
  rho6 (i : Nat) (b : NF) : T (imp (ex i (all i b)) b)
  rho1 (i j : Nat) : T (ex i (NF.eq i j))
  rho7 (a b c : Nat) : T (imp (NF.eq c a) (imp (NF.eq c b) (NF.eq a b)))
  rho5 (a b c : Nat) : T (imp (NF.eq c a) (imp (rel c b) (rel a b)))
  rho3 (a b c : Nat) : T (imp (NF.eq a b) (imp (rel c a) (rel c b)))
  vacRel (a b c : Nat) : c ≠ a → c ≠ b → T (imp (rel a b) (all c (rel a b)))

instance {Ax : NF → Prop} : Rows (Thm Ax) where
  gen := .gen
  rho2 := .rho2
  rho4 := .rho4
  rho6 := .rho6
  rho1 := .rho1
  rho7 := .rho7
  rho5 := .rho5
  rho3 := .rho3
  vacRel := .vacRel

variable {Ax : NF → Prop} {T : NF → Prop}

/-- Hypothesis `k` of a list, as a derivation. -/
theorem h0 {G : List NF} {a : NF} : Der NF.imp T (a :: G) a := .hyp (List.mem_cons_self ..)
theorem h1 {G : List NF} {a b : NF} : Der NF.imp T (b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem h2 {G : List NF} {a b c : NF} : Der NF.imp T (c :: b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

section PropLayer

variable (hC : Classical NF.imp NF.bot T)
include hC

theorem thm_of_der0 {a : NF} (d : Der NF.imp T [] a) : T a :=
  d.sound hC (fun _ hx => absurd hx List.not_mem_nil)

/-- Two-hypothesis deduction. -/
theorem ded2 {a b c : NF} (d : Der NF.imp T [b, a] c) : T (imp a (imp b c)) :=
  thm_of_der0 hC (deduction hC (deduction hC d))

theorem ded1 {a c : NF} (d : Der NF.imp T [a] c) : T (imp a c) :=
  thm_of_der0 hC (deduction hC d)

theorem ded3 {a b c d : NF} (dd : Der NF.imp T [c, b, a] d) :
    T (imp a (imp b (imp c d))) :=
  thm_of_der0 hC (deduction hC (deduction hC (deduction hC dd)))

theorem syl {a b c : NF} (hab : T (imp a b)) (hbc : T (imp b c)) : T (imp a c) :=
  ded1 hC (.mp (.ax hbc) (.mp (.ax hab) h0))

/-- `(a → b) → (¬b → ¬a)` -/
theorem contra_thm (a b : NF) : T (imp (imp a b) (imp (neg b) (neg a))) :=
  ded3 hC (.mp h1 (.mp h2 h0))

theorem contra {a b : NF} (h : T (imp a b)) : T (imp (neg b) (neg a)) :=
  hC.mp (contra_thm hC a b) h

theorem dne (a : NF) : T (imp (neg (neg a)) a) := by
  -- Peirce at `bot`: from `¬a → a`, which `¬¬a` and ex falso supply.
  have inner : Der NF.imp T [neg (neg a)] (imp (imp a NF.bot) a) :=
    deduction hC (.mp (.ax (hC.efq a)) (.mp h1 h0))
  exact ded1 hC (.mp (.ax (hC.peirce a NF.bot)) inner)

theorem dni (a : NF) : T (imp a (neg (neg a))) :=
  ded2 hC (.mp h0 h1)

/-- Case split: `(¬a → c) → ((b → c) → ((a → b) → c))`. -/
theorem imp_cases (a b c : NF) :
    T (imp (imp (neg a) c) (imp (imp b c) (imp (imp a b) c))) := by
  apply ded3 hC
  -- hypotheses: (¬a → c), (b → c), (a → b); goal c, by Peirce at bot on c.
  have inner : Der NF.imp T [neg c, imp a b, imp b c, imp (neg a) c] c := by
    have na : Der NF.imp T [neg c, imp a b, imp b c, imp (neg a) c] (neg a) :=
      deduction hC (.mp (Der.hyp (a := neg c) (by simp))
        (.mp (Der.hyp (a := imp b c) (by simp)) (.mp (Der.hyp (a := imp a b) (by simp)) h0)))
    exact .mp (Der.hyp (a := imp (neg a) c) (by simp)) na
  exact .mp (.ax (hC.peirce c NF.bot)) (deduction hC inner)

theorem vac_bot (i : Nat) : T (imp NF.bot (all i NF.bot)) := hC.efq _

end PropLayer

/-! ## Quantifier basics -/

section Quant

variable (hC : Classical NF.imp NF.bot T) [R : Rows T]
include hC

theorem all_mono (i : Nat) {a b : NF} (h : T (imp a b)) : T (imp (all i a) (all i b)) :=
  hC.mp (R.rho2 i a b) (R.gen i h)

theorem ex_mono (i : Nat) {a b : NF} (h : T (imp a b)) : T (imp (ex i a) (ex i b)) :=
  contra hC (all_mono hC i (contra hC h))

/-- If `a → ∀i a` then `∃i a → a`. -/
theorem ex_elim_of_vac {i : Nat} {a : NF} (h : T (imp a (all i a))) : T (imp (ex i a) a) :=
  syl hC (ex_mono hC i h) (R.rho6 i a)

/-- If `a → ∀i a` then `¬a → ∀i ¬a`. -/
theorem vac_neg {i : Nat} {a : NF} (h : T (imp a (all i a))) :
    T (imp (neg a) (all i (neg a))) :=
  -- ¬a → ¬∃i a = ¬¬∀i¬a → ∀i¬a
  syl hC (contra hC (ex_elim_of_vac hC h)) (dne hC (all i (neg a)))

/-- Vacuity for an implication from vacuity of its two sides. -/
theorem vac_imp {i : Nat} {a b : NF} (ha : T (imp a (all i a))) (hb : T (imp b (all i b))) :
    T (imp (imp a b) (all i (imp a b))) := by
  have hna : T (imp (neg a) (all i (imp a b))) :=
    syl hC (vac_neg hC ha) (all_mono hC i (ded2 hC (.mp (.ax (hC.efq b)) (.mp h1 h0))))
  have hbb : T (imp b (all i (imp a b))) :=
    syl hC hb (all_mono hC i (hC.k b a))
  exact hC.mp (hC.mp (imp_cases hC a b (all i (imp a b))) hna) hbb

/-- Vacuity under a quantifier, by commuting the two. -/
theorem vac_all {i j : Nat} {a : NF} (ha : T (imp a (all i a))) :
    T (imp (all j a) (all i (all j a))) :=
  syl hC (all_mono hC j ha) (R.rho4 j i a)

end Quant

section Fresh

variable (hC : Classical NF.imp NF.bot (Thm Ax))
include hC

/-- Vacuity for every formula not containing the label. -/
theorem vac_of_not_occurs (i : Nat) :
    ∀ f : NF, ¬ Occurs i f → Thm Ax (imp f (all i f))
  | rel a b, h => .vacRel a b i (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  | NF.eq a b, h => .vacEq a b i (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  | NF.bot, _ => vac_bot hC i
  | imp a b, h => vac_imp hC (vac_of_not_occurs i a (fun o => h (Or.inl o)))
      (vac_of_not_occurs i b (fun o => h (Or.inr o)))
  | all _ a, h => vac_all hC (vac_of_not_occurs i a (fun o => h (Or.inr o)))

/-- `∃i a → a` when `i` does not occur in `a`. -/
theorem ex_elim (i : Nat) {a : NF} (h : ¬ Occurs i a) : Thm Ax (imp (ex i a) a) :=
  ex_elim_of_vac hC (vac_of_not_occurs hC i a h)

/-! ## Equality is an equivalence relation -/

theorem eq_refl (x : Nat) : Thm Ax (NF.eq x x) := by
  -- Choose a label `c` different from `x`; `rho1` gives `∃c (c = x)`.
  have h7 : Thm Ax (imp (NF.eq (x + 1) x) (NF.eq x x)) :=
    ded1 hC (.mp (.mp (.ax (.rho7 x x (x + 1))) h0) h0)
  have hex : Thm Ax (ex (x + 1) (NF.eq x x)) := hC.mp (ex_mono hC (x + 1) h7) (.rho1 (x + 1) x)
  have hno : ¬ Occurs (x + 1) (NF.eq x x) := by
    simp only [Occurs]; omega
  exact hC.mp (ex_elim hC (x + 1) hno) hex

theorem eq_symm (x y : Nat) : Thm Ax (imp (NF.eq x y) (NF.eq y x)) :=
  -- rho7: x = y → (x = x → y = x)
  ded1 hC (.mp (.mp (.ax (.rho7 y x x)) h0) (.ax (eq_refl hC x)))

theorem eq_trans (x y z : Nat) : Thm Ax (imp (NF.eq x y) (imp (NF.eq y z) (NF.eq x z))) :=
  -- y = x and y = z give x = z by rho7.
  ded2 hC (.mp (.mp (.ax (.rho7 x z y)) (.mp (.ax (eq_symm hC x y)) h1)) h0)

end Fresh

end SetTheory.BusyBeaver.ZFC.Tarski
