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
theorem h0 {G : List NF} {a : NF} : Der NF.imp (Thm Ax) (a :: G) a := .hyp (List.mem_cons_self ..)
theorem h1 {G : List NF} {a b : NF} : Der NF.imp (Thm Ax) (b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem h2 {G : List NF} {a b c : NF} : Der NF.imp (Thm Ax) (c :: b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

section PropLayer

variable (hC : Classical NF.imp NF.bot (Thm Ax))
include hC

/-- Derivations from hypotheses discharge into theorems. -/
theorem of_der {G : List NF} {a : NF} (d : Der NF.imp (Thm Ax) G a)
    (hG : ∀ x, x ∈ G → Thm Ax x) : Thm Ax a :=
  d.sound hC hG

theorem thm_of_der0 {a : NF} (d : Der NF.imp (Thm Ax) [] a) : Thm Ax a :=
  of_der hC d (fun _ hx => absurd hx List.not_mem_nil)

/-- Two-hypothesis deduction. -/
theorem ded2 {a b c : NF} (d : Der NF.imp (Thm Ax) [b, a] c) : Thm Ax (imp a (imp b c)) :=
  thm_of_der0 hC (deduction hC (deduction hC d))

theorem ded1 {a c : NF} (d : Der NF.imp (Thm Ax) [a] c) : Thm Ax (imp a c) :=
  thm_of_der0 hC (deduction hC d)

theorem ded3 {a b c d : NF} (dd : Der NF.imp (Thm Ax) [c, b, a] d) :
    Thm Ax (imp a (imp b (imp c d))) :=
  thm_of_der0 hC (deduction hC (deduction hC (deduction hC dd)))

theorem syl {a b c : NF} (hab : Thm Ax (imp a b)) (hbc : Thm Ax (imp b c)) :
    Thm Ax (imp a c) :=
  ded1 hC (.mp (.ax hbc) (.mp (.ax hab) h0))

/-- `(a → b) → (¬b → ¬a)` -/
theorem contra_thm (a b : NF) : Thm Ax (imp (imp a b) (imp (neg b) (neg a))) :=
  ded3 hC (.mp h1 (.mp h2 h0))

theorem contra {a b : NF} (h : Thm Ax (imp a b)) : Thm Ax (imp (neg b) (neg a)) :=
  hC.mp (contra_thm hC a b) h

theorem dne (a : NF) : Thm Ax (imp (neg (neg a)) a) := by
  -- Peirce at `bot`: from `¬a → a`, which `¬¬a` and ex falso supply.
  apply ded1 hC
  have inner : Der NF.imp (Thm Ax) [neg (neg a)] (imp (imp a NF.bot) a) :=
    deduction hC (.mp (.ax (hC.efq a)) (.mp h1 h0))
  exact .mp (.ax (hC.peirce a NF.bot)) inner

theorem dni (a : NF) : Thm Ax (imp a (neg (neg a))) :=
  ded2 hC (.mp h0 h1)

/-- Classical contraposition in the reverse direction. -/
theorem contra_rev {a b : NF} (h : Thm Ax (imp (neg a) (neg b))) : Thm Ax (imp b a) := by
  have h' := contra hC h
  exact syl hC (syl hC (dni hC b) h') (dne hC a)

/-- Case split: `(¬a → c) → ((b → c) → ((a → b) → c))`. -/
theorem imp_cases (a b c : NF) :
    Thm Ax (imp (imp (neg a) c) (imp (imp b c) (imp (imp a b) c))) := by
  apply ded3 hC
  -- hypotheses: (¬a → c), (b → c), (a → b); goal c, by Peirce at bot on c.
  have inner : Der NF.imp (Thm Ax) [neg c, imp a b, imp b c, imp (neg a) c] c := by
    have na : Der NF.imp (Thm Ax) [neg c, imp a b, imp b c, imp (neg a) c] (neg a) :=
      deduction hC (.mp (Der.hyp (a := neg c) (by simp))
        (.mp (Der.hyp (a := imp b c) (by simp)) (.mp (Der.hyp (a := imp a b) (by simp)) h0)))
    exact .mp (Der.hyp (a := imp (neg a) c) (by simp)) na
  exact .mp (.ax (hC.peirce c NF.bot)) (deduction hC inner)

end PropLayer

/-! ## Quantifier basics -/

section Quant

variable (hC : Classical NF.imp NF.bot (Thm Ax))
include hC

theorem all_mono (i : Nat) {a b : NF} (h : Thm Ax (imp a b)) :
    Thm Ax (imp (all i a) (all i b)) :=
  hC.mp (.rho2 i a b) (.gen i h)

theorem ex_mono (i : Nat) {a b : NF} (h : Thm Ax (imp a b)) :
    Thm Ax (imp (ex i a) (ex i b)) :=
  contra hC (all_mono hC i (contra hC h))

/-- The B axiom of each quantifier: `a → ∀i ∃i a`. -/
theorem b_axiom (i : Nat) (a : NF) : Thm Ax (imp a (all i (ex i a))) := by
  have h6 : Thm Ax (imp (ex i (all i (neg a))) (neg a)) := .rho6 i (neg a)
  have h' : Thm Ax (imp a (neg (ex i (all i (neg a))))) :=
    syl hC (dni hC a) (contra hC h6)
  -- ¬ ex i (∀i ¬a) = ¬¬ ∀i ¬∀i ¬a, and ∀i ¬∀i ¬a = ∀i ∃i a.
  have := syl hC h' (dne hC (all i (neg (all i (neg a)))))
  exact this

/-- If `a → ∀i a` then `∃i a → a`. -/
theorem ex_elim_of_vac {i : Nat} {a : NF} (h : Thm Ax (imp a (all i a))) :
    Thm Ax (imp (ex i a) a) :=
  syl hC (ex_mono hC i h) (.rho6 i a)

/-- If `a → ∀i a` then `¬a → ∀i ¬a`. -/
theorem vac_neg {i : Nat} {a : NF} (h : Thm Ax (imp a (all i a))) :
    Thm Ax (imp (neg a) (all i (neg a))) := by
  have e := ex_elim_of_vac hC h
  -- ¬a → ¬∃i a = ¬¬∀i¬a → ∀i¬a
  exact syl hC (contra hC e) (dne hC (all i (neg a)))

theorem vac_bot (i : Nat) : Thm Ax (imp NF.bot (all i NF.bot)) := hC.efq _

/-- Vacuity for every formula not containing the label. -/
theorem vac_of_not_occurs (i : Nat) :
    ∀ f : NF, ¬ Occurs i f → Thm Ax (imp f (all i f))
  | rel a b, h => .vacRel a b i (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  | NF.eq a b, h => .vacEq a b i (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  | NF.bot, _ => vac_bot hC i
  | imp a b, h => by
      have ha := vac_of_not_occurs i a (fun o => h (Or.inl o))
      have hb := vac_of_not_occurs i b (fun o => h (Or.inr o))
      have hna : Thm Ax (imp (neg a) (all i (imp a b))) :=
        syl hC (vac_neg hC ha) (all_mono hC i (ded2 hC (.mp (.ax (hC.efq b)) (.mp h1 h0))))
      have hbb : Thm Ax (imp b (all i (imp a b))) :=
        syl hC hb (all_mono hC i (hC.k b a))
      exact hC.mp (hC.mp (imp_cases hC a b (all i (imp a b))) hna) hbb
  | all j a, h => by
      have ha := vac_of_not_occurs i a (fun o => h (Or.inr o))
      exact syl hC (all_mono hC j ha) (.rho4 j i a)

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
