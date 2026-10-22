import BusyBeaver.ZFC.Kalmar
import BusyBeaver.ZFC.TarskiCalculus

/-!
Common derived rules for named calculi.  The admissibility argument keeps
atomic equality vacuity explicit; it cannot silently strengthen ThmK.
The propositional proofs are factored from TarskiDerived.lean and KThmK.lean.
-/
namespace SetTheory.BusyBeaver.ZFC.NamedDerived
open Tarski Tarski.NF Kalmar
variable {D : NF → Prop}

structure QuantifierRules (D : NF → Prop) : Prop where
  gen : ∀ i {a}, D a → D (all i a)
  distribute : ∀ i a b, D (imp (all i (imp a b)) (imp (all i a) (all i b)))
  commute : ∀ i j a, D (imp (all i (all j a)) (all j (all i a)))
  eliminate : ∀ i a, D (imp (ex i (all i a)) a)

/-- Which equality atoms have the atomic vacuity required by this client. -/
def Admissible (eqAllowed : Nat → Nat → Prop) : NF → Prop
  | .rel _ _ => True
  | .eq a b => eqAllowed a b
  | .bot => True
  | .imp a b => Admissible eqAllowed a ∧ Admissible eqAllowed b
  | .all _ a => Admissible eqAllowed a

theorem admissible_all : ∀ f : NF, Admissible (fun _ _ => True) f
  | .rel _ _ => trivial
  | .eq _ _ => trivial
  | .bot => trivial
  | .imp a b => ⟨admissible_all a, admissible_all b⟩
  | .all _ a => admissible_all a

/-- Hypothesis `k` of a list, as a derivation. -/
theorem h0 {G : List NF} {a : NF} : Der NF.imp (D) (a :: G) a := .hyp (List.mem_cons_self ..)
theorem h1 {G : List NF} {a b : NF} : Der NF.imp (D) (b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
theorem h2 {G : List NF} {a b c : NF} : Der NF.imp (D) (c :: b :: a :: G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

section PropLayer

variable (hC : Classical NF.imp NF.bot D)
include hC

/-- Derivations from hypotheses discharge into theorems. -/
theorem of_der {G : List NF} {a : NF} (d : Der NF.imp (D) G a)
    (hG : ∀ x, x ∈ G → D x) : D a :=
  d.sound hC hG

theorem thm_of_der0 {a : NF} (d : Der NF.imp (D) [] a) : D a :=
  of_der hC d (fun _ hx => absurd hx List.not_mem_nil)

/-- Two-hypothesis deduction. -/
theorem ded2 {a b c : NF} (d : Der NF.imp (D) [b, a] c) : D (imp a (imp b c)) :=
  thm_of_der0 hC (deduction hC (deduction hC d))

theorem ded1 {a c : NF} (d : Der NF.imp (D) [a] c) : D (imp a c) :=
  thm_of_der0 hC (deduction hC d)

theorem ded3 {a b c d : NF} (dd : Der NF.imp (D) [c, b, a] d) :
    D (imp a (imp b (imp c d))) :=
  thm_of_der0 hC (deduction hC (deduction hC (deduction hC dd)))

theorem syl {a b c : NF} (hab : D (imp a b)) (hbc : D (imp b c)) :
    D (imp a c) :=
  ded1 hC (.mp (.ax hbc) (.mp (.ax hab) h0))

/-- `(a → b) → (¬b → ¬a)` -/
theorem contra_thm (a b : NF) : D (imp (imp a b) (imp (neg b) (neg a))) :=
  ded3 hC (.mp h1 (.mp h2 h0))

theorem contra {a b : NF} (h : D (imp a b)) : D (imp (neg b) (neg a)) :=
  hC.mp (contra_thm hC a b) h

theorem dne (a : NF) : D (imp (neg (neg a)) a) := by
  -- Peirce at `bot`: from `¬a → a`, which `¬¬a` and ex falso supply.
  apply ded1 hC
  have inner : Der NF.imp (D) [neg (neg a)] (imp (imp a NF.bot) a) :=
    deduction hC (.mp (.ax (hC.efq a)) (.mp h1 h0))
  exact .mp (.ax (hC.peirce a NF.bot)) inner

theorem dni (a : NF) : D (imp a (neg (neg a))) :=
  ded2 hC (.mp h0 h1)

/-- Classical contraposition in the reverse direction. -/
theorem contra_rev {a b : NF} (h : D (imp (neg a) (neg b))) : D (imp b a) := by
  have h' := contra hC h
  exact syl hC (syl hC (dni hC b) h') (dne hC a)

/-- Case split: `(¬a → c) → ((b → c) → ((a → b) → c))`. -/
theorem imp_cases (a b c : NF) :
    D (imp (imp (neg a) c) (imp (imp b c) (imp (imp a b) c))) := by
  apply ded3 hC
  -- hypotheses: (¬a → c), (b → c), (a → b); goal c, by Peirce at bot on c.
  have inner : Der NF.imp (D) [neg c, imp a b, imp b c, imp (neg a) c] c := by
    have na : Der NF.imp (D) [neg c, imp a b, imp b c, imp (neg a) c] (neg a) :=
      deduction hC (.mp (Der.hyp (a := neg c) (by simp))
        (.mp (Der.hyp (a := imp b c) (by simp)) (.mp (Der.hyp (a := imp a b) (by simp)) h0)))
    exact .mp (Der.hyp (a := imp (neg a) c) (by simp)) na
  exact .mp (.ax (hC.peirce c NF.bot)) (deduction hC inner)

end PropLayer

/-! ## Quantifier basics -/

section Quant

variable (hC : Classical NF.imp NF.bot D) (hQ : QuantifierRules D)
include hC hQ

theorem all_mono (i : Nat) {a b : NF} (h : D (imp a b)) :
    D (imp (all i a) (all i b)) :=
  hC.mp (hQ.distribute i a b) (hQ.gen i h)

theorem ex_mono (i : Nat) {a b : NF} (h : D (imp a b)) :
    D (imp (ex i a) (ex i b)) :=
  contra hC (all_mono hC hQ i (contra hC h))

/-- The B axiom of each quantifier: `a → ∀i ∃i a`. -/
theorem b_axiom (i : Nat) (a : NF) : D (imp a (all i (ex i a))) := by
  have h6 : D (imp (ex i (all i (neg a))) (neg a)) := hQ.eliminate i (neg a)
  have h' : D (imp a (neg (ex i (all i (neg a))))) :=
    syl hC (dni hC a) (contra hC h6)
  -- ¬ ex i (∀i ¬a) = ¬¬ ∀i ¬∀i ¬a, and ∀i ¬∀i ¬a = ∀i ∃i a.
  have := syl hC h' (dne hC (all i (neg (all i (neg a)))))
  exact this

/-- If `a → ∀i a` then `∃i a → a`. -/
theorem ex_elim_of_vac {i : Nat} {a : NF} (h : D (imp a (all i a))) :
    D (imp (ex i a) a) :=
  syl hC (ex_mono hC hQ i h) (hQ.eliminate i a)

/-- If `a → ∀i a` then `¬a → ∀i ¬a`. -/
theorem vac_neg {i : Nat} {a : NF} (h : D (imp a (all i a))) :
    D (imp (neg a) (all i (neg a))) := by
  have e := ex_elim_of_vac hC hQ h
  -- ¬a → ¬∃i a = ¬¬∀i¬a → ∀i¬a
  exact syl hC (contra hC e) (dne hC (all i (neg a)))

omit hQ in
theorem vac_bot (i : Nat) : D (imp NF.bot (all i NF.bot)) := hC.efq _

/-- Atomic vacuity extends structurally, with exactly the client's equality guard. -/
theorem vac_of_not_occurs (i : Nat) (eqAllowed : Nat → Nat → Prop)
    (hRel : ∀ a b, i ≠ a → i ≠ b → D (imp (rel a b) (all i (rel a b))))
    (hEq : ∀ a b, eqAllowed a b → i ≠ a → i ≠ b →
      D (imp (NF.eq a b) (all i (NF.eq a b)))) :
    ∀ f : NF, Admissible eqAllowed f → ¬ Occurs i f → D (imp f (all i f))
  | rel a b, _, h => hRel a b (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  | NF.eq a b, hf, h => hEq a b hf (fun e => h (Or.inl e)) (fun e => h (Or.inr e))
  | NF.bot, _, _ => hC.efq _
  | imp a b, hf, h => by
      have ha := vac_of_not_occurs i eqAllowed hRel hEq a hf.1 (fun o => h (Or.inl o))
      have hb := vac_of_not_occurs i eqAllowed hRel hEq b hf.2 (fun o => h (Or.inr o))
      have hna : D (imp (neg a) (all i (imp a b))) :=
        syl hC (vac_neg hC hQ ha)
          (all_mono hC hQ i (ded2 hC (.mp (.ax (hC.efq b)) (.mp h1 h0))))
      have hbb : D (imp b (all i (imp a b))) :=
        syl hC hb (all_mono hC hQ i (hC.k b a))
      exact hC.mp (hC.mp (imp_cases hC a b (all i (imp a b))) hna) hbb
  | all j a, hf, h => by
      have ha := vac_of_not_occurs i eqAllowed hRel hEq a hf (fun o => h (Or.inr o))
      exact syl hC (all_mono hC hQ j ha) (hQ.commute j i a)

end Quant
#print axioms vac_of_not_occurs
end SetTheory.BusyBeaver.ZFC.NamedDerived
