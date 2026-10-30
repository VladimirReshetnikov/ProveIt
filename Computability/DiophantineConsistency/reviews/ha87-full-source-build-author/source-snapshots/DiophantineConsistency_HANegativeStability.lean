import DiophantineConsistency.HADeduction

/-! # Object-language stability proofs in intuitionistic arithmetic

The syntactic fragment below contains falsity, negations of arbitrary
formulas, conjunctions, and universals. Every stability theorem constructs
an `HA.Derives` tree. In particular, no universal double-negation-elimination
rule is added and no classical derivation is converted to an HA derivation.
The closed-negation theorem can be applied to a separately bound no-zero
sentence without using any arithmetic axioms.
-/

set_option Elab.async false
namespace DiophantineConsistency.HA
open SetTheory.PA

def neg (a : Formula) : Formula := .imp a .bot
def doubleNeg (a : Formula) : Formula := neg (neg a)

/-- A sufficient syntactic fragment, not a claim that every stable formula
has this shape. Atomic equality, disjunction and existence are not cases. -/
inductive Negative : Formula → Prop
  | bot : Negative .bot
  | neg (a : Formula) : Negative (neg a)
  | and {a b : Formula} : Negative a → Negative b → Negative (.and a b)
  | all {a : Formula} : Negative a → Negative (.all a)

namespace Derives

theorem contrapose {G : List Formula} {a b : Formula}
    (h : Derives G (.imp a b)) : Derives G (.imp (neg b) (neg a)) := by
  apply Derives.impI
  apply Derives.impI
  exact (Derives.ass _ (neg b) (by simp)).mp
    (((h.prepend (neg b)).prepend a).mp (.ass _ a List.mem_cons_self))

theorem doubleNeg_map {G : List Formula} {a b : Formula}
    (h : Derives G (.imp a b)) :
    Derives G (.imp (doubleNeg a) (doubleNeg b)) :=
  h.contrapose.contrapose

theorem doubleNeg_intro (G : List Formula) (a : Formula) :
    Derives G (.imp a (doubleNeg a)) := by
  apply Derives.impI
  apply Derives.impI
  exact (Derives.ass _ (neg a) List.mem_cons_self).mp (.ass _ a (by simp))

theorem stable_bot (G : List Formula) :
    Derives G (.imp (doubleNeg .bot) .bot) :=
  .impI G _ _ ((Derives.ass _ _ List.mem_cons_self).mp (.identity _ .bot))

theorem stable_neg (G : List Formula) (a : Formula) :
    Derives G (.imp (doubleNeg (neg a)) (neg a)) := by
  apply Derives.impI
  apply Derives.impI
  apply (Derives.ass _ (doubleNeg (neg a)) (by simp)).mp
  exact (Derives.doubleNeg_intro _ a).mp (.ass _ a List.mem_cons_self)

theorem stable_and {a b : Formula}
    (ha : ∀ G, Derives G (.imp (doubleNeg a) a))
    (hb : ∀ G, Derives G (.imp (doubleNeg b) b)) (G : List Formula) :
    Derives G (.imp (doubleNeg (.and a b)) (.and a b)) := by
  apply Derives.impI
  apply Derives.andI
  · exact (ha _).mp ((Derives.and_left _ a b).doubleNeg_map.mp
      (.ass _ _ List.mem_cons_self))
  · exact (hb _).mp ((Derives.and_right _ a b).doubleNeg_map.mp
      (.ass _ _ List.mem_cons_self))

/-- The opened variable is fresh for every shifted assumption. The exact
PAHF substitution identity restores the body after universal elimination. -/
theorem stable_all {a : Formula}
    (ha : ∀ G, Derives G (.imp (doubleNeg a) a)) (G : List Formula) :
    Derives G (.imp (doubleNeg (.all a)) (.all a)) := by
  apply Derives.impI
  apply Derives.allI
  apply (ha _).mp
  let H := (doubleNeg (.all a) :: G).map (Formula.rename Nat.succ)
  have hall : Derives H (.imp (Formula.rename Nat.succ (.all a)) a) := by
    apply Derives.impI
    have he := Derives.allE (Formula.rename Nat.succ (.all a) :: H)
      (Formula.rename (SetTheory.up Nat.succ) a)
      (.var 0) (.ass _ (Formula.rename Nat.succ (.all a)) List.mem_cons_self)
    simpa only [Formula.subst_instTerm_var_zero_rename_up_succ] using he
  apply hall.doubleNeg_map.mp
  exact .ass H _ List.mem_cons_self

end Derives

namespace Negative

theorem stable {a : Formula} (h : Negative a) (G : List Formula) :
    Derives G (.imp (doubleNeg a) a) := by
  induction h generalizing G with
  | bot => exact .stable_bot G
  | neg a => exact .stable_neg G a
  | and _ _ iha ihb => exact .stable_and iha ihb G
  | all _ ih => exact .stable_all ih G

theorem closeN {a : Formula} (ha : Negative a) (n : Nat) :
    Negative (Formula.closeN n a) := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih => exact ih (.all ha)

theorem sealPA {a : Formula} (ha : Negative a) : Negative (Formula.sealPA a) :=
  ha.closeN (Formula.bound a)

theorem proves_stability {a : Formula} (ha : Negative a) :
    Proves (.imp (doubleNeg a) a) :=
  .of_derives (ha.stable [])

end Negative

/-- Any finite universal closure of any negation has an HA stability proof.
No closedness or decidability assumption on the formula under negation is
needed. In particular its body may contain existential quantifiers. -/
theorem closeN_neg_stability (n : Nat) (a : Formula) :
    Proves (.imp (doubleNeg (Formula.closeN n (neg a)))
      (Formula.closeN n (neg a))) :=
  ((Negative.neg a).closeN n).proves_stability

theorem sealPA_neg_stability (a : Formula) :
    Proves (.imp (doubleNeg (Formula.sealPA (neg a))) (Formula.sealPA (neg a))) :=
  (Negative.neg a).sealPA.proves_stability

end DiophantineConsistency.HA
