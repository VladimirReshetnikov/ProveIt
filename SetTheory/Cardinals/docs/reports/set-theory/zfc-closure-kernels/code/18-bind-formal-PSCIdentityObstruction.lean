import Init

/-!
# An identity-quantifier obstruction for the actual fixed-slot PSC wrapper

This is a proof-system counterinterpretation, not a first-order membership model.
It matches `psc_template` at ProveIt commit
96836f9eea3540e96322c3d28c7127a582aae223, including its binder scopes.

Every quantifier is interpreted as the identity Boolean operation.  The
membership atom R(i,j) is true exactly when i >= 2 and j = 0.  Thus both
primitive Bottom and R(0,0) evaluate to false.  Every emitted PSC matrix at
k = code + 2 is valid, regardless of the formula substituted for the matrix.

The derivation system includes the retained logical rows, optional old/dual
quantifier rows, explosion, same-variable specialization, S4/S5 strengthening,
and irreflexivity.  It still cannot derive its designated falsity.

The theorem concerns finite syntax and derivations.  An adapter from actual
numeric codes and an unbounded simulation of the emitted binary machine are
separate obligations and are not asserted here.
-/

namespace PSCIdentityObstruction

inductive Formula where
  | truth : Formula
  | bottom : Formula
  | rel : Nat → Nat → Formula
  | imp : Formula → Formula → Formula
  | all : Nat → Formula → Formula
  deriving DecidableEq, Repr

open Formula

def relation (i j : Nat) : Bool :=
  if j = 0 then decide (2 ≤ i) else false

def eval : Formula → Bool
  | truth => true
  | bottom => false
  | rel i j => relation i j
  | imp A B => !eval A || eval B
  | all _ A => eval A

def neg (F A : Formula) : Formula := imp A F
def conj (F A B : Formula) : Formula := neg F (imp A (neg F B))
def disj (F A B : Formula) : Formula := imp (neg F A) B
def ex (F : Formula) (i : Nat) (A : Formula) : Formula :=
  neg F (all i (neg F A))

def sub (x y z : Nat) : Formula :=
  all z (imp (rel z x) (rel z y))

def localBound (F : Formula) (k : Nat) (A : Formula) : Formula :=
  all 0 (ex F k (all 1 (imp A (sub 1 k 0))))

def guard (F : Formula) (k : Nat) : Formula :=
  disj F (sub 0 1 k) (rel 0 k)

def closed (F : Formula) (k : Nat) (A : Formula) : Formula :=
  all 0 (imp (guard F k) (all 1 (imp A (rel 1 k))))

def support (F : Formula) (k : Nat) (A : Formula) : Formula :=
  all 1 (imp (rel 1 k) (ex F 0 A))

def psc (F : Formula) (k : Nat) (A : Formula) : Formula :=
  imp (localBound F k A)
    (all 1 (ex F k (conj F (closed F k A) (support F k A))))

def rho8 (A B C U : Formula) : Formula :=
  imp (imp (imp C U) A) (imp (imp A C) (imp B C))

def distribution (i : Nat) (A B : Formula) : Formula :=
  imp (all i (imp A B)) (imp (all i A) (all i B))

def commutation (i j : Nat) (A : Formula) : Formula :=
  imp (all i (all j A)) (all j (all i A))

def oldRho6 (F : Formula) (i : Nat) (A : Formula) : Formula :=
  imp (ex F i (all i A)) A

def dualRho6 (F : Formula) (i : Nat) (A : Formula) : Formula :=
  imp A (all i (ex F i A))

def sameVariableUI (i : Nat) (A : Formula) : Formula := imp (all i A) A
def four (i : Nat) (A : Formula) : Formula := imp (all i A) (all i (all i A))
def five (F : Formula) (i : Nat) (A : Formula) : Formula :=
  imp (neg F (all i A)) (all i (neg F (all i A)))
def irreflexivity (F : Formula) (i : Nat) : Formula := all i (neg F (rel i i))

theorem eval_bottom : eval bottom = false := rfl
theorem eval_relativeFalse : eval (rel 0 0) = false := rfl

theorem relation_zero_left (j : Nat) : relation 0 j = false := by
  simp [relation]

theorem relation_one_left (j : Nat) : relation 1 j = false := by
  simp [relation]

theorem relation_self (i : Nat) : relation i i = false := by
  by_cases hi : i = 0
  · subst i
    rfl
  · simp [relation, hi]

theorem eval_psc (F A : Formula) (k : Nat)
    (hF : eval F = false) (hk : 2 ≤ k) : eval (psc F k A) = true := by
  cases hA : eval A <;>
    simp [psc, localBound, guard, closed, support, sub, disj, conj,
      ex, neg, eval, relation, hF, hA, hk]

theorem eval_psc_codePlusTwo (F A : Formula) (code : Nat)
    (hF : eval F = false) : eval (psc F (code + 2) A) = true := by
  apply eval_psc F A (code + 2) hF
  exact Nat.le_add_left 2 code

theorem eval_rho8 (A B C U : Formula) : eval (rho8 A B C U) = true := by
  cases hA : eval A <;> cases hB : eval B <;>
    cases hC : eval C <;> cases hU : eval U <;>
    simp [rho8, eval, hA, hB, hC, hU]

theorem eval_distribution (i : Nat) (A B : Formula) :
    eval (distribution i A B) = true := by
  cases hA : eval A <;> cases hB : eval B <;>
    simp [distribution, eval, hA, hB]

theorem eval_commutation (i j : Nat) (A : Formula) :
    eval (commutation i j A) = true := by
  cases hA : eval A <;> simp [commutation, eval, hA]

theorem eval_oldRho6 (F A : Formula) (i : Nat) (hF : eval F = false) :
    eval (oldRho6 F i A) = true := by
  cases hA : eval A <;> simp [oldRho6, ex, neg, eval, hF, hA]

theorem eval_dualRho6 (F A : Formula) (i : Nat) (hF : eval F = false) :
    eval (dualRho6 F i A) = true := by
  cases hA : eval A <;> simp [dualRho6, ex, neg, eval, hF, hA]

theorem eval_sameVariableUI (i : Nat) (A : Formula) :
    eval (sameVariableUI i A) = true := by
  cases hA : eval A <;> simp [sameVariableUI, eval, hA]

theorem eval_four (i : Nat) (A : Formula) : eval (four i A) = true := by
  cases hA : eval A <;> simp [four, eval, hA]

theorem eval_five (F A : Formula) (i : Nat) (hF : eval F = false) :
    eval (five F i A) = true := by
  cases hA : eval A <;> simp [five, neg, eval, hF, hA]

theorem eval_irreflexivity (F : Formula) (i : Nat) (hF : eval F = false) :
    eval (irreflexivity F i) = true := by
  simp [irreflexivity, neg, eval, relation_self, hF]

/- The `modal` constructor is stronger than the actual emitted rows: it allows
every formula whose identity-quantifier evaluation is true for *every*
membership-atom valuation with R(0,0) false.  In particular adding still more
purely modal axioms cannot defeat the counterinterpretation. -/
def identityEval (r : Nat → Nat → Bool) : Formula → Bool
  | truth => true
  | bottom => false
  | rel i j => r i j
  | imp A B => !identityEval r A || identityEval r B
  | all _ A => identityEval r A

def IdentityValid (A : Formula) : Prop :=
  ∀ r : Nat → Nat → Bool, r 0 0 = false → identityEval r A = true

theorem identityEval_relation (A : Formula) : identityEval relation A = eval A := by
  induction A with
  | truth => rfl
  | bottom => rfl
  | rel i j => rfl
  | imp A B hA hB => simp [identityEval, eval, hA, hB]
  | all i A hA => simp [identityEval, eval, hA]

inductive Derives (F : Formula) : Formula → Prop where
  | truth : Derives F truth
  | rho8 (A B C U : Formula) : Derives F (rho8 A B C U)
  | distribution (i : Nat) (A B : Formula) : Derives F (distribution i A B)
  | commutation (i j : Nat) (A : Formula) : Derives F (commutation i j A)
  | old (i : Nat) (A : Formula) : Derives F (oldRho6 F i A)
  | dual (i : Nat) (A : Formula) : Derives F (dualRho6 F i A)
  | vacuity (i j k : Nat) : Derives F (imp (rel i j) (all k (rel i j)))
  | same (i : Nat) (A : Formula) : Derives F (sameVariableUI i A)
  | four (i : Nat) (A : Formula) : Derives F (four i A)
  | five (i : Nat) (A : Formula) : Derives F (five F i A)
  | explosion (A : Formula) : Derives F (imp F A)
  | psc (k : Nat) (A : Formula) (hk : 2 ≤ k) : Derives F (psc F k A)
  | ir (i : Nat) : Derives F (irreflexivity F i)
  | modal (A : Formula) (hA : IdentityValid A) : Derives F A
  | mp {A B : Formula} : Derives F A → Derives F (imp A B) → Derives F B
  | gen (i : Nat) {A : Formula} : Derives F A → Derives F (all i A)

theorem derivation_sound {F A : Formula} (hF : eval F = false)
    (h : Derives F A) : eval A = true := by
  induction h with
  | truth => rfl
  | rho8 A B C U => exact eval_rho8 A B C U
  | distribution i A B => exact eval_distribution i A B
  | commutation i j A => exact eval_commutation i j A
  | old i A => exact eval_oldRho6 F A i hF
  | dual i A => exact eval_dualRho6 F A i hF
  | vacuity i j k => exact eval_sameVariableUI k (rel i j)
  | same i A => exact eval_sameVariableUI i A
  | four i A => exact eval_four i A
  | five i A => exact eval_five F A i hF
  | explosion A => simp [eval, hF]
  | psc k A hk => exact eval_psc F A k hF hk
  | ir i => exact eval_irreflexivity F i hF
  | modal A hA =>
      rw [← identityEval_relation A]
      exact hA relation rfl
  | mp hA hAB ihA ihAB =>
      simpa [eval, ihA] using ihAB
  | gen i hA ihA => exact ihA

theorem no_designated_falsity {F : Formula} (hF : eval F = false) :
    ¬ Derives F F := by
  intro h
  have ht := derivation_sound hF h
  rw [hF] at ht
  cases ht

theorem bottom_calculus_consistent : ¬ Derives bottom bottom :=
  no_designated_falsity rfl

theorem relative_calculus_consistent : ¬ Derives (rel 0 0) (rel 0 0) :=
  no_designated_falsity rfl

def properUISample : Formula := imp (all 2 (rel 2 0)) (rel 0 0)

theorem properUISample_false : eval properUISample = false := rfl

theorem properUISample_underivable {F : Formula} (hF : eval F = false) :
    ¬ Derives F properUISample := by
  intro h
  have ht := derivation_sound hF h
  rw [properUISample_false] at ht
  cases ht

#print axioms eval_psc
#print axioms derivation_sound
#print axioms bottom_calculus_consistent
#print axioms relative_calculus_consistent
#print axioms properUISample_underivable

end PSCIdentityObstruction
