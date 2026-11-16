import PA194PAeqLanguage
set_option autoImplicit false
set_option maxHeartbeats 5000000

/-! Mathematical inventory of the 0/S/+/*/= PA presentation, checked against
PAeq238 and its unchanged vendored FA/Robinson/PA definitions at upstream pin
84049b5e753190cf328cbc2d2710791ad32ad59c. Addition recursion is on its FIRST
argument. Independently authored Lean definitions; no axiom image proof is
asserted by this inventory. -/
namespace PA194PAeq
open LO LO.FirstOrder

def implies {ξ : Type} {n : Nat} (p q : Semiformula language ξ n) : Semiformula language ξ n := .or p.neg q

def reflexivity : Proposition language := .all (eq (.bvar 0) (.bvar 0))
def symmetry : Proposition language := .all (.all
  (implies (eq (.bvar 1) (.bvar 0)) (eq (.bvar 0) (.bvar 1))))
def transitivity : Proposition language := .all (.all (.all
  (implies (eq (.bvar 2) (.bvar 1))
    (implies (eq (.bvar 1) (.bvar 0)) (eq (.bvar 2) (.bvar 0))))))
def succCongruence : Proposition language := .all (.all
  (implies (eq (.bvar 0) (.bvar 1)) (eq (succ (.bvar 0)) (succ (.bvar 1)))))
def addCongruence : Proposition language := .all (.all (.all (.all
  (implies (eq (.bvar 0) (.bvar 1)) (implies (eq (.bvar 2) (.bvar 3))
    (eq (add (.bvar 0) (.bvar 2)) (add (.bvar 1) (.bvar 3))))))))
def mulCongruence : Proposition language := .all (.all (.all (.all
  (implies (eq (.bvar 0) (.bvar 1)) (implies (eq (.bvar 2) (.bvar 3))
    (eq (mul (.bvar 0) (.bvar 2)) (mul (.bvar 1) (.bvar 3))))))))
def addZero : Proposition language := .all (eq (add zero (.bvar 0)) (.bvar 0))
def addSucc : Proposition language := .all (.all
  (eq (add (succ (.bvar 0)) (.bvar 1)) (succ (add (.bvar 0) (.bvar 1)))))
def mulZero : Proposition language := .all (eq (mul zero (.bvar 0)) zero)
def mulSucc : Proposition language := .all (.all
  (eq (mul (succ (.bvar 1)) (.bvar 0)) (add (.bvar 0) (mul (.bvar 1) (.bvar 0)))))
def zeroNotSucc : Proposition language := .all ((eq zero (succ (.bvar 0))).neg)
def succInjective : Proposition language := .all (.all
  (implies (eq (succ (.bvar 1)) (succ (.bvar 0))) (eq (.bvar 1) (.bvar 0))))

def fixedAxioms : List (Proposition language) :=
  [reflexivity,symmetry,transitivity,succCongruence,addCongruence,mulCongruence,
   addZero,addSucc,mulZero,mulSucc,zeroNotSucc,succInjective]

/-- Arbitrary free parameters remain allowed; only the induction variable is bound. -/
def inductionFormula (p : Semiproposition language 1) : Proposition language :=
  implies (Semiformula.rewAux (Rew.subst ![zero]) p)
    (implies (.all (implies p (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) p)))
      (.all p))

/-- A theory definition, not Lean axioms or an assumed adequacy result. -/
inductive PAeqAxiom : Proposition language → Prop
  | fixed (p) : p ∈ fixedAxioms → PAeqAxiom p
  | induction (p : Semiproposition language 1) : PAeqAxiom (inductionFormula p)

/-- Close every free parameter, including those of induction instances. -/
def ordinaryPAeq : Theory language :=
  fun σ => ∃ p : Proposition language, PAeqAxiom p ∧ p.univCl = σ

end PA194PAeq

