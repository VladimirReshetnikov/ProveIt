import ConciseIPRA.PR
import ConciseIPRA.NativeBiInterpretation

/-!
# Puiseux finite-output target

STATUS: UNCOMPILED INTERFACE, not a completed Puiseux proof.
Written against the inspected ProveIt commit
d851229c33ef395db8dc04baf28c6a291073f61e (Lean 4.32.0).

Every field below must be replaced by a concrete primitive-recursive syntax
tree and accompanied by its decoding/correctness proof. In particular, a
predicate called `factorJet` is not granted its mathematical meaning.

No theorem of Puiseux, implicit functions, algebraic closure, or soundness
reflection is assumed as an axiom. There are no omitted proof terms.
The only proved result below transfers an ALREADY SUPPLIED iPRA derivation
through ProveIt's existing interpretation.
-/

namespace PuiseuxIPRA

open LeanProofs.ConciseIPRA

/-- Concrete PR programs still to implement.
All encodings are natural-number encodings of finite data. -/
structure Programs where
  /-- Valid finite exact-algebraic polynomial input. -/
  inputOK : PR 1
  /-- Finite Newton tree, common ramification, pole data, simple leaves,
      radius/majorant data, and algebraic extension certificates. -/
  packet : PR 1
  /-- Coherent finite coefficient output at the requested precision. -/
  jets : PR 2
  /-- Check the finite packet, including ramification and degree accounting. -/
  packetOK : PR 2
  /-- Check the coefficientwise complete factorization identity through N.
      With e the ramification, p the common pole bound, a_r the original
      coefficients, W_i the returned power-series jets, and m_i their
      multiplicities, this means every relevant coefficient of
        sum_r T^((d-r)*p) * a_r(T^e) * Z^r
          = a_d(T^e) * product_i (Z-W_i(T))^m_i.
      All exponents are nonnegative; the finite check covers every
      Z-degree 0,...,d and every requested T-degree. -/
  factorJet : PR 4
  /-- Check agreement of the N-jet with the truncation of the (N+1)-jet. -/
  prefixOK : PR 5
  /-- Check weighted coefficient bounds for all coefficients in the N-jet. -/
  majorantOK : PR 3
  /-- Numerical less-or-equal test, returning 1 for true. -/
  le : PR 2
  /-- Check the finite geometric-tail estimate from N through M for every
      normalized branch, using the rational radius in the packet. -/
  tailOK : PR 6

private def args2 {n : Nat} (a b : PTm n) : Fin 2 → PTm n :=
  Fin.cases a (fun _ => b)

private def args3 {n : Nat} (a b c : PTm n) : Fin 3 → PTm n :=
  Fin.cases a (args2 b c)

private def args4 {n : Nat} (a b c d : PTm n) : Fin 4 → PTm n :=
  Fin.cases a (args3 b c d)

private def args5 {n : Nat} (a b c d e : PTm n) : Fin 5 → PTm n :=
  Fin.cases a (args4 b c d e)

private def args6 {n : Nat} (a b c d e f : PTm n) : Fin 6 → PTm n :=
  Fin.cases a (args5 b c d e f)

private def one {n : Nat} : PTm n :=
  PTm.succ PTm.zero

private def isTrue {n : Nat} (t : PTm n) : Fm PTm n :=
  Fm.eq t one

/-- Free variables: 0 = precision N, 1 = polynomial input p.
All displayed conditions are equations of PR terms, hence quantifier-free. -/
def jetMatrix (C : Programs) : Fm PTm 2 :=
  let p : PTm 2 := PTm.var 1
  let n : PTm 2 := PTm.var 0
  let q := PTm.app C.packet (fun _ => p)
  let j := PTm.app C.jets (args2 p n)
  let jNext := PTm.app C.jets (args2 p (PTm.succ n))
  Fm.imp (isTrue (PTm.app C.inputOK (fun _ => p)))
    (Fm.and (isTrue (PTm.app C.packetOK (args2 p q)))
      (Fm.and (isTrue (PTm.app C.factorJet (args4 p q n j)))
        (Fm.and (isTrue (PTm.app C.prefixOK (args5 p q n j jNext)))
          (isTrue (PTm.app C.majorantOK (args3 q n j))))))

/-- Free variables: 0 = M, 1 = N, 2 = polynomial input p. -/
def tailMatrix (C : Programs) : Fm PTm 3 :=
  let p : PTm 3 := PTm.var 2
  let n : PTm 3 := PTm.var 1
  let m : PTm 3 := PTm.var 0
  let q := PTm.app C.packet (fun _ => p)
  let jn := PTm.app C.jets (args2 p n)
  let jm := PTm.app C.jets (args2 p m)
  Fm.imp
    (Fm.and (isTrue (PTm.app C.inputOK (fun _ => p)))
      (isTrue (PTm.app C.le (args2 n m))))
    (isTrue (PTm.app C.tailOK (args6 p q n m jn jm)))

/-- The actual closed formula, rather than an unspecified proposition. -/
def PuiseuxSentence (C : Programs) : Fm PTm 0 :=
  Fm.and
    (Fm.all (Fm.all (jetMatrix C)))
    (Fm.all (Fm.all (Fm.all (tailMatrix C))))

/-- These structural checks certify only the shape of the induction matrices. -/
theorem jetMatrix_qf (C : Programs) : (jetMatrix C).QF := by
  simp [jetMatrix, isTrue, Fm.QF]

theorem tailMatrix_qf (C : Programs) : (tailMatrix C).QF := by
  simp [tailMatrix, isTrue, Fm.QF]

/-- Completion requires a term of this type for the concrete program tuple,
not just a theorem about standard natural numbers or completed complex fields. -/
abbrev InternalPuiseux (C : Programs) : Prop :=
  Prf PRAAx ([] : List (Fm PTm 0)) (PuiseuxSentence C)

/-- Existing repository transport, conditional on the completed derivation.
This theorem does not provide that derivation. -/
theorem suppliedDerivation_toNative (C : Programs) (h : InternalPuiseux C) :
    NPrf [] (NFm.ofPRA (PuiseuxSentence C)) := by
  exact (pra_iff_native
    (Γ := ([] : List (Fm PTm 0)))
    (φ := PuiseuxSentence C)).mp h

end PuiseuxIPRA

