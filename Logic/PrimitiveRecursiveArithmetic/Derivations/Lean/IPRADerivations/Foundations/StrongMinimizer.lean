import IPRADerivations.Foundations.ApproximateWitness
import IPRADerivations.Foundations.StrongConvexity

/-!
# Rational stability of actual finite-net minimizers

Packet `foundations/ipra_finite_use_framework_2026-11-15_v2`, the regularity
component of `cor:strong-minimizer`. The selected points are the existing
primitive recursive least argmin, with the precision packed into its input.
Two applications of the finite-net theorem give their residual bounds. An
independently checked strong-convexity certificate for the residual converts
those bounds into a distance estimate.

The signed objective numerator is exactly `I + R(y)`, where `R` is the
nonnegative residual. Identifying an application's residual with its objective
gap is an explicit adapter obligation. The midpoint certificate states strong
convexity of this same residual and is retained as an object-theory premise.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.StrongMinimizer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n m : ℕ} {Γ : List (Fm PTm n)}

/-- The finite approximation programs and their displayed numerator error budgets. -/
structure Approximation where
  net : PTm 2
  score : PTm 2
  residual : PTm 2
  domain : Fm PTm 2
  close : Fm PTm 3
  bound : PR 2
  witnessError : PR 2
  modulusError : PR 2
  upperError : PR 2
  lowerError : PR 2

/-- Lift a point/data body so its data is the second component of `(precision,data)`. -/
def indexedTerm (body : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] body

def indexedDomain (body : Fm PTm 2) : Fm PTm 2 := body.subst ![var 0, sndT (var 1)]

/-- The actual point returned by the existing finite-net least argmin. -/
def pick (A : Approximation) (k x : PTm n) : PTm n :=
  ApproximateWitness.selected A.net A.score (ap2 A.bound k x) (pairT k x)

/-- The complete error produced by the finite-net witness theorem. -/
def error (A : Approximation) (k x : PTm n) : PTm n :=
  ap2 A.witnessError k x + ap2 A.modulusError k x +
    ap2 A.upperError k x + ap2 A.lowerError k x

/-- The six source approximation contracts at a single precision. -/
def queryInputs (A : Approximation) (k x : PTm n) : Fm PTm n :=
  let data := pairT k x
  let K := ap2 A.bound k x
  let R := indexedTerm A.residual
  let domain := indexedDomain A.domain
  .ex (ApproximateWitness.domainAt domain (var 0) (Syn.shift data) ⋏
      le (inst2 R (var 0) (Syn.shift data)) (Syn.shift (ap2 A.witnessError k x))) ⋏
    (ApproximateWitness.netDomain domain A.net K data ⋏
      (.all (ApproximateWitness.coverage domain A.close A.net
        (Syn.shift K) (Syn.shift data) (var 0)) ⋏
      (.all (ApproximateWitness.domainAt domain (var 0) (Syn.shift data) ⟶
        ApproximateWitness.modulus A.close A.net R (Syn.shift K) (Syn.shift data)
          (var 0) (Syn.shift (ap2 A.modulusError k x))) ⋏
      (ApproximateWitness.upperEvaluation A.net A.score R K data (ap2 A.upperError k x) ⋏
        ApproximateWitness.lowerEvaluation A.net A.score R K data (ap2 A.lowerError k x)))))

/-- Unpack the fixed data argument in an indexed residual evaluation. -/
theorem indexed_term_at (body : PTm 2) (k y x : PTm n) :
    Γ ⊢[PRAAx] inst2 (indexedTerm body) y (pairT k x) ≐ inst2 body y x := by
  have same : inst2 (indexedTerm body) y (pairT k x) =
      inst2 body y (sndT (pairT k x)) := by
    simp only [indexedTerm, inst2, Syn.subst_subst]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [same]
  exact congrInst2 body (.eqRefl _) (snd_pair _ _)

/-- Each query's local witnesses yield the selected residual bound. -/
theorem selected_residual (A : Approximation) (k x : PTm n)
    (contracts : Γ ⊢[PRAAx] queryInputs A k x) :
    Γ ⊢[PRAAx] le (inst2 A.residual (pick A k x) x) (error A k x) := by
  have result := ApproximateWitness.approximate_witness_exists
    A.net A.score (indexedTerm A.residual) (indexedDomain A.domain) A.close
    (ap2 A.bound k x) (pairT k x) (ap2 A.witnessError k x) (ap2 A.modulusError k x)
    (ap2 A.upperError k x) (ap2 A.lowerError k x)
    (.andE₁ contracts) (.andE₁ (.andE₂ contracts))
    (.andE₁ (.andE₂ (.andE₂ contracts)))
    (.andE₁ (.andE₂ (.andE₂ (.andE₂ contracts))))
    (.andE₁ (.andE₂ (.andE₂ (.andE₂ (.andE₂ contracts)))))
    (.andE₂ (.andE₂ (.andE₂ (.andE₂ (.andE₂ contracts)))))
  exact le_congr (indexed_term_at A.residual k (pick A k x) x) (.eqRefl _)
    (.andE₂ (.andE₂ result))

/-- Adding an arbitrary signed baseline preserves a natural residual inequality. -/
theorem objective_upper (lower : ZT n) {R E : PTm n}
    (h : Γ ⊢[PRAAx] le R E) :
    Γ ⊢[PRAAx] zle (lower + ZT.ofNat R) (lower + ZT.ofNat E) := by
  have slack := natEq (eq_add_of_le h)
  refine zle_of_toZ (monus E R) ?_
  simp only [ZT.toZ_add, ZT.toZ_ofNat]
  simp only [Q.mk_add, map_add] at slack
  linear_combination -slack

/-- The signed baseline is a lower bound for every nonnegative residual. -/
theorem objective_lower (lower : ZT n) (R : PTm n) :
    Γ ⊢[PRAAx] zle lower (lower + ZT.ofNat R) := by
  refine zle_of_toZ R ?_
  simp only [ZT.toZ_add, ZT.toZ_ofNat]

/-- The midpoint strong-convexity premise, at the actual two selected points.
`midpoint`, `distanceNum` and `distanceDen` are arbitrary fixed PR term bodies. -/
def midpointConvexity (A : Approximation) (midpoint distanceNum distanceDen : PTm 3)
    (N M x D m Q : PTm n) (lower : ZT n) : Fm PTm n :=
  let left := pick A N x
  let right := pick A M x
  let middle := inst3 midpoint left right x
  let a := inst3 distanceNum left right x
  let b := inst3 distanceDen left right x
  let Fmid := lower + ZT.ofNat (inst2 A.residual middle x)
  let Fleft := lower + ZT.ofNat (inst2 A.residual left x)
  let Fright := lower + ZT.ofNat (inst2 A.residual right x)
  zle (ZT.ofNat (two * (Q * b * b)) * Fmid + ZT.ofNat (two * (D * m * a * a)))
    (ZT.ofNat (Q * b * b) * (Fleft + Fright))

/-- Quantitative pair stability from the actual finite-net selectors and
an explicit scalar error schedule. -/
theorem selected_pair_stable (A : Approximation) (midpoint distanceNum distanceDen : PTm 3)
    (N M s x D m Q : PTm n) (lower : ZT n)
    (atN : Γ ⊢[PRAAx] queryInputs A N x)
    (atM : Γ ⊢[PRAAx] queryInputs A M x)
    (positiveD : Γ ⊢[PRAAx] le one D) (positiveCoefficient : Γ ⊢[PRAAx] le one m)
    (convexity : Γ ⊢[PRAAx] midpointConvexity A midpoint distanceNum distanceDen N M x D m Q lower)
    (schedule : Γ ⊢[PRAAx] le
      (Q * (error A N x + error A M x) * pw two (N + s) * pw two (N + s)) (D * m)) :
    Γ ⊢[PRAAx] le
      (pw two (N + s) * inst3 distanceNum (pick A N x) (pick A M x) x)
      (inst3 distanceDen (pick A N x) (pick A M x) x) := by
  have left := selected_residual A N x atN
  have right := selected_residual A M x atM
  have leftBudget := le_trans left (le_add_right (error A N x) (error A M x))
  have rightBudget := le_trans right (le_add_left (error A M x) (error A N x))
  have result := StrongConvexity.rational_diameter lower
    (lower + ZT.ofNat (inst2 A.residual (inst3 midpoint (pick A N x) (pick A M x) x) x))
    (lower + ZT.ofNat (inst2 A.residual (pick A N x) x))
    (lower + ZT.ofNat (inst2 A.residual (pick A M x) x))
    D m Q _ _ (error A N x + error A M x) one (pw two (N + s))
    positiveD positiveCoefficient (objective_lower _ _)
    (objective_upper lower leftBudget) (objective_upper lower rightBudget) convexity
    (le_congr (.eqRefl _) (by ipra_ring) schedule)
  exact le_congr (.eqRefl _) (one_mul _) result

/-- Slots are `N,M,s,x,D,m,Q` and the two signed parts of the lower baseline. -/
def pairFormula (A : Approximation) (midpoint distanceNum distanceDen : PTm 3) : Fm PTm 9 :=
  let N := var 0
  let M := var 1
  let s := var 2
  let x := var 3
  let D := var 4
  let m := var 5
  let Q := var 6
  let lower : ZT 9 := ⟨var 7, var 8⟩
  let a := inst3 distanceNum (pick A N x) (pick A M x) x
  let b := inst3 distanceDen (pick A N x) (pick A M x) x
  queryInputs A N x ⟶ queryInputs A M x ⟶
    le one D ⟶ le one m ⟶ le one Q ⟶ le one b ⟶
    midpointConvexity A midpoint distanceNum distanceDen N M x D m Q lower ⟶
    le (Q * (error A N x + error A M x) * pw two (N + s) * pw two (N + s)) (D * m) ⟶
      (le one b ⋏ le (pw two (N + s) * a) b)

/-- The actual selector pair has the stated rational distance bound from
its local approximation contracts and numeric precision schedule. -/
theorem selected_pair_closed (A : Approximation) (midpoint distanceNum distanceDen : PTm 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9 (pairFormula A midpoint distanceNum distanceDen) := by
  apply closeUniv 9
  refine .impI (.impI (.impI (.impI (.impI (.impI (.impI (.impI ?_)))))))
  refine .andI (Prf.hyp (by simp)) ?_
  exact selected_pair_stable A midpoint distanceNum distanceDen
    (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟨var 7, var 8⟩
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))
    (Prf.hyp (by simp)) (Prf.hyp (by simp)) (Prf.hyp (by simp))

#print axioms selected_residual
#print axioms selected_pair_closed

end LeanProofs.IPRA.Foundations.StrongMinimizer
