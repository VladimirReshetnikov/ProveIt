import IPRADerivations.Analysis.Optimization.Convexity.RationalConvexArguments
import IPRADerivations.Core.CongruenceTactic

/-!
# The named modulus at the original rational arguments

The two horizontal endpoint codes alone determine the clock. The
original cofinal multiplicative comparisons use the original rational
endpoint and interior query codes. The finite proof may enlarge the
common scale in order to form the secants without changing that clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalOriginalConvexModulus

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (succ)
open RationalConvexArguments (arguments clock endpointDen firstNumerator secondNumerator enlargedDen interiorNumerator
  original_geometry original_proximity original_interior_queries original_endpoint_queries endpoint_den_positive)
open RationalConvexSecantWeights (leftPoint rightPoint leftRemainder rightRemainder displacement)
open RationalConvexClockRescale (left_point_rescale right_point_rescale)
open RationalNestedConvexModulus (presented witnessIndex witnessExponent pointInputs afterWitnesses)
open RationalNamedLocalModulus (named_center_modulus powerComparisons)
open RationalIntervalPowerComparison (centerOrder subst_centerOrder)
open RationalConvexSecants (nonnegative)
open RationalNestedIntervals (center centerF subst_center)
open RationalArithmetic (recode add multiply)
open GaussianRationalSyntheticBounds (natCode)
open RationalValueBounds (radius)
open RationalArgmin (transitive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sourceLeft (a : PTm n) : PTm n := multiply RationalAlgebra.half a
def sourceRight (b : PTm n) : PTm n := add b (natCode one)

def witnessed (L U : PR 3) (W : PR 2) (q o x : PTm n) : Fm PTm n :=
  presented L U W q x ⋏ le (witnessIndex W q x) o

def sourceInputs (L U : PR 3) (W : PR 2) (a b u v o x : PTm n) : Fm PTm n :=
  witnessed L U W (sourceLeft a) o x ⋏
    (witnessed L U W (sourceRight b) o x ⋏ (witnessed L U W (recode u) o x ⋏ witnessed L U W (recode v) o x))

def sourcePowerComparisons (L U : PR 3) (a b u v o x : PTm n) : Fm PTm n :=
  let d := enlargedDen a b u v
  let p := firstNumerator a b*endpointDen u v
  let q := secondNumerator a b*endpointDen u v
  let i := interiorNumerator a b u v
  let j := interiorNumerator a b v u
  centerOrder L U (recode v) (sourceLeft a) (recode u) (leftRemainder p i) (displacement i j) o x ⋏
    centerOrder L U (recode u) (sourceRight b) (recode v) (rightRemainder d q j) (displacement i j) o x

theorem source_queries (a b u v : PTm n) (h : Γ ⊢[PRAAx] arguments a b u v) : Γ ⊢[PRAAx]
    (leftPoint (enlargedDen a b u v) (firstNumerator a b*endpointDen u v) ≐ sourceLeft a) ⋏
    ((rightPoint (enlargedDen a b u v) (secondNumerator a b*endpointDen u v) ≐ sourceRight b) ⋏
      ((RationalCubeMidpoint.fraction (interiorNumerator a b u v) (enlargedDen a b u v) ≐ recode u) ⋏
       (RationalCubeMidpoint.fraction (interiorNumerator a b v u) (enlargedDen a b u v) ≐ recode v))) := by
  have h₀ : Γ ⊢[PRAAx] nonnegative a := le_of_lt h.andE₁
  have h₁ := transitive h₀ (transitive h.andE₂.andE₁ (transitive h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂))
  have he := original_endpoint_queries a b h₀ h₁
  have d := endpoint_den_positive (Γ := Γ) a b
  have r := endpoint_den_positive (Γ := Γ) u v
  exact .andI ((left_point_rescale _ _ _ d r).eqTrans he.andE₁)
    (.andI ((right_point_rescale _ _ _ d r).eqTrans he.andE₂) (original_interior_queries a b u v h))

@[simp] theorem subst_witnessed {m : ℕ} (σ : Fin n → PTm m) (L U : PR 3) (W : PR 2) (q o x : PTm n) :
    (witnessed L U W q o x).subst σ =
      witnessed L U W (Syn.subst σ q) (Syn.subst σ o) (Syn.subst σ x) := by
  simp [witnessed,presented,witnessIndex,witnessExponent,RationalNestedIntervals.positiveWitness,RationalConvexFiniteModulus.eps]

theorem witnessed_congr (L U : PR 3) (W : PR 2) (q r o x : PTm n) (e : Γ ⊢[PRAAx] q ≐ r)
    (h : Γ ⊢[PRAAx] witnessed L U W q o x) : Γ ⊢[PRAAx] witnessed L U W r o x := by
  have hw := Prf.eqSubst (Ax := PRAAx) (Γ := Γ) (witnessed L U W (var 0) (var 1) (var 2) : Fm PTm 3)
    (![q,o,x] : Fin 3 → PTm n) ![r,o,x] ?_ ?_
  · simpa only [subst_witnessed,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using hw
  · intro j
    fin_cases j
    · exact e
    · exact .eqRefl _
    · exact .eqRefl _
  · simpa only [subst_witnessed,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using h

theorem order_queries_congr (L U : PR 3) (X Y Z X' Y' Z' A B o x : PTm n)
    (ex : Γ ⊢[PRAAx] X ≐ X') (ey : Γ ⊢[PRAAx] Y ≐ Y') (ez : Γ ⊢[PRAAx] Z ≐ Z')
    (h : Γ ⊢[PRAAx] centerOrder L U X Y Z A B o x) : Γ ⊢[PRAAx] centerOrder L U X' Y' Z' A B o x := by
  have hw := Prf.eqSubst (Ax := PRAAx) (Γ := Γ)
    (centerOrder L U (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : Fm PTm 7)
    (![X,Y,Z,A,B,o,x] : Fin 7 → PTm n) ![X',Y',Z',A,B,o,x] ?_ ?_
  · simpa [subst_centerOrder] using hw
  · intro j
    fin_cases j
    · exact ex
    · exact ey
    · exact ez
    · exact .eqRefl _
    · exact .eqRefl _
    · exact .eqRefl _
    · exact .eqRefl _
  · simpa [subst_centerOrder] using h

theorem center_query_congr (L U : PR 3) (p x : PTm n) {q r : PTm n} (e : Γ ⊢[PRAAx] q ≐ r) :
    Γ ⊢[PRAAx] center L U q p x ≐ center L U r p x := by
  ipra_congr (center L U (var 0) (var 1) (var 2) : PTm 3) with [e, .eqRefl p, .eqRefl x]

theorem original_named_modulus (L U : PR 3) (W : PR 2) (a b u v k t o x : PTm n)
    (h : Γ ⊢[PRAAx] arguments a b u v) (hi : Γ ⊢[PRAAx] sourceInputs L U W a b u v o x)
    (ho : Γ ⊢[PRAAx] sourcePowerComparisons L U a b u v o x)
    (hd : Γ ⊢[PRAAx] radius u v one (pw two (clock (centerF L U) a b k x))) :
    Γ ⊢[PRAAx] radius (center L U (recode u) (succ (succ t)) x) (center L U (recode v) (succ (succ t)) x)
      (pw two k+pw two t) (pw two k*pw two t) := by
  let D := enlargedDen a b u v
  let P := firstNumerator a b*endpointDen u v
  let Q := secondNumerator a b*endpointDen u v
  let X := interiorNumerator a b u v
  let Y := interiorNumerator a b v u
  let A := leftPoint D P
  let B := rightPoint D Q
  let C := RationalCubeMidpoint.fraction X D
  let E := RationalCubeMidpoint.fraction Y D
  have eq := source_queries a b u v h
  have ha := witnessed_congr L U W (sourceLeft a) A o x eq.andE₁.eqSymm hi.andE₁
  have hb := witnessed_congr L U W (sourceRight b) B o x eq.andE₂.andE₁.eqSymm hi.andE₂.andE₁
  have hu := witnessed_congr L U W (recode u) C o x eq.andE₂.andE₂.andE₁.eqSymm hi.andE₂.andE₂.andE₁
  have hv := witnessed_congr L U W (recode v) E o x eq.andE₂.andE₂.andE₂.eqSymm hi.andE₂.andE₂.andE₂
  have pts : Γ ⊢[PRAAx] pointInputs L U W D P Q X Y x := .andI ha.andE₁ (.andI hb.andE₁ (.andI hu.andE₁ hv.andE₁))
  have off : Γ ⊢[PRAAx] afterWitnesses W D P Q X Y o x := .andI ha.andE₂ (.andI hb.andE₂ (.andI hu.andE₂ hv.andE₂))
  have powers : Γ ⊢[PRAAx] powerComparisons L U D P Q X Y o x := .andI
    (order_queries_congr L U (recode v) (sourceLeft a) (recode u) E A C (leftRemainder P X) (displacement X Y) o x
      eq.andE₂.andE₂.andE₂.eqSymm eq.andE₁.eqSymm eq.andE₂.andE₂.andE₁.eqSymm ho.andE₁)
    (order_queries_congr L U (recode u) (sourceRight b) (recode v) C B E (rightRemainder D Q Y) (displacement X Y) o x
      eq.andE₂.andE₂.andE₁.eqSymm eq.andE₂.andE₁.eqSymm eq.andE₂.andE₂.andE₂.eqSymm ho.andE₂)
  have hc := named_center_modulus L U W D P Q X Y k t o x (original_geometry a b u v h) pts off powers
    (original_proximity (centerF L U) a b u v k x h hd)
  exact RationalValueBounds.radius_congr (center_query_congr L U _ _ eq.andE₂.andE₂.andE₁)
    (center_query_congr L U _ _ eq.andE₂.andE₂.andE₂) (.eqRefl _) (.eqRefl _) hc

theorem actual_original_named_modulus_closed (L U : PR 3) (W : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((arguments (var 0) (var 1) (var 2) (var 3) ⋏
      sourceInputs L U W (var 0) (var 1) (var 2) (var 3) (var 6) (var 7)) ⟶
      sourcePowerComparisons L U (var 0) (var 1) (var 2) (var 3) (var 6) (var 7) ⟶
      radius (var 2) (var 3) one (pw two (clock (centerF L U) (var 0) (var 1) (var 4) (var 7))) ⟶
      radius (center L U (recode (var 2)) (succ (succ (var 5))) (var 7))
        (center L U (recode (var 3)) (succ (succ (var 5))) (var 7))
        (pw two (var 4)+pw two (var 5)) (pw two (var 4)*pw two (var 5))) :=
  closeUniv 8 (.impI (.impI (.impI (original_named_modulus L U W _ _ _ _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalOriginalConvexModulus
