import P74PositiveGuard
import PairEvalRingBridge

/-! Source-only first-factor binding for the literal 74 graph. The product
and other three residue premises are explicit. Imported drafts are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.FirstFactor74Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveFactorUnits2011
open PairEvalRingBridgeDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta
def X (beta : V) (v : Fin 14 → V) : V := q beta v*v 6
def Y (beta : V) (v : Fin 14 → V) : V := (q beta v*(q beta v*q beta v))*v 7
def m (beta : V) (v : Fin 14 → V) : V := X beta v*Y beta v*Y beta v
def k (v : Fin 14 → V) : V := v 9+v 10

/-- Positive beta and slots J,w,s force the exact first parameter m≥2. -/
theorem m_at_least_two (beta : V) (v : Fin 14 → V)
    (hb : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7) : 2≤m beta v := by
  have hp : 1≤v 0*beta := pos_iff_one_le.mp (mul_pos hJ hb)
  have hq : 2≤q beta v := by dsimp [q]; nlinarith
  have hqp : 0<q beta v := lt_of_lt_of_le (by simp : (0:V)<2) hq
  have hw1 : 1≤v 6 := pos_iff_one_le.mp hw
  have hX : 2≤X beta v := calc
    2≤q beta v := hq
    _≤q beta v*v 6 := le_mul_of_one_le_right (Arithmetic.zero_le _) hw1
  have hYp : 0<Y beta v := by
    dsimp [Y]; exact mul_pos (mul_pos hqp (mul_pos hqp hqp)) hs
  have hY : 1≤Y beta v := pos_iff_one_le.mp hYp
  calc
    2≤X beta v := hX
    _≤X beta v*Y beta v := le_mul_of_one_le_right (Arithmetic.zero_le _) hY
    _≤X beta v*Y beta v*Y beta v := le_mul_of_one_le_right (Arithmetic.zero_le _) hY
    _=m beta v := rfl

/-- Exact signed first-factor cut with the beta cast stated explicitly. -/
theorem first_eval (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) :
    (P74PositiveGuard.graph p).first.evalRing (fun j => ι (v j)) =
      ι (v 8*v 8)-ι ((m beta v*k v)*(m beta v*k v+k v)) := by
  simp [P74PositiveGuard.graph,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,q,X,Y,m,k,hbeta,
    map_add,map_mul,map_one] <;> ring

/-- The literal first factor can feed the five-unit extraction once the
actual product and three modulo-four exclusions have been supplied. -/
theorem first_factor_units (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta)
    (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7) (a b guard t : Pair V)
    (hp : Equivalent (product5 (pairEval (P74PositiveGuard.graph p).first v)
      a b guard t) (natural (1:V)))
    (ha : pairResidue a ≠ -1) (hb' : pairResidue b ≠ -1)
    (ht : pairResidue t ≠ -1) :
    v 8*v 8=(m beta v*k v)*(m beta v*k v+k v)+1 ∧
      a.1=a.2+1 ∧ b.1=b.2+1 ∧ guard.1=guard.2+1 ∧ t.1=t.2+1 := by
  exact five_positive_of_first_eval _ v (m beta v) (v 8) (k v)
    (m_at_least_two beta v hb hJ hw hs) a b guard t
    (first_eval p beta v hbeta) hp ha hb' ht

end DiophantineConsistency.FirstFactor74Draft

#print axioms DiophantineConsistency.FirstFactor74Draft.m_at_least_two
#print axioms DiophantineConsistency.FirstFactor74Draft.first_eval
#print axioms DiophantineConsistency.FirstFactor74Draft.first_factor_units
