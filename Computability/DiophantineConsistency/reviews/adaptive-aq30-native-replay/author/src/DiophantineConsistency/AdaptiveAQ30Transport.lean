import DiophantineConsistency.AdaptiveAQ30Maps
import DiophantineConsistency.AdaptiveAQ40Transport
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ30Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveAQ40Transport
open AdaptiveAQ30Facts AdaptiveAQ30Maps AdaptiveAQ30Positive
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def fill (p : Fin 4 → ℕ) : Fin 31 → Expr (Fin 30) := ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5,.var 6,.var 7,.var 8,.var 9,.var 10,.var 11,.var 12,.var 13,.var 14,.var 15,.var 16,.var 17,bt p,.var 18,.var 19,.var 20,.var 21,.var 22,.var 23,.var 24,.var 25,.var 26,.var 27,.var 28,.var 29]
theorem extend_inputs (p : Fin 4 → ℕ) (v : Fin 30 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveAQ30Literal.literal (fun j => (p j:ℤ))) v) :
    ∀ i, Equivalent (splitEval (.var i) (extend p v)) (splitEval (fill p i) v) := by
  have ht := signed_w_positive p v hv hz
  have hlt : (splitEval (bt p) v).2 < (splitEval (bt p) v).1 := by simpa [wp,wm] using ht
  have hm : magnitude (splitEval (bt p) v) = (splitEval (bt p) v).1-(splitEval (bt p) v).2 := by
    simp [magnitude,tsub_eq_zero_of_le (le_of_lt hlt)]
  intro i
  fin_cases i <;> try exact equivalent_refl _
  change Equivalent (natural (magnitude (splitEval (bt p) v))) (splitEval (bt p) v)
  simp [Equivalent,natural,hm,tsub_add_cancel_of_le (le_of_lt hlt)]
#print axioms extend_inputs
theorem subst_id {σ : Type*} (e : Expr σ) : e.subst (fun i => .var i) = e := by
  induction e <;> simp [Expr.subst, *]

theorem residual_equiv (p : Fin 4 → ℕ) (v : Fin 30 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveAQ30Literal.literal (fun j => (p j:ℤ))) v) (i : Fin 22) :
    InternalZero ((AdaptiveAQ31Context.residuals (fun j => (p j:ℤ)) i).subst AdaptiveAQ31Context.newFill) (extend p v) ↔
    InternalZero (((AdaptiveAQ31Context.residuals (fun j => (p j:ℤ)) i).subst AdaptiveAQ31Context.newFill).subst (fill p)) v := by
  have h := subst_equiv_hetero ((AdaptiveAQ31Context.residuals (fun j => (p j:ℤ)) i).subst AdaptiveAQ31Context.newFill)
    (fun i => .var i) (fill p) (extend p v) v (extend_inputs p v hv hz)
  simpa only [subst_id,InternalZero,splitEval] using equivalent_zero_iff h

theorem extend_zero (p : Fin 4 → ℕ) (v : Fin 30 → V) (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveAQ30Literal.literal (fun j => (p j:ℤ))) v) :
    InternalZero (AdaptiveAQ31Literal.literal (fun j => (p j:ℤ))) (extend p v) := by
  have hall := (AdaptiveAQ30Zeros.sum_zero (fun j => (p j:ℤ)) v).mp hz
  rw [← AdaptiveAQ31Literal.new_literal]
  apply (AdaptiveAQ31Zeros.sum_zero (fun j => (p j:ℤ)) AdaptiveAQ31Context.newFill (extend p v)).mpr
  intro i
  apply (residual_equiv p v hv hz i).mpr
  fin_cases i
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 0) v
    exact hall 0
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 1) v
    exact hall 1
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 2) v
    exact hall 2
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 3) v
    exact hall 3
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 4) v
    exact hall 4
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 5) v
    exact hall 5
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 6) v
    exact hall 6
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 7) v
    exact hall 7
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 8) v
    exact hall 8
  · change InternalZero (bt p - bt p) v
    simp only [InternalZero]
    exact add_comm _ _
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 9) v
    exact hall 9
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 10) v
    exact hall 10
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 11) v
    exact hall 11
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 12) v
    exact hall 12
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 13) v
    exact hall 13
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 14) v
    exact hall 14
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 15) v
    exact hall 15
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 16) v
    exact hall 16
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 17) v
    exact hall 17
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 18) v
    exact hall 18
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 19) v
    exact hall 19
  · change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 20) v
    exact hall 20
#print axioms extend_zero
def lift : Fin 30 → Expr (Fin 31) := ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5,.var 6,.var 7,.var 8,.var 9,.var 10,.var 11,.var 12,.var 13,.var 14,.var 15,.var 16,.var 17,.var 19,.var 20,.var 21,.var 22,.var 23,.var 24,.var 25,.var 26,.var 27,.var 28,.var 29,.var 30]
theorem lift_inputs (v : Fin 31 → V) :
    ∀ i, Equivalent (splitEval (lift i) v) (splitEval (.var i) (project v)) := by
  intro i
  fin_cases i <;> exact equivalent_refl _

theorem project_inputs (p : Fin 4 → ℕ) (v : Fin 31 → V)
    (hz : InternalZero (AdaptiveAQ31Literal.literal (fun j => (p j:ℤ))) v) :
    ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill p i) (project v)) := by
  have hall := (AdaptiveAQ31Zeros.sum_zero (fun j => (p j:ℤ)) AdaptiveAQ31Context.newFill v).mp (by rw [AdaptiveAQ31Literal.new_literal]; exact hz)
  have h9 := hall 9
  change InternalZero (.var 18 - (bt p).subst lift) v at h9
  change (splitEval (.var 18 - (bt p).subst lift) v).1 = (splitEval (.var 18 - (bt p).subst lift) v).2 at h9
  rw [splitEval_sub] at h9
  change Equivalent (splitEval (.var 18) v) (splitEval ((bt p).subst lift) v) at h9
  have hbt := subst_equiv_hetero (bt p) lift (fun i => .var i) v (project v) (lift_inputs v)
  rw [subst_id] at hbt
  have hw := equivalent_trans h9 hbt
  intro i
  fin_cases i <;> try exact equivalent_refl _
  exact hw
#print axioms project_inputs
theorem project_residual_equiv (p : Fin 4 → ℕ) (v : Fin 31 → V)
    (hz : InternalZero (AdaptiveAQ31Literal.literal (fun j => (p j:ℤ))) v) (i : Fin 22) :
    InternalZero ((AdaptiveAQ31Context.residuals (fun j => (p j:ℤ)) i).subst AdaptiveAQ31Context.newFill) v ↔
    InternalZero (((AdaptiveAQ31Context.residuals (fun j => (p j:ℤ)) i).subst AdaptiveAQ31Context.newFill).subst (fill p)) (project v) := by
  have h := subst_equiv_hetero ((AdaptiveAQ31Context.residuals (fun j => (p j:ℤ)) i).subst AdaptiveAQ31Context.newFill)
    (fun i => .var i) (fill p) v (project v) (project_inputs p v hz)
  simpa only [subst_id,InternalZero,splitEval] using equivalent_zero_iff h

theorem project_zero (p : Fin 4 → ℕ) (v : Fin 31 → V)
    (hz : InternalZero (AdaptiveAQ31Literal.literal (fun j => (p j:ℤ))) v) :
    InternalZero (AdaptiveAQ30Literal.literal (fun j => (p j:ℤ))) (project v) := by
  have hall := (AdaptiveAQ31Zeros.sum_zero (fun j => (p j:ℤ)) AdaptiveAQ31Context.newFill v).mp (by rw [AdaptiveAQ31Literal.new_literal]; exact hz)
  apply (AdaptiveAQ30Zeros.sum_zero (fun j => (p j:ℤ)) (project v)).mpr
  intro i
  fin_cases i
  · have h := (project_residual_equiv p v hz 0).mp (hall 0)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 0) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 1).mp (hall 1)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 1) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 2).mp (hall 2)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 2) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 3).mp (hall 3)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 3) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 4).mp (hall 4)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 4) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 5).mp (hall 5)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 5) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 6).mp (hall 6)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 6) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 7).mp (hall 7)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 7) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 8).mp (hall 8)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 8) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 10).mp (hall 10)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 9) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 11).mp (hall 11)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 10) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 12).mp (hall 12)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 11) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 13).mp (hall 13)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 12) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 14).mp (hall 14)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 13) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 15).mp (hall 15)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 14) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 16).mp (hall 16)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 15) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 17).mp (hall 17)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 16) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 18).mp (hall 18)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 17) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 19).mp (hall 19)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 18) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 20).mp (hall 20)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 19) (project v) at h
    exact h
  · have h := (project_residual_equiv p v hz 21).mp (hall 21)
    change InternalZero (AdaptiveAQ30Zeros.residuals (fun j => (p j:ℤ)) 20) (project v) at h
    exact h
#print axioms project_zero
end DiophantineConsistency.AdaptiveAQ30Transport
