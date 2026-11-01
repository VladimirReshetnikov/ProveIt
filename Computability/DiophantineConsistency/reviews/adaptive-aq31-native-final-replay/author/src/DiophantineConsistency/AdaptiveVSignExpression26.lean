import DiophantineConsistency.AdaptiveNamedValues33
import DiophantineConsistency.AdaptiveDirectOrdinate86AuxNorm
import DiophantineConsistency.AdaptiveAQ40Transport
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveVSignExpression26
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveAQ40Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rank13 (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let b : Expr (Fin 13) := .var 0 * .constant (p 0)
  let q := 1+b
  ((.var 2 + (q-.var 1)*b) * (q*q-1)) + (.var 0*(.constant (p 2)+.constant (p 3)*q))
def c13 : Expr (Fin 13) := .var 9 + .var 7*(.var 9+.var 10)
def f13 : Expr (Fin 13) := .var 3 * .var 3
def core : Expr (Fin 3 ⊕ Fin 13) :=
  .var (.inl 2) * (.var (.inr 5) * .var (.inl 1) - .var (.inl 0)) - .var (.inl 1)
def namedFill : Fin 3 ⊕ Fin 13 → Expr (Fin 26)
  | .inl i => ![.var 16,.var 17,.var 24] i
  | .inr i => .var ⟨i.val, by omega⟩
def originalFill (p : Fin 4 → ℤ) : Fin 3 ⊕ Fin 13 → Expr (Fin 13)
  | .inl i => ![rank13 p,c13,f13] i
  | .inr i => .var i

theorem named_syntax (p : Fin 4 → ℤ) : core.subst namedFill = AdaptiveNamedValues33.vExpression p := by rfl
theorem original_syntax (p : Fin 4 → ℤ) : core.subst (originalFill p) = AdaptiveDirectOrdinate86AuxNorm.eV p := by rfl

theorem named_equiv (p : Fin 4 → ℤ) (v : Fin 26 → V)
    (hz : InternalZero (AdaptiveNamedValues26.literal p) v) :
    Equivalent (pairEval (AdaptiveNamedValues33.vExpression p) v)
      (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV p) (fun i => v ⟨i.val, by omega⟩)) := by
  let v22 : Fin 22 → V := fun i => v (AdaptiveNamedValues26.embed i)
  let v17 : Fin 17 → V := fun i => v22 (AdaptiveNamedValues22.embed i)
  let v13 : Fin 13 → V := fun i => v ⟨i.val, by omega⟩
  have hz22 : InternalZero (AdaptiveNamedValues22.literal p) v22 :=
    AdaptiveNamedValues26.literal_zero_project p v hz
  have hz17 : InternalZero (AdaptiveRankWitness17.literal p) v17 :=
    AdaptiveNamedValues22.literal_zero_project p v22 hz22
  have hr := (AdaptiveRankWitness17.literal_zero_parts p v17).mp hz17 |>.2
  have hc := (AdaptiveNamedValues22.literal_zero_parts p v22).mp hz22 |>.2.1
  have hf := (AdaptiveNamedValues26.literal_zero_parts p v).mp hz |>.2.2.2.1
  change InternalZero ((.var 16) - (rank13 p).subst (fun i => .var ⟨i.val, by omega⟩) : Expr (Fin 17)) v17 at hr
  change InternalZero ((.var 17) - c13.subst (fun i => .var ⟨i.val, by omega⟩) : Expr (Fin 22)) v22 at hc
  change InternalZero ((.var 24) - f13.subst (fun i => .var ⟨i.val, by omega⟩) : Expr (Fin 26)) v at hf
  have her := (AdaptiveSquareWitnessDirect14.sub_zero_iff_equiv _ _ v17).mp hr
  have hec := (AdaptiveSquareWitnessDirect14.sub_zero_iff_equiv _ _ v22).mp hc
  have hef := (AdaptiveSquareWitnessDirect14.sub_zero_iff_equiv _ _ v).mp hf
  change Equivalent (splitEval (.var 16 : Expr (Fin 17)) v17) (splitEval ((rank13 p).subst (fun i => .var ⟨i.val, by omega⟩)) v17) at her
  change Equivalent (splitEval (.var 17 : Expr (Fin 22)) v22) (splitEval (c13.subst (fun i => .var ⟨i.val, by omega⟩)) v22) at hec
  change Equivalent (splitEval (.var 24 : Expr (Fin 26)) v) (splitEval (f13.subst (fun i => .var ⟨i.val, by omega⟩)) v) at hef
  rw [splitEval_subst_var] at her hec hef
  have hin : ∀ i, Equivalent (splitEval (namedFill i) v) (splitEval (originalFill p i) v13) := by
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · exact her
      · exact hec
      · exact hef
    | inr i => exact equivalent_refl _
  have h := subst_equiv_hetero core namedFill (originalFill p) v v13 hin
  rw [named_syntax, original_syntax] at h
  exact h

theorem positive_of_13 (p : Fin 4 → ℤ) (v : Fin 26 → V)
    (hz : InternalZero (AdaptiveNamedValues26.literal p) v)
    (hsign : (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV p) (fun i => v ⟨i.val, by omega⟩)).2 <
      (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV p) (fun i => v ⟨i.val, by omega⟩)).1) :
    (pairEval (AdaptiveNamedValues33.vExpression p) v).2 < (pairEval (AdaptiveNamedValues33.vExpression p) v).1 := by
  have he := named_equiv p v hz
  change (pairEval (AdaptiveNamedValues33.vExpression p) v).1 +
      (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV p) (fun i => v ⟨i.val, by omega⟩)).2 =
      (pairEval (AdaptiveNamedValues33.vExpression p) v).2 +
      (pairEval (AdaptiveDirectOrdinate86AuxNorm.eV p) (fun i => v ⟨i.val, by omega⟩)).1 at he
  by_contra hn
  have hle := le_of_not_gt hn
  have hlt := add_lt_add_of_le_of_lt hle hsign
  rw [he] at hlt
  exact (_root_.lt_irrefl _) hlt
#print axioms named_equiv
#print axioms positive_of_13
#print axioms named_syntax
#print axioms original_syntax
end DiophantineConsistency.AdaptiveVSignExpression26
