import P64QCube77Binding
import P64QCube77OldFacts

/-! Draft: same-valuation positive-zero equivalence for the 77 and 78 graphs. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace P64QCube77Existence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem same_zero_iff (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀i,0<v i) :
    InternalZero (P64QCube77.graph (fun j => (p j:ℤ))).output v ↔
      InternalZero (P64QCube78.graph (fun j => (p j:ℤ))).output v := by
  let pp : Fin 4 → ℤ := fun j => (p j:ℤ)
  let z : Fin 14 → DiffRing V := fun i => ι (v i)
  let g := P64QCube78.graph pp
  let a := g.A0.evalRing z
  let m := g.M.evalRing z
  let w := g.W.evalRing z
  let n := g.Na.evalRing z
  let l := g.Lt.evalRing z
  constructor
  · intro hz
    have hs : (a*n-1)*(a*n-1)+m*m+w*w+l*l=0 := by
      rw [internalZero_iff,P64QCube77Binding.output_eval] at hz
      exact hz
    have hsq := mul_self_nonneg (a*n-1)
    have hm := mul_self_nonneg m
    have hw := mul_self_nonneg w
    have hl := mul_self_nonneg l
    have hunit : a*n=1 := by
      have hzero : a*n-1=0 := mul_self_eq_zero.mp (by linarith)
      exact sub_eq_zero.mp hzero
    have hm0 : m=0 := mul_self_eq_zero.mp (by linarith)
    have hw0 : w=0 := mul_self_eq_zero.mp (by linarith)
    have hl0 : l=0 := mul_self_eq_zero.mp (by linarith)
    have hlt : InternalZero g.Lt v := (internalZero_iff _ _).mpr hl0
    obtain ⟨ha,hn⟩ := P64QCube77Unit.positive_factors hunit
      (P64QCube77Unit.first_ne_neg_of_transport p v hv hlt)
    rw [internalZero_iff,P64QCube78GraphSplit.output_shape]
    simp only [Expr.evalRing_add,Expr.evalRing_mul,Expr.evalRing_sub,Expr.evalRing_ofNat]
    change a*a+m*m+w*w+n*n+l*l-2=0
    rw [ha,hm0,hw0,hn,hl0]
    norm_num
  · intro hz
    obtain ⟨ha,hm,hw,hn,hl⟩ := P64QCube77OldFacts.residuals p v hv hz
    change a=1 at ha
    change m=0 at hm
    change w=0 at hw
    change n=1 at hn
    change l=0 at hl
    rw [internalZero_iff,P64QCube77Binding.output_eval]
    change (a*n-1)*(a*n-1)+m*m+w*w+l*l=0
    rw [ha,hm,hw,hn,hl]
    norm_num

theorem positive_zero_iff (p : Fin 4 → ℕ) :
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube77.graph (fun j => (p j:ℤ))).output v) ↔
    (∃v : Fin 14 → V, (∀i,0<v i) ∧
      InternalZero (P64QCube78.graph (fun j => (p j:ℤ))).output v) := by
  constructor <;> rintro ⟨v,hv,hz⟩
  · exact ⟨v,hv,(same_zero_iff p v hv).mp hz⟩
  · exact ⟨v,hv,(same_zero_iff p v hv).mpr hz⟩

#print axioms P64QCube77Existence.same_zero_iff
#print axioms P64QCube77Existence.positive_zero_iff
end P64QCube77Existence
