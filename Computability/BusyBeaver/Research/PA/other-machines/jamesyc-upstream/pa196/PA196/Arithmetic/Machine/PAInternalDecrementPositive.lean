module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalDecrementPositiveCell
public import PA196.Arithmetic.Machine.PAInternalIncrement
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.DecrementPositive
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Coding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def output (pre v rest : V) : V :=
  CarryCode.rightFile pre (4*repeatBits v 1 (CarryCode.rightFile rest 0)+2)
noncomputable def time (pre : V) : V := 2*CarryCode.cost pre+4

def outputGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y pre v rest. ∃ rt k, !CarryCode.rightGraph rt rest 0 ∧
    !repeatGraph k v 1 rt ∧ !CarryCode.rightGraph y pre (4*k+2)”
def timeGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “y pre. ∃ a, !CarryCode.costGraph a pre ∧ y=2*a+4”
instance output_defined : 𝚺ᴬ₁-Function₃ (output : V → V → V → V) via outputGraph :=
  .mk fun b => by simp [outputGraph,CarryCode.right_defined.df,repeat_defined.df,output]
instance time_defined : 𝚺ᴬ₁-Function₁ (time : V → V) via timeGraph :=
  .mk fun b => by simp [timeGraph,CarryCode.cost_defined.df,time]
end Coding
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
/-- Arbitrary-model positive decrement. The extra leading one is retained in
its exact centered configuration, not discarded as a file normalization. -/
theorem segment (pre v rest l : V) : ∃ qs ls rs,
    Segment (time pre) qs ls rs 1 l (Increment.input pre (v+1) rest)
      40 l (2*output pre v rest+1) := by
  let t := repeatBits v 1 (CarryCode.rightFile rest 0)
  let lp := CarryCode.leftFile pre l
  obtain ⟨qa,la,ra,ha⟩ := CarryFile.segment pre l (8*t+4)
  obtain ⟨qb,lb,rb,hb⟩ := DecrementPositiveCell.segment lp t
  obtain ⟨qc,lc,rc,hc⟩ := ReturnFile.segment pre (2*l+1) (4*t+2)
  unfold Phase at hc
  have hn : ReturnCode.leftFile pre (2*l+1)=2*lp+1 := by
    simpa only [one_add_one_eq_two] using CarryReturn.relation pre l
  rw [hn] at hc
  have hd : (2*lp+1)/2=lp := by simpa only [one_add_one_eq_two,Bool.toNat_true,Nat.cast_one] using LeftPhase.bit_div true lp
  have hm : (2*lp+1)%2=1 := by simpa only [one_add_one_eq_two,Bool.toNat_true,Nat.cast_one] using LeftPhase.bit_mod true lp
  have hdl : (2*l+1)/2=l := by simpa only [one_add_one_eq_two,Bool.toNat_true,Nat.cast_one] using LeftPhase.bit_div true l
  have hml : (2*l+1)%2=1 := by simpa only [one_add_one_eq_two,Bool.toNat_true,Nat.cast_one] using LeftPhase.bit_mod true l
  rw [hd,hm,hdl,hml] at hc
  have hp : (1+1)*(4*t+2)+1=8*t+5 := by ring1
  rw [hp] at hc
  obtain ⟨q1,l1,r1,h1⟩ := segment_compose ha hb
  obtain ⟨q2,l2,r2,h2⟩ := segment_compose h1 hc
  have ht : CarryCode.cost pre+4+CarryCode.cost pre=time pre := by unfold time; ring1
  have hi : Increment.input pre (v+1) rest=CarryCode.rightFile pre (8*t+4) := by
    unfold Increment.input
    rw [repeat_succ]
    congr 1
    dsimp [t]
    ring1
  exact ⟨q2,l2,r2, by simpa only [ht,hi,output,t,one_add_one_eq_two] using h2⟩
end Models

def sentence : ArithmeticSentence :=
  “∀ pre v rest l, ∃ i o c, !Increment.inputGraph i pre (v+1) rest ∧
    !outputGraph o pre v rest ∧ !timeGraph c pre ∧
    ∃ qs ls rs, !segmentFormula c qs ls rs 1 l i 40 l (2*o+1)”
theorem pa_proves_positive_decrement : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [Increment.input_defined.df,output_defined.df,time_defined.df,
    segment_correct,numeral_eq_natCast]
  exact segment
#print axioms segment
#print axioms pa_proves_positive_decrement
end PA196.Arithmetic.Machine.PA.InternalTrace.DecrementPositive

