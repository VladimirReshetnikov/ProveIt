module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalForwardFile
public import M6PA.Model.PAInternalSelectedCell
public import M6PA.Model.PAInternalCarryReturnRelation
public import M6PA.Model.PAInternalIncrementTail
public import M6PA.Model.PAInternalCarryFile
public import M6PA.Model.PAInternalReturnFile
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace.Increment
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ScanBits
attribute [local irreducible] Step StepFormula.formula
section Coding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def input (pre v rest : V) : V :=
  CarryCode.rightFile pre (4*repeatBits v 1 (CarryCode.rightFile rest 0))
noncomputable def output (pre v rest : V) : V :=
  CarryCode.rightFile pre (4*repeatBits (v+1) 1 (CarryCode.rightFile rest 6)+2)
noncomputable def time (pre v rest : V) : V :=
  2*CarryCode.cost pre+2*CarryCode.cost rest+2*v+11

def inputGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y pre v rest. ∃ rt k, !CarryCode.rightGraph rt rest 0 ∧
    !repeatGraph k v 1 rt ∧ !CarryCode.rightGraph y pre (4*k)”
def outputGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y pre v rest. ∃ rt k, !CarryCode.rightGraph rt rest 6 ∧
    !repeatGraph k (v+1) 1 rt ∧ !CarryCode.rightGraph y pre (4*k+2)”
def timeGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “y pre v rest. ∃ a b, !CarryCode.costGraph a pre ∧ !CarryCode.costGraph b rest ∧
    y=2*a+2*b+2*v+11”
instance input_defined : 𝚺ᴬ₁-Function₃ (input : V → V → V → V) via inputGraph :=
  .mk fun b => by simp [inputGraph,CarryCode.right_defined.df,repeat_defined.df,input]
instance output_defined : 𝚺ᴬ₁-Function₃ (output : V → V → V → V) via outputGraph :=
  .mk fun b => by simp [outputGraph,CarryCode.right_defined.df,repeat_defined.df,output,numeral_eq_natCast]
instance time_defined : 𝚺ᴬ₁-Function₃ (time : V → V → V → V) via timeGraph :=
  .mk fun b => by simp [timeGraph,CarryCode.cost_defined.df,time,numeral_eq_natCast]
end Coding

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

/-- Exact append-one increment with a decomposed prefix, selected value and suffix.
Both files may have nonstandard model length. The final endpoint is left-headed. -/
theorem segment (pre v rest l : V) : ∃ qs ls rs,
    Segment (time pre v rest) qs ls rs 64 l (input pre v rest)
      40 (l/2) ((1+1)*output pre v rest+l%2) := by
  let lp := ReturnCode.leftFile pre l
  let lc := repeatBits v 1 (4*lp+1)
  let lm := CarryCode.leftFile rest lc
  let li := repeatBits (v+1) 1 (4*lp+1)
  obtain ⟨qa,la,ra,ha⟩ := ForwardFile.segment pre l (4*repeatBits v 1 (CarryCode.rightFile rest 0))
  obtain ⟨qb,lb,rb,hb⟩ := SelectedCell.segment v lp (CarryCode.rightFile rest 0)
  obtain ⟨qc,lcq,rc,hc⟩ := CarryFile.segment rest lc (0 : V)
  obtain ⟨qd,ld,rd,hd⟩ := IncrementTail.segment lm
  obtain ⟨qe,le,re,he⟩ := ReturnFile.segment rest li (6 : V)
  have hn : ReturnCode.leftFile rest li=(1+1)*lm+1 := by
    dsimp [li,lm,lc]
    rw [repeat_succ]
    exact CarryReturn.relation rest (repeatBits v 1 (4*lp+1))
  unfold Phase at he
  rw [hn] at he
  have hdiv : ((1+1)*lm+1)/2=lm := by simpa using LeftPhase.bit_div true lm
  have hmod : ((1+1)*lm+1)%2=1 := by simpa using LeftPhase.bit_mod true lm
  rw [hdiv,hmod] at he
  have hthirteen : (1+1)*(6 : V)+1=13 := by ring1
  rw [hthirteen] at he
  obtain ⟨qf,lf,rf,hf⟩ := ReturnCell.segment (v+1) lp (CarryCode.rightFile rest 6)
  obtain ⟨qg,lg,rg,hg⟩ := ReturnFile.segment pre l
    (4*repeatBits (v+1) 1 (CarryCode.rightFile rest 6)+2)
  obtain ⟨q1,l1,r1,h1⟩ := segment_compose ha hb
  obtain ⟨q2,l2,r2,h2⟩ := segment_compose h1 hc
  obtain ⟨q3,l3,r3,h3⟩ := segment_compose h2 hd
  obtain ⟨q4,l4,r4,h4⟩ := segment_compose h3 he
  obtain ⟨q5,l5,r5,h5⟩ := segment_compose h4 hf
  obtain ⟨q6,l6,r6,h6⟩ := segment_compose h5 hg
  have ht : CarryCode.cost pre+(v+2)+CarryCode.cost rest+6+
      CarryCode.cost rest+((v+1)+2)+CarryCode.cost pre=time pre v rest := by
    unfold time
    ring1
  exact ⟨q6,l6,r6,by simpa only [ht,input,output] using h6⟩
end Models

def sentence : ArithmeticSentence :=
  “∀ pre v rest l, ∃ i o c a b, !inputGraph i pre v rest ∧
    !outputGraph o pre v rest ∧ !timeGraph c pre v rest ∧
    !divDef a l 2 ∧ !remDef b l 2 ∧
    ∃ qs ls rs, !segmentFormula c qs ls rs 64 l i 40 a ((1+1)*o+b)”
theorem pa_proves_append_one_increment : theory ⊢ sentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [sentence,models_iff]
  simp [input_defined.df,output_defined.df,time_defined.df,div_defined.df,rem_defined.df,
    segment_correct,numeral_eq_natCast]
  exact segment

#print axioms segment
#print axioms pa_proves_append_one_increment
end M6.Arithmetic.PA.InternalTrace.Increment

