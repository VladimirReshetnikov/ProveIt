module
public import M6PA.Model.PATheory
public import M6PA.Model.PAInternalFileGraphs
public import M6PA.Model.PAInternalFileGuards
@[expose] public section
namespace M6.Arithmetic.PA.InternalTrace.FileBoxes
open M6 M6.Arithmetic.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ScanBits FileLayout M6.Runtime Symbolic

def wordGraph : List Seg → 𝚺ᴬ₁.Semisentence 4
  | [] => .mkSigma “y n xs t. y=t”
  | .bit b::ss => .mkSigma “y n xs t. ∃ z, !(wordGraph ss) z n xs t ∧ y=(1+1)*z+↑(b.toNat)”
  | .run b a c::ss => .mkSigma “y n xs t. ∃ z, !(wordGraph ss) z n xs t ∧
      !repeatGraph y (↑a*n+↑c) ↑(b.toNat) z”
  | .box x::ss => .mkSigma “y n xs t. ∃ z, !(wordGraph ss) z n xs t ∧ !(boxGraph x) y xs z”

def configGraph : SConf → 𝚺ᴬ₁.Semisentence 5
  | (q,false,l,r) => .mkSigma “sq sl sr n xs. sq=↑(NativeRows.code q) ∧
      !(wordGraph l) sl n xs 0 ∧ !(wordGraph r) sr n xs 0”
  | (q,true,l,r) => .mkSigma “sq sl sr n xs. sq=↑(NativeRows.code q) ∧
      ∃ a b c, !(wordGraph l) a n xs 0 ∧ !(wordGraph r) b n xs 0 ∧
      !divDef sl a 2 ∧ !remDef c a 2 ∧ sr=(1+1)*b+c”

def guardGraph : Branch → 𝚺ᴬ₁.Semisentence 1
  | none => .mkSigma “xs. ⊤”
  | some (r,true) => .mkSigma “xs. !(valueGraph r) 0 xs”
  | some (r,false) => .mkSigma “xs. ∃ v, !(valueGraph r) v xs ∧ v≠0”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
instance word_defined (s : List Seg) : 𝚺ᴬ₁-Function₃
    (fun n xs t : V => word n (box xs) s t) via wordGraph s := by
  induction s with
  | nil => exact .mk fun v => by simp [wordGraph,word]
  | cons x ss ih =>
    cases x with
    | bit b => exact .mk fun v => by simp [wordGraph,ih.df,word,numeral_eq_natCast]
    | run b a c => exact .mk fun v => by simp [wordGraph,ih.df,repeat_defined.df,word,numeral_eq_natCast]
    | box x => exact .mk fun v => by simp [wordGraph,ih.df,(box_defined x).df,word]

lemma config_correct (s : SConf) (q l r n xs : V) :
    (V ⊧/![q,l,r,n,xs] (configGraph s).val) ↔
      q=(config n (box xs) denseControl s).q ∧
      l=(config n (box xs) denseControl s).left ∧
      r=(config n (box xs) denseControl s).right := by
  rcases s with ⟨sq,onl,sl,sr⟩
  cases onl <;> simp [configGraph,(word_defined sl).df,(word_defined sr).df,
    div_defined.df,rem_defined.df,config,denseControl,numeral_eq_natCast]

lemma guard_correct (br : Branch) (xs : V) :
    (V ⊧/![xs] (guardGraph br).val) ↔ Guard xs br := by
  cases br with
  | none => simp [guardGraph,Guard]
  | some p =>
    rcases p with ⟨r,z⟩
    cases z <;> simp [guardGraph,(value_defined r).df,Guard,eq_comm]
end Models
#print axioms word_defined
#print axioms config_correct
#print axioms guard_correct
end M6.Arithmetic.PA.InternalTrace.FileBoxes

