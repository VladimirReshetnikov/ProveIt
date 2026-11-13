module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCheckerBlueprint
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCheckerStandard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ActualTableCoding ActualCheckerRows ActualCheckerBlueprint ActualRuleExpression SourceCantorInternal
open NativeCalculus.ActualBasis.Code

@[simp] theorem encodeTable_nil : encodeTable []=0 := rfl
@[simp] theorem encodeTable_cons (x : Option Nat) (xs : List (Option Nat)) :
    encodeTable (x::xs)=optionCode x ∷ encodeTable xs := rfl

theorem encodeTable_concat (xs : List (Option Nat)) (x : Option Nat) :
    encodeTable (xs++[x]) = concat (encodeTable xs) (optionCode x) := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp [ih]

theorem encodeTable_replicate (n : Nat) :
    encodeTable (List.replicate n none)=repeatVec 0 n := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,ih,optionCode]

theorem rows_standard (n : Nat) (xs : List (Option Nat)) :
    rows n (encodeTable xs) = encodeTable ((List.range n).map fun i =>
      ruleCheck (fun k => xs.getD k none) (M6.Source.Cantor.decode i).1 (M6.Source.Cantor.decode i).2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [rows_succ,ih]
    have hl := congrArg Prod.fst (decode_standard n)
    have hr := congrArg Prod.snd (decode_standard n)
    simp only [Prod.fst,Prod.snd] at hl hr
    rw [ruleValue,hl,hr,rule_standard]
    simp [List.range_succ,List.map_append,encodeTable_concat]

theorem table_standard (fuel bound : Nat) :
    tableValue fuel bound = encodeTable (table bound fuel) := by
  induction fuel with
  | zero => simp [table,encodeTable_replicate]
  | succ fuel ih => rw [table_succ,ih,rows_standard]; rfl

theorem verify_standard (code : Nat) : verifyValue code=optionCode (verify code) := by
  unfold verifyValue
  rw [table_standard,nth_encoded_table _ _ _ (by rfl)]
  have hl := congrArg Prod.fst (decode_standard code)
  have hr := congrArg Prod.snd (decode_standard code)
  simp only [Prod.fst,Prod.snd] at hl hr
  rw [hl,hr]
  rfl

theorem verifyGraph_standard (z code : Nat) :
    verifyGraph.val.Evalb ![z,code] ↔ z=optionCode (verify code) := by
  rw [verify_graph,verify_standard]

#print axioms rows_standard
#print axioms table_standard
#print axioms verifyGraph_standard
end M6.PA.ActualCheckerStandard

