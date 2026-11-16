module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualCompilerBlueprint
public import M6PA.Scheduler.ActualAtomCompilerCorrect
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.ActualCompilerStandard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ActualWordCoding ActualCompilerRows ActualCompilerBlueprint ActualCompilerRuleExpression
open SourceCantorInternal NativeCalculus.ActualBasis.Code

theorem encodeRows_concat (rows : List (List Nat)) (word : List Nat) :
    encodeRows (rows++[word])=concat (encodeRows rows) (encode word) := by
  simp [encodeRows,List.map_append,encode_concat]

theorem encodeRows_replicate (n : Nat) : encodeRows (List.replicate n [])=repeatVec 0 n := by
  induction n with
  | zero => simp [encodeRows]
  | succ n ih => simpa [encodeRows,List.replicate_succ] using congrArg (fun xs : Nat => 0 ∷ xs) ih

theorem rows_standard (n : Nat) (xs : List (List Nat)) :
    rows n (encodeRows xs)=encodeRows ((List.range n).map fun i =>
      ruleCompileAtoms (fun k => xs.getD k []) (M6.Source.Cantor.decode i).1 (M6.Source.Cantor.decode i).2) := by
  induction n with
  | zero => simp [encodeRows]
  | succ n ih =>
    rw [rows_succ,ih]
    have hl := congrArg Prod.fst (decode_standard n)
    have hr := congrArg Prod.snd (decode_standard n)
    simp only [Prod.fst,Prod.snd] at hl hr
    rw [ruleValue,hl,hr,rule_standard]
    simp [List.range_succ,List.map_append,encodeRows_concat]

theorem table_standard (fuel bound : Nat) :
    tableValue fuel bound=encodeRows (compilerAtomTable bound fuel) := by
  induction fuel with
  | zero => simp [compilerAtomTable,encodeRows_replicate]
  | succ fuel ih => rw [table_succ,ih,rows_standard]; rfl

theorem compiled_standard (code : Nat) : compiledValue code=encode (compiledAtoms code) := by
  unfold compiledValue
  rw [table_standard,nth_encodeRows]
  simp [compiledAtoms,decodeLeft,decodeRight,decodeState_standard]

theorem compiledGraph_standard (z code : Nat) :
    compiledGraph.val.Evalb ![z,code] ↔ z=encode (compiledAtoms code) := by
  rw [compiled_graph,compiled_standard]

/-- Exact agreement with the executable compiler; this calibration is Nat-only,
while the graph construction itself works in every I-Sigma-1 model. -/
theorem compiled_word (code : Nat) :
    compiledValue code=encode (M6.Source.CommandAtomEncoding.atoms (compileCertificate code)) := by
  rw [compiled_standard,compiledAtoms_eq]

#print axioms rows_standard
#print axioms table_standard
#print axioms compiled_word
end M6.PA.ActualCompilerStandard

