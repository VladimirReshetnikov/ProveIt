module
public import M6PA.Theory
public import M6PA.Model.PATheory
public import M6PA.Scheduler.ActualAtomCompiler
@[expose] public section
open M6.Arithmetic.PA
namespace M6.PA.NativeCalculus.ActualBasis.Code
open M6.Source M6.Source.Cantor M6.Source.Enumeration
open M6.Source.ActualCommandMacros M6.Source.CommandAtomEncoding

/-- Only the exact bounded child fields are queried; invalid payloads do not
create a hidden recursive dependency beyond the finite preceding table. -/
theorem ruleCompileAtoms_agrees (rec : Nat → List Nat) (words : Nat → List Command)
    (tag data : Nat) (hr : ∀ n,n≤data → rec n=atoms (words n)) :
    ruleCompileAtoms rec tag data=atoms (ruleCompile words tag data) := by
  by_cases ht : tag<11
  · have hcases : tag=0 ∨ tag=1 ∨ tag=2 ∨ tag=3 ∨ tag=4 ∨ tag=5 ∨
      tag=6 ∨ tag=7 ∨ tag=8 ∨ tag=9 ∨ tag=10 := by omega
    rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · cases hf : unpack3 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨b,p,q⟩
        have hb:=unpack3_bounds data b p q hf
        simp [ruleCompileAtoms,ruleCompile,hf,hr p hb.2.1,hr q hb.2.2,atoms,List.map_append]
    · cases hf : unpack2 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,p⟩
        have hb:=unpack2_bounds data a p hf
        simp [ruleCompileAtoms,ruleCompile,hf,hr p hb.2,atoms,List.map_append]
    · cases hf : unpack2 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b⟩
        simp [ruleCompileAtoms,ruleCompile,hf,atoms,apply_ite]
    · cases hf : unpack3 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b,c⟩
        simp [ruleCompileAtoms,ruleCompile,hf,atoms,apply_ite]
    · cases hf : unpack3 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b,c⟩
        simp [ruleCompileAtoms,ruleCompile,hf,atoms,apply_ite]
    · cases hf : unpack3 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b,c⟩
        simp [ruleCompileAtoms,ruleCompile,hf,atoms,apply_ite]
    · cases hf : unpack3 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b,c⟩
        simp [ruleCompileAtoms,ruleCompile,hf,atoms,apply_ite]
    · cases hf : unpack2 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b⟩
        simp [ruleCompileAtoms,ruleCompile,hf,atoms,apply_ite]
    · cases hf : unpack3 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b,c⟩
        simp [ruleCompileAtoms,ruleCompile,hf,atoms,apply_ite]
    · cases hf : unpack4 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b,c,u⟩
        by_cases hg : u≤a <;> simp [ruleCompileAtoms,ruleCompile,hf,atoms,hg]
    · cases hf : unpack3 data with
      | none => simp [ruleCompileAtoms,ruleCompile,hf,atoms]
      | some v =>
        rcases v with ⟨a,b,c⟩
        by_cases hg : c≠a ∧ c≠b <;> simp [ruleCompileAtoms,ruleCompile,hf,atoms,hg]
  · obtain ⟨n,rfl⟩ : ∃ n,tag=n+11 := ⟨tag-11,by omega⟩
    simp [ruleCompileAtoms,ruleCompile,atoms]

theorem compilerAtomTable_lookup (bound fuel n : Nat) (hn : n≤bound) :
    (compilerAtomTable bound fuel).getD n []=atoms (compileTree fuel n) := by
  induction fuel generalizing n with
  | zero => simp [compilerAtomTable,compileTree,atoms,List.getD,show n<bound+1 by omega]
  | succ fuel ih =>
    simp only [compilerAtomTable,List.getD,List.getElem?_map,
      List.getElem?_range (show n<bound+1 by omega),Option.map_some,Option.getD_some,compileTree]
    apply ruleCompileAtoms_agrees
    intro k hk
    exact ih k (Nat.le_trans hk (Nat.le_trans (decode_bounds n).2 hn))

theorem compiledAtoms_eq (code : Nat) : compiledAtoms code=atoms (compileCertificate code) :=
  compilerAtomTable_lookup _ _ _ (Nat.le_refl _)

#print axioms ruleCompileAtoms_agrees
#print axioms compilerAtomTable_lookup
#print axioms compiledAtoms_eq
end M6.PA.NativeCalculus.ActualBasis.Code

