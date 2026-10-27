import BusyBeaver.ZFC.ArithmeticDagRootPerm222
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace SetTheory.BusyBeaver.ZFC.ArithmeticDagRootPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticDagMacrosPerm222 ArithmeticDagRootPerm222 ArithmeticCantor RMDag
open DiophantineConsistency.ArithmeticCommandStepPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (st : AS V) : IR (.node 123) (enc {st with s1:=0,p2:=0}) .normal
    (enc {st with s1:=0,p2:=0}) := ifeq_eq _ rfl
example (st : AS V) : IR (.node 123) (enc {st with s1:=0,p2:=1}) (.brk 1)
    (enc {st with s1:=0,p2:=0}) := ifeq_ne _ (by simp)
example (st : AS V) : IR (.node 123) (enc {st with s1:=1,p2:=0}) (.brk 1)
    (enc {st with s1:=0,p2:=0}) := ifeq_ne _ (by simp)

example (np t S d pl : V) :
    ∃y, IR (.node 141) (enc (⟨np,t,S,0,d,1,0,0,pl⟩ : AS V)) .halt y :=
  dispatch_nip_halt _ ⟨rfl,rfl⟩ rfl rfl

example (np t S pl : V) :
    f236 (⟨np,t,S,0,0,0,0,0,pl⟩ : AS V)=
      ⟨np,gateValue (first (second pl)) (first pl) 0,
        axStackValue (first (second pl)) 0 (first pl) 0 0 t S,0,0,0,0,0,second (second pl)⟩ := by
  simpa using ax_eval np t S 0 0 0 pl

example (pl np t S d h : V) :
    ArithmeticControlFile.regValue (enc (boundary pl np t S d h)) 6=np := reg_enc _ 6
example (pl np t S d h : V) :
    ArithmeticControlFile.regValue (enc (boundary pl np t S d h)) 3=d := reg_enc _ 3
example (pl np t S d h : V) :
    ArithmeticControlFile.regValue (enc (boundary pl np t S d h)) 7=h := reg_enc _ 7

/-- The real candidate4 and all-zero initial working state need no root-run premise. -/
example :
    (DiophantineConsistency.ArithmeticEnumStepPerm222.enumValue
      (DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue (0:V) 4 (stateValue 0 0 0 0))=0 ∧
      ∃y,IR (.node 0) (enc (boundary (0:V) 4 0 0 0 0)) .halt y) ∨
    ∃pl' np' t' S' d' h',
      DiophantineConsistency.ArithmeticEnumStepPerm222.enumValue
        (DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue (0:V) 4 (stateValue 0 0 0 0))=
        DiophantineConsistency.ArithmeticEnumStepPerm222.liveValue pl' np' (stateValue t' S' d' h') ∧
      Rn (.node 0) (boundary (0:V) 4 0 0 0 0) (boundary pl' np' t' S' d' h') ∧
      (pl'<0 ∨ np'=4+1) := root_step 0 4 0 0 0 0

#print axioms cancel463
#print axioms eqR
#print axioms ifeq_eq
#print axioms ifeq_ne
#print axioms nip_halt
#print axioms l457
#print axioms axWord_checked
#print axioms ax_eval
#print axioms l236
#print axioms dispatch_ax
#print axioms command_step
#print axioms fetch_run
#print axioms root_step
end SetTheory.BusyBeaver.ZFC.ArithmeticDagRootPerm222Checks
