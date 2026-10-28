import DiophantineConsistency.ArithmeticSite215

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticSite215Checks
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticSymbolicCore215 ArithmeticSite215
open ArithmeticCantor (first second cantor first_cantor second_cantor)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example : ∀ r : Fin 9, KSim.physOf r.val<9 := fun r => physical_lt r r.isLt
example {Q : List Bool} {e : Edge} (h : SiteCoverage.LeafAt KSource215.t215 Q e) :
    KSim.checkEdge KTableCore.tm215 Q e=true ∧ Q.length≤48 := ⟨source_checked h,source_length h⟩
example {Q : List Bool} {r : Nat} : ¬ SiteCoverage.LeafAt KSource215.t215 Q (.node r) := source_not_node
/-- The last logical selector uses physical slot1, without a fallback. -/
example : KSim.physOf 8=1 := rfl
private theorem first_leaf : SiteCoverage.LeafAt KSource215.t215
    [false,false,false] (.decnz 8) := .left (.left (.left (.here _)))
example (v : Fin 9 → V) (hz : v 1=0) :
    ReachPos (startValue 0 v 1 [false,false,false])
      (targetValue 0 v 1 (breakPath 1 [false,false,false])
        (KSim.allOnes (stripPath false 1 [false,false,false])) (.plain .none)) :=
  source_decnz_zero 0 v 1 (by simp) first_leaf (by simpa [getValue,KSim.physOf] using hz)
example (gap k : V) (v : Fin 9 → V) (hk : 0<k) {Q : List Bool} {r : Nat}
    (h : SiteCoverage.LeafAt KSource215.t215 Q (.inc r)) :
    ∃ clock : V, 0<clock ∧ runFrom clock (startValue gap v k Q)=
      targetValue gap v k (incPath Q) (KSim.allOnes Q) (.plain (.inc (KSim.physOf r))) :=
  source_inc gap v k hk h
/-- Zero gap and a single spare are permitted in both DEC branches. -/
example (v : Fin 9 → V) {Q : List Bool} {r : Nat}
    (h : SiteCoverage.LeafAt KSource215.t215 Q (.decnz r)) (hz : getValue v (KSim.physOf r)=0) :
    ReachPos (startValue 0 v 1 Q)
      (targetValue 0 v 1 (breakPath 1 Q) (KSim.allOnes (stripPath false 1 Q)) (.plain .none)) :=
  source_decnz_zero 0 v 1 (by simp) h hz
example (v : Fin 9 → V) {Q : List Bool} {r : Nat}
    (h : SiteCoverage.LeafAt KSource215.t215 Q (.decnz r)) (hn : getValue v (KSim.physOf r)≠0) :
    ReachPos (startValue 0 v 1 Q)
      (targetValue 0 v 1 (incPath Q) (KSim.allOnes Q) (.plain (.dec (KSim.physOf r)))) :=
  source_decnz_positive 0 v 1 (by simp) h hn
example (gap k : V) (v : Fin 9 → V) (hk : 0<k) {Q : List Bool}
    (h : SiteCoverage.LeafAt KSource215.t215 Q .halt) :
    ∃ clock : V, 0<clock ∧ first (runFrom clock (startValue gap v k Q))=0 := source_halt gap v k hk h
/-- Terminal state retains a nontrivial complete tape payload. -/
example (R : V) : first (frameSparse 230 1 R)=0 ∧ second (frameSparse 230 1 R)=cantor 1 R := by
  simp only [frameSparse,first_cantor,second_cantor,sparseCode_terminal,Nat.cast_zero,and_self]
example (gap k : V) (v : Fin 9 → V) (r : Fin 9) (P : List Bool) (ovf : Bool) :
    targetValue gap v k P ovf (.plain (.inc r.val))=
      targetValue gap (Function.update v r (v r+1)) (k+1) P ovf (.plain .none) := increment_target gap v k r P ovf
example (gap k : V) (v : Fin 9 → V) (r : Fin 9) (P : List Bool) (ovf : Bool) :
    targetValue gap v k P ovf (.plain (.dec r.val))=frameSparse 84 1
      (pathValue P (bitPrefix false (gap+((64+(if ovf then 1 else 0)+1-P.length:Nat):V))
        (2*plain (Function.update v r (v r-1)) k+1))) := decrement_target gap v k r P ovf

#print axioms physical_lt
#print axioms source_checked
#print axioms source_length
#print axioms source_not_node
#print axioms source_inc_bounds
#print axioms source_decnz_bounds
#print axioms start_format
#print axioms target_format
#print axioms increment_target
#print axioms decrement_target
#print axioms runTo_actual
#print axioms halt_interpret
#print axioms runHalt_actual
#print axioms source_inc
#print axioms source_decnz_zero
#print axioms source_decnz_positive
#print axioms source_break
#print axioms source_continue
#print axioms source_halt
end DiophantineConsistency.ArithmeticSite215Checks
