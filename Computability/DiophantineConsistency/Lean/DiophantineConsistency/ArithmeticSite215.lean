import DiophantineConsistency.ArithmeticHome215
import BusyBeaver.ZFC.KSites215

/-! Every actual 215 source site executes on arbitrary internal data. The
closed finite checker certificate supplies all source checks; the arithmetic
Home executor supplies their clocks. No ordinary-Nat simulation is used. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticSite215
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath
open KRuntimeCore (BoxSt Branch SConf Seg)
open ArithmeticMachineTape215 ArithmeticRegisterBoxes215 ArithmeticSymbolicCore215
open ArithmeticCantor (first second first_cantor second_cantor)

private theorem physical_table : ∀ r : Fin 9, KSim.physOf r.val<9 := by decide +kernel
theorem physical_lt (r : Nat) (hr : r<9) : KSim.physOf r<9 := physical_table ⟨r,hr⟩

/-- Actual source membership supplies the closed certificate, not a runtime premise. -/
theorem source_checked {Q : List Bool} {e : Edge} (h : SiteCoverage.LeafAt KSource215.t215 Q e) :
    KSim.checkEdge KTableCore.tm215 Q e=true := by
  simpa only [List.reverse_nil,List.nil_append] using
    SiteCoverage.allSites_sound _ h [] KSites215.all_sites
theorem source_length {Q : List Bool} {e : Edge} (h : SiteCoverage.LeafAt KSource215.t215 Q e) :
    Q.length≤48 := KSim.checkEdge_length (source_checked h)
theorem source_not_node {Q : List Bool} {r : Nat} :
    ¬ SiteCoverage.LeafAt KSource215.t215 Q (.node r) := by
  intro h
  have hh := source_checked h
  simp only [KSim.checkEdge,Bool.false_eq_true] at hh

theorem checked_inc {Q : List Bool} {r : Nat}
    (h : KSim.checkEdge KTableCore.tm215 Q (.inc r)=true) :
    Q.length≤48 ∧ r<9 ∧ KSim.runTo KTableCore.tm215 none Q
      (KSim.tgtConf (incPath Q) (KSim.allOnes Q) (.plain (.inc (KSim.physOf r))))=true := by
  simpa only [KSim.checkEdge,Bool.and_eq_true_iff,decide_eq_true_eq,and_assoc] using h
theorem checked_decnz {Q : List Bool} {r : Nat}
    (h : KSim.checkEdge KTableCore.tm215 Q (.decnz r)=true) :
    Q.length≤48 ∧ r<9 ∧
      KSim.runTo KTableCore.tm215 (some (KSim.physOf r,true)) Q
        (KSim.tgtConf (breakPath 1 Q) (KSim.allOnes (stripPath false 1 Q)) (.plain .none))=true ∧
      KSim.runTo KTableCore.tm215 (some (KSim.physOf r,false)) Q
        (KSim.tgtConf (incPath Q) (KSim.allOnes Q) (.plain (.dec (KSim.physOf r))))=true := by
  simpa only [KSim.checkEdge,Bool.and_eq_true_iff,decide_eq_true_eq,and_assoc] using h

theorem source_inc_bounds {Q : List Bool} {r : Nat}
    (h : SiteCoverage.LeafAt KSource215.t215 Q (.inc r)) : r<9 ∧ KSim.physOf r<9 := by
  have hr := (checked_inc (source_checked h)).2.1
  exact ⟨hr,physical_lt r hr⟩
theorem source_decnz_bounds {Q : List Bool} {r : Nat}
    (h : SiteCoverage.LeafAt KSource215.t215 Q (.decnz r)) : r<9 ∧ KSim.physOf r<9 := by
  have hr := (checked_decnz (source_checked h)).2.1
  exact ⟨hr,physical_lt r hr⟩

section Internal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def startValue (gap : V) (v : Fin 9 → V) (k : V) (Q : List Bool) : V :=
  interpret gap v k (KSim.start Q)
noncomputable def targetValue (gap : V) (v : Fin 9 → V) (k : V)
    (P : List Bool) (overflow : Bool) (effect : BoxSt) : V :=
  interpret gap v k (KSim.tgtConf P overflow effect)

/-- Finite path bits applied to the complete arbitrary suffix. -/
noncomputable def pathValue : List Bool → V → V
  | [],z => z
  | b::P,z => 2*pathValue P z+digit b
theorem flat_path (gap : V) (v : Fin 9 → V) (k : V) (P : List Bool) (z : V) :
    flatValue gap v k (P.map Seg.bit) z=pathValue P z := by
  induction P with
  | nil => rfl
  | cons b P ih => simp only [List.map_cons,flatValue,segValue,pathValue,ih]

theorem start_format (gap : V) (v : Fin 9 → V) (k : V) (Q : List Bool) :
    startValue gap v k Q=frameSparse 84 1
      (pathValue Q (bitPrefix false (gap+((64-Q.length:Nat):V)) (2*plain v k+1))) := by
  simp only [startValue,KSim.start,KSim.D0,interpret,ArithmeticHome215.flatValue_append,
    flat_path,flatValue,segValue,one_mul,Nat.cast_one,digit_true,mul_zero,zero_add,
    boxTail,plainTail_zero]

theorem target_format (gap : V) (v : Fin 9 → V) (k : V)
    (P : List Bool) (overflow : Bool) (effect : BoxSt) :
    targetValue gap v k P overflow effect=frameSparse 84 1
      (pathValue P (bitPrefix false
        (gap+((64+(if overflow then 1 else 0)+KSim.growth effect-P.length:Nat):V))
        (2*boxValue v k effect+1))) := by
  simp only [targetValue,KSim.tgtConf,KSim.D0,interpret,ArithmeticHome215.flatValue_append,
    flat_path,flatValue,segValue,one_mul,Nat.cast_one,digit_true,mul_zero,zero_add,boxValue]

theorem increment_target (gap : V) (v : Fin 9 → V) (k : V) (r : Fin 9)
    (P : List Bool) (overflow : Bool) :
    targetValue gap v k P overflow (.plain (.inc r.val))=
      targetValue gap (Function.update v r (v r+1)) (k+1) P overflow (.plain .none) := by
  rw [target_format,target_format,box_incremented,box_plain]
  rfl

/-- Positive DEC keeps its extra distance cell and does not append a spare. -/
theorem decrement_target (gap : V) (v : Fin 9 → V) (k : V) (r : Fin 9)
    (P : List Bool) (overflow : Bool) :
    targetValue gap v k P overflow (.plain (.dec r.val))=frameSparse 84 1
      (pathValue P (bitPrefix false
        (gap+((64+(if overflow then 1 else 0)+1-P.length:Nat):V))
        (2*plain (Function.update v r (v r-1)) k+1))) := by
  rw [target_format,box_decremented]
  rfl

theorem runTo_actual (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {br : Branch} (hv : BranchValid br v) {Q : List Bool} {target : SConf}
    (h : KSim.runTo KTableCore.tm215 br Q target=true) :
    ReachPos (startValue gap v k Q) (interpret gap v k target) := by
  unfold KSim.runTo at h
  cases he : KHomeReady.exec KTableCore.tm215 br (fun s => KRuntimeCore.sMatches s target)
      KSim.FUEL (KSim.start Q) false with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at h
  | some s => exact ArithmeticHome215.exec_matches_actual gap v k hk hv he

theorem halt_interpret (gap : V) (v : Fin 9 → V) (k : V) {s : SConf}
    (h : KSim.isHalt s=true) : first (interpret gap v k s)=0 := by
  obtain ⟨q,onl,l,r⟩ := s
  simp only [KSim.isHalt,beq_iff_eq] at h
  subst q
  cases onl <;> simp only [interpret,leftFrame,frameSparse,first_cantor,
    sparseCode_terminal,Nat.cast_zero]

theorem runHalt_actual (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} (h : KSim.runHalt KTableCore.tm215 Q=true) :
    ∃ clock : V, 0<clock ∧ first (runFrom clock (startValue gap v k Q))=0 := by
  unfold KSim.runHalt at h
  cases he : KHomeReady.exec KTableCore.tm215 none KSim.isHalt KSim.FUEL (KSim.start Q) false with
  | none => simp only [he,Option.isSome_none,Bool.false_eq_true] at h
  | some s =>
    obtain ⟨hh,clock,hc,hr⟩ := ArithmeticHome215.exec_actual gap v k hk (br:=none) trivial he
    refine ⟨clock,hc,?_⟩
    rw [startValue,hr]
    exact halt_interpret gap v k hh

theorem source_inc (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {r : Nat} (h : SiteCoverage.LeafAt KSource215.t215 Q (.inc r)) :
    ReachPos (startValue gap v k Q)
      (targetValue gap v k (incPath Q) (KSim.allOnes Q) (.plain (.inc (KSim.physOf r)))) :=
  runTo_actual gap v k hk (br:=none) trivial (checked_inc (source_checked h)).2.2

theorem source_decnz_zero (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {r : Nat} (h : SiteCoverage.LeafAt KSource215.t215 Q (.decnz r))
    (hz : getValue v (KSim.physOf r)=0) :
    ReachPos (startValue gap v k Q)
      (targetValue gap v k (breakPath 1 Q) (KSim.allOnes (stripPath false 1 Q)) (.plain .none)) :=
  runTo_actual gap v k hk (br:=some (KSim.physOf r,true)) hz (checked_decnz (source_checked h)).2.2.1

theorem source_decnz_positive (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {r : Nat} (h : SiteCoverage.LeafAt KSource215.t215 Q (.decnz r))
    (hn : getValue v (KSim.physOf r)≠0) :
    ReachPos (startValue gap v k Q)
      (targetValue gap v k (incPath Q) (KSim.allOnes Q) (.plain (.dec (KSim.physOf r)))) :=
  runTo_actual gap v k hk (br:=some (KSim.physOf r,false)) hn (checked_decnz (source_checked h)).2.2.2

theorem source_break (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {j : Nat} (h : SiteCoverage.LeafAt KSource215.t215 Q (.brk j)) :
    ReachPos (startValue gap v k Q)
      (targetValue gap v k (breakPath j Q) (KSim.allOnes (stripPath false j Q)) (.plain .none)) := by
  have hc := source_checked h
  simp only [KSim.checkEdge,Bool.and_eq_true_iff,decide_eq_true_eq] at hc
  exact runTo_actual gap v k hk (br:=none) trivial hc.2

theorem source_continue (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} {j : Nat} (h : SiteCoverage.LeafAt KSource215.t215 Q (.cont j)) :
    ReachPos (startValue gap v k Q)
      (targetValue gap v k (continuePath j Q) false (.plain .none)) := by
  have hc := source_checked h
  simp only [KSim.checkEdge,Bool.and_eq_true_iff,decide_eq_true_eq] at hc
  exact runTo_actual gap v k hk (br:=none) trivial hc.2

theorem source_halt (gap : V) (v : Fin 9 → V) (k : V) (hk : 0<k)
    {Q : List Bool} (h : SiteCoverage.LeafAt KSource215.t215 Q .halt) :
    ∃ clock : V, 0<clock ∧ first (runFrom clock (startValue gap v k Q))=0 := by
  have hc := source_checked h
  simp only [KSim.checkEdge,Bool.and_eq_true_iff,decide_eq_true_eq] at hc
  exact runHalt_actual gap v k hk hc.2

end Internal
end DiophantineConsistency.ArithmeticSite215
