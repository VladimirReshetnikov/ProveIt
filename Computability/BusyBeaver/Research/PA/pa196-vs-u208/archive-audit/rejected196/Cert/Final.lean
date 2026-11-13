import Cert.Before
import Cert.Batch0
import Cert.Batch1
import Cert.Batch2
import Cert.Batch3
import Cert.Batch4
import Cert.Batch5
import Cert.Batch6
import Cert.Batch7
import Cert.Batch8
import Cert.Batch9
import Cert.Batch10
import Cert.Batch11
import Cert.Batch12
import Cert.Batch13
import Cert.Batch14
import Cert.Batch15
import Cert.Batch16
import Cert.Batch17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RejectAudit
attribute [local irreducible] safeRun

theorem safe_compose {n m : Nat} {a b c : Conf}
    (h : safeRun n a = some b) (k : safeRun m b = some c) :
    safeRun (n+m) a = some c := by
  rw [safe_run_add, h]
  exact k

theorem certified_trace : safeRun 43563 (0,0,0) = some (196,9,4666729603487156070353191189271344578560) := by
  exact (safe_compose seg0 (safe_compose seg1 (safe_compose seg2 (safe_compose seg3 (safe_compose seg4 (safe_compose seg5 (safe_compose seg6 (safe_compose seg7 (safe_compose seg8 (safe_compose seg9 (safe_compose seg10 (safe_compose seg11 (safe_compose seg12 (safe_compose seg13 (safe_compose seg14 (safe_compose seg15 (safe_compose seg16 (safe_compose seg17 (safe_compose seg18 (safe_compose seg19 (safe_compose seg20 (safe_compose seg21 (safe_compose seg22 (safe_compose seg23 (safe_compose seg24 (safe_compose seg25 (safe_compose seg26 (safe_compose seg27 (safe_compose seg28 (safe_compose seg29 (safe_compose seg30 (safe_compose seg31 (safe_compose seg32 (safe_compose seg33 (safe_compose seg34 (safe_compose seg35 (safe_compose seg36 (safe_compose seg37 (safe_compose seg38 (safe_compose seg39 (safe_compose seg40 (safe_compose seg41 (safe_compose seg42 (safe_compose seg43 (safe_compose seg44 (safe_compose seg45 (safe_compose seg46 (safe_compose seg47 (safe_compose seg48 (safe_compose seg49 (safe_compose seg50 (safe_compose seg51 (safe_compose seg52 (safe_compose seg53 (safe_compose seg54 (safe_compose seg55 (safe_compose seg56 (safe_compose seg57 (safe_compose seg58 (safe_compose seg59 (safe_compose seg60 (safe_compose seg61 (safe_compose seg62 (safe_compose seg63 (safe_compose seg64 (safe_compose seg65 (safe_compose seg66 (safe_compose seg67 (safe_compose seg68 (safe_compose seg69 (safe_compose seg70 (safe_compose seg71 (safe_compose seg72 (safe_compose seg73 (safe_compose seg74 (safe_compose seg75 (safe_compose seg76 (safe_compose seg77 (safe_compose seg78 (safe_compose seg79 (safe_compose seg80 (safe_compose seg81 (safe_compose seg82 (safe_compose seg83 (safe_compose seg84 (safe_compose seg85 (safe_compose seg86 (safe_compose seg87 (safe_compose seg88 (safe_compose seg89 (safe_compose seg90 (safe_compose seg91 (safe_compose seg92 (safe_compose seg93 (safe_compose seg94 (safe_compose seg95 (safe_compose seg96 (safe_compose seg97 (safe_compose seg98 (safe_compose seg99 (safe_compose seg100 (safe_compose seg101 (safe_compose seg102 (safe_compose seg103 (safe_compose seg104 (safe_compose seg105 (safe_compose seg106 (safe_compose seg107 (safe_compose seg108 (safe_compose seg109 (safe_compose seg110 (safe_compose seg111 (safe_compose seg112 (safe_compose seg113 (safe_compose seg114 (safe_compose seg115 (safe_compose seg116 (safe_compose seg117 (safe_compose seg118 (safe_compose seg119 (safe_compose seg120 (safe_compose seg121 (safe_compose seg122 (safe_compose seg123 (safe_compose seg124 (safe_compose seg125 (safe_compose seg126 (safe_compose seg127 (safe_compose seg128 (safe_compose seg129 (safe_compose seg130 (safe_compose seg131 (safe_compose seg132 (safe_compose seg133 (safe_compose seg134 (safe_compose seg135 (safe_compose seg136 (safe_compose seg137 (safe_compose seg138 (safe_compose seg139 (safe_compose seg140 (safe_compose seg141 (safe_compose seg142 (safe_compose seg143 (safe_compose seg144 (safe_compose seg145 (safe_compose seg146 (safe_compose seg147 (safe_compose seg148 (safe_compose seg149 (safe_compose seg150 (safe_compose seg151 (safe_compose seg152 (safe_compose seg153 (safe_compose seg154 (safe_compose seg155 (safe_compose seg156 (safe_compose seg157 (safe_compose seg158 (safe_compose seg159 (safe_compose seg160 (safe_compose seg161 (safe_compose seg162 (safe_compose seg163 (safe_compose seg164 (safe_compose seg165 (safe_compose seg166 (safe_compose seg167 (safe_compose seg168 (safe_compose seg169 seg170))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem certified_before : safeRun 43562 (0,0,0) = some (63,4,9333459206974312140706382378542689157121) := by
  exact (safe_compose seg0 (safe_compose seg1 (safe_compose seg2 (safe_compose seg3 (safe_compose seg4 (safe_compose seg5 (safe_compose seg6 (safe_compose seg7 (safe_compose seg8 (safe_compose seg9 (safe_compose seg10 (safe_compose seg11 (safe_compose seg12 (safe_compose seg13 (safe_compose seg14 (safe_compose seg15 (safe_compose seg16 (safe_compose seg17 (safe_compose seg18 (safe_compose seg19 (safe_compose seg20 (safe_compose seg21 (safe_compose seg22 (safe_compose seg23 (safe_compose seg24 (safe_compose seg25 (safe_compose seg26 (safe_compose seg27 (safe_compose seg28 (safe_compose seg29 (safe_compose seg30 (safe_compose seg31 (safe_compose seg32 (safe_compose seg33 (safe_compose seg34 (safe_compose seg35 (safe_compose seg36 (safe_compose seg37 (safe_compose seg38 (safe_compose seg39 (safe_compose seg40 (safe_compose seg41 (safe_compose seg42 (safe_compose seg43 (safe_compose seg44 (safe_compose seg45 (safe_compose seg46 (safe_compose seg47 (safe_compose seg48 (safe_compose seg49 (safe_compose seg50 (safe_compose seg51 (safe_compose seg52 (safe_compose seg53 (safe_compose seg54 (safe_compose seg55 (safe_compose seg56 (safe_compose seg57 (safe_compose seg58 (safe_compose seg59 (safe_compose seg60 (safe_compose seg61 (safe_compose seg62 (safe_compose seg63 (safe_compose seg64 (safe_compose seg65 (safe_compose seg66 (safe_compose seg67 (safe_compose seg68 (safe_compose seg69 (safe_compose seg70 (safe_compose seg71 (safe_compose seg72 (safe_compose seg73 (safe_compose seg74 (safe_compose seg75 (safe_compose seg76 (safe_compose seg77 (safe_compose seg78 (safe_compose seg79 (safe_compose seg80 (safe_compose seg81 (safe_compose seg82 (safe_compose seg83 (safe_compose seg84 (safe_compose seg85 (safe_compose seg86 (safe_compose seg87 (safe_compose seg88 (safe_compose seg89 (safe_compose seg90 (safe_compose seg91 (safe_compose seg92 (safe_compose seg93 (safe_compose seg94 (safe_compose seg95 (safe_compose seg96 (safe_compose seg97 (safe_compose seg98 (safe_compose seg99 (safe_compose seg100 (safe_compose seg101 (safe_compose seg102 (safe_compose seg103 (safe_compose seg104 (safe_compose seg105 (safe_compose seg106 (safe_compose seg107 (safe_compose seg108 (safe_compose seg109 (safe_compose seg110 (safe_compose seg111 (safe_compose seg112 (safe_compose seg113 (safe_compose seg114 (safe_compose seg115 (safe_compose seg116 (safe_compose seg117 (safe_compose seg118 (safe_compose seg119 (safe_compose seg120 (safe_compose seg121 (safe_compose seg122 (safe_compose seg123 (safe_compose seg124 (safe_compose seg125 (safe_compose seg126 (safe_compose seg127 (safe_compose seg128 (safe_compose seg129 (safe_compose seg130 (safe_compose seg131 (safe_compose seg132 (safe_compose seg133 (safe_compose seg134 (safe_compose seg135 (safe_compose seg136 (safe_compose seg137 (safe_compose seg138 (safe_compose seg139 (safe_compose seg140 (safe_compose seg141 (safe_compose seg142 (safe_compose seg143 (safe_compose seg144 (safe_compose seg145 (safe_compose seg146 (safe_compose seg147 (safe_compose seg148 (safe_compose seg149 (safe_compose seg150 (safe_compose seg151 (safe_compose seg152 (safe_compose seg153 (safe_compose seg154 (safe_compose seg155 (safe_compose seg156 (safe_compose seg157 (safe_compose seg158 (safe_compose seg159 (safe_compose seg160 (safe_compose seg161 (safe_compose seg162 (safe_compose seg163 (safe_compose seg164 (safe_compose seg165 (safe_compose seg166 (safe_compose seg167 (safe_compose seg168 (safe_compose seg169 beforeLast))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem rejected_shift_reaches_halt : (run false 43563 (0,0,0)).1 = 196 := by
  have h := (safe_run_sound 43563 (0,0,0) _ certified_trace).1
  exact congrArg Prod.fst h

theorem rejected_combined_reaches_halt : (run true 43563 (0,0,0)).1 = 196 := by
  have h := (safe_run_sound 43563 (0,0,0) _ certified_trace).2
  exact congrArg Prod.fst h


theorem before_not_halted (variant : Bool) :
    (run variant 43562 (0,0,0)).1 = 63 := by
  cases variant with
  | false => exact congrArg Prod.fst (safe_run_sound 43562 (0,0,0) _ certified_before).1
  | true => exact congrArg Prod.fst (safe_run_sound 43562 (0,0,0) _ certified_before).2

theorem run_add (variant : Bool) (n m : Nat) (c : Conf) :
    run variant (n+m) c = run variant m (run variant n c) := by
  induction n generalizing c with
  | zero => simp [run]
  | succ n ih => simp only [Nat.succ_add,run]; exact ih _

theorem run_halted (variant : Bool) (n : Nat) (c : Conf) (h : c.1 = 196) :
    run variant n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    have hs : step variant c = c := by
      rcases c with ⟨q,l,r⟩
      simp [step] at h ⊢
      simp [h]
    rw [hs]
    exact ih

theorem not_halted_before (variant : Bool) (n : Nat) (hn : n < 43563) :
    (run variant n (0,0,0)).1 ≠ 196 := by
  intro h
  have hp : n + (43562-n) = 43562 := by omega
  have hs := run_halted variant (43562-n) (run variant n (0,0,0)) h
  have he : (run variant 43562 (0,0,0)).1 = 196 := by
    rw [← hp, run_add, hs]
    exact h
  have hn63 := before_not_halted variant
  omega

#print axioms certified_trace
#print axioms rejected_shift_reaches_halt
#print axioms rejected_combined_reaches_halt
#print axioms not_halted_before
end RejectAudit
