module
public import M6.Source.ActualHeadSelectors
@[expose] public section
namespace M6.Source.ActualCommandMacros
open Cantor Enumeration ActualAXCode
open AXCode (wim wal wn wex)

def headWord (j a b c : Nat) : List Command :=
  DISCARD ++ ([.ax c a b] ++ List.replicate (j+1) .shift) ++ popHeads (9-j)

theorem head1_total (a b c t w : Nat) :
    commandsEval (headWord 1 a b c) ⟨t,w,0,0⟩ =
      some ⟨rho1 a b,w,0,0⟩ := by
  unfold headWord
  refine @append_total (DISCARD ++ ([.ax c a b] ++ List.replicate (1+1) .shift))
    (popHeads (9-1)) ⟨t,w,0,0⟩ ⟨rho1 a b,([rho3 a b c,rho4 a b c,rho5 a b c,rho6 a b,rho7 a b c,rho8 a b c 0,wal 0 0] ++ [0]).foldr pair w,0,rho2 a b c⟩ ⟨rho1 a b,w,0,0⟩ ?_ ?_
  · apply append_total (DISCARD_total t w)
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      commandsEval,ax_step,Option.bind_some,pa135Heads,List.foldr_cons,List.foldr_nil,Nat.zero_add]
    simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,
      AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]
  · exact popHeads_stack [rho3 a b c,rho4 a b c,rho5 a b c,rho6 a b,rho7 a b c,rho8 a b c 0,wal 0 0] (rho1 a b) 0 w 0 (rho2 a b c)
#print axioms head1_total

theorem head2_total (a b c t w : Nat) :
    commandsEval (headWord 2 a b c) ⟨t,w,0,0⟩ =
      some ⟨rho2 a b c,w,0,0⟩ := by
  unfold headWord
  refine @append_total (DISCARD ++ ([.ax c a b] ++ List.replicate (2+1) .shift))
    (popHeads (9-2)) ⟨t,w,0,0⟩ ⟨rho2 a b c,([rho4 a b c,rho5 a b c,rho6 a b,rho7 a b c,rho8 a b c 0,wal 0 0] ++ [0]).foldr pair w,0,rho3 a b c⟩ ⟨rho2 a b c,w,0,0⟩ ?_ ?_
  · apply append_total (DISCARD_total t w)
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      commandsEval,ax_step,Option.bind_some,pa135Heads,List.foldr_cons,List.foldr_nil,Nat.zero_add]
    simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,
      AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]
  · exact popHeads_stack [rho4 a b c,rho5 a b c,rho6 a b,rho7 a b c,rho8 a b c 0,wal 0 0] (rho2 a b c) 0 w 0 (rho3 a b c)
#print axioms head2_total

theorem head3_total (a b c t w : Nat) :
    commandsEval (headWord 3 a b c) ⟨t,w,0,0⟩ =
      some ⟨rho3 a b c,w,0,0⟩ := by
  unfold headWord
  refine @append_total (DISCARD ++ ([.ax c a b] ++ List.replicate (3+1) .shift))
    (popHeads (9-3)) ⟨t,w,0,0⟩ ⟨rho3 a b c,([rho5 a b c,rho6 a b,rho7 a b c,rho8 a b c 0,wal 0 0] ++ [0]).foldr pair w,0,rho4 a b c⟩ ⟨rho3 a b c,w,0,0⟩ ?_ ?_
  · apply append_total (DISCARD_total t w)
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      commandsEval,ax_step,Option.bind_some,pa135Heads,List.foldr_cons,List.foldr_nil,Nat.zero_add]
    simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,
      AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]
  · exact popHeads_stack [rho5 a b c,rho6 a b,rho7 a b c,rho8 a b c 0,wal 0 0] (rho3 a b c) 0 w 0 (rho4 a b c)
#print axioms head3_total

theorem head4_total (a b c t w : Nat) :
    commandsEval (headWord 4 a b c) ⟨t,w,0,0⟩ =
      some ⟨rho4 a b c,w,0,0⟩ := by
  unfold headWord
  refine @append_total (DISCARD ++ ([.ax c a b] ++ List.replicate (4+1) .shift))
    (popHeads (9-4)) ⟨t,w,0,0⟩ ⟨rho4 a b c,([rho6 a b,rho7 a b c,rho8 a b c 0,wal 0 0] ++ [0]).foldr pair w,0,rho5 a b c⟩ ⟨rho4 a b c,w,0,0⟩ ?_ ?_
  · apply append_total (DISCARD_total t w)
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      commandsEval,ax_step,Option.bind_some,pa135Heads,List.foldr_cons,List.foldr_nil,Nat.zero_add]
    simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,
      AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]
  · exact popHeads_stack [rho6 a b,rho7 a b c,rho8 a b c 0,wal 0 0] (rho4 a b c) 0 w 0 (rho5 a b c)
#print axioms head4_total

theorem head5_total (a b c t w : Nat) :
    commandsEval (headWord 5 a b c) ⟨t,w,0,0⟩ =
      some ⟨rho5 a b c,w,0,0⟩ := by
  unfold headWord
  refine @append_total (DISCARD ++ ([.ax c a b] ++ List.replicate (5+1) .shift))
    (popHeads (9-5)) ⟨t,w,0,0⟩ ⟨rho5 a b c,([rho7 a b c,rho8 a b c 0,wal 0 0] ++ [0]).foldr pair w,0,rho6 a b⟩ ⟨rho5 a b c,w,0,0⟩ ?_ ?_
  · apply append_total (DISCARD_total t w)
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      commandsEval,ax_step,Option.bind_some,pa135Heads,List.foldr_cons,List.foldr_nil,Nat.zero_add]
    simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,
      AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]
  · exact popHeads_stack [rho7 a b c,rho8 a b c 0,wal 0 0] (rho5 a b c) 0 w 0 (rho6 a b)
#print axioms head5_total

theorem head6_total (a b c t w : Nat) :
    commandsEval (headWord 6 a b c) ⟨t,w,0,0⟩ =
      some ⟨rho6 a b,w,0,0⟩ := by
  unfold headWord
  refine @append_total (DISCARD ++ ([.ax c a b] ++ List.replicate (6+1) .shift))
    (popHeads (9-6)) ⟨t,w,0,0⟩ ⟨rho6 a b,([rho8 a b c 0,wal 0 0] ++ [0]).foldr pair w,0,rho7 a b c⟩ ⟨rho6 a b,w,0,0⟩ ?_ ?_
  · apply append_total (DISCARD_total t w)
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      commandsEval,ax_step,Option.bind_some,pa135Heads,List.foldr_cons,List.foldr_nil,Nat.zero_add]
    simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,
      AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]
  · exact popHeads_stack [rho8 a b c 0,wal 0 0] (rho6 a b) 0 w 0 (rho7 a b c)
#print axioms head6_total

theorem head7_total (a b c t w : Nat) :
    commandsEval (headWord 7 a b c) ⟨t,w,0,0⟩ =
      some ⟨rho7 a b c,w,0,0⟩ := by
  unfold headWord
  refine @append_total (DISCARD ++ ([.ax c a b] ++ List.replicate (7+1) .shift))
    (popHeads (9-7)) ⟨t,w,0,0⟩ ⟨rho7 a b c,([wal 0 0] ++ [0]).foldr pair w,0,rho8 a b c 0⟩ ⟨rho7 a b c,w,0,0⟩ ?_ ?_
  · apply append_total (DISCARD_total t w)
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      commandsEval,ax_step,Option.bind_some,pa135Heads,List.foldr_cons,List.foldr_nil,Nat.zero_add]
    simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,
      AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]
  · exact popHeads_stack [wal 0 0] (rho7 a b c) 0 w 0 (rho8 a b c 0)
#print axioms head7_total
def head8Word (a b c u : Nat) : List Command :=
  (DISCARD ++ J u) ++ ([.ax c (a-u) b] ++ List.replicate 9 .shift) ++ H

theorem head8_total (a b c u t w : Nat) (hu : u ≤ a) :
    commandsEval (head8Word a b c u) ⟨t,w,0,0⟩ =
      some ⟨rho8 a b c u,w,0,0⟩ := by
  have hadd : u+(a-u)=a := by omega
  unfold head8Word
  refine @append_total ((DISCARD ++ J u) ++ ([.ax c (a-u) b] ++ List.replicate 9 .shift)) H
    ⟨t,w,0,0⟩ ⟨rho8 a b c u,pair 0 w,0,wal u 0⟩ ⟨rho8 a b c u,w,0,0⟩ ?_ ?_
  · refine append_total (append_total (DISCARD_total t w) (J_total u w)) ?_
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,
      commandsEval,ax_step,Option.bind_some,pa135Heads,List.foldr_cons,List.foldr_nil,Nat.zero_add,hadd]
    simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,
      AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]
  · exact H_total (rho8 a b c u) 0 w 0 (wal u 0)
#print axioms head8_total
end M6.Source.ActualCommandMacros

