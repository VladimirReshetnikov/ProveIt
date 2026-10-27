import DiophantineConsistency.ArithmeticEnumFairPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumFairPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222 ArithmeticEnumFairPerm222
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

example (w : V) : ∃ time,run time (liveValue 0 4 w)=0 ∨
    ∃ w',run time (liveValue 0 4 w)=liveValue 0 4 w' := reach_from_four 4 w le_rfl
example (word np w : V) : ∃ t ≤ word,
    run t (liveValue word np w)=embedValue np (ArithmeticCommandRunPerm222.terminal word w) :=
  drain_terminal word np w
example (w : V) : ∃ t ≤ (0 : V)+1,
    run t (liveValue 0 0 w)=
      if ArithmeticCommandRunPerm222.evalValue (0+1) w=0 then 0
      else liveValue 0 (0+1) (ArithmeticCommandRunPerm222.evalValue (0+1) w-1) :=
  drain_boundary 0 w
example (word w : V) (hn : word≠0) (h : 4 ≤ word-1)
    (hall : ∀ w,ArithmeticCommandRunPerm222.evalValue word w=0) :
    ∃ t,run t (liveValue 0 4 w)=0 := halts_of_word word 4 w hn h hall

#print axioms enum_active
#print axioms enum_boundary
#print axioms embed_defined
#print axioms enum_embed_succ
#print axioms enum_embed_active
#print axioms paired_or_stopped
#print axioms drain_terminal
#print axioms embed_terminal_eval
#print axioms drain
#print axioms drain_boundary
#print axioms reach_offset
#print axioms reach_of_le
#print axioms reach_from_four
#print axioms halts_of_word
end DiophantineConsistency.ArithmeticEnumFairPerm222Checks
