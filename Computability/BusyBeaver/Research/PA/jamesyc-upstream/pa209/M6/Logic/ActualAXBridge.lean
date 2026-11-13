module
public import M6.Source.ActualAXCode
public import M6.Logic.ActualAXLogic
@[expose] public section

/-! Explicit additive bridge from the literal actual AX arithmetic profile
to finite witnesses in the historical PA-sound calculus. No reverse basis
equivalence and no full source execution theorem is asserted here. -/
namespace M6.PA.NativeCalculus
open M6.Source

private theorem im_eq (a b : Nat) : AXCode.wim a b = wim a b := by simp only [AXCode.wim,wim]
private theorem all_eq (a b : Nat) : AXCode.wal a b = wal a b := by simp only [AXCode.wal,wal]
private theorem mem_eq (a b : Nat) : AXCode.wel a b = wel a b := rfl
private theorem eq_eq (a b : Nat) : AXCode.weq a b = weq a b := rfl
private theorem neg_eq (a : Nat) : AXCode.wn a = wn a := by simp only [AXCode.wn,wn,im_eq]
private theorem and_eq (a b : Nat) : AXCode.wa a b = wa a b := by simp only [AXCode.wa,wa,neg_eq,im_eq]
private theorem ex_eq (a b : Nat) : AXCode.wex a b = wex a b := by simp only [AXCode.wex,wex,neg_eq,all_eq]

theorem actual_bundle_eq (a b c : Nat) :
    ActualAXCode.bundle a b c = ActualAX.rawBundle a b c := by
  simp only [ActualAXCode.bundle,ActualAXCode.memVac,ActualAXCode.separation,ActualAXCode.point,
    ActualAX.rawBundle,ActualAX.memVacuity,ActualAX.separationBody,ActualAX.point,
    im_eq,all_eq,mem_eq,neg_eq,and_eq]

theorem actual_heads_eq (a b c u h : Nat) :
    ActualAXCode.pa135Heads a b c u h =
      [rho1 a b,rho2 a b c,ActualAX.head3 a b c,rho4 a b c,ActualAX.head5 a b c,
       rho6 a b,ActualAX.head7 a b c,rho8 a b c u,wal u h] := by
  simp only [ActualAXCode.pa135Heads,ActualAXCode.rho1,ActualAXCode.rho2,ActualAXCode.rho3,
    ActualAXCode.rho4,ActualAXCode.rho5,ActualAXCode.rho6,ActualAXCode.rho7,ActualAXCode.rho8,
    AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,
    rho1,rho2,rho4,rho6,rho8,ActualAX.head3,ActualAX.head5,ActualAX.head7,
    im_eq,all_eq,mem_eq,eq_eq,ex_eq]

theorem actual_heads_proved (a b c u h : Nat) (hdom : u ≤ a) (hh : Proved h) :
    ∀ n ∈ ActualAXCode.pa135Heads a b c u h, Proved n := by
  rw [actual_heads_eq]
  rcases hh with ⟨dh⟩
  intro n hn
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.r1 a b⟩
  · exact ⟨.r2 a b c⟩
  · exact ⟨ActualAX.head3_proof a b c⟩
  · exact ⟨.r4 a b c⟩
  · exact ⟨ActualAX.head5_proof a b c⟩
  · exact ⟨.r6 a b⟩
  · exact ⟨ActualAX.head7_proof a b c⟩
  · exact ⟨.r8 a b c u hdom⟩
  · exact ⟨.all u dh⟩

theorem actual_gate_proved (a b c : Nat) : Proved (ActualAXCode.gate a b c) := by
  unfold ActualAXCode.gate
  split
  · exact ⟨.truth⟩
  · rename_i hg
    rw [actual_bundle_eq]
    exact ⟨ActualAX.rawBundle_proof a b c (fun h => hg (Or.inl h)) (fun h => hg (Or.inr h))⟩

#print axioms actual_bundle_eq
#print axioms actual_heads_proved
#print axioms actual_gate_proved
end M6.PA.NativeCalculus

