import DiophantineConsistency.ArithmeticRegisterBoxes215

/-! # Clock-bounded reaches of the literal decimal215 machine

`ArithmeticRegisterBoxes215.Reach x y` is `∃ t, runFrom t x = y`. Here `ReachB x y B`
also bounds the clock by an explicit internal `B`, with the composition, single
step and transition-row lemmas of `ArithmeticRegisterBoxes215`, and the two scans,
whose exact clocks are the scanned lengths. These are the primitives from which the
box, symbolic, Home and site executions would be re-proved with explicit clocks.
No existing statement is changed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.ArithmeticRuntimeBoundTape
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticTapePrefix254 ArithmeticMachineTape215
open ArithmeticRegisterBoxes215
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `Reach` within at most `B` machine steps. -/
def ReachB (x y B : V) : Prop := ∃ t ≤ B, runFrom t x = y

/-- `ReachPos` within at most `B` machine steps. -/
def ReachPosB (x y B : V) : Prop := ∃ t : V, 0 < t ∧ t ≤ B ∧ runFrom t x = y

theorem ReachB.reach {x y B : V} (h : ReachB x y B) : Reach x y := by
  obtain ⟨t, _, ht⟩ := h; exact ⟨t, ht⟩
theorem ReachPosB.reachPos {x y B : V} (h : ReachPosB x y B) : ReachPos x y := by
  obtain ⟨t, ht0, _, ht⟩ := h; exact ⟨t, ht0, ht⟩
theorem ReachB.mono {x y B C : V} (h : ReachB x y B) (hBC : B ≤ C) : ReachB x y C := by
  obtain ⟨t, ht, h⟩ := h; exact ⟨t, le_trans ht hBC, h⟩
theorem ReachPosB.mono {x y B C : V} (h : ReachPosB x y B) (hBC : B ≤ C) : ReachPosB x y C := by
  obtain ⟨t, h0, ht, h⟩ := h; exact ⟨t, h0, le_trans ht hBC, h⟩
theorem ReachB.refl (x : V) : ReachB x x 0 := ⟨0, le_rfl, runFrom_zero x⟩
theorem ReachB.of_eq {x y : V} (h : x = y) : ReachB x y 0 := ⟨0, le_rfl, (runFrom_zero x).trans h⟩
theorem ReachB.trans {x y z A B : V} (h : ReachB x y A) (g : ReachB y z B) : ReachB x z (A + B) := by
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨u, hu, g⟩ := g
  exact ⟨t + u, _root_.add_le_add ht hu, by rw [runFrom_add, h, g]⟩
theorem ReachB.of_step {x y : V} (h : ArithmeticMachineStep215.stepValue x = y) : ReachB x y 1 :=
  ⟨1, le_rfl, (run_one x).trans h⟩
theorem ReachPosB.of_step {x y : V} (h : ArithmeticMachineStep215.stepValue x = y) :
    ReachPosB x y 1 := ⟨1, by simp, le_rfl, (run_one x).trans h⟩
theorem ReachPosB.trans_reach {x y z A B : V} (h : ReachPosB x y A) (g : ReachB y z B) :
    ReachPosB x z (A + B) := by
  obtain ⟨t, h0, ht, h⟩ := h
  obtain ⟨u, hu, g⟩ := g
  exact ⟨t + u, lt_of_lt_of_le h0 le_self_add, _root_.add_le_add ht hu,
    by rw [runFrom_add, h, g]⟩
theorem ReachB.trans_positive {x y z A B : V} (h : ReachB x y A) (g : ReachPosB y z B) :
    ReachPosB x z (A + B) := by
  obtain ⟨t, ht, h⟩ := h
  obtain ⟨u, h0, hu, g⟩ := g
  exact ⟨t + u, lt_of_lt_of_le h0 le_add_self, _root_.add_le_add ht hu,
    by rw [runFrom_add, h, g]⟩

theorem stRB {q q' : Nat} {b w : Bool} {L R X B : V}
    (h : KTableCore.tm215 q b = some (w,true,q'))
    (g : ReachB (frameSparse q' (2*L+digit w) R) X B) :
    ReachB (frameSparse q L (2*R+digit b)) X (1 + B) :=
  (ReachB.of_step (step_right h L R)).trans g
theorem stLB {q q' : Nat} {b w : Bool} {L R X B : V}
    (h : KTableCore.tm215 q b = some (w,false,q'))
    (g : ReachB (leftFrame q' L (2*R+digit w)) X B) :
    ReachB (frameSparse q L (2*R+digit b)) X (1 + B) :=
  (ReachB.of_step (step_left h L R)).trans g
theorem stLLB {q q' : Nat} {b w : Bool} {L R X B : V}
    (h : KTableCore.tm215 q b = some (w,false,q'))
    (g : ReachB (leftFrame q' L (2*R+digit w)) X B) :
    ReachB (leftFrame q (2*L+digit b) R) X (1 + B) :=
  (ReachB.of_step (step_left_facing h L R)).trans g

/-- The right scan takes exactly its length. -/
theorem scan_rightB (q : Nat) (b w : Bool)
    (h : KTableCore.tm215 q b = some (w,true,q)) (n L R : V) :
    ReachB (frameSparse q L (bitPrefix b n R)) (frameSparse q (bitPrefix w n L) R) n :=
  ⟨n, le_rfl, scan_right q b w h n L R⟩

/-- The left scan takes exactly its length. -/
theorem scan_leftB (q : Nat) (b w : Bool)
    (h : KTableCore.tm215 q b = some (w,false,q)) (n L R : V) :
    ReachB (leftFrame q (bitPrefix b n L) R) (leftFrame q L (bitPrefix w n R)) n :=
  ⟨n, le_rfl, scan_left q b w h n L R⟩

end DiophantineConsistency.ArithmeticRuntimeBoundTape
