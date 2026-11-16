module
public import M6.Source.NIPGuard
public import M6.Source.Unpair
public import M6.Source.Determinism
@[expose] public section

/-! Complete literal S36 command semantics, including the sum-one guard and
Cantor-stack pop. Normal root return is `.exited`, not halting; the global
command-enumeration driver will separately restart at source ordinal zero. -/
namespace M6.Source.S36Command

def registers (t w h : Nat) (f : Registers) : Registers :=
  Unpair.registers ⟨w,h,0,0,write f 1 t⟩

def start (t w h : Nat) (f : Registers) : Configuration :=
  ⟨.at 3911, registers t w h f⟩

def normal (t w h : Nat) (f : Registers) : Configuration :=
  ⟨.exited, registers t w h f⟩

def halted (t w h : Nat) (f : Registers) : Configuration :=
  ⟨.halted, registers t w h f⟩

private theorem register_bridge (t w h x y : Nat) (f : Registers) :
    S36Lift.registers ⟨t,h,x,Unpair.registers ⟨w,0,0,y,f⟩⟩ =
      Unpair.registers ⟨w,h,x,y,write f 1 t⟩ := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;>
    by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [S36Lift.registers, Unpair.registers, write]

def popCost (w : Nat) : Nat :=
  Unpair.loopCost w (0,0) + (3*(Cantor.decode w).2+1) + (3*(Cantor.decode w).1+1)

/-- The literal command halts when the sum of its incoming witnesses is one. -/
theorem halt_of_sum_one (t w h : Nat) (f : Registers) (hs : t+h = 1) :
    Steps exactSites (6*t+7*h+10) (start t w h f) (halted h w 0 f) := by
  have q := NIPGuard.s36_halts_of_sum_one t h (Unpair.registers ⟨w,0,0,0,f⟩) hs
  simpa only [NIPGuard.configAt, register_bridge, start, halted, registers] using q

/-- Otherwise it returns the old H as T and pops exactly the Cantor-coded stack.
N,A,D,L are preserved, and X=Y=0 at both boundaries. -/
theorem normal_of_sum_ne_one (t w h : Nat) (f : Registers) (hs : t+h ≠ 1) :
    Steps exactSites ((8*t+9*h+9) + popCost w)
      (start t w h f) (normal h (Cantor.decode w).2 (Cantor.decode w).1 f) := by
  have before := NIPGuard.s36_reaches_stack_of_sum_ne_one t h
    (Unpair.registers ⟨w,0,0,0,f⟩) hs
  simp only [NIPGuard.configAt, register_bridge] at before
  have after := Unpair.unpair w (write f 1 h)
  exact Unpair.steps_trans before after

/-- Every natural input has a finite command outcome. This is not a theorem of
nonhalting for the global enumeration driver. -/
theorem total (t w h : Nat) (f : Registers) :
    (t+h = 1 ∧ ∃ n, Steps exactSites n (start t w h f) (halted h w 0 f)) ∨
    (t+h ≠ 1 ∧ ∃ n, Steps exactSites n (start t w h f)
      (normal h (Cantor.decode w).2 (Cantor.decode w).1 f)) := by
  by_cases hs : t+h = 1
  · exact Or.inl ⟨hs, _, halt_of_sum_one t w h f hs⟩
  · exact Or.inr ⟨hs, _, normal_of_sum_ne_one t w h f hs⟩

/-- The zero stack alias is handled uniformly, without a nonzero-stack premise. -/
theorem normal_zero_stack (t h : Nat) (f : Registers) (hs : t+h ≠ 1) :
    Steps exactSites ((8*t+9*h+9) + popCost 0)
      (start t 0 h f) (normal h 0 0 f) :=
  normal_of_sum_ne_one t 0 h f hs

/-- Exact halting characterization for this one source invocation. Normal root
return is absorbing here; restarting the global enumerator is a separate driver. -/
theorem halts_iff_sum_one (t w h : Nat) (f : Registers) :
    Halts exactSites (start t w h f) ↔ t+h = 1 := by
  constructor
  · rintro ⟨n,r,hr⟩
    by_cases hs : t+h = 1
    · exact hs
    · have hn := normal_of_sum_ne_one t w h f hs
      have he := stable_outcomes_unique hr hn rfl rfl
      have hc := congrArg Configuration.control he
      cases hc
  · intro hs
    exact ⟨_, _, halt_of_sum_one t w h f hs⟩

#print axioms halt_of_sum_one
#print axioms normal_of_sum_ne_one
#print axioms total
#print axioms halts_iff_sum_one
end M6.Source.S36Command

