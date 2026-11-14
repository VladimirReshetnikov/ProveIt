import PA194CompilerCorrectness

/-! Conditional equivalence of source and parent halting, adapted from the
upstream PA196 finite-run proof. Coverage is explicit. -/
set_option autoImplicit false
namespace PA194SourceHalting
open M6.Zip M6.Source PA194RuntimeEngine PA194PrimitiveSimulation PA194CompilerCorrectness

theorem source_halt_to_parent
    (sites : Array Site) (paths : Nat → Path) (count : Nat)
    (coverage : Coverage sites paths count)
    (i gap : Nat) (vs : List Nat) (hi : i < count) (hv : 10 ≤ vs.length)
    (hh : CycleHalts sites ⟨.at i,readFile vs⟩) :
    Halts machine (frame (paths i) gap vs) := by
  obtain ⟨steps,hs⟩ := hh
  induction steps generalizing i gap vs with
  | zero => cases hs
  | succ steps ih =>
    obtain ⟨code,hcode,himpl⟩ := coverage i hi
    have hstep : cycleStep sites ⟨.at i,readFile vs⟩ = restart (execute code (readFile vs)) := by
      simp only [cycleStep,M6.Source.step,hcode]
    simp only [cycleRun,hstep] at hs
    cases code with
    | halt => exact himpl gap vs hv
    | inc r next =>
      obtain ⟨j,gap',ws,hj,hw,he,hr⟩ := himpl gap vs hv
      rw [he] at hs
      exact Halts.of_reach hr.reach (ih j gap' ws hj hw hs)
    | dec r z next =>
      obtain ⟨j,gap',ws,hj,hw,he,hr⟩ := himpl gap vs hv
      rw [he] at hs
      exact Halts.of_reach hr.reach (ih j gap' ws hj hw hs)
    | jump next =>
      obtain ⟨j,gap',ws,hj,hw,he,hr⟩ := himpl gap vs hv
      rw [he] at hs
      exact Halts.of_reach hr.reach (ih j gap' ws hj hw hs)

theorem source_halts_iff_parent
    (sites : Array Site) (paths : Nat → Path) (count : Nat)
    (coverage : Coverage sites paths count)
    (i gap : Nat) (vs : List Nat) (hi : i < count) (hv : 10 ≤ vs.length) :
    CycleHalts sites ⟨.at i,readFile vs⟩ ↔ Halts machine (frame (paths i) gap vs) := by
  constructor
  · exact source_halt_to_parent sites paths count coverage i gap vs hi hv
  · intro h
    exact Classical.byContradiction (fun hn =>
      source_nonhalt_to_physical sites paths count coverage i gap vs hi hv hn h)

#print axioms source_halt_to_parent
#print axioms source_halts_iff_parent
end PA194SourceHalting
