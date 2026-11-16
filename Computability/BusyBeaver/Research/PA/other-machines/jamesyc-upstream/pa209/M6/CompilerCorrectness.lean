module
public import M6.PrimitiveSimulation
public import M6.PositiveInvariant
@[expose] public section

namespace M6.CompilerCorrectness
open M6.Zip M6.Runtime M6.Source M6.Table M6.PrimitiveSimulation

def Coverage (sites : Array Site) (paths : Nat → Path) (count : Nat) : Prop :=
  ∀ i, i < count → ∃ code, resolveAt sites i = some code ∧ Implements paths count (paths i) code

private theorem nonhalt_next (sites : Array Site) (c : Configuration)
    (h : ¬ CycleHalts sites c) : ¬ CycleHalts sites (cycleStep sites c) := by
  rintro ⟨n,hn⟩
  exact h ⟨n+1,hn⟩

theorem source_nonhalt_to_physical (sites : Array Site) (paths : Nat → Path) (count : Nat)
    (coverage : Coverage sites paths count)
    (i n : Nat) (vs : List Nat) (hi : i < count) (hv : 10 ≤ vs.length)
    (hn : ¬ CycleHalts sites ⟨.at i,readFile vs⟩) :
    ¬ Halts machine (frame (paths i) n vs) := by
  let Inv : Conf → Prop := fun c => ∃ i n vs, i < count ∧ 10 ≤ vs.length ∧
    (¬ CycleHalts sites ⟨.at i,readFile vs⟩) ∧ c = frame (paths i) n vs
  apply not_halts_of_positive_invariant machine Inv
  · intro c hc
    obtain ⟨j,m,ws,hj,hw,hno,rfl⟩ := hc
    obtain ⟨code,hcode,himpl⟩ := coverage j hj
    have hstep : cycleStep sites ⟨.at j,readFile ws⟩ = restart (execute code (readFile ws)) := by
      simp only [cycleStep,M6.Source.step,hcode]
    have hnext := nonhalt_next sites ⟨.at j,readFile ws⟩ hno
    rw [hstep] at hnext
    have hprog : Progress paths count (paths j) code m ws := by
      cases code with
      | halt =>
        exact False.elim (hnext ⟨0,rfl⟩)
      | inc r next => exact himpl m ws hw
      | dec r z next => exact himpl m ws hw
      | jump next => exact himpl m ws hw
    obtain ⟨k,m',ws',hk,hw',he,hreach⟩ := hprog
    rw [he] at hnext
    exact ⟨frame (paths k) m' ws',hreach,k,m',ws',hk,hw',hnext,rfl⟩
  · exact ⟨i,n,vs,hi,hv,hn,rfl⟩

#print axioms source_nonhalt_to_physical
end M6.CompilerCorrectness
