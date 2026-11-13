module
public import PA196.RuntimeContracts
public import PA196.Frame
public import M6.Source.FileInvariant
public import M6.Source.CyclicDeterminism

@[expose] public section

namespace PA196.PrimitiveSimulation
open M6.Zip M6.Runtime M6.Source PA196.Table
open PA196.RuntimeContracts (Contract check sound)

def frame (path : Path) (n : Nat) (vs : List Nat) : Conf := conc n vs (PA196.Frame.rootFrame path)

def Progress (paths : Nat → Path) (count : Nat) (p : Path) (code : Instruction)
    (n : Nat) (vs : List Nat) : Prop :=
  ∃ k n' vs', k < count ∧ 10 ≤ vs'.length ∧
    restart (execute code (readFile vs)) = ⟨.at k, readFile vs'⟩ ∧
    Reach1 machine (frame p n vs) (frame (paths k) n' vs')

def Implements (paths : Nat → Path) (count : Nat) (p : Path) (code : Instruction) : Prop :=
  ∀ n vs, 10 ≤ vs.length →
    match code with
    | .halt => Halts machine (frame p n vs)
    | _ => Progress paths count p code n vs

private theorem destination_restart (next : Option Nat) (r : Registers) :
    restart ⟨destination next,r⟩ = ⟨.at (next.getD 0),r⟩ := by
  cases next <;> rfl

theorem checked_progress (paths : Nat → Path) (p : Path) (k extra fuel : Nat)
    (effect : Eff) (branch : Branch)
    (hc : check fuel ⟨branch, PA196.RuntimeContracts.rootFrame p,
      PA196.RuntimeContracts.rootFrame (paths k) extra effect⟩ = true)
    (hp : (paths k).length ≤ 38) (n : Nat) (vs : List Nat) (hv : Valid branch vs) :
    Reach1 machine (frame p n vs) (frame (paths k) (n + extra) (effectFile effect vs)) := by
  have h := sound fuel _ hc n vs hv
  change Reach1 machine (conc n vs (PA196.Frame.rootFrame p))
    (conc n vs (PA196.Frame.rootFrame (paths k) extra effect)) at h
  rw [PA196.Frame.rootFrame_effect _ hp] at h
  exact h

theorem implements_inc (paths : Nat → Path) (count : Nat) (p : Path)
    (r : Fin 9) (next : Option Nat) (extra fuel : Nat)
    (hk : next.getD 0 < count) (hp : (paths (next.getD 0)).length ≤ 38)
    (hc : check fuel ⟨none, PA196.RuntimeContracts.rootFrame p,
      PA196.RuntimeContracts.rootFrame (paths (next.getD 0)) extra (.inc (physicalRegister r))⟩ = true) :
    Implements paths count p (.inc r next) := by
  intro n vs hv
  refine ⟨next.getD 0,n+extra,effectFile (.inc (physicalRegister r)) vs,hk,
    effectFile_valid_length _ vs hv,?_,?_⟩
  · simp only [execute,destination_restart]
    congr 1
    exact (readFile_increment_with_spare vs (by omega) r).symm
  · exact checked_progress paths p _ extra fuel _ none hc hp n vs ⟨hv,trivial⟩

theorem implements_jump (paths : Nat → Path) (count : Nat) (p : Path)
    (next : Option Nat) (extra fuel : Nat)
    (hk : next.getD 0 < count) (hp : (paths (next.getD 0)).length ≤ 38)
    (hc : check fuel ⟨none, PA196.RuntimeContracts.rootFrame p,
      PA196.RuntimeContracts.rootFrame (paths (next.getD 0)) extra .none⟩ = true) :
    Implements paths count p (.jump next) := by
  intro n vs hv
  refine ⟨next.getD 0,n+extra,vs,hk,hv,?_,?_⟩
  · exact destination_restart next (readFile vs)
  · exact checked_progress paths p _ extra fuel .none none hc hp n vs ⟨hv,trivial⟩

theorem implements_dec (paths : Nat → Path) (count : Nat) (p : Path)
    (r : Fin 9) (zero positive : Option Nat) (ez ep fz fp : Nat)
    (hz : zero.getD 0 < count) (hn : positive.getD 0 < count)
    (hpz : (paths (zero.getD 0)).length ≤ 38) (hpp : (paths (positive.getD 0)).length ≤ 38)
    (cz : check fz ⟨some (physicalRegister r,true), PA196.RuntimeContracts.rootFrame p,
      PA196.RuntimeContracts.rootFrame (paths (zero.getD 0)) ez .none⟩ = true)
    (cp : check fp ⟨some (physicalRegister r,false), PA196.RuntimeContracts.rootFrame p,
      PA196.RuntimeContracts.rootFrame (paths (positive.getD 0)) ep (.dec (physicalRegister r))⟩ = true) :
    Implements paths count p (.dec r zero positive) := by
  intro n vs hv
  by_cases he : readFile vs r = 0
  · refine ⟨zero.getD 0,n+ez,vs,hz,hv,?_,?_⟩
    · simp only [execute,he,ite_true,destination_restart]
    · exact checked_progress paths p _ ez fz .none _ cz hpz n vs ⟨hv,he⟩
  · refine ⟨positive.getD 0,n+ep,effectFile (.dec (physicalRegister r)) vs,hn,
      effectFile_valid_length _ vs hv,?_,?_⟩
    · simp only [execute,he,ite_false,destination_restart]
      congr 1
      exact (readFile_decr vs (by omega) r).symm
    · exact checked_progress paths p _ ep fp _ _ cp hpp n vs ⟨hv,he⟩

theorem implements_halt (paths : Nat → Path) (count : Nat) (p : Path) (fuel : Nat)
    (hc : PA196.RuntimeContracts.haltCheck fuel none (PA196.RuntimeContracts.rootFrame p) = true) :
    Implements paths count p .halt := by
  intro n vs hv
  exact PA196.RuntimeContracts.halt_sound fuel none _ hc n vs ⟨hv,trivial⟩

structure Entry (paths : Nat → Path) (count : Nat) where
  site : Site
  code : Instruction
  proof : Implements paths count site.path code

#print axioms implements_inc
#print axioms implements_dec
#print axioms implements_halt
end PA196.PrimitiveSimulation
