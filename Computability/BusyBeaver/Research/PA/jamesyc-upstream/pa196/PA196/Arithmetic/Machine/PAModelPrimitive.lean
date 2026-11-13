module
public import PA196.Arithmetic.Machine.PAInternalPhysicalRegisters
public import PA196.Arithmetic.Machine.InternalModelSource
public import PA196.Arithmetic.Machine.PAInternalPhysicalFrame
public import PA196.Arithmetic.Machine.PAInternalUniformOracle
public import PA196.Arithmetic.Machine.PAInternalTerminalContract
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.ModelPrimitive
open M6 M6.Source M6.Runtime
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open InternalTrace PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource InternalTrace.PhysicalRegisters
open PA196.RuntimeContracts (check)

section Models
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
def HaltsAt (m : Symbolic.ModelConf V) : Prop :=
  ∃ k qs ls rs lf rf, 0<k ∧ Segment k qs ls rs m.q m.left m.right 215 lf rf

def Progress (paths : Nat → Path) (count : Nat) (p : Path) (code : Instruction)
    (n xs : V) : Prop :=
  ∃ k n' xs', k < count ∧ (10 : V) ≤ len xs' ∧
    PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.restart (PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.execute code (PhysicalRegisters.readFile xs)) =
      ⟨.at k, PhysicalRegisters.readFile xs'⟩ ∧
    Symbolic.Progress true (PhysicalFrame.frame p n xs) (PhysicalFrame.frame (paths k) n' xs')

private theorem destination_restart (next : Option Nat) (r : Fin 9 → V) :
    PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.restart ⟨destination next,r⟩ = ⟨.at (next.getD 0),r⟩ := by
  cases next <;> rfl

lemma update_length_le : ∀ (r : Nat) (f : V → V) (xs : V),
    len xs ≤ len (FileEffects.update r f xs)
  | 0,f,xs => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · simp [hz,FileEffects.update]
    · simp [ha,FileEffects.update]
  | n+1,f,xs => by
    rcases nil_or_adjoin xs with hz | ⟨a,as,ha⟩
    · simp [hz]
    · simp only [ha,FileEffects.update,fstIdx_adjoin,sndIdx_adjoin,len_adjoin,
        add_le_add_iff_right]
      exact update_length_le n f as
lemma effect_length_valid (e : Eff) (xs : V) (h : (10 : V)≤len xs) :
    (10 : V)≤len (FileEffects.effect e xs) := by
  cases e with
  | none => exact h
  | inc r =>
    simp only [FileEffects.effect,len_concat]
    exact le_trans h (le_trans (update_length_le r (·+1) xs) (by simp))
  | dec r => exact le_trans h (update_length_le r (·-1) xs)

theorem checked_progress (paths : Nat → Path) (p : Path) (k extra fuel : Nat)
    (effect : Eff) (branch : Branch)
    (hc : check fuel ⟨branch, OriginalCheck.frame p,
      OriginalCheck.frame (paths k) extra effect⟩ = true)
    (hp : (paths k).length ≤ 38) (n xs : V) (hv : (10 : V)≤len xs)
    (hg : FileBoxes.Guard xs branch) :
    Symbolic.Progress true (PhysicalFrame.frame p n xs)
      (PhysicalFrame.frame (paths k) (n + extra) (FileEffects.effect effect xs)) := by
  have h := FileBoxes.checked_contract n xs hv fuel _ hc hg
  change Symbolic.Progress true (PhysicalFrame.frame p n xs)
    (Symbolic.config n (FileBoxes.box xs) Symbolic.denseControl (OriginalCheck.frame (paths k) extra effect)) at h
  rw [PhysicalFrame.root_effect _ hp] at h
  exact h
end Models

def Implements (paths : Nat → Path) (count : Nat) (p : Path) (code : Instruction) : Prop :=
  ∀ {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] (n xs : V), (10 : V) ≤ len xs →
    match code with
    | .halt => HaltsAt (PhysicalFrame.frame p n xs)
    | _ => Progress paths count p code n xs

theorem implements_inc (paths : Nat → Path) (count : Nat) (p : Path)
    (r : Fin 9) (next : Option Nat) (extra fuel : Nat)
    (hk : next.getD 0 < count) (hp : (paths (next.getD 0)).length ≤ 38)
    (hc : check fuel ⟨none, OriginalCheck.frame p,
      OriginalCheck.frame (paths (next.getD 0)) extra (.inc (physicalRegister r))⟩ = true) :
    Implements paths count p (.inc r next) := by
  intro V _ _ n xs hv
  refine ⟨next.getD 0,n+extra,FileEffects.effect (.inc (physicalRegister r)) xs,hk,
    effect_length_valid _ xs hv,?_,?_⟩
  · simp only [PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.execute,destination_restart]
    congr 1
    exact (PhysicalRegisters.read_increment xs hv r).symm
  · exact checked_progress paths p _ extra fuel _ none hc hp n xs hv trivial

theorem implements_jump (paths : Nat → Path) (count : Nat) (p : Path)
    (next : Option Nat) (extra fuel : Nat)
    (hk : next.getD 0 < count) (hp : (paths (next.getD 0)).length ≤ 38)
    (hc : check fuel ⟨none, OriginalCheck.frame p,
      OriginalCheck.frame (paths (next.getD 0)) extra .none⟩ = true) :
    Implements paths count p (.jump next) := by
  intro V _ _ n xs hv
  refine ⟨next.getD 0,n+extra,xs,hk,hv,?_,?_⟩
  · exact destination_restart next (PhysicalRegisters.readFile xs)
  · exact checked_progress paths p _ extra fuel .none none hc hp n xs hv trivial

theorem implements_dec (paths : Nat → Path) (count : Nat) (p : Path)
    (r : Fin 9) (zero positive : Option Nat) (ez ep fz fp : Nat)
    (hz : zero.getD 0 < count) (hn : positive.getD 0 < count)
    (hpz : (paths (zero.getD 0)).length ≤ 38) (hpp : (paths (positive.getD 0)).length ≤ 38)
    (cz : check fz ⟨some (physicalRegister r,true), OriginalCheck.frame p,
      OriginalCheck.frame (paths (zero.getD 0)) ez .none⟩ = true)
    (cp : check fp ⟨some (physicalRegister r,false), OriginalCheck.frame p,
      OriginalCheck.frame (paths (positive.getD 0)) ep (.dec (physicalRegister r))⟩ = true) :
    Implements paths count p (.dec r zero positive) := by
  intro V _ _ n xs hv
  by_cases he : PhysicalRegisters.readFile xs r = 0
  · refine ⟨zero.getD 0,n+ez,xs,hz,hv,?_,?_⟩
    · simp only [PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.execute,he,ite_true,destination_restart]
    · apply checked_progress paths p _ ez fz .none _ cz hpz n xs hv
      simpa only [FileBoxes.Guard,FileLayout.value_nth,PhysicalRegisters.readFile] using he
  · refine ⟨positive.getD 0,n+ep,FileEffects.effect (.dec (physicalRegister r)) xs,hn,
      effect_length_valid _ xs hv,?_,?_⟩
    · simp only [PA196.Arithmetic.Machine.PA.InternalTrace.ModelSource.execute,he,ite_false,destination_restart]
      congr 1
      exact (PhysicalRegisters.read_decrement xs hv r).symm
    · apply checked_progress paths p _ ep fp _ _ cp hpp n xs hv
      simpa only [FileBoxes.Guard,FileLayout.value_nth,PhysicalRegisters.readFile] using he

theorem implements_halt (paths : Nat → Path) (count : Nat) (p : Path) (fuel : Nat)
    (hc : PA196.RuntimeContracts.haltCheck fuel none (OriginalCheck.frame p) = true) :
    Implements paths count p .halt := by
  intro V _ _ n xs hv
  exact FileBoxes.checked_halt n xs hv fuel none _ hc trivial

structure Entry (paths : Nat → Path) (count : Nat) where
  site : Site
  code : Instruction
  proof : Implements paths count site.path code
#print axioms implements_inc
#print axioms implements_dec
#print axioms implements_halt
end PA196.Arithmetic.Machine.PA.ModelPrimitive
