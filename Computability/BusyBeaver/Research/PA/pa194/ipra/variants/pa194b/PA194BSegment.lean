import PA194BRelation
import PA194BExceptions

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2200000

namespace PA194BSimulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194BRows PA194BModelSteps

def translated (a : Action) : Action := (a.1,a.2.1,rho a.2.2)

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable abbrev pStep (x : V) : V := ConPA.Machine.step primaryTable x
noncomputable abbrev bStep (x : V) : V := ConPA.Machine.step variantTable x

/-- The two incoming right moves establish the history condition every
time the next primary control is one of the two folded readers. -/
theorem nextRelated (q : Fin 194) (b : Fin 2) (l r : V) :
    Relation (next (primary q.val b.val) l r) (next (translated (primary q.val b.val)) l r) := by
  let a := primary q.val b.val
  change Relation (next a l r) (next (translated a) l r)
  by_cases d : a.2.1 = 0
  · simp only [next,translated,d,if_pos]
    refine configBounded a.2.2 (oldTarget q b) _ _ ?_ ?_
    · intro h
      have hd := congrArg (fun row : Action => row.2.1) (incoming39 q b h)
      exact False.elim (Nat.zero_ne_one (d.symm.trans hd))
    · intro h
      have hd := congrArg (fun row : Action => row.2.1) (incoming52 q b h)
      exact False.elim (Nat.zero_ne_one (d.symm.trans hd))
  · simp only [next,translated,d,if_false]
    refine configBounded a.2.2 (oldTarget q b) _ _ ?_ ?_
    · intro h
      have hw := congrArg (fun row : Action => row.1) (incoming39 q b h)
      change a.1 = 1 at hw
      rw [hw,Nat.cast_one]
      exact stackMod l 1 (by norm_num)
    · intro h
      have hw := congrArg (fun row : Action => row.1) (incoming52 q b h)
      change a.1 = 0 at hw
      rw [hw,Nat.cast_zero]
      exact stackMod l 0 (by norm_num)

private theorem exception39zero (l r : V) (hl : l%2 = 1) (hr : r%2 = 0) :
    bStep^[3] (config (rho 39) l r) = next (translated (primary 39 0)) l r := by
  have lsplit : stack (l/2) 1 = l := by simpa only [hl] using components l
  have rsplit : stack (r/2) 0 = r := by simpa only [hr] using components r
  calc
    bStep^[3] (config (rho 39) l r) =
        bStep^[3] (config 39 (stack (l/2) 1) (stack (r/2) 0)) := by
      rw [lsplit,rsplit,show rho 39 = 39 by decide]
    _ = config 72 (stack (stack (l/2) 1) 0) (r/2) := PA194BExceptions.historyOne (l/2) (r/2)
    _ = _ := by
      rw [lsplit,show primary 39 0 = (0,1,53) by decide]
      simp [next,translated,stack,show rho 53 = 72 by decide]

private theorem exception52zero (l r : V) (hl : l%2 = 0) (hr : r%2 = 0) :
    bStep^[5] (config (rho 52) l r) = next (translated (primary 52 0)) l r := by
  have lsplit : stack (l/2) 0 = l := by simpa only [hl] using components l
  have rsplit : stack (r/2) 0 = r := by simpa only [hr] using components r
  calc
    bStep^[5] (config (rho 52) l r) =
        bStep^[5] (config 39 (stack (l/2) 0) (stack (r/2) 0)) := by
      rw [lsplit,rsplit,show rho 52 = 39 by decide]
    _ = config 106 (stack (stack (l/2) 0) 0) (r/2) := PA194BExceptions.historyZero (l/2) (r/2)
    _ = _ := by
      rw [lsplit,show primary 52 0 = (0,1,73) by decide]
      simp [next,translated,stack,show rho 73 = 106 by decide]

private theorem exceptionReadOne (q : Nat) (hq : q = 39 ∨ q = 52) (l r : V) (hr : r%2 = 1) :
    bStep^[1] (config (rho q) l r) = next (translated (primary q 1)) l r := by
  have rsplit : stack (r/2) 1 = r := by simpa only [hr] using components r
  have hq' : rho q = 39 := by rcases hq with rfl | rfl <;> decide
  have row : primary q 1 = (1,1,54) := by rcases hq with rfl | rfl <;> decide
  calc
    bStep^[1] (config (rho q) l r) = bStep (config 39 l (stack (r/2) 1)) := by
      rw [hq',Function.iterate_one,rsplit]
    _ = config 53 (stack l 1) (r/2) := PA194BExceptions.readOne l (r/2)
    _ = _ := by rw [row]; simp [next,translated,stack,show rho 54 = 53 by decide]

private theorem matching (q : Fin 194) (b : Fin 2) (l r : V)
    (hr : r%2 = (b.val : V)) (h39 : q.val = 39 → l%2 = 1) (h52 : q.val = 52 → l%2 = 0) :
    ∃ k : Nat, 0 < k ∧ bStep^[k] (config (rho q.val) l r) =
      next (translated (primary q.val b.val)) l r := by
  have hb := b.isLt
  by_cases e39 : q.val = 39
  · by_cases eb : b.val = 0
    · refine ⟨3,by decide,?_⟩
      rw [e39,eb]
      exact exception39zero l r (h39 e39) (by simpa [eb] using hr)
    · have eb' : b.val = 1 := by omega
      refine ⟨1,by decide,?_⟩
      rw [eb']
      exact exceptionReadOne q.val (Or.inl e39) l r (by simpa [eb'] using hr)
  · by_cases e52 : q.val = 52
    · by_cases eb : b.val = 0
      · refine ⟨5,by decide,?_⟩
        rw [e52,eb]
        exact exception52zero l r (h52 e52) (by simpa [eb] using hr)
      · have eb' : b.val = 1 := by omega
        refine ⟨1,by decide,?_⟩
        rw [eb']
        exact exceptionReadOne q.val (Or.inr e52) l r (by simpa [eb'] using hr)
    · refine ⟨1,by decide,?_⟩
      rw [Function.iterate_one]
      have hl := rhoLive q
      have he := stepRow actions (rho q.val) b.val l r hb (by rw [counts.1]; omega) hr
      change bStep (config (rho q.val) l r) = next (action (rho q.val) b.val) l r at he
      rwa [ordinary q b e39 e52] at he

theorem segment {x y : V} (h : Relation x y) :
    ∃ k : Nat, 0 < k ∧ Relation (pStep x) (bStep^[k] y) := by
  obtain ⟨q,l,r,hq,rfl,rfl,h39,h52⟩ := configs h
  by_cases e : q = 194
  · subst q
    refine ⟨1,by decide,?_⟩
    rw [Function.iterate_one,rhoHalt]
    rw [show pStep (config 194 l r) = config 194 l r from by
      simpa only [tableOld] using halted PA194Rows.rows PA194GenericBridge.rowCount l r]
    rw [show bStep (config 194 l r) = config 194 l r from halted actions counts.1 l r]
    simpa only [rhoHalt] using configBounded 194 (by decide) l r
      (fun f => False.elim ((by decide : (194 : Nat) ≠ 39) f))
      (fun f => False.elim ((by decide : (194 : Nat) ≠ 52) f))
  · have qlt : q < 194 := by omega
    let qf : Fin 194 := ⟨q,qlt⟩
    have go (b : Fin 2) (hr : r % 2 = (b.val : V)) :
        ∃ k : Nat, 0 < k ∧ Relation (pStep (config q l r))
          (bStep^[k] (config (rho q) l r)) := by
      obtain ⟨k,hk,hs⟩ := matching qf b l r hr h39 h52
      have hp := stepRow PA194Rows.rows q b.val l r b.isLt
        (by rw [PA194GenericBridge.rowCount]; have := b.isLt; omega) hr
      rw [tableOld] at hp
      change pStep (config q l r) = next (primary q b.val) l r at hp
      refine ⟨k,hk,?_⟩
      rw [hp,hs]
      exact nextRelated qf b l r
    rcases mod_two r with hr | hr
    · exact go 0 (by simpa using hr)
    · exact go 1 (by simpa using hr)

#print axioms nextRelated
#print axioms segment
end models
end PA194BSimulation
