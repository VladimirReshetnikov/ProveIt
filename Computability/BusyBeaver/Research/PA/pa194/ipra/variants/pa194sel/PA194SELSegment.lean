import PA194SELRelation

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2200000

namespace PA194SELSimulation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PA194SELRows PA194BModelSteps
open PA194BRows (primary oldTarget)

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable abbrev pStep (x : V) : V := ConPA.Machine.step primaryTable x
noncomputable abbrev sStep (x : V) : V := ConPA.Machine.step variantTable x

/-- The literal selector returns to the old head position after two steps.
The helper then executes the specified right move, restoring the same
left-neighbor bit and preserving both tape exteriors. -/
theorem selectorThree (values : List Action) (hv : values.length = 388)
    (q selector helper a dest : Nat) (hq : q < 194) (hs : selector < 194)
    (hh : helper < 194) (ha : a < 2)
    (first : values.getD (2*q) (0,0,194) = (0,0,selector))
    (second : values.getD (2*selector+a) (0,0,194) = (a,1,helper))
    (third : values.getD (2*helper) (0,0,194) = (0,1,dest)) (l r : V) :
    (ConPA.Machine.step (table values))^[3] (config q (stack l (a : V)) (stack r 0)) =
      config dest (stack (stack l (a : V)) 0) r := by
  have h1 := left values hv q a 0 0 selector hq ha (by decide) l r first
  have h2 := right values hv selector a a helper hs ha l (stack r 0) second
  have h3 := right values hv helper 0 0 dest hh (by decide) (stack l (a : V)) r third
  simp only [Nat.cast_zero] at h1 h2 h3
  rw [show 3 = 2+1 by decide,Function.iterate_succ_apply',
    show 2 = 1+1 by decide,Function.iterate_succ_apply',Function.iterate_one,h1,h2,h3]

theorem nextRelated (q : Fin 194) (b : Fin 2) (l r : V) :
    Relation (next (primary q.val b.val) l r) (next (translated (primary q.val b.val)) l r) := by
  let a := primary q.val b.val
  change Relation (next a l r) (next (translated a) l r)
  by_cases d : a.2.1 = 0
  · simp only [next,translated,d,if_pos]
    refine configBounded a.2.2 (oldTarget q b) _ _ ?_
    intro f hf h
    exact False.elim (Nat.zero_ne_one (d.symm.trans (incoming q b f hf h).2))
  · simp only [next,translated,d,if_false]
    refine configBounded a.2.2 (oldTarget q b) _ _ ?_
    intro f hf h
    have hw : a.1 = f.history := (incoming q b f hf h).1
    rw [hw]
    have hb : (f.history : V) < 2 := by exact_mod_cast (foldBounds f hf).2
    exact stackMod l _ hb

private theorem exception (q : Fin 194) (f : Fold) (hf : special q.val = some f) (l r : V)
    (hl : l % 2 = (f.history : V)) (hr : r % 2 = 0) :
    sStep^[3] (config (rho q.val) l r) = next (translated (primary q.val 0)) l r := by
  have hcheck := specialCertificate q
  simp only [validSpecial,hf,decide_eq_true_eq] at hcheck
  obtain ⟨hbit,hsel,hhelp,hold,hfirst,hsecond,hthird⟩ := hcheck
  have hq := rhoLive q
  have lsplit : stack (l/2) (f.history : V) = l := by simpa only [hl] using components l
  have rsplit : stack (r/2) 0 = r := by simpa only [hr] using components r
  calc
    sStep^[3] (config (rho q.val) l r) =
        sStep^[3] (config (rho q.val) (stack (l/2) (f.history : V)) (stack (r/2) 0)) := by
      rw [lsplit,rsplit]
    _ = config (rho (primary q.val 0).2.2) (stack (stack (l/2) (f.history : V)) 0) (r/2) :=
      selectorThree actions counts.1 (rho q.val) f.selector f.helper f.history
        (rho (primary q.val 0).2.2) hq hsel hhelp hbit hfirst hsecond hthird (l/2) (r/2)
    _ = _ := by
      rw [lsplit]
      have hw : (primary q.val 0).1 = 0 := congrArg Prod.fst hold
      have hd : (primary q.val 0).2.1 = 1 := congrArg (fun a : Action => a.2.1) hold
      simp [stack,next,translated,hw,hd]

private theorem matching (q : Fin 194) (b : Fin 2) (l r : V)
    (hr : r%2 = (b.val : V)) (hg : ∀ f ∈ folds, q.val = f.origin → l%2 = (f.history : V)) :
    ∃ k : Nat, 0 < k ∧ sStep^[k] (config (rho q.val) l r) =
      next (translated (primary q.val b.val)) l r := by
  have hb := b.isLt
  by_cases ho : (special q.val).isNone = true ∨ b.val = 1
  · refine ⟨1,by decide,?_⟩
    rw [Function.iterate_one]
    have hl := rhoLive q
    have he := stepRow actions (rho q.val) b.val l r hb (by rw [counts.1]; omega) hr
    change sStep (config (rho q.val) l r) = next (action (rho q.val) b.val) l r at he
    rwa [ordinary q b ho] at he
  · have hb0 : b.val = 0 := by
      have hb1 : b.val ≠ 1 := fun f => ho (Or.inr f)
      omega
    rw [hb0,Nat.cast_zero] at hr
    obtain ⟨f,hf⟩ : ∃ f, special q.val = some f := by
      cases he : special q.val with
      | none => exact False.elim (ho (Or.inl (by simp [he])))
      | some f => exact ⟨f,rfl⟩
    have ⟨hm,hq⟩ := found hf
    refine ⟨3,by decide,?_⟩
    rw [hb0]
    exact exception q f hf l r (hg f hm hq.symm) hr

theorem segment {x y : V} (h : Relation x y) :
    ∃ k : Nat, 0 < k ∧ Relation (pStep x) (sStep^[k] y) := by
  obtain ⟨q,l,r,hq,rfl,rfl,hg⟩ := configs h
  by_cases e : q = 194
  · subst q
    refine ⟨1,by decide,?_⟩
    rw [Function.iterate_one,rhoHalt]
    rw [show pStep (config 194 l r) = config 194 l r from
      by simpa only [tableOld] using halted PA194Rows.rows PA194GenericBridge.rowCount l r]
    rw [show sStep (config 194 l r) = config 194 l r from halted actions counts.1 l r]
    simpa only [rhoHalt] using configBounded 194 (by decide) l r hg
  · have qlt : q < 194 := by omega
    let qf : Fin 194 := ⟨q,qlt⟩
    have go (b : Fin 2) (hr : r % 2 = (b.val : V)) :
        ∃ k : Nat, 0 < k ∧ Relation (pStep (config q l r))
          (sStep^[k] (config (rho q) l r)) := by
      obtain ⟨k,hk,hs⟩ := matching qf b l r hr hg
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

#print axioms selectorThree
#print axioms nextRelated
#print axioms segment
end models
end PA194SELSimulation
