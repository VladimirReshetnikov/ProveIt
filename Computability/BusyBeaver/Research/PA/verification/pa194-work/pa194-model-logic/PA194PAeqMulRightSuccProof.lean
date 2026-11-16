import PA194PAeqAddLtAdd
import PA194PAeqMulRightZeroProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulRightSucc
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped PA194PAeq.AddLawsAt PA194PAeq.MulRightZero
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {Γ : List Fm}

def prop : Semiproposition language 1 := .all
  (eq (mul (.bvar 1) (succ (.bvar 0))) (add (mul (.bvar 1) (.bvar 0)) (.bvar 1)))
def axioms : List Fm := AddLtAdd.axioms ++ [mulZero,mulSucc,inductionFormula prop]
theorem axioms_closed (p : Fm) (hp : p ∈ axioms) : p.freeVariables = ∅ := by
  simp only [axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with h | rfl | rfl | rfl
  · exact AddLtAdd.axioms_closed p h
  all_goals decide

theorem axioms_shift : ND.shifted axioms = axioms := by
  change axioms.map Semiformula.shift = axioms
  calc
    _ = axioms.map id := List.map_congr_left (fun p hp => AddOne.shift_id p (axioms_closed p hp))
    _ = axioms := List.map_id axioms

theorem subset_assoc (p : Fm) (hp : p ∈ AddAssoc.axioms) : p ∈ axioms := by simp [axioms,AddLtAdd.subset_assoc p hp]
theorem subset_comm (p : Fm) (hp : p ∈ AddComm.axioms) : p ∈ axioms := by simp [axioms,AddLtAdd.subset_comm p hp]

noncomputable def ihAt (x y : Tm) (h : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![x]) prop)) :
    ND.Proof Γ (eq (mul x (succ y)) (add (mul x y) x)) := by
  have h1 := ND.allElim _ y h
  simpa [prop,eq,add,mul,succ,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using h1

noncomputable def baseAt (y : Tm) : ND.Proof axioms
    (eq (mul zero (succ y)) (add (mul zero y) zero)) := by
  have h1 := mulZeroAt (succ y) (Γ := axioms) (by simp [axioms])
  have h2 := addCongrAt (mul zero y) zero zero zero (Γ := axioms)
    (by simp [axioms,AddLtAdd.axioms]) (mulZeroAt y (by simp [axioms]))
    (LessCongrTyped.reflAt zero (by simp [axioms,AddLtAdd.axioms]))
  have h3 := addZeroAt zero (Γ := axioms) (by simp [axioms,AddLtAdd.axioms])
  exact transAt _ _ _ (by simp [axioms,AddLtAdd.axioms]) h1
    (symmAt _ _ (by simp [axioms,AddLtAdd.axioms]) (transAt _ _ _ (by simp [axioms,AddLtAdd.axioms]) h2 h3))

noncomputable def stepAt (x y : Tm) : ND.Proof ((Semiformula.rewAux (Rew.subst ![x]) prop)::axioms)
    (eq (mul (succ x) (succ y)) (add (mul (succ x) y) (succ x))) := by
  let Δ := (Semiformula.rewAux (Rew.subst ![x]) prop)::axioms
  have ih := ihAt x y (Γ := Δ) (ND.assumption (by simp [Δ]))
  have h1 := mulSuccAt x (succ y) (Γ := Δ) (by simp [Δ,axioms])
  have h2 := addCongrAt (succ y) (succ y) (mul x (succ y)) (add (mul x y) x) (Γ := Δ)
    (by simp [Δ,axioms,AddLtAdd.axioms]) (LessCongrTyped.reflAt _ (by simp [Δ,axioms,AddLtAdd.axioms])) ih
  have h3 := addSuccAt y (add (mul x y) x) (Γ := Δ) (by simp [Δ,axioms,AddLtAdd.axioms])
  have h4 := succCongrAt _ _ (Γ := Δ) (by simp [Δ,axioms,AddLtAdd.axioms])
    (symmAt _ _ (by simp [Δ,axioms,AddLtAdd.axioms])
      (assocAt y (mul x y) x (by intro p hp; simp [Δ,subset_assoc p hp])))
  have hr0 := AddComm.rightSuccAt (add y (mul x y)) x
  have hr : ND.Proof Δ (eq (add (add y (mul x y)) (succ x)) (succ (add (add y (mul x y)) x))) :=
    ND.weaken hr0 (by intro p hp; simp [Δ,subset_comm p hp])
  have h5 := symmAt _ _ (Γ := Δ) (by simp [Δ,axioms,AddLtAdd.axioms]) hr
  have hm := mulSuccAt x y (Γ := Δ) (by simp [Δ,axioms])
  have h6 := symmAt _ _ (Γ := Δ) (by simp [Δ,axioms,AddLtAdd.axioms])
    (addCongrAt (mul (succ x) y) (add y (mul x y)) (succ x) (succ x)
      (by simp [Δ,axioms,AddLtAdd.axioms]) hm (LessCongrTyped.reflAt _ (by simp [Δ,axioms,AddLtAdd.axioms])))
  exact transAt _ _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h1
    (transAt _ _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h2
      (transAt _ _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h3
        (transAt _ _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h4
          (transAt _ _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h5 h6))))
noncomputable def base : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
  change ND.Proof axioms (.all _)
  apply ND.allIntro
  have h := baseAt (.fvar 0)
  rw [axioms_shift]
  convert h using 1
  simp [prop,eq,add,mul,succ,zero,Semiformula.free,Rewriting.free,Semiformula.rewAux,
    Rew.free,Rew.subst,Rew.func,Rew.q,emptyFn]
  all_goals rfl

noncomputable def inductionStep : ND.Proof axioms
    (.all (implies prop (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop))) := by
  apply ND.allIntro
  rw [axioms_shift]
  change ND.Proof axioms ((prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  change ND.Proof axioms (prop.free 🡒 (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  apply ND.impIntro
  change ND.Proof _ (.all _)
  apply ND.allIntro
  have h := stepAt (.fvar 1) (.fvar 0)
  convert h using 1
  simp [ND.shifted,axioms_shift,prop,eq,add,mul,succ,zero,Semiformula.free,Rewriting.free,
    Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.free,Rew.shift,Rew.map,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · change Semiformula.rewAux _ (Semiformula.rewAux _ _) = _
    simp [Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.shift,Rew.map,emptyFn]
    all_goals rfl
  · exact axioms_shift
  case e'_2 =>
    change Semiformula.rewAux _ (Semiformula.rewAux _ _) = _
    simp [eq,add,mul,succ,Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.subst,emptyFn]
    all_goals rfl

noncomputable def proof : ND.Proof axioms (.all prop) := by
  have ind : ND.Proof axioms (inductionFormula prop) := ND.assumption (by simp [axioms])
  change ND.Proof axioms
    ((Semiformula.rewAux (Rew.subst ![zero]) prop) 🡒
      ((.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) 🡒 .all prop)) at ind
  have st : ND.Proof axioms (.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) := inductionStep
  exact ND.mp st (ND.mp base ind)
#print axioms proof
#print axioms inductionStep
#print axioms baseAt
#print axioms stepAt
end PA194PAeq.MulRightSucc
