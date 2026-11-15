import PA194PAeqEqRelExt
import PA194PAeqAddOneProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddRightSucc
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.EqRelExt
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {Γ : List Fm}

def prop : Semiproposition language 1 := .all
  (eq (add (.bvar 1) (succ (.bvar 0))) (succ (add (.bvar 1) (.bvar 0))))
def axioms : List Fm := [addZero,addSucc,symmetry,transitivity,succCongruence,inductionFormula prop]

noncomputable def ihAt (x y : Tm) (h : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![x]) prop)) :
    ND.Proof Γ (eq (add x (succ y)) (succ (add x y))) := by
  have h1 := ND.allElim _ y h
  simpa [prop,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using h1

noncomputable def baseAt (y : Tm) : ND.Proof axioms
    (eq (add zero (succ y)) (succ (add zero y))) := by
  have h1 := addZeroAt (succ y) (Γ := axioms) (by simp [axioms])
  have h2 := succCongrAt _ _ (Γ := axioms) (by simp [axioms]) (addZeroAt y (by simp [axioms]))
  exact transAt _ _ _ (by simp [axioms]) h1 (symmAt _ _ (by simp [axioms]) h2)

noncomputable def stepAt (x y : Tm) : ND.Proof ((Semiformula.rewAux (Rew.subst ![x]) prop)::axioms)
    (eq (add (succ x) (succ y)) (succ (add (succ x) y))) := by
  let Δ := (Semiformula.rewAux (Rew.subst ![x]) prop)::axioms
  have ih : ND.Proof Δ (eq (add x (succ y)) (succ (add x y))) := ihAt x y (ND.assumption (by simp [Δ]))
  have h1 := addSuccAt x (succ y) (Γ := Δ) (by simp [Δ,axioms])
  have h2 := succCongrAt _ _ (Γ := Δ) (by simp [Δ,axioms]) ih
  have h3 := succCongrAt _ _ (Γ := Δ) (by simp [Δ,axioms]) (addSuccAt x y (by simp [Δ,axioms]))
  exact transAt _ _ _ (by simp [Δ,axioms]) h1
    (transAt _ _ _ (by simp [Δ,axioms]) h2 (symmAt _ _ (by simp [Δ,axioms]) h3))

theorem axioms_shift : ND.shifted axioms = axioms := by
  have h1 : addZero.freeVariables = ∅ := by decide
  have h2 : addSucc.freeVariables = ∅ := by decide
  have h3 : symmetry.freeVariables = ∅ := by decide
  have h4 : transitivity.freeVariables = ∅ := by decide
  have h5 : succCongruence.freeVariables = ∅ := by decide
  have h6 : (inductionFormula prop).freeVariables = ∅ := by decide
  simp [ND.shifted,axioms,shift_id _ h1,shift_id _ h2,shift_id _ h3,shift_id _ h4,shift_id _ h5,shift_id _ h6]

noncomputable def base : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
  change ND.Proof axioms (.all _)
  apply ND.allIntro
  have h := baseAt (.fvar 0)
  rw [axioms_shift]
  convert h using 1
  simp [prop,eq,add,succ,zero,Semiformula.free,Rewriting.free,Semiformula.rewAux,
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
  simp [ND.shifted,axioms_shift,prop,eq,add,succ,zero,Semiformula.free,Rewriting.free,
    Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.free,Rew.shift,Rew.map,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · change Semiformula.rewAux _ (Semiformula.rewAux _ _) = _
    simp [Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.shift,Rew.map,emptyFn]
    all_goals rfl
  · exact axioms_shift
  case e'_2 =>
    change Semiformula.rewAux _ (Semiformula.rewAux _ _) = _
    simp [eq,add,succ,Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.subst,emptyFn]
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
end PA194PAeq.AddRightSucc
