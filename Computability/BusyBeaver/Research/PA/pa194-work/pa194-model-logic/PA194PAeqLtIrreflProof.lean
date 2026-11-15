import PA194PAeqLessShift
import PA194PAeqEqRelExt
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.LtIrrefl
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.EqRelExt PA194PAeq.LessShift
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {Γ : List Fm}

def prop : Semiproposition language 1 := ∼ less (.bvar 0) (.bvar 0)
def axioms : List Fm := [addZero,addSucc,symmetry,transitivity,succInjective,zeroNotSucc,inductionFormula prop]
theorem axioms_closed (p : Fm) (hp : p ∈ axioms) : p.freeVariables = ∅ := by
  simp only [axioms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem axioms_shift : ND.shifted axioms = axioms := by
  change axioms.map Semiformula.shift = axioms
  calc
    _ = axioms.map id := List.map_congr_left (fun p hp => shift_id p (axioms_closed p hp))
    _ = axioms := List.map_id axioms

noncomputable def zeroNotSuccAt (t : Tm) (h : zeroNotSucc ∈ Γ) : ND.Proof Γ (∼ eq zero (succ t)) := by
  have d : ND.Proof Γ zeroNotSucc := ND.assumption h
  have e := ND.allElim _ t d
  simpa [zeroNotSucc,eq,zero,succ,Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using e
noncomputable def succInjAt (s t : Tm) (h : succInjective ∈ Γ)
    (d : ND.Proof Γ (eq (succ s) (succ t))) : ND.Proof Γ (eq s t) := by
  have d0 : ND.Proof Γ succInjective := ND.assumption h
  have d1 := ND.allElim _ s d0
  have d2 := ND.allElim _ t d1
  have he : ND.Proof Γ (eq (succ s) (succ t) 🡒 eq s t) := by
    simpa [succInjective,implies,Semiformula.imp_eq,eq,succ,Semiformula.neg_eq,Semiformula.neg,
      Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using d2
  exact ND.mp d he

noncomputable def base : ND.Proof axioms (∼ less zero zero) := by
  apply ND.byContradiction
  change ND.Proof (less zero zero :: axioms) ⊥
  let Γ := less zero zero :: axioms
  let P : Semiproposition language 1 := eq (add (Rew.bShift zero) (succ (.bvar 0))) (Rew.bShift zero)
  have hp0 : ND.Proof Γ (less zero zero) := ND.assumption (by simp [Γ])
  have hp : ND.Proof Γ (∃⁰ P) := by convert hp0 using 1 <;> rfl
  apply ND.exsElim hp
  let Δ := P.free :: ND.shifted Γ
  let witness : Tm := .fvar 0
  have hIn (p : Fm) (hm : p ∈ axioms) : p ∈ Δ := by
    have hγ : p ∈ Γ := by simp [Γ,hm]
    change p ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨p,hγ,shift_id p (axioms_closed p hm)⟩
  have hw : ND.Proof Δ (eq (add zero (succ witness)) zero) := by
    have h : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    simpa [P,witness,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,zero,emptyFn] using h
  have hz := addZeroAt (succ witness) (Γ := Δ) (hIn _ (by simp [axioms]))
  have he : ND.Proof Δ (eq zero (succ witness)) :=
    symmAt _ _ (hIn _ (by simp [axioms])) (transAt _ _ _ (hIn _ (by simp [axioms])) (symmAt _ _ (hIn _ (by simp [axioms])) hz) hw)
  exact ND.contradiction he (zeroNotSuccAt witness (hIn _ (by simp [axioms])))

noncomputable def stepAt (x : Tm) : ND.Proof ((∼less x x)::axioms) (∼ less (succ x) (succ x)) := by
  apply ND.byContradiction
  change ND.Proof (less (succ x) (succ x) :: (∼less x x)::axioms) ⊥
  let Γ := less (succ x) (succ x) :: (∼less x x)::axioms
  let P : Semiproposition language 1 := eq (add (Rew.bShift (succ x)) (succ (.bvar 0))) (Rew.bShift (succ x))
  have hp0 : ND.Proof Γ (less (succ x) (succ x)) := ND.assumption (by simp [Γ])
  have hp : ND.Proof Γ (∃⁰ P) := by convert hp0 using 1 <;> rfl
  apply ND.exsElim hp
  let Δ := P.free :: ND.shifted Γ
  let x' : Tm := Rew.shift x
  let witness : Tm := .fvar 0
  have hIn (p : Fm) (hm : p ∈ axioms) : p ∈ Δ := by
    have hγ : p ∈ Γ := by simp [Γ,hm]
    change p ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨p,hγ,shift_id p (axioms_closed p hm)⟩
  have hfreeShift (t : Tm) :
      (Rew.bind ![&0] (fun m => &(m+1))) (Rew.bShift t) = Rew.shift t := by
    simpa [Rew.free] using (Rew.free_bShift_app t)
  have hw : ND.Proof Δ (eq (add (succ x') (succ witness)) (succ x')) := by
    have h : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    simpa [P,x',witness,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn,substShift,hfreeShift] using h
  have hs := addSuccAt x' (succ witness) (Γ := Δ) (hIn _ (by simp [axioms]))
  have heSucc : ND.Proof Δ (eq (succ (add x' (succ witness))) (succ x')) :=
    transAt _ _ _ (hIn _ (by simp [axioms])) (symmAt _ _ (hIn _ (by simp [axioms])) hs) hw
  have he : ND.Proof Δ (eq (add x' (succ witness)) x') := succInjAt _ _ (hIn _ (by simp [axioms])) heSucc
  let Q : Semiproposition language 1 := eq (add (Rew.bShift x') (succ (.bvar 0))) (Rew.bShift x')
  have hlt : ND.Proof Δ (less x' x') := by
    change ND.Proof Δ (∃⁰ Q)
    apply ND.exsIntro Q witness
    simpa [Q,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using he
  have hnot0 : ND.Proof Γ (∼less x x) := ND.assumption (by simp [Γ])
  have hnot : ND.Proof Δ (∼less x' x') := by
    have h := ND.weaken (ND.shiftProof hnot0) (Δ := Δ) (by intro p hp; simp [Δ,hp])
    simpa [x',Semiformula.shift,Rewriting.shift,Semiformula.rewAux_neg,← Semiformula.neg_eq,shiftLess] using h
  exact ND.contradiction hlt hnot
noncomputable def inductionStep : ND.Proof axioms
    (.all (implies prop (Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop))) := by
  apply ND.allIntro
  rw [axioms_shift]
  change ND.Proof axioms ((prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop).free)
  have d := ND.impIntro (stepAt (.fvar 0))
  convert d using 1
  simp [prop,less,implies,Semiformula.free,Rewriting.free,Semiformula.imp_eq,Semiformula.neg_eq,
    Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,zero,emptyFn,substShift,Rewriting.app,Semiformula.rew]
  constructor
  · change Semiformula.rewAux _ _ = _
    simp [Semiformula.rewAux,Rew.func,Rew.q,emptyFn]
    all_goals rfl
  · change Semiformula.rewAux _ _ = _
    simp [Semiformula.rewAux,Rew.func,Rew.q,emptyFn]
    all_goals rfl
noncomputable def proof : ND.Proof axioms (.all prop) := by
  have ind : ND.Proof axioms (inductionFormula prop) := ND.assumption (by simp [axioms])
  change ND.Proof axioms
    ((Semiformula.rewAux (Rew.subst ![zero]) prop) 🡒
      ((.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) 🡒 .all prop)) at ind
  have b : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
    convert base using 1
    simp [prop,less,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,Rewriting.app,Semiformula.rew]
    simp [Semiformula.rewAux_neg,Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.q,Rew.func,emptyFn]
    all_goals rfl
  have st : ND.Proof axioms (.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) := inductionStep
  exact ND.mp st (ND.mp b ind)
theorem axioms_mem (p : Fm) (hp : p ∈ axioms) : p.univCl ∈ ordinaryPAeq := by
  simp only [axioms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨symmetry,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨succInjective,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨zeroNotSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula prop,.induction prop,rfl⟩

def resultSentence : Sentence language := (Semiformula.all prop).univCl
noncomputable def theoryProof : ordinaryPAeq.Proof resultSentence := by
  let A : List (Sentence language) := axioms.map Semiformula.univCl
  apply ND.listTheoryProof (A := A)
  · have he : (Semiformula.all prop).freeVariables = ∅ := by decide
    have hmap : List.map (fun (φ : Sentence language) => (φ : Proposition language)) A = axioms := by
      change List.map (fun (φ : Sentence language) => (φ : Proposition language)) (axioms.map Semiformula.univCl) = axioms
      rw [List.map_map]
      calc
        _ = axioms.map id := List.map_congr_left (fun p hp => AddOne.coe_closed p (axioms_closed p hp))
        _ = axioms := List.map_id axioms
    change ND.Proof (List.map (fun (φ : Sentence language) => (φ : Proposition language)) A) (resultSentence : Proposition language)
    rw [hmap]
    simpa [resultSentence,AddOne.coe_closed _ he] using proof
  · intro φ hφ
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hφ
    exact axioms_mem p hp

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.ltIrrefl : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb resultSentence : Semiproposition language 0) := by
  change _ = (resultSentence : Proposition language)
  unfold resultSentence
  rw [AddOne.coe_closed _ (by decide)]
  rfl
#print axioms source_formula
#print axioms theoryProof
#print axioms proof
#print axioms inductionStep
#print axioms base
#print axioms stepAt
end PA194PAeq.LtIrrefl
