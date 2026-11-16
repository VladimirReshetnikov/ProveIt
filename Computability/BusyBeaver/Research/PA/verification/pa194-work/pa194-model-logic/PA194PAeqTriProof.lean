import PA194PAeqTriTransport
import PA194PAeqZeroLeProof
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.TriProof
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped PA194PAeq.TriSucc PA194PAeq.TriTransport
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {Γ : List Fm}
def prop : Semiproposition language 1 := .all (tri (.bvar 1) (.bvar 0))
def axioms : List Fm := AddLtAdd.axioms ++ ZeroLe.axioms ++ [inductionFormula prop]
theorem axioms_closed (p : Fm) (hp : p ∈ axioms) : p.freeVariables = ∅ := by
  simp only [axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (hp | hp) | rfl
  · exact AddLtAdd.axioms_closed p hp
  · simp only [ZeroLe.axioms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  · decide
noncomputable def zeroLeAt (y : Tm) (hax : ∀ p ∈ ZeroLe.axioms, p ∈ Γ) :
    ND.Proof Γ (eq zero y ⋎ less zero y) := by
  have h := ND.allElim _ y (ND.weaken ZeroLe.proof hax)
  convert h using 1
  simp [ZeroLe.prop,less,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift]
  change _ = Semiformula.rewAux _ _
  simp [Semiformula.rewAux,Rew.q,Rew.func,emptyFn,substShift]
  all_goals rfl
noncomputable def ihAt (x y : Tm) (h : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![x]) prop)) :
    ND.Proof Γ (tri x y) := by
  have h1 := ND.allElim _ y h
  have hx : (Rew.subst ![y]).q (Rew.bShift (Rew.bShift x)) = Rew.bShift x := by
    rw [Rew.q_comp_bShift_app]
    simp [substShift]
  simp only [Rew.subst,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hx
  convert h1 using 1
  simp [prop,tri,less,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift]
  all_goals simp [hx] <;> constructor <;> rfl
noncomputable def baseAt (y : Tm) : ND.Proof axioms (tri zero y) := by
  have h := zeroLeAt y (Γ := axioms) (by intro p hp; simp [axioms,hp])
  apply ND.orElim h
  · have he : ND.Proof (eq zero y :: axioms) (eq zero y) := ND.assumption (by simp)
    exact ND.orRight (ND.orLeft he)
  · have hl : ND.Proof (less zero y :: axioms) (less zero y) := ND.assumption (by simp)
    exact ND.orLeft hl
noncomputable def stepAt (x y : Tm) : ND.Proof ((Semiformula.rewAux (Rew.subst ![x]) prop) :: axioms)
    (tri (succ x) y) := by
  let Γ := (Semiformula.rewAux (Rew.subst ![x]) prop) :: axioms
  have h := zeroLeAt y (Γ := Γ) (by intro p hp; simp [Γ,axioms,hp])
  apply ND.orElim h
  · let Δ := eq zero y :: Γ
    have he : ND.Proof Δ (eq zero y) := ND.assumption (by simp [Δ])
    have hz : ND.Proof Δ (less zero (succ x)) := by
      let P : Semiproposition language 1 := eq (add (Rew.bShift zero) (succ (.bvar 0))) (Rew.bShift (succ x))
      change ND.Proof Δ (∃⁰ P)
      apply ND.exsIntro P x
      simpa [P,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using
        (addZeroAt (succ x) (Γ := Δ) (by simp [Δ,Γ,axioms,AddLtAdd.axioms]))
    have hr : ND.Proof Δ (eq (succ x) (succ x)) := reflAt _ (by simp [Δ,Γ,axioms,AddLtAdd.axioms])
    have hy : ND.Proof Δ (less y (succ x)) := lessCongrAt zero (succ x) y (succ x) he hr hz
      (by simp [Δ,Γ,axioms,AddLtAdd.axioms]) (by simp [Δ,Γ,axioms,AddLtAdd.axioms])
      (by simp [Δ,Γ,axioms,AddLtAdd.axioms]) (by simp [Δ,Γ,axioms,AddLtAdd.axioms])
    exact ND.orRight (ND.orRight hy)
  · let Δ := less zero y :: Γ
    let P : Semiproposition language 1 := eq (add (Rew.bShift zero) (succ (.bvar 0))) (Rew.bShift y)
    have hl0 : ND.Proof Δ (less zero y) := ND.assumption (by simp [Δ])
    have hl : ND.Proof Δ (∃⁰ P) := by convert hl0 using 1 <;> rfl
    apply ND.exsElim hl
    let Ψ := P.free :: ND.shifted Δ
    let x' : Tm := Rew.shift x
    let y' : Tm := Rew.shift y
    let v : Tm := .fvar 0
    have hIn (p : Fm) (hm : p ∈ axioms) : p ∈ Ψ := by
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨p,by simp [Δ,Γ,hm],shift_id p (axioms_closed p hm)⟩
    have hfreeShift (t : Tm) : (Rew.bind ![&0] (fun m => &(m+1))) (Rew.bShift t) = Rew.shift t := by
      simpa [Rew.free] using (Rew.free_bShift_app t)
    have hw : ND.Proof Ψ (eq (add zero (succ v)) y') := by
      have hw' : ND.Proof Ψ P.free := ND.assumption (by simp [Ψ])
      simpa [P,y',v,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,zero,emptyFn,substShift,hfreeShift] using hw'
    have hz : ND.Proof Ψ (eq (add zero (succ v)) (succ v)) := addZeroAt _ (hIn _ (by simp [axioms,AddLtAdd.axioms]))
    have he : ND.Proof Ψ (eq (succ v) y') := transAt _ _ _ (hIn _ (by simp [axioms,AddLtAdd.axioms]))
      (symmAt _ _ (hIn _ (by simp [axioms,AddLtAdd.axioms])) hz) hw
    have ihshift : ND.Proof Ψ (Semiformula.rewAux (Rew.subst ![x']) prop) := by
      have hi : ND.Proof Ψ (Semiformula.shift (Semiformula.rewAux (Rew.subst ![x]) prop)) := by
        apply ND.assumption
        change _ ∈ P.free :: ND.shifted Δ
        apply List.mem_cons_of_mem
        exact List.mem_map.mpr ⟨_,by simp [Δ,Γ],rfl⟩
      have hs1 : Rew.shift.q (Rew.bShift x) = Rew.bShift (Rew.shift x) := Rew.q_comp_bShift_app Rew.shift x
      have hs2 : Rew.shift.q.q (Rew.bShift (Rew.bShift x)) = Rew.bShift (Rew.bShift (Rew.shift x)) := by
        rw [Rew.q_comp_bShift_app, Rew.q_comp_bShift_app]
      simp only [Rew.shift,Rew.map,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hs1 hs2
      convert hi using 1
      simp [x',prop,tri,less,eq,add,succ,Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.shift,Rew.map,Rew.subst,Rew.func,Rew.q,emptyFn]
      all_goals simp [hs1,hs2] <;> constructor <;> rfl
    have hit : ND.Proof Ψ (tri x' v) := ihAt x' v ihshift
    have hsucc : ND.Proof Ψ (tri (succ x') (succ v)) := TriSucc.atTerms x' v hit (by intro p hp; exact hIn p (by simp [axioms,hp]))
    have hout : ND.Proof Ψ (tri (succ x') y') := TriTransport.transport _ _ _ hsucc he
      (hIn _ (by simp [axioms,AddLtAdd.axioms])) (hIn _ (by simp [axioms,AddLtAdd.axioms]))
      (hIn _ (by simp [axioms,AddLtAdd.axioms])) (hIn _ (by simp [axioms,AddLtAdd.axioms]))
    have hshift (t : Tm) : (Rew.shift.q) (Rew.bShift t) = Rew.bShift (Rew.shift t) := Rew.q_comp_bShift_app Rew.shift t
    simp only [Rew.shift,Rew.map,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hshift
    change ND.Proof Ψ (Semiformula.rewAux Rew.shift (tri (succ x) y))
    convert hout using 1
    simp [x',y',tri,less,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func,Rew.q,eq,add,succ,emptyFn,hshift]
    all_goals constructor <;> rfl
theorem axioms_shift : ND.shifted axioms = axioms := by
  change axioms.map Semiformula.shift = axioms
  calc
    _ = axioms.map id := List.map_congr_left (fun p hp => shift_id p (axioms_closed p hp))
    _ = axioms := List.map_id axioms
noncomputable def base : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
  change ND.Proof axioms (.all _)
  apply ND.allIntro
  have h := baseAt (.fvar 0)
  rw [axioms_shift]
  convert h using 1
  simp [prop,tri,less,eq,add,succ,zero,Semiformula.free,Rewriting.free,Semiformula.rewAux,
    Rew.free,Rew.subst,Rew.func,Rew.q,emptyFn]
  all_goals repeat' constructor <;> rfl
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
  simp [ND.shifted,axioms_shift,prop,tri,less,eq,add,succ,zero,Semiformula.free,Rewriting.free,
    Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.free,Rew.shift,Rew.map,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · change Semiformula.rewAux _ (Semiformula.rewAux _ _) = _
    simp [Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.shift,Rew.map,emptyFn]
    all_goals repeat' constructor <;> rfl
  · exact axioms_shift
  case e'_2 =>
    change Semiformula.rewAux _ (Semiformula.rewAux _ _) = _
    simp [tri,less,eq,add,succ,Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.subst,emptyFn]
    all_goals repeat' constructor <;> rfl
noncomputable def proof : ND.Proof axioms (.all prop) := by
  have ind : ND.Proof axioms (inductionFormula prop) := ND.assumption (by simp [axioms])
  change ND.Proof axioms
    ((Semiformula.rewAux (Rew.subst ![zero]) prop) 🡒
      ((.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) 🡒 .all prop)) at ind
  exact ND.mp inductionStep (ND.mp base ind)
theorem axioms_mem (p : Fm) (hp : p ∈ axioms) : p.univCl ∈ ordinaryPAeq := by
  simp only [axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (hp | hp) | rfl
  · exact AddLtAdd.axioms_mem p hp
  · simp only [ZeroLe.axioms,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨reflexivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
    · exact ⟨inductionFormula ZeroLe.prop,.induction ZeroLe.prop,rfl⟩
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
        _ = axioms.map id := List.map_congr_left (fun p hp => coe_closed p (axioms_closed p hp))
        _ = axioms := List.map_id axioms
    change ND.Proof (List.map (fun (φ : Sentence language) => (φ : Proposition language)) A) (resultSentence : Proposition language)
    rw [hmap]
    simpa [resultSentence,coe_closed _ he] using proof
  · intro φ hφ
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hφ
    exact axioms_mem p hp

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.ltTri : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb resultSentence : Semiproposition language 0) := by
  change _ = (resultSentence : Proposition language)
  unfold resultSentence
  rw [coe_closed _ (by decide)]
  rfl
#print axioms proof
#print axioms theoryProof
#print axioms source_formula
end PA194PAeq.TriProof
