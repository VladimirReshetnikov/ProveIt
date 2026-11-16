import PA194PAeqMulRightSuccProof
import PA194PAeqMulRightZeroProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulComm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.AddLawsAt
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def prop : Semiproposition language 1 := .all (eq (mul (.bvar 1) (.bvar 0)) (mul (.bvar 0) (.bvar 1)))
def axioms : List Fm := MulRightZero.axioms ++ MulRightSucc.axioms ++ [inductionFormula prop]

noncomputable def rightZeroAt (y : Tm) : ND.Proof axioms (eq (mul y zero) zero) := by
  have h : ND.Proof axioms (.all MulRightZero.prop) :=
    ND.weaken MulRightZero.mulRightZeroProof (by intro p hp; simp [axioms,hp])
  have e := ND.allElim _ y h
  simpa [MulRightZero.prop,eq,mul,zero,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn] using e

noncomputable def rightSuccAt (y x : Tm) : ND.Proof axioms (eq (mul y (succ x)) (add (mul y x) y)) := by
  have h : ND.Proof axioms (.all MulRightSucc.prop) :=
    ND.weaken MulRightSucc.proof (by intro p hp; simp [axioms,hp])
  have h1 := ND.allElim _ y h
  have h2 := ND.allElim _ x h1
  simpa [MulRightSucc.prop,eq,add,mul,succ,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using h2

noncomputable def ihAt (x y : Tm) {Γ : List Fm} (h : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![x]) prop)) :
    ND.Proof Γ (eq (mul x y) (mul y x)) := by
  have e := ND.allElim _ y h
  simpa [prop,eq,mul,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift] using e

noncomputable def baseAt (y : Tm) : ND.Proof axioms (eq (mul zero y) (mul y zero)) := by
  have h1 := MulRightZero.mulZeroAt y (Γ := axioms) (by simp [axioms,MulRightZero.axioms,MulRightSucc.axioms,AddLtAdd.axioms])
  have h2 := symmAt _ _ (Γ := axioms) (by simp [axioms,MulRightZero.axioms,MulRightSucc.axioms,AddLtAdd.axioms]) (rightZeroAt y)
  exact transAt _ _ _ (by simp [axioms,MulRightZero.axioms,MulRightSucc.axioms,AddLtAdd.axioms]) h1 h2

noncomputable def stepAt (x y : Tm) : ND.Proof ((Semiformula.rewAux (Rew.subst ![x]) prop)::axioms)
    (eq (mul (succ x) y) (mul y (succ x))) := by
  let Δ := (Semiformula.rewAux (Rew.subst ![x]) prop)::axioms
  have ih : ND.Proof Δ (eq (mul x y) (mul y x)) := ihAt x y (ND.assumption (by simp [Δ]))
  have h1 := MulRightZero.mulSuccAt x y (Γ := Δ) (by simp [Δ,axioms,MulRightZero.axioms,MulRightSucc.axioms,AddLtAdd.axioms])
  have h2 := addCongrAt y y (mul x y) (mul y x) (Γ := Δ)
    (by simp [Δ,axioms,MulRightSucc.axioms,AddLtAdd.axioms])
    (LessCongrTyped.reflAt y (by simp [Δ,axioms,MulRightSucc.axioms,AddLtAdd.axioms])) ih
  have hc : ∀ p ∈ AddComm.axioms, p ∈ Δ := by
    intro p hp
    have hh := MulRightSucc.subset_comm p hp
    simp [Δ,axioms,hh]
  have h3 := commAt y (mul y x) (Γ := Δ) hc
  have hr : ND.Proof Δ (eq (mul y (succ x)) (add (mul y x) y)) :=
    ND.weaken (rightSuccAt y x) (by intro p hp; simp [Δ,hp])
  have h4 := symmAt _ _ (Γ := Δ) (by simp [Δ,axioms,MulRightZero.axioms,MulRightSucc.axioms,AddLtAdd.axioms]) hr
  exact transAt _ _ _ (by simp [Δ,axioms,MulRightZero.axioms,MulRightSucc.axioms,AddLtAdd.axioms]) h1
    (transAt _ _ _ (by simp [Δ,axioms,MulRightZero.axioms,MulRightSucc.axioms,AddLtAdd.axioms]) h2
      (transAt _ _ _ (by simp [Δ,axioms,MulRightZero.axioms,MulRightSucc.axioms,AddLtAdd.axioms]) h3 h4))

theorem axioms_shift : ND.shifted axioms = axioms := by
  have h : (inductionFormula prop).freeVariables = ∅ := by decide
  change ND.shifted (MulRightZero.axioms ++ MulRightSucc.axioms ++ [inductionFormula prop]) = _
  simp only [ND.shifted,List.map_append,List.map_cons,List.map_nil]
  change ND.shifted MulRightZero.axioms ++ ND.shifted MulRightSucc.axioms ++ [(inductionFormula prop).shift] = _
  rw [MulRightZero.axioms_shift,MulRightSucc.axioms_shift,AddOne.shift_id _ h]
  rfl
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
theorem axioms_closed (p : Fm) (hp : p ∈ axioms) : p.freeVariables = ∅ := by
  simp only [axioms,MulRightZero.axioms,MulRightSucc.axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with ((rfl | rfl | rfl | rfl | rfl) | (h | rfl | rfl | rfl)) | rfl
  all_goals try exact AddLtAdd.axioms_closed p h
  all_goals decide

theorem axioms_mem (p : Fm) (hp : p ∈ axioms) : p.univCl ∈ ordinaryPAeq := by
  simp only [axioms,MulRightZero.axioms,MulRightSucc.axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with ((rfl | rfl | rfl | rfl | rfl) | (h | rfl | rfl | rfl)) | rfl
  · exact ⟨mulZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨mulSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula MulRightZero.prop,.induction MulRightZero.prop,rfl⟩
  · exact AddLtAdd.axioms_mem p h
  · exact ⟨mulZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨mulSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula MulRightSucc.prop,.induction MulRightSucc.prop,rfl⟩
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
    (Rewriting.emb PeanoMinus.Axiom.mulComm : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb resultSentence : Semiproposition language 0) := by
  change _ = (resultSentence : Proposition language)
  unfold resultSentence
  rw [AddOne.coe_closed _ (by decide)]
  rfl
#print axioms source_formula
#print axioms theoryProof
#print axioms proof
#print axioms inductionStep
#print axioms baseAt
#print axioms stepAt
end PA194PAeq.MulComm
