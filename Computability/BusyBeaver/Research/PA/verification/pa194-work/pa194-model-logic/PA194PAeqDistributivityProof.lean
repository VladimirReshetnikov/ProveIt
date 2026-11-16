import PA194PAeqAddShuffle
import PA194PAeqAddLtAdd
import PA194PAeqMulRightZeroProof
import PA194PAeqAddCongrAtTyped
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.Distributivity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.MulRightZero PA194PAeq.AddLawsAt
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {Γ : List Fm}

def prop : Semiproposition language 1 := .all (.all
  (eq (mul (.bvar 2) (add (.bvar 1) (.bvar 0)))
    (add (mul (.bvar 2) (.bvar 1)) (mul (.bvar 2) (.bvar 0)))))
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

theorem subset_assoc (p : Fm) (hp : p ∈ AddAssoc.axioms) : p ∈ axioms := by
  simp [axioms,AddLtAdd.subset_assoc p hp]
theorem subset_comm (p : Fm) (hp : p ∈ AddComm.axioms) : p ∈ axioms := by
  simp [axioms,AddLtAdd.subset_comm p hp]

noncomputable def ihAt (x y z : Tm) (h : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![x]) prop)) :
    ND.Proof Γ (eq (mul x (add y z)) (add (mul x y) (mul x z))) := by
  have h1 := ND.allElim _ y h
  have h2 := ND.allElim _ z h1
  simpa [prop,eq,add,mul,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift,substShiftTwice] using h2

noncomputable def baseAt (y z : Tm) : ND.Proof axioms
    (eq (mul zero (add y z)) (add (mul zero y) (mul zero z))) := by
  have h1 := mulZeroAt (add y z) (Γ := axioms) (by simp [axioms])
  have h2 := addCongrAt (mul zero y) zero (mul zero z) zero (Γ := axioms)
    (by simp [axioms,AddLtAdd.axioms]) (mulZeroAt y (by simp [axioms])) (mulZeroAt z (by simp [axioms]))
  have h3 := addZeroAt zero (Γ := axioms) (by simp [axioms,AddLtAdd.axioms])
  exact transAt _ _ _ (by simp [axioms,AddLtAdd.axioms]) h1
    (symmAt _ _ (by simp [axioms,AddLtAdd.axioms]) (transAt _ _ _ (by simp [axioms,AddLtAdd.axioms]) h2 h3))

noncomputable def stepAt (x y z : Tm) : ND.Proof ((Semiformula.rewAux (Rew.subst ![x]) prop)::axioms)
    (eq (mul (succ x) (add y z)) (add (mul (succ x) y) (mul (succ x) z))) := by
  let Δ := (Semiformula.rewAux (Rew.subst ![x]) prop)::axioms
  have ih : ND.Proof Δ (eq (mul x (add y z)) (add (mul x y) (mul x z))) :=
    ihAt x y z (ND.assumption (by simp [Δ]))
  have h1 := mulSuccAt x (add y z) (Γ := Δ) (by simp [Δ,axioms])
  have h2 := addCongrAt (add y z) (add y z) (mul x (add y z)) (add (mul x y) (mul x z)) (Γ := Δ)
    (by simp [Δ,axioms,AddLtAdd.axioms]) (LessCongrTyped.reflAt _ (by simp [Δ,axioms,AddLtAdd.axioms])) ih
  have h3 := shuffle y z (mul x y) (mul x z) (Γ := Δ)
    (by intro p hp; simp [Δ,subset_assoc p hp]) (by intro p hp; simp [Δ,subset_comm p hp])
    (by simp [Δ,axioms,AddLtAdd.axioms]) (by simp [Δ,axioms,AddLtAdd.axioms])
    (by simp [Δ,axioms,AddLtAdd.axioms]) (by simp [Δ,axioms,AddLtAdd.axioms])
  have h4 := addCongrAt (mul (succ x) y) (add y (mul x y)) (mul (succ x) z) (add z (mul x z)) (Γ := Δ)
    (by simp [Δ,axioms,AddLtAdd.axioms]) (mulSuccAt x y (by simp [Δ,axioms])) (mulSuccAt x z (by simp [Δ,axioms]))
  exact transAt _ _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h1
    (transAt _ _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h2
      (transAt _ _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h3 (symmAt _ _ (by simp [Δ,axioms,AddLtAdd.axioms]) h4)))

noncomputable def base : ND.Proof axioms (Semiformula.rewAux (Rew.subst ![zero]) prop) := by
  change ND.Proof axioms (.all _)
  apply ND.allIntro
  change ND.Proof _ (.all _)
  apply ND.allIntro
  have h := baseAt (.fvar 1) (.fvar 0)
  rw [axioms_shift,axioms_shift]
  convert h using 1
  simp [prop,eq,add,zero,Semiformula.free,Rewriting.free,Semiformula.rewAux,
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
  change ND.Proof _ (.all _)
  apply ND.allIntro
  have h := stepAt (.fvar 2) (.fvar 1) (.fvar 0)
  convert h using 1
  simp [ND.shifted,axioms_shift,prop,eq,add,mul,succ,zero,Semiformula.free,Rewriting.free,
    Semiformula.shift,Rewriting.shift,Semiformula.rewAux,Rew.free,Rew.shift,Rew.map,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · change Semiformula.rewAux _ (Semiformula.rewAux _ (Semiformula.rewAux _ _)) = _
    simp [Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.shift,Rew.map,emptyFn]
    all_goals rfl
  · change ND.shifted (ND.shifted axioms) = axioms
    rw [axioms_shift,axioms_shift]
  case e'_2 =>
    change Semiformula.rewAux _ (Semiformula.rewAux _ (Semiformula.rewAux _ _)) = _
    simp [eq,add,mul,succ,Semiformula.rewAux,Rew.q,Rew.func,Rew.free,Rew.subst,emptyFn]
    all_goals rfl

noncomputable def proof : ND.Proof axioms (.all prop) := by
  have ind : ND.Proof axioms (inductionFormula prop) := ND.assumption (by simp [axioms])
  change ND.Proof axioms
    ((Semiformula.rewAux (Rew.subst ![zero]) prop) 🡒
      ((.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) 🡒 .all prop)) at ind
  have st : ND.Proof axioms (.all (prop 🡒 Semiformula.rewAux (Rew.subst ![succ (.bvar 0)]) prop)) := inductionStep
  exact ND.mp st (ND.mp base ind)

theorem axioms_mem (p : Fm) (hp : p ∈ axioms) : p.univCl ∈ ordinaryPAeq := by
  simp only [axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with h | rfl | rfl | rfl
  · exact AddLtAdd.axioms_mem p h
  · exact ⟨mulZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨mulSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
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
    (Rewriting.emb PeanoMinus.Axiom.distr : ArithmeticSemiformula ℕ 0) =
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
end PA194PAeq.Distributivity
