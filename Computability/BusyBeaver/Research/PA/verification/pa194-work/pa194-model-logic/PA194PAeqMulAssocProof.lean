import PA194PAeqMulLawsAt
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulAssoc
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped
open PA194PAeq.MulRightZero PA194PAeq.MulCongrTyped PA194PAeq.MulLawsAt
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {Γ : List Fm}

def prop : Semiproposition language 1 := .all (.all
  (eq (mul (mul (.bvar 2) (.bvar 1)) (.bvar 0)) (mul (.bvar 2) (mul (.bvar 1) (.bvar 0)))))
def axioms : List Fm := Distributivity.axioms ++ MulComm.axioms ++ [mulCongruence,inductionFormula prop]

theorem axioms_closed (p : Fm) (hp : p ∈ axioms) : p.freeVariables = ∅ := by
  simp only [axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (h | h) | rfl | rfl
  · exact Distributivity.axioms_closed p h
  · exact MulComm.axioms_closed p h
  all_goals decide

theorem axioms_shift : ND.shifted axioms = axioms := by
  change axioms.map Semiformula.shift = axioms
  calc
    _ = axioms.map id := List.map_congr_left (fun p hp => AddOne.shift_id p (axioms_closed p hp))
    _ = axioms := List.map_id axioms

noncomputable def ihAt (x y z : Tm) (h : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![x]) prop)) :
    ND.Proof Γ (eq (mul (mul x y) z) (mul x (mul y z))) := by
  have h1 := ND.allElim _ y h
  have h2 := ND.allElim _ z h1
  simpa [prop,eq,mul,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift,substShiftTwice] using h2

noncomputable def baseAt (y z : Tm) : ND.Proof axioms
    (eq (mul (mul zero y) z) (mul zero (mul y z))) := by
  have h1 := mulCongrAt (mul zero y) zero z z (Γ := axioms) (by simp [axioms])
    (mulZeroAt y (by simp [axioms,Distributivity.axioms])) (LessCongrTyped.reflAt z (by simp [axioms,Distributivity.axioms,AddLtAdd.axioms]))
  have h2 := mulZeroAt z (Γ := axioms) (by simp [axioms,Distributivity.axioms])
  have h3 := symmAt _ _ (Γ := axioms) (by simp [axioms,Distributivity.axioms,AddLtAdd.axioms])
    (mulZeroAt (mul y z) (by simp [axioms,Distributivity.axioms]))
  exact transAt _ _ _ (by simp [axioms,Distributivity.axioms,AddLtAdd.axioms]) h1
    (transAt _ _ _ (by simp [axioms,Distributivity.axioms,AddLtAdd.axioms]) h2 h3)

noncomputable def stepAt (x y z : Tm) : ND.Proof ((Semiformula.rewAux (Rew.subst ![x]) prop)::axioms)
    (eq (mul (mul (succ x) y) z) (mul (succ x) (mul y z))) := by
  let Δ := (Semiformula.rewAux (Rew.subst ![x]) prop)::axioms
  have ih := ihAt x y z (Γ := Δ) (ND.assumption (by simp [Δ]))
  have hd : ∀ p ∈ Distributivity.axioms, p ∈ Δ := by intro p hp; simp [Δ,axioms,hp]
  have hc : ∀ p ∈ MulComm.axioms, p ∈ Δ := by intro p hp; simp [Δ,axioms,hp]
  have h1 := mulCongrAt (mul (succ x) y) (add y (mul x y)) z z (Γ := Δ) (by simp [Δ,axioms])
    (mulSuccAt x y (by simp [Δ,axioms,Distributivity.axioms])) (LessCongrTyped.reflAt z (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms]))
  have h2 := commAt (add y (mul x y)) z (Γ := Δ) hc
  have h3 := distrAt z y (mul x y) (Γ := Δ) hd
  have h4 := addCongrAt (mul z y) (mul y z) (mul z (mul x y)) (mul (mul x y) z) (Γ := Δ)
    (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms]) (commAt z y hc) (commAt z (mul x y) hc)
  have h5 := addCongrAt (mul y z) (mul y z) (mul (mul x y) z) (mul x (mul y z)) (Γ := Δ)
    (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms]) (LessCongrTyped.reflAt _ (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms])) ih
  have h6 := symmAt _ _ (Γ := Δ) (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms])
    (mulSuccAt x (mul y z) (by simp [Δ,axioms,Distributivity.axioms]))
  exact transAt _ _ _ (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms]) h1
    (transAt _ _ _ (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms]) h2
      (transAt _ _ _ (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms]) h3
        (transAt _ _ _ (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms]) h4
          (transAt _ _ _ (by simp [Δ,axioms,Distributivity.axioms,AddLtAdd.axioms]) h5 h6))))
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
  rcases hp with (h | h) | rfl | rfl
  · exact Distributivity.axioms_mem p h
  · exact MulComm.axioms_mem p h
  · exact ⟨mulCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
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
    (Rewriting.emb PeanoMinus.Axiom.mulAssoc : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb resultSentence : Semiproposition language 0) := by
  change _ = (resultSentence : Proposition language)
  unfold resultSentence
  rw [AddOne.coe_closed _ (by decide)]
  rfl
#print axioms theoryProof
#print axioms source_formula
#print axioms proof
#print axioms inductionStep
#print axioms baseAt
#print axioms stepAt
end PA194PAeq.MulAssoc
