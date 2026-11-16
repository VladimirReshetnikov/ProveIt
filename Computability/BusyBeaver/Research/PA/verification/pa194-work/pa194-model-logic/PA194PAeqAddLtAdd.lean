import PA194PAeqAddLawsAt
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.AddLtAdd
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped PA194PAeq.AddLawsAt
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def axioms : List Fm := [addZero,addSucc,addCongruence,reflexivity,symmetry,transitivity,succCongruence,
  inductionFormula AddAssoc.prop,inductionFormula AddRightZero.prop,inductionFormula AddRightSucc.prop,inductionFormula AddComm.prop]
theorem axioms_closed (p : Fm) (hp : p ∈ axioms) : p.freeVariables = ∅ := by
  simp only [axioms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem subset_assoc (p : Fm) (hp : p ∈ AddAssoc.axioms) : p ∈ axioms := by
  simp only [AddAssoc.axioms,axioms,List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
  tauto
theorem subset_comm (p : Fm) (hp : p ∈ AddComm.axioms) : p ∈ axioms := by
  simp only [AddComm.axioms,AddRightZero.axioms,AddRightSucc.axioms,axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp ⊢
  tauto

noncomputable def atTerms (a b c : Tm) : ND.Proof axioms (less a b 🡒 less (add a c) (add b c)) := by
  apply ND.impIntro
  let Γ := less a b :: axioms
  let P : Semiproposition language 1 := eq (add (Rew.bShift a) (succ (.bvar 0))) (Rew.bShift b)
  have hp0 : ND.Proof Γ (less a b) := ND.assumption (by simp [Γ])
  have hp : ND.Proof Γ (∃⁰ P) := by convert hp0 using 1 <;> rfl
  apply ND.exsElim hp
  let Δ := P.free :: ND.shifted Γ
  let a' : Tm := Rew.shift a
  let b' : Tm := Rew.shift b
  let c' : Tm := Rew.shift c
  let witness : Tm := .fvar 0
  have hIn (p : Fm) (hm : p ∈ axioms) : p ∈ Δ := by
    have hγ : p ∈ Γ := by simp [Γ,hm]
    change p ∈ P.free :: ND.shifted Γ
    apply List.mem_cons_of_mem
    exact List.mem_map.mpr ⟨p,hγ,shift_id p (axioms_closed p hm)⟩
  have hfreeShift (t : Tm) :
      (Rew.bind ![&0] (fun m => &(m+1))) (Rew.bShift t) = Rew.shift t := by
    simpa [Rew.free] using (Rew.free_bShift_app t)
  have hw : ND.Proof Δ (eq (add a' (succ witness)) b') := by
    have h : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    simpa [P,a',b',witness,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,emptyFn,substShift,hfreeShift] using h
  have hAssoc : ∀ p ∈ AddAssoc.axioms, p ∈ Δ := fun p hp => hIn p (subset_assoc p hp)
  have hComm : ∀ p ∈ AddComm.axioms, p ∈ Δ := fun p hp => hIn p (subset_comm p hp)
  have h1 : ND.Proof Δ (eq (add (add a' c') (succ witness)) (add (add a' (succ witness)) c')) :=
    swapMiddle a' c' (succ witness) hAssoc hComm (hIn _ (by simp [axioms])) (hIn _ (by simp [axioms]))
      (hIn _ (by simp [axioms])) (hIn _ (by simp [axioms]))
  have h2 : ND.Proof Δ (eq (add (add a' (succ witness)) c') (add b' c')) :=
    addCongrAt _ _ _ _ (hIn _ (by simp [axioms])) hw (reflAt c' (hIn _ (by simp [axioms])))
  have he : ND.Proof Δ (eq (add (add a' c') (succ witness)) (add b' c')) :=
    transAt _ _ _ (hIn _ (by simp [axioms])) h1 h2
  let Q : Semiproposition language 1 := eq (add (Rew.bShift (add a' c')) (succ (.bvar 0))) (Rew.bShift (add b' c'))
  have hq : ND.Proof Δ (∃⁰ Q) := by
    apply ND.exsIntro Q witness
    simpa [Q,eq,add,succ,Semiformula.rewAux,Rew.subst,Rew.func,emptyFn,substShift] using he
  have hshift (t : Tm) : (Rew.shift.q) (Rew.bShift t) = Rew.bShift (Rew.shift t) := by exact Rew.q_comp_bShift_app Rew.shift t
  simp only [Rew.shift,Rew.map,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hshift
  change ND.Proof Δ (Semiformula.rewAux Rew.shift (less (add a c) (add b c)))
  simpa [Δ,Q,a',b',c',P,less,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func,Rew.q,eq,add,succ,emptyFn,hshift] using hq
theorem axioms_shift : ND.shifted axioms = axioms := by
  change axioms.map Semiformula.shift = axioms
  calc
    _ = axioms.map id := List.map_congr_left (fun p hp => shift_id p (axioms_closed p hp))
    _ = axioms := List.map_id axioms

def body : Semiproposition language 3 := less (.bvar 2) (.bvar 1) 🡒
  less (add (.bvar 2) (.bvar 0)) (add (.bvar 1) (.bvar 0))
def expected : Proposition language := .all (.all (.all body))

theorem source_normalized : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.addLtAdd : ArithmeticSemiformula ℕ 0) = expected := by rfl

noncomputable def certificate : ND.Proof axioms expected := by
  unfold expected
  apply ND.allIntro
  apply ND.allIntro
  apply ND.allIntro
  have h := atTerms (.fvar 2) (.fvar 1) (.fvar 0)
  simp only [ND.shifted,List.map_cons,List.map_nil]
  change ND.Proof (ND.shifted (ND.shifted (ND.shifted axioms))) _
  rw [axioms_shift,axioms_shift,axioms_shift]
  convert h using 1
  simp [body,less,eq,add,succ,zero,Semiformula.free,Rewriting.free,Semiformula.imp_eq,
    Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor <;> rfl

theorem axioms_mem (p : Fm) (hp : p ∈ axioms) : p.univCl ∈ ordinaryPAeq := by
  simp only [axioms,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨reflexivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨symmetry,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨succCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula AddAssoc.prop,.induction AddAssoc.prop,rfl⟩
  · exact ⟨inductionFormula AddRightZero.prop,.induction AddRightZero.prop,rfl⟩
  · exact ⟨inductionFormula AddRightSucc.prop,.induction AddRightSucc.prop,rfl⟩
  · exact ⟨inductionFormula AddComm.prop,.induction AddComm.prop,rfl⟩

def targetSentence : Sentence language := expected.univCl
noncomputable def theoryProof : ordinaryPAeq.Proof targetSentence := by
  let A : List (Sentence language) := axioms.map Semiformula.univCl
  apply ND.listTheoryProof (A := A)
  · have he : expected.freeVariables = ∅ := by decide
    have hmap : List.map (fun (φ : Sentence language) => (φ : Proposition language)) A = axioms := by
      change List.map (fun (φ : Sentence language) => (φ : Proposition language)) (axioms.map Semiformula.univCl) = axioms
      rw [List.map_map]
      calc
        _ = axioms.map id := List.map_congr_left (fun p hp => coe_closed p (axioms_closed p hp))
        _ = axioms := List.map_id axioms
    change ND.Proof (List.map (fun (φ : Sentence language) => (φ : Proposition language)) A) (targetSentence : Proposition language)
    rw [hmap]
    simpa [targetSentence,coe_closed _ he] using certificate
  · intro φ hφ
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hφ
    exact axioms_mem p hp

theorem source_formula : PA194PAeq.formula
    (Rewriting.emb PeanoMinus.Axiom.addLtAdd : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb targetSentence : Semiproposition language 0) := by
  change _ = (targetSentence : Proposition language)
  unfold targetSentence
  rw [coe_closed _ (by decide)]
  exact source_normalized
#print axioms source_formula
#print axioms theoryProof
#print axioms certificate
#print axioms atTerms
end PA194PAeq.AddLtAdd
