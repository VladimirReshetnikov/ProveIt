import PA194PAeqOneLeSuccProof
import PA194PAeqLeTransport
import PA194PAeqQuoteProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.OneLeOfZeroLt
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeq.AddOne PA194PAeq.EqRelExt PA194PAeq.LeTransport
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩

def axioms : List Fm := OneLeSucc.axioms ++ [addCongruence,symmetry]
theorem axioms_closed (p : Fm) (hp : p ∈ axioms) : p.freeVariables = ∅ := by
  simp only [axioms,OneLeSucc.axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl <;> decide

noncomputable def helperAt (y : Tm) {Γ : List Fm} (hΓ : ∀ p ∈ OneLeSucc.axioms, p ∈ Γ) :
    ND.Proof Γ (le (succ zero) (succ y)) := by
  have h : ND.Proof Γ (.all OneLeSucc.prop) := ND.weaken OneLeSucc.proof hΓ
  have e := ND.allElim _ y h
  convert e using 1
  simp [OneLeSucc.prop,le,less,eq,add,succ,zero,Semiformula.rewAux,Rew.subst,Rew.func,Rew.q,emptyFn,substShift]
  change _ = Semiformula.rewAux _ _
  simp [Semiformula.rewAux,Rew.q,Rew.func,emptyFn,substShift]
  all_goals rfl

noncomputable def atTerm (x : Tm) : ND.Proof axioms (less zero x 🡒 le (succ zero) x) := by
  apply ND.impIntro
  let Γ := less zero x :: axioms
  let P : Semiproposition language 1 := eq (add (Rew.bShift zero) (succ (.bvar 0))) (Rew.bShift x)
  have hp0 : ND.Proof Γ (less zero x) := ND.assumption (by simp [Γ])
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
  have hw : ND.Proof Δ (eq (add zero (succ witness)) x') := by
    have h : ND.Proof Δ P.free := ND.assumption (by simp [Δ])
    simpa [P,x',witness,Semiformula.free,Rewriting.free,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,eq,add,succ,zero,emptyFn,substShift,hfreeShift] using h
  have hzero : ND.Proof Δ (eq (add zero (succ witness)) (succ witness)) :=
    addZeroAt (succ witness) (hIn _ (by simp [axioms,OneLeSucc.axioms]))
  have hEq : ND.Proof Δ (eq (succ witness) x') :=
    transAt _ _ _ (hIn _ (by simp [axioms,OneLeSucc.axioms]))
      (symmAt _ _ (hIn _ (by simp [axioms,OneLeSucc.axioms])) hzero) hw
  have hle : ND.Proof Δ (le (succ zero) (succ witness)) :=
    helperAt witness (by intro p hp; exact hIn p (by simp [axioms,hp]))
  have hres : ND.Proof Δ (le (succ zero) x') := transport (succ zero) (succ witness) x' hle hEq
    (hIn _ (by simp [axioms,OneLeSucc.axioms])) (hIn _ (by simp [axioms,OneLeSucc.axioms]))
    (hIn _ (by simp [axioms,OneLeSucc.axioms])) (hIn _ (by simp [axioms,OneLeSucc.axioms]))
  have hshift (t : Tm) : (Rew.shift.q) (Rew.bShift t) = Rew.bShift (Rew.shift t) := by exact Rew.q_comp_bShift_app Rew.shift t
  simp only [Rew.shift,Rew.map,Rew.q,emptyFn,Matrix.vecCons_empty_eq_singleton] at hshift
  change ND.Proof Δ (Semiformula.rewAux Rew.shift (le (succ zero) x))
  convert hres using 1
  simp [Δ,P,x',le,less,Semiformula.rewAux,Rew.shift,Rew.map,Rew.func,Rew.q,eq,add,succ,zero,emptyFn,hshift]
  all_goals rfl
theorem axioms_shift : ND.shifted axioms = axioms := by
  change axioms.map Semiformula.shift = axioms
  calc
    _ = axioms.map id := List.map_congr_left (fun p hp => shift_id p (axioms_closed p hp))
    _ = axioms := List.map_id axioms

def prop : Semiproposition language 1 :=
  less zero (.bvar 0) 🡒 (eq (succ zero) (.bvar 0) ⋎ less (succ zero) (.bvar 0))
def expected : Proposition language := .all prop

noncomputable def certificate : ND.Proof axioms expected := by
  unfold expected
  apply ND.allIntro
  rw [axioms_shift]
  have h := atTerm (.fvar 0)
  convert h using 1
  simp [prop,le,less,eq,add,succ,zero,Semiformula.free,Rewriting.free,Semiformula.imp_eq,
    Semiformula.neg_eq,Semiformula.neg,Semiformula.rewAux,Rew.free,Rew.subst,Rew.func,Rew.q,emptyFn]
  constructor
  · change Semiformula.rewAux _ _ = _
    simp [Semiformula.rewAux,Rew.q,Rew.func,emptyFn]
    all_goals rfl
  · change Semiformula.rewAux _ _ = _
    simp [Semiformula.rewAux,Rew.q,Rew.func,emptyFn]
    all_goals rfl

theorem axioms_mem (p : Fm) (hp : p ∈ axioms) : p.univCl ∈ ordinaryPAeq := by
  simp only [axioms,OneLeSucc.axioms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl | rfl
  · exact ⟨addZero,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨addSucc,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨reflexivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨transitivity,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨succCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨inductionFormula OneLeSucc.prop,.induction OneLeSucc.prop,rfl⟩
  · exact ⟨addCongruence,.fixed _ (by simp [fixedAxioms]),rfl⟩
  · exact ⟨symmetry,.fixed _ (by simp [fixedAxioms]),rfl⟩

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
    (Rewriting.emb PeanoMinus.Axiom.oneLeOfZeroLt : ArithmeticSemiformula ℕ 0) =
    (Rewriting.emb targetSentence : Semiproposition language 0) := by
  change _ = (targetSentence : Proposition language)
  unfold targetSentence
  rw [coe_closed _ (by decide)]
  rfl
#print axioms source_formula
#print axioms theoryProof
#print axioms atTerm
end PA194PAeq.OneLeOfZeroLt
