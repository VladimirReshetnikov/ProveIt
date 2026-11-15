import PA194PAeqQuadSpecialization
import PA194PAeqReflexivityAt
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.MulCongruenceInternal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqSpecialization PA194PAeqQuadSpecialization
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

def body : Semiproposition language 4 :=
  implies (eq (.bvar 0) (.bvar 1)) (implies (eq (.bvar 2) (.bvar 3)) (eq (mul (.bvar 0) (.bvar 2)) (mul (.bvar 1) (.bvar 3))))
theorem source_mem : mulCongruence.univCl ∈ ordinaryPAeq :=
  ⟨mulCongruence, .fixed _ (by simp [fixedAxioms]), rfl⟩
theorem source_quote : (⌜mulCongruence.univCl⌝ : V) = ^∀ ^∀ ^∀ ^∀ (⌜body⌝ : V) := by
  have h : mulCongruence.freeVariables = ∅ := by decide
  rw [Sentence.quote_def]
  rw [show (mulCongruence.univCl : AddOne.Fm) = mulCongruence from AddOne.coe_closed _ h]
  change (⌜(Semiformula.all (Semiformula.all (Semiformula.all (Semiformula.all body))))⌝ : V) = _
  rfl

noncomputable def atTerms (t u v w : Term V language) :
    (ordinaryPAeq.internalize V) ⊢! (⌜body⌝ : Semiformula V language 4).subst ![t,u,v,w] := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let p : Semiformula V language 4 := ⌜body⌝
  have hd : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ p) ∅ := by
    refine ⟨axm {⌜mulCongruence.univCl⌝} ⌜mulCongruence.univCl⌝, ?_⟩
    have h := (target_axiom_witness ordinaryPAeq mulCongruence.univCl source_mem :
      Proof ordinaryPAeq (axm {⌜mulCongruence.univCl⌝} ⌜mulCongruence.univCl⌝ : V) ⌜mulCongruence.univCl⌝)
    simpa [T,p,source_quote,Proof,Semiformula.quote_def,← singleton_eq_insert] using h
  exact paeqQuadProof T ∅ p t u v w hd

noncomputable def atTermsCode (t u v w : V) : V :=
  paeqQuadCode (⌜body⌝ : V) t u v w 0 (axm {⌜mulCongruence.univCl⌝} ⌜mulCongruence.univCl⌝)

theorem atTerms_val (t u v w : Term V language) : (atTerms t u v w).val = atTermsCode t.val u.val v.val w.val := by
  simp [atTerms,atTermsCode,paeqQuadProof_val,Semiformula.quote_def,← emptyset_def]

theorem atTermsCode_valid {t u v w : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) (hv : IsSemiterm language 0 v) (hw : IsSemiterm language 0 w) :
    letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
    Proof ordinaryPAeq (atTermsCode t u v w) (subst language (t∷(u∷(v∷(w∷0)))) (⌜body⌝ : V)) := by
  letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
  let tt : Term V language := ⟨t,ht⟩
  let uu : Term V language := ⟨u,hu⟩
  let vv : Term V language := ⟨v,hv⟩
  let ww : Term V language := ⟨w,hw⟩
  have h := (atTerms tt uu vv ww).derivationOf
  simpa [atTerms_val, atTermsCode, tt, uu, vv, ww, Proof, Semiformula.quote_def,
    SemitermVec.val_succ, ← singleton_eq_insert] using h

noncomputable def atTermsGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out t u v w. ∃ a s d,
    a = ↑(Encodable.encode mulCongruence.univCl) ∧ !insertDef s a 0 ∧ !axmGraph d s a ∧
    !paeqQuadGraph out ↑(Encodable.encode body) t u v w 0 d”

theorem atTermsGraph_iff (out t u v w : V) :
    atTermsGraph.val.Evalb ![out,t,u,v,w] ↔ out = atTermsCode t u v w := by
  haveI := paeqQuadGraph_defined (V := V)
  simp [atTermsGraph,atTermsCode,Semiformula.quote_eq_encode,Sentence.quote_eq_encode,
    Matrix.comp_vecCons'',numeral_eq_natCast, singleton_eq_insert, emptyset_def]

instance atTermsCode_defined : 𝚺₁-Function₄ (atTermsCode : V → V → V → V → V) via atTermsGraph :=
  .mk fun v => by
    change atTermsGraph.val.Evalb v ↔ v 0 = atTermsCode (v 1) (v 2) (v 3) (v 4)
    have hv : ![v 0,v 1,v 2,v 3,v 4] = v := by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun m => Fin.cases rfl (fun n => Fin.elim0 n) m) l) k) j) i
    simpa only [hv] using atTermsGraph_iff (v 0) (v 1) (v 2) (v 3) (v 4)

#print axioms atTerms_val
#print axioms atTermsCode_valid
#print axioms atTermsCode_defined
#print axioms source_mem
#print axioms source_quote
#print axioms atTerms
end PA194PAeq.MulCongruenceInternal
