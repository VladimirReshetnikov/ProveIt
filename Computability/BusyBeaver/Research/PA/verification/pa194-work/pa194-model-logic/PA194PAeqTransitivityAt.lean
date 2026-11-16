import PA194PAeqTripleSpecialization
import PA194PAeqReflexivityAt
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.Transitivity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqSpecialization PA194PAeqTripleSpecialization
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

def body : Semiproposition language 3 :=
  implies (eq (.bvar 2) (.bvar 1)) (implies (eq (.bvar 1) (.bvar 0)) (eq (.bvar 2) (.bvar 0)))
theorem source_mem : transitivity.univCl ∈ ordinaryPAeq :=
  ⟨transitivity, .fixed _ (by simp [fixedAxioms]), rfl⟩
theorem source_quote : (⌜transitivity.univCl⌝ : V) = ^∀ ^∀ ^∀ (⌜body⌝ : V) := by
  have h : transitivity.freeVariables = ∅ := by decide
  rw [Sentence.quote_def]
  rw [show (transitivity.univCl : AddOne.Fm) = transitivity from AddOne.coe_closed _ h]
  change (⌜(Semiformula.all (Semiformula.all (Semiformula.all body)))⌝ : V) = _
  rfl

noncomputable def atTerms (t u v : Term V language) :
    (ordinaryPAeq.internalize V) ⊢! (⌜body⌝ : Semiformula V language 3).subst ![t,u,v] := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let p : Semiformula V language 3 := ⌜body⌝
  have hd : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ p) ∅ := by
    refine ⟨axm {⌜transitivity.univCl⌝} ⌜transitivity.univCl⌝, ?_⟩
    have h := (target_axiom_witness ordinaryPAeq transitivity.univCl source_mem :
      Proof ordinaryPAeq (axm {⌜transitivity.univCl⌝} ⌜transitivity.univCl⌝ : V) ⌜transitivity.univCl⌝)
    simpa [T,p,source_quote,Proof,Semiformula.quote_def,← singleton_eq_insert] using h
  exact paeqTripleProof T ∅ p t u v hd

noncomputable def atTermsCode (t u v : V) : V :=
  paeqTripleCode (⌜body⌝ : V) t u v 0 (axm {⌜transitivity.univCl⌝} ⌜transitivity.univCl⌝)

theorem atTerms_val (t u v : Term V language) : (atTerms t u v).val = atTermsCode t.val u.val v.val := by
  simp [atTerms,atTermsCode,paeqTripleProof_val,Semiformula.quote_def,← emptyset_def]

theorem atTermsCode_valid {t u v : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) (hv : IsSemiterm language 0 v) :
    letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
    Proof ordinaryPAeq (atTermsCode t u v) (subst language (t∷(u∷(v∷0))) (⌜body⌝ : V)) := by
  letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
  let tt : Term V language := ⟨t,ht⟩
  let uu : Term V language := ⟨u,hu⟩
  let vv : Term V language := ⟨v,hv⟩
  have h := (atTerms tt uu vv).derivationOf
  simpa [atTerms_val, atTermsCode, tt, uu, vv, Proof, Semiformula.quote_def,
    SemitermVec.val_succ, ← singleton_eq_insert] using h

noncomputable def atTermsGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out t u v. ∃ a s d,
    a = ↑(Encodable.encode transitivity.univCl) ∧ !insertDef s a 0 ∧ !axmGraph d s a ∧
    !paeqTripleGraph out ↑(Encodable.encode body) t u v 0 d”

theorem atTermsGraph_iff (out t u v : V) :
    atTermsGraph.val.Evalb ![out,t,u,v] ↔ out = atTermsCode t u v := by
  haveI := paeqTripleGraph_defined (V := V)
  simp [atTermsGraph,atTermsCode,Semiformula.quote_eq_encode,Sentence.quote_eq_encode,
    Matrix.comp_vecCons'',numeral_eq_natCast, singleton_eq_insert, emptyset_def]

instance atTermsCode_defined : 𝚺₁-Function₃ (atTermsCode : V → V → V → V) via atTermsGraph :=
  .mk fun v => by
    change atTermsGraph.val.Evalb v ↔ v 0 = atTermsCode (v 1) (v 2) (v 3)
    have hv : ![v 0,v 1,v 2,v 3] = v := by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun m => Fin.elim0 m) l) k) j) i
    simpa only [hv] using atTermsGraph_iff (v 0) (v 1) (v 2) (v 3)

#print axioms atTerms_val
#print axioms atTermsCode_valid
#print axioms atTermsCode_defined
#print axioms source_mem
#print axioms source_quote
#print axioms atTerms
end PA194PAeq.Transitivity
