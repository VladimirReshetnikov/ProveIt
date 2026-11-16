import PA194PAeqDoubleSpecialization
import PA194PAeqReflexivityAt
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.Symmetry
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqSpecialization PA194PAeqDoubleSpecialization
local instance (n : Nat) : DecidableEq (PA194PAeq.Func n) := by
  intro a b; cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)
local instance (n : Nat) : DecidableEq (PA194PAeq.Rel n) := by
  intro a b; cases a <;> cases b; exact isTrue rfl
local instance : PA194PAeq.language.DecidableEq := ⟨fun _ => inferInstance, fun _ => inferInstance⟩
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

def body : Semiproposition language 2 :=
  implies (eq (.bvar 1) (.bvar 0)) (eq (.bvar 0) (.bvar 1))
theorem source_mem : symmetry.univCl ∈ ordinaryPAeq :=
  ⟨symmetry, .fixed _ (by simp [fixedAxioms]), rfl⟩
theorem source_quote : (⌜symmetry.univCl⌝ : V) = ^∀ ^∀ (⌜body⌝ : V) := by
  have h : symmetry.freeVariables = ∅ := by decide
  rw [Sentence.quote_def]
  rw [show (symmetry.univCl : AddOne.Fm) = symmetry from AddOne.coe_closed _ h]
  change (⌜(Semiformula.all (Semiformula.all body))⌝ : V) = _
  rfl

noncomputable def atTerms (t u : Term V language) :
    (ordinaryPAeq.internalize V) ⊢! (⌜body⌝ : Semiformula V language 2).subst ![t,u] := by
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let p : Semiformula V language 2 := ⌜body⌝
  have hd : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ p) ∅ := by
    refine ⟨axm {⌜symmetry.univCl⌝} ⌜symmetry.univCl⌝, ?_⟩
    have h := (target_axiom_witness ordinaryPAeq symmetry.univCl source_mem :
      Proof ordinaryPAeq (axm {⌜symmetry.univCl⌝} ⌜symmetry.univCl⌝ : V) ⌜symmetry.univCl⌝)
    simpa [T,p,source_quote,Proof,Semiformula.quote_def,← singleton_eq_insert] using h
  exact paeqDoubleProof T ∅ p t u hd

noncomputable def atTermsCode (t u : V) : V :=
  paeqDoubleCode (⌜body⌝ : V) t u 0 (axm {⌜symmetry.univCl⌝} ⌜symmetry.univCl⌝)

theorem atTerms_val (t u : Term V language) : (atTerms t u).val = atTermsCode t.val u.val := by
  simp [atTerms,atTermsCode,paeqDoubleProof_val,Semiformula.quote_def,← emptyset_def]

theorem atTermsCode_valid {t u : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) :
    letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
    Proof ordinaryPAeq (atTermsCode t u) (subst language (t∷(u∷0)) (⌜body⌝ : V)) := by
  letI : ordinaryPAeq.Δ₁ := (ordinaryPAeq.internalize V).Δ₁
  let tt : Term V language := ⟨t,ht⟩
  let uu : Term V language := ⟨u,hu⟩
  have h := (atTerms tt uu).derivationOf
  simpa [atTerms_val, atTermsCode, tt, uu, Proof, Semiformula.quote_def,
    SemitermVec.val_succ, ← singleton_eq_insert] using h

noncomputable def atTermsGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out t u. ∃ a s d,
    a = ↑(Encodable.encode symmetry.univCl) ∧ !insertDef s a 0 ∧ !axmGraph d s a ∧
    !paeqDoubleGraph out ↑(Encodable.encode body) t u 0 d”

theorem atTermsGraph_iff (out t u : V) :
    atTermsGraph.val.Evalb ![out,t,u] ↔ out = atTermsCode t u := by
  haveI := paeqDoubleGraph_defined (V := V)
  simp [atTermsGraph,atTermsCode,Semiformula.quote_eq_encode,Sentence.quote_eq_encode,
    Matrix.comp_vecCons'',numeral_eq_natCast, singleton_eq_insert, emptyset_def]

instance atTermsCode_defined : 𝚺₁-Function₂ (atTermsCode : V → V → V) via atTermsGraph :=
  .mk fun v => by
    change atTermsGraph.val.Evalb v ↔ v 0 = atTermsCode (v 1) (v 2)
    have hv : ![v 0,v 1,v 2] = v := by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
    simpa only [hv] using atTermsGraph_iff (v 0) (v 1) (v 2)

#print axioms atTerms_val
#print axioms atTermsCode_valid
#print axioms atTermsCode_defined
#print axioms source_mem
#print axioms source_quote
#print axioms atTerms
end PA194PAeq.Symmetry
