import PA194PAeqSuccCongruenceAt
import PA194PAeqReflexivityExact
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.SuccCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint PA194PAeqModusPonens PA194PAeqDoubleSpecialization
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

def antecedent : Semiproposition language 2 := eq (.bvar 0) (.bvar 1)
def consequent : Semiproposition language 2 := eq (succ (.bvar 0)) (succ (.bvar 1))
noncomputable def succTerm (t : V) : V := ^func 1 1 (?[t] : V)

theorem antecedent_quote : (⌜antecedent⌝ : V) = equalityCode (^#0) (^#1) := by
  change ((⌜antecedent⌝ : Semiformula V language 2).val : V) = _
  simp [antecedent,eq,equalityCode,Matrix.vecHead,Matrix.vecTail]
  rfl

theorem consequent_quote : (⌜consequent⌝ : V) = equalityCode (succTerm (^#0)) (succTerm (^#1)) := by
  change ((⌜consequent⌝ : Semiformula V language 2).val : V) = _
  simp [consequent,eq,succ,succTerm,equalityCode,Matrix.vecHead,Matrix.vecTail]
  constructor
  · rfl
  · change (↑(Encodable.encode (Func.succ : language.Func 1)) : V) = 1
    simp [PA194PAeq.functionEncodable, Encodable.encode]

theorem body_quote : (⌜body⌝ : V) = imp language (⌜antecedent⌝ : V) (⌜consequent⌝ : V) := by
  change (⌜(antecedent 🡒 consequent)⌝ : V) = _
  simp only [Semiformula.imp_eq, Semiformula.quote_or, PA194PAeqBind.paeq_quote_neg, imp]

theorem body_subst {t u : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) :
    subst language (t∷(u∷(0:V))) (⌜body⌝ : V) =
      imp language (equalityCode t u) (equalityCode (succTerm t) (succTerm u)) := by
  have hw : IsSemitermVec language 2 0 (t∷(u∷(0:V))) := by simp [ht,hu]
  have ha : IsSemiformula language 2 (⌜antecedent⌝ : V) := by
    rw [antecedent_quote]; apply equality_valid <;> simp
  have hc : IsSemiformula language 2 (⌜consequent⌝ : V) := by
    rw [consequent_quote]; apply equality_valid <;> simp [succTerm,source_functions]
  rw [body_quote]
  simp only [imp]
  rw [substs_or ha.neg.isUFormula hc.isUFormula, substs_neg ha hw,
    antecedent_quote, consequent_quote,
    equality_subst hw (by simp) (by simp),
    equality_subst hw (by simp [succTerm,source_functions]) (by simp [succTerm,source_functions])]
  simp [succTerm,source_functions,ht.isUTerm,hu.isUTerm]

noncomputable def liftCode (t u d : V) : V :=
  paeqMPCode (equalityCode t u) (equalityCode (succTerm t) (succTerm u)) 0 (atTermsCode t u) d

theorem liftCode_valid {t u d : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) :
    letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
    Proof ordinaryPAeq d (equalityCode t u) →
      Proof ordinaryPAeq (liftCode t u d) (equalityCode (succTerm t) (succTerm u)) := by
  letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
  intro hd
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  have hs (x : V) (hx : IsSemiterm language 0 x) : IsSemiterm language 0 (succTerm x) := by
    simp [succTerm,source_functions,hx]
  let p : Formula V language := ⟨equalityCode t u, equality_valid ht hu⟩
  let q : Formula V language := ⟨equalityCode (succTerm t) (succTerm u), equality_valid (hs t ht) (hs u hu)⟩
  let dp : T ⊢!ᵈᵉʳ insert p ∅ := by
    refine ⟨d, ?_⟩
    simpa [T,p,Proof,instΔ₁Theory,Theory.internalize,← singleton_eq_insert] using hd
  let di : T ⊢!ᵈᵉʳ insert (p 🡒 q) ∅ := by
    let b : Semiformula V language 2 := ⌜body⌝
    let tt : Term V language := ⟨t,ht⟩
    let uu : Term V language := ⟨u,hu⟩
    let seed : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ b) ∅ := by
      refine ⟨axm {⌜succCongruence.univCl⌝} ⌜succCongruence.univCl⌝, ?_⟩
      have h := (target_axiom_witness ordinaryPAeq succCongruence.univCl source_mem :
        Proof ordinaryPAeq (axm {⌜succCongruence.univCl⌝} ⌜succCongruence.univCl⌝ : V) ⌜succCongruence.univCl⌝)
      simpa [T,b,source_quote,Proof,Semiformula.quote_def,instΔ₁Theory,← singleton_eq_insert] using h
    let e := paeqDoubleProof T ∅ b tt uu seed
    have he := e.derivationOf
    change DerivationOf T.theory e.val (insert (subst language (t∷(u∷(0:V))) (⌜body⌝ : V)) 0) at he
    rw [body_subst ht hu] at he
    change DerivationOf ordinaryPAeq e.val (insert (imp language (equalityCode t u) (equalityCode (succTerm t) (succTerm u))) 0) at he
    refine ⟨atTermsCode t u, ?_⟩
    simpa [e,paeqDoubleProof_val,atTermsCode,seed,T,b,tt,uu,p,q,Proof,instΔ₁Theory,
      Semiformula.quote_def,Semiformula.val_substs,Sequent.val_insert,SemitermVec.val_succ,body_subst ht hu,Semiformula.imp_def,imp,
      ← singleton_eq_insert,← emptyset_def] using he
  let result := paeqMPProof T ∅ p q di dp
  have hr := result.derivationOf
  simpa [result,paeqMPProof_val,liftCode,T,p,q,di,dp,Proof,instΔ₁Theory,Theory.internalize,← singleton_eq_insert,← emptyset_def] using hr

noncomputable def liftGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out t u d. ∃ vt vu st su p q di,
    !adjoinDef vt t 0 ∧ !adjoinDef vu u 0 ∧
    !qqFuncDef st 1 1 vt ∧ !qqFuncDef su 1 1 vu ∧
    !equalityGraph p t u ∧ !equalityGraph q st su ∧
    !atTermsGraph di t u ∧ !paeqMPGraph out p q 0 di d”

theorem liftGraph_iff (out t u d : V) :
    liftGraph.val.Evalb ![out,t,u,d] ↔ out = liftCode t u d := by
  haveI := paeqMPGraph_defined (V := V)
  simp [liftGraph,liftCode,succTerm,Matrix.comp_vecCons'']

instance liftCode_defined : 𝚺₁-Function₃ (liftCode : V → V → V → V) via liftGraph :=
  .mk fun v => by
    change liftGraph.val.Evalb v ↔ v 0 = liftCode (v 1) (v 2) (v 3)
    have hv : ![v 0,v 1,v 2,v 3] = v := by funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.cases rfl (fun m => Fin.elim0 m) l) k) j) i
    simpa only [hv] using liftGraph_iff (v 0) (v 1) (v 2) (v 3)

#print axioms liftCode_defined
#print axioms liftCode_valid
#print axioms body_subst
#print axioms antecedent_quote
#print axioms consequent_quote
#print axioms body_quote
end PA194PAeq.SuccCongruence
