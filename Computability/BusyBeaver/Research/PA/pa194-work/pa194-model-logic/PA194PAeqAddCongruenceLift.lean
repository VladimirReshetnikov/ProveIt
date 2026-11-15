import PA194PAeqAddCongruenceAt
import PA194PAeqReflexivityExact
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.AddCongruenceInternal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint PA194PAeqModusPonens PA194PAeqQuadSpecialization
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

def firstAntecedent : Semiproposition language 4 := eq (.bvar 0) (.bvar 1)
def secondAntecedent : Semiproposition language 4 := eq (.bvar 2) (.bvar 3)
def consequent : Semiproposition language 4 := eq (add (.bvar 0) (.bvar 2)) (add (.bvar 1) (.bvar 3))
noncomputable def addTerm (t u : V) : V := ^func 2 2 (?[t,u] : V)
theorem first_quote : (⌜firstAntecedent⌝ : V) = equalityCode (^#0) (^#1) := by
  change ((⌜firstAntecedent⌝ : Semiformula V language 4).val : V) = _
  simp [firstAntecedent,eq,equalityCode,Matrix.vecHead,Matrix.vecTail]; rfl
theorem second_quote : (⌜secondAntecedent⌝ : V) = equalityCode (^#2) (^#3) := by
  change ((⌜secondAntecedent⌝ : Semiformula V language 4).val : V) = _
  simp [secondAntecedent,eq,equalityCode,Matrix.vecHead,Matrix.vecTail]; rfl
theorem consequent_quote : (⌜consequent⌝ : V) = equalityCode (addTerm (^#0) (^#2)) (addTerm (^#1) (^#3)) := by
  change ((⌜consequent⌝ : Semiformula V language 4).val : V) = _
  simp [consequent,eq,add,addTerm,equalityCode,Matrix.vecHead,Matrix.vecTail]
  constructor
  · rfl
  · change (↑(Encodable.encode (Func.add : language.Func 2)) : V) = 2
    simp [PA194PAeq.functionEncodable,Encodable.encode]
theorem body_quote : (⌜body⌝ : V) = imp language (⌜firstAntecedent⌝ : V)
    (imp language (⌜secondAntecedent⌝ : V) (⌜consequent⌝ : V)) := by
  change (⌜(firstAntecedent 🡒 (secondAntecedent 🡒 consequent))⌝ : V) = _
  simp only [Semiformula.imp_eq, Semiformula.quote_or, PA194PAeqBind.paeq_quote_neg, imp]
theorem body_subst {t u v w : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u)
    (hv : IsSemiterm language 0 v) (hw : IsSemiterm language 0 w) :
    subst language (t∷(u∷(v∷(w∷(0:V))))) (⌜body⌝ : V) =
      imp language (equalityCode t u) (imp language (equalityCode v w) (equalityCode (addTerm t v) (addTerm u w))) := by
  have hlt2 : (2:V) < 4 := by norm_num
  have hlt3 : (3:V) < 4 := by norm_num
  have hvect : IsSemitermVec language 4 0 (t∷(u∷(v∷(w∷(0:V))))) := by
    simp [ht,hu,hv,hw,show (4:V)=3+1 by norm_num,show (3:V)=2+1 from two_add_one_eq_three.symm]
  have hn : (t∷(u∷(v∷(w∷(0:V))))).[3] = w := by
    simp [show (3:V)=2+1 by norm_num,← one_add_one_eq_two]
  have ha : IsSemiformula language 4 (⌜firstAntecedent⌝ : V) := by
    rw [first_quote]; apply equality_valid <;> simp [hlt2,hlt3]
  have hb : IsSemiformula language 4 (⌜secondAntecedent⌝ : V) := by
    rw [second_quote]; apply equality_valid <;> simp [hlt2,hlt3]
  have hc : IsSemiformula language 4 (⌜consequent⌝ : V) := by
    rw [consequent_quote]; apply equality_valid <;> simp [addTerm,source_functions,hlt2,hlt3]
  have hinner : IsSemiformula language 4 (imp language (⌜secondAntecedent⌝ : V) ⌜consequent⌝) :=
    IsSemiformula.imp.mpr ⟨hb,hc⟩
  rw [body_quote]
  simp only [imp]
  rw [substs_or ha.neg.isUFormula (by simpa [imp] using hinner.isUFormula), substs_neg ha hvect,
    substs_or hb.neg.isUFormula hc.isUFormula, substs_neg hb hvect,
    first_quote, second_quote, consequent_quote,
    equality_subst hvect (by simp [hlt2,hlt3]) (by simp [hlt2,hlt3]),
    equality_subst hvect (by simp [hlt2,hlt3]) (by simp [hlt2,hlt3]),
    equality_subst hvect (by simp [addTerm,source_functions,hlt2,hlt3]) (by simp [addTerm,source_functions,hlt2,hlt3])]
  simp [addTerm,source_functions,ht.isUTerm,hu.isUTerm,hv.isUTerm,hw.isUTerm,hn]

noncomputable def liftCode (t u v w d e : V) : V :=
  let p := equalityCode t u
  let q := equalityCode v w
  let r := equalityCode (addTerm t v) (addTerm u w)
  let di := atTermsCode t u v w
  let first := paeqMPCode p (imp language q r) 0 di d
  paeqMPCode q r 0 first e

theorem liftCode_valid {t u v w d e : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) (hv : IsSemiterm language 0 v) (hw : IsSemiterm language 0 w) :
    letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
    Proof ordinaryPAeq d (equalityCode t u) → Proof ordinaryPAeq e (equalityCode v w) →
      Proof ordinaryPAeq (liftCode t u v w d e) (equalityCode (addTerm t v) (addTerm u w)) := by
  letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
  intro hd he
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let p : Formula V language := ⟨equalityCode t u, equality_valid ht hu⟩
  let q : Formula V language := ⟨equalityCode v w, equality_valid hv hw⟩
  have hadd (x y : V) (hx : IsSemiterm language 0 x) (hy : IsSemiterm language 0 y) : IsSemiterm language 0 (addTerm x y) := by
    simp [addTerm,source_functions,hx,hy]
  let r : Formula V language := ⟨equalityCode (addTerm t v) (addTerm u w), equality_valid (hadd t v ht hv) (hadd u w hu hw)⟩
  let dp : T ⊢!ᵈᵉʳ insert p ∅ := by
    refine ⟨d, ?_⟩
    simpa [T,p,Proof,instΔ₁Theory,Theory.internalize,← singleton_eq_insert] using hd
  let dq : T ⊢!ᵈᵉʳ insert q ∅ := by
    refine ⟨e, ?_⟩
    simpa [T,q,Proof,instΔ₁Theory,Theory.internalize,← singleton_eq_insert] using he
  let di : T ⊢!ᵈᵉʳ insert (p 🡒 (q 🡒 r)) ∅ := by
    let b : Semiformula V language 4 := ⌜body⌝
    let tt : Term V language := ⟨t,ht⟩
    let uu : Term V language := ⟨u,hu⟩
    let vv : Term V language := ⟨v,hv⟩
    let ww : Term V language := ⟨w,hw⟩
    let seed : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ ∀⁰ b) ∅ := by
      refine ⟨axm {⌜addCongruence.univCl⌝} ⌜addCongruence.univCl⌝, ?_⟩
      have h := (target_axiom_witness ordinaryPAeq addCongruence.univCl source_mem :
        Proof ordinaryPAeq (axm {⌜addCongruence.univCl⌝} ⌜addCongruence.univCl⌝ : V) ⌜addCongruence.univCl⌝)
      simpa [T,b,source_quote,Proof,Semiformula.quote_def,instΔ₁Theory,← singleton_eq_insert] using h
    let z := paeqQuadProof T ∅ b tt uu vv ww seed
    have hz := z.derivationOf
    change DerivationOf T.theory z.val (insert (subst language (t∷(u∷(v∷(w∷(0:V))))) (⌜body⌝ : V)) 0) at hz
    rw [body_subst ht hu hv hw] at hz
    change DerivationOf ordinaryPAeq z.val (insert (imp language (equalityCode t u) (imp language (equalityCode v w) (equalityCode (addTerm t v) (addTerm u w)))) 0) at hz
    refine ⟨atTermsCode t u v w, ?_⟩
    simpa [z,paeqQuadProof_val,atTermsCode,seed,T,b,tt,uu,vv,ww,p,q,r,Proof,instΔ₁Theory,
      Semiformula.quote_def,Semiformula.val_substs,Sequent.val_insert,SemitermVec.val_succ,Semiformula.imp_def,imp,
      ← singleton_eq_insert,← emptyset_def] using hz
  let first := paeqMPProof T ∅ p (q 🡒 r) di dp
  let result := paeqMPProof T ∅ q r first dq
  have hr := result.derivationOf
  simpa [result,first,paeqMPProof_val,liftCode,T,p,q,r,di,dp,dq,Proof,instΔ₁Theory,Theory.internalize,Semiformula.imp_def,imp,← singleton_eq_insert,← emptyset_def] using hr

noncomputable def liftGraph : 𝚺₁.Semisentence 7 := .mkSigma
  “out t u v w d e. ∃ tv uw args1 args2 a b p q r n di first,
    !adjoinDef tv v 0 ∧ !adjoinDef args1 t tv ∧ !qqFuncDef a 2 2 args1 ∧
    !adjoinDef uw w 0 ∧ !adjoinDef args2 u uw ∧ !qqFuncDef b 2 2 args2 ∧
    !equalityGraph p t u ∧ !equalityGraph q v w ∧ !equalityGraph r a b ∧
    !(impGraph language) n q r ∧ !atTermsGraph di t u v w ∧
    !paeqMPGraph first p n 0 di d ∧ !paeqMPGraph out q r 0 first e”
theorem liftGraph_defined : 𝚺₁.DefinedFunction
    (fun z : Fin 6 → V => liftCode (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)) liftGraph := by
  haveI := paeqMPGraph_defined (V := V)
  exact .mk fun z => by simp [liftGraph,liftCode,addTerm,Matrix.comp_vecCons'']

#print axioms liftGraph_defined
#print axioms liftCode_valid
#print axioms body_subst
#print axioms first_quote
#print axioms consequent_quote
#print axioms body_quote
end PA194PAeq.AddCongruenceInternal
