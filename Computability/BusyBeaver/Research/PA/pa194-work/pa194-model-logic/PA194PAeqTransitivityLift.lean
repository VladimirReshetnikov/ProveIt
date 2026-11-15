import PA194PAeqTransitivityAt
import PA194PAeqReflexivityExact
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeq.Transitivity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqTermBlueprint PA194PAeqModusPonens PA194PAeqTripleSpecialization
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable local instance : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta

def firstAntecedent : Semiproposition language 3 := eq (.bvar 2) (.bvar 1)
def secondAntecedent : Semiproposition language 3 := eq (.bvar 1) (.bvar 0)
def consequent : Semiproposition language 3 := eq (.bvar 2) (.bvar 0)
theorem first_quote : (⌜firstAntecedent⌝ : V) = equalityCode (^#2) (^#1) := by
  change ((⌜firstAntecedent⌝ : Semiformula V language 3).val : V) = _
  simp [firstAntecedent,eq,equalityCode,Matrix.vecHead,Matrix.vecTail]; rfl
theorem second_quote : (⌜secondAntecedent⌝ : V) = equalityCode (^#1) (^#0) := by
  change ((⌜secondAntecedent⌝ : Semiformula V language 3).val : V) = _
  simp [secondAntecedent,eq,equalityCode,Matrix.vecHead,Matrix.vecTail]; rfl
theorem consequent_quote : (⌜consequent⌝ : V) = equalityCode (^#2) (^#0) := by
  change ((⌜consequent⌝ : Semiformula V language 3).val : V) = _
  simp [consequent,eq,equalityCode,Matrix.vecHead,Matrix.vecTail]; rfl
theorem body_quote : (⌜body⌝ : V) = imp language (⌜firstAntecedent⌝ : V)
    (imp language (⌜secondAntecedent⌝ : V) (⌜consequent⌝ : V)) := by
  change (⌜(firstAntecedent 🡒 (secondAntecedent 🡒 consequent))⌝ : V) = _
  simp only [Semiformula.imp_eq, Semiformula.quote_or, PA194PAeqBind.paeq_quote_neg, imp]
theorem body_subst {t u v : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) (hv : IsSemiterm language 0 v) :
    subst language (t∷(u∷(v∷(0:V)))) (⌜body⌝ : V) =
      imp language (equalityCode v u) (imp language (equalityCode u t) (equalityCode v t)) := by
  have hlt : (2:V) < 3 := by norm_num
  have hw : IsSemitermVec language 3 0 (t∷(u∷(v∷(0:V)))) := by simp [ht,hu,hv,show (3:V)=2+1 from two_add_one_eq_three.symm]
  have ha : IsSemiformula language 3 (⌜firstAntecedent⌝ : V) := by
    rw [first_quote]; apply equality_valid <;> simp [hlt]
  have hb : IsSemiformula language 3 (⌜secondAntecedent⌝ : V) := by
    rw [second_quote]; apply equality_valid <;> simp [hlt]
  have hc : IsSemiformula language 3 (⌜consequent⌝ : V) := by
    rw [consequent_quote]; apply equality_valid <;> simp [hlt]
  have hinner : IsSemiformula language 3 (imp language (⌜secondAntecedent⌝ : V) ⌜consequent⌝) :=
    IsSemiformula.imp.mpr ⟨hb,hc⟩
  rw [body_quote]
  simp only [imp]
  rw [substs_or ha.neg.isUFormula (by simpa [imp] using hinner.isUFormula), substs_neg ha hw,
    substs_or hb.neg.isUFormula hc.isUFormula, substs_neg hb hw,
    first_quote, second_quote, consequent_quote,
    equality_subst hw (by simp [hlt]) (by simp [hlt]),
    equality_subst hw (by simp [hlt]) (by simp [hlt]), equality_subst hw (by simp [hlt]) (by simp [hlt])]
  simp

noncomputable def liftCode (t u v d e : V) : V :=
  let p := equalityCode t u
  let q := equalityCode u v
  let r := equalityCode t v
  let di := atTermsCode v u t
  let first := paeqMPCode p (imp language q r) 0 di d
  paeqMPCode q r 0 first e

theorem liftCode_valid {t u v d e : V} (ht : IsSemiterm language 0 t) (hu : IsSemiterm language 0 u) (hv : IsSemiterm language 0 v) :
    letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
    Proof ordinaryPAeq d (equalityCode t u) → Proof ordinaryPAeq e (equalityCode u v) →
      Proof ordinaryPAeq (liftCode t u v d e) (equalityCode t v) := by
  letI : ordinaryPAeq.Δ₁ := PA194PAeqBind.ordinaryPAeq_delta
  intro hd he
  let T : InternalTheory V language := ⟨ordinaryPAeq, PA194PAeqBind.ordinaryPAeq_delta⟩
  let p : Formula V language := ⟨equalityCode t u, equality_valid ht hu⟩
  let q : Formula V language := ⟨equalityCode u v, equality_valid hu hv⟩
  let r : Formula V language := ⟨equalityCode t v, equality_valid ht hv⟩
  let dp : T ⊢!ᵈᵉʳ insert p ∅ := by
    refine ⟨d, ?_⟩
    simpa [T,p,Proof,instΔ₁Theory,Theory.internalize,← singleton_eq_insert] using hd
  let dq : T ⊢!ᵈᵉʳ insert q ∅ := by
    refine ⟨e, ?_⟩
    simpa [T,q,Proof,instΔ₁Theory,Theory.internalize,← singleton_eq_insert] using he
  let di : T ⊢!ᵈᵉʳ insert (p 🡒 (q 🡒 r)) ∅ := by
    let b : Semiformula V language 3 := ⌜body⌝
    let tt : Term V language := ⟨v,hv⟩
    let uu : Term V language := ⟨u,hu⟩
    let vv : Term V language := ⟨t,ht⟩
    let seed : T ⊢!ᵈᵉʳ insert (∀⁰ ∀⁰ ∀⁰ b) ∅ := by
      refine ⟨axm {⌜transitivity.univCl⌝} ⌜transitivity.univCl⌝, ?_⟩
      have h := (target_axiom_witness ordinaryPAeq transitivity.univCl source_mem :
        Proof ordinaryPAeq (axm {⌜transitivity.univCl⌝} ⌜transitivity.univCl⌝ : V) ⌜transitivity.univCl⌝)
      simpa [T,b,source_quote,Proof,Semiformula.quote_def,instΔ₁Theory,← singleton_eq_insert] using h
    let z := paeqTripleProof T ∅ b tt uu vv seed
    have hz := z.derivationOf
    change DerivationOf T.theory z.val (insert (subst language (v∷(u∷(t∷(0:V)))) (⌜body⌝ : V)) 0) at hz
    rw [body_subst hv hu ht] at hz
    change DerivationOf ordinaryPAeq z.val (insert (imp language (equalityCode t u) (imp language (equalityCode u v) (equalityCode t v))) 0) at hz
    refine ⟨atTermsCode v u t, ?_⟩
    simpa [z,paeqTripleProof_val,atTermsCode,seed,T,b,tt,uu,vv,p,q,r,Proof,instΔ₁Theory,
      Semiformula.quote_def,Semiformula.val_substs,Sequent.val_insert,SemitermVec.val_succ,Semiformula.imp_def,imp,
      ← singleton_eq_insert,← emptyset_def] using hz
  let first := paeqMPProof T ∅ p (q 🡒 r) di dp
  let result := paeqMPProof T ∅ q r first dq
  have hr := result.derivationOf
  simpa [result,first,paeqMPProof_val,liftCode,T,p,q,r,di,dp,dq,Proof,instΔ₁Theory,Theory.internalize,Semiformula.imp_def,imp,← singleton_eq_insert,← emptyset_def] using hr

noncomputable def liftGraph : 𝚺₁.Semisentence 6 := .mkSigma
  “out t u v d e. ∃ p q r n di first,
    !equalityGraph p t u ∧ !equalityGraph q u v ∧ !equalityGraph r t v ∧
    !(impGraph language) n q r ∧ !atTermsGraph di v u t ∧
    !paeqMPGraph first p n 0 di d ∧ !paeqMPGraph out q r 0 first e”
theorem liftGraph_defined : 𝚺₁.DefinedFunction
    (fun w : Fin 5 → V => liftCode (w 0) (w 1) (w 2) (w 3) (w 4)) liftGraph := by
  haveI := paeqMPGraph_defined (V := V)
  exact .mk fun w => by simp [liftGraph,liftCode,Matrix.comp_vecCons'']

#print axioms liftGraph_defined
#print axioms liftCode_valid
#print axioms body_subst
#print axioms first_quote
#print axioms consequent_quote
#print axioms body_quote
end PA194PAeq.Transitivity
