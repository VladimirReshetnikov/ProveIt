module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentInsert
@[expose] public section

/-! Accepted-code closures for the literal relational-source propositional
sequent premises in Foundation Derivation.Phi. Quantifier rules are not included. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def resolveDisjunction {Γ : List V} {a c : V}
    (d : Context Γ (nativeOr a c)) (nc : Context Γ (wn c)) : Context Γ a := by
  let na : Context (wn a :: Γ) (wn a) := .assumption (by simp)
  exact (Context.mp (.mp na (d.up (wn a))) (nc.up (wn a))).deduction.dne

theorem translationAnd_eq (a b : V) :
    ActualArithmeticGraph.eval translationAnd a b 0 0 = wa a b := by
  simp [translationAnd,wa,wn,wim,implicationValue,ActualArithmeticGraph.eval,
    ActualHeadGraphs.im,ActualHeadGraphs.neg,ActualHeadGraphs.conj,ActualHeadGraphs.implicationExpr]

noncomputable def conjunctionSequent {a b c : V}
    (pa : Certificate (nativeOr a c)) (pb : Certificate (nativeOr b c))
    (h : Certificate (wim (wa a b) c)) : Certificate c := by
  let nc : Context [wn c] (wn c) := .assumption (by simp)
  let ca : Context [wn c] a := resolveDisjunction (.closed pa) nc
  let cb : Context [wn c] b := resolveDisjunction (.closed pb) nc
  let cc : Context [wn c] c := .mp (ca.andIntro cb) (.closed h)
  exact (Context.mp cc nc).deduction.dne.empty

noncomputable def cutSequent {a na c : V}
    (pa : Certificate (nativeOr a c)) (pn : Certificate (nativeOr na c))
    (h : Certificate (wim na (wn a))) : Certificate c := by
  let nc : Context [wn c] (wn c) := .assumption (by simp)
  let ca : Context [wn c] a := resolveDisjunction (.closed pa) nc
  let cn : Context [wn c] (wn a) :=
    .mp (resolveDisjunction (.closed pn) nc) (.closed h)
  exact (Context.mp ca cn).deduction.dne.empty

theorem sequent_verum_certificate (param s : V) (hm : qqVerum∈s) :
    ∃ code, verifyValue code=sequentCode param s+1 := by
  obtain ⟨arrow,ha⟩ := member_certificate param s qqVerum hm
  rw [translate_verum] at ha
  let out := (truthCertificate (V:=V)).mp ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

theorem sequent_and_certificate (param s p q dp dq : V)
    (hp : IsUFormula language p) (hq : IsUFormula language q) (hm : qqAnd p q∈s)
    (hdp : verifyValue dp=sequentCode param (insert p s)+1)
    (hdq : verifyValue dq=sequentCode param (insert q s)+1) :
    ∃ code, verifyValue code=sequentCode param s+1 := by
  obtain ⟨left,hl⟩ := insert_accepted_disjunction param s p dp hdp
  obtain ⟨right,hr⟩ := insert_accepted_disjunction param s q dq hdq
  obtain ⟨arrow,ha⟩ := member_certificate param s (qqAnd p q) hm
  rw [translate_and param p q hp hq,translationAnd_eq] at ha
  let out := conjunctionSequent (⟨left,hl⟩ : Certificate
    (nativeOr (translate param p) (sequentCode param s)))
    (⟨right,hr⟩ : Certificate (nativeOr (translate param q) (sequentCode param s))) ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

theorem sequent_or_certificate (param s p q dpq : V)
    (hp : IsUFormula language p) (hq : IsUFormula language q) (hm : qqOr p q∈s)
    (hd : verifyValue dpq=sequentCode param (insert p (insert q s))+1) :
    ∃ code, verifyValue code=sequentCode param s+1 := by
  obtain ⟨arrow,ha⟩ := member_certificate param s (qqOr p q) hm
  rw [translate_or param p q hp hq,translationOr_eq] at ha
  let toS : Certificate (wim (nativeOr (translate param p) (translate param q))
    (sequentCode param s)) := ⟨arrow,ha⟩
  obtain ⟨fold,hfold⟩ := sequent_eliminate_certificate param (insert p (insert q s))
    (sequentCode param s) (by
      intro r hr
      have hx : r=p ∨ r=q ∨ r∈s := by simpa using hr
      rcases hx with he | he | hs
      · subst r
        let out := implicationCompose (orLeft (translate param p) (translate param q)) toS
        exact ⟨out.code,out.accepted⟩
      · subst r
        let out := implicationCompose (orRight (translate param p) (translate param q)) toS
        exact ⟨out.code,out.accepted⟩
      · exact member_certificate param s r hs)
  let out := (⟨dpq,hd⟩ : Certificate (sequentCode param (insert p (insert q s)))).mp ⟨fold,hfold⟩
  exact ⟨out.code,out.accepted⟩

theorem sequent_cut_certificate (param s p dp dn : V) (hp : IsUFormula language p)
    (hdp : verifyValue dp=sequentCode param (insert p s)+1)
    (hdn : verifyValue dn=sequentCode param (insert (Bootstrapping.neg language p) s)+1) :
    ∃ code, verifyValue code=sequentCode param s+1 := by
  obtain ⟨left,hl⟩ := insert_accepted_disjunction param s p dp hdp
  obtain ⟨right,hr⟩ := insert_accepted_disjunction param s (Bootstrapping.neg language p) dn hdn
  obtain ⟨forward,backward,hforward,hbackward⟩ := nnf_certificates p param hp
  let out := cutSequent (⟨left,hl⟩ : Certificate (nativeOr (translate param p) (sequentCode param s)))
    (⟨right,hr⟩ : Certificate
      (nativeOr (translate param (Bootstrapping.neg language p)) (sequentCode param s))) ⟨forward,hforward⟩
  exact ⟨out.code,out.accepted⟩

#print axioms resolveDisjunction
#print axioms translationAnd_eq
#print axioms conjunctionSequent
#print axioms cutSequent
#print axioms sequent_verum_certificate
#print axioms sequent_and_certificate
#print axioms sequent_or_certificate
#print axioms sequent_cut_certificate
end M6.PA.RelationalSource.Numeric

