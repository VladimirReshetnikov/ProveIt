import PA194PAeqMulAssocProof
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.MulOrderLemmas
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PA194PAeq.AddOne PA194PAeq.AddCongrTyped PA194PAeq.EqRelExt PA194PAeq.LessCongrTyped
open PA194PAeq.MulRightZero PA194PAeq.MulCongrTyped PA194PAeq.MulLawsAt
variable {Γ : List Fm}

noncomputable def rightDistrAt (a b c : Tm) (hax : ∀ p ∈ MulAssoc.axioms, p ∈ Γ) :
    ND.Proof Γ (eq (mul (add a b) c) (add (mul a c) (mul b c))) := by
  have hc : ∀ p ∈ MulComm.axioms, p ∈ Γ := by intro p hp; exact hax p (by simp [MulAssoc.axioms,hp])
  have hd : ∀ p ∈ Distributivity.axioms, p ∈ Γ := by intro p hp; exact hax p (by simp [MulAssoc.axioms,hp])
  have h1 := commAt (add a b) c hc
  have h2 := distrAt c a b hd
  have h3 := addCongrAt (mul c a) (mul a c) (mul c b) (mul b c)
    (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) (commAt c a hc) (commAt c b hc)
  exact transAt _ _ _ (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) h1
    (transAt _ _ _ (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) h2 h3)

noncomputable def positiveFactorAt (u c v : Tm) (hcv : ND.Proof Γ (eq c (succ v)))
    (hax : ∀ p ∈ MulAssoc.axioms, p ∈ Γ) :
    ND.Proof Γ (eq (mul (succ u) c) (succ (add v (mul u c)))) := by
  have h1 := mulSuccAt u c (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms]))
  have h2 := addCongrAt c (succ v) (mul u c) (mul u c)
    (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) hcv
    (reflAt _ (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])))
  have h3 := addSuccAt v (mul u c) (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms]))
  exact transAt _ _ _ (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) h1
    (transAt _ _ _ (hax _ (by simp [MulAssoc.axioms,Distributivity.axioms,AddLtAdd.axioms])) h2 h3)
#print axioms rightDistrAt
#print axioms positiveFactorAt
end PA194PAeq.MulOrderLemmas
