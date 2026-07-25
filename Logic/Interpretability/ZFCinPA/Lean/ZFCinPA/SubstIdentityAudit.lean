import ZFCinPA.SubstIdentity

/-!
# Audit for the heterogeneous self-substitution identity

Three layers, kept visible in their types:

* the raw identity `subst_bvarVec_eq_self`, which reduces to Foundation's
  homogeneous `Bootstrapping.subst_eq_self` through the self-improving
  hypothesis `isSemitermVec_of_bvarVec`;
* its typed readings — on `.val`, and as an equation modulo the arity
  weakening `Semiformula.castLE`;
* the compiler-facing corollary `translate_emb_srcP_bvars`, which is the
  form the certificate-field spines consume: a placeholder atom carrying
  the identity argument list translates to the *raw* model-coded leaf.

The `#print axioms` lines must show only Lean's three standard classical
axioms: the module introduces no trust boundary of its own.
-/

namespace LeanProofs.ZFCinPA.SubstIdentityAudit

open LeanProofs.ZFCinPA.SubstIdentity

/-! ## The raw identity -/

#check @isSemitermVec_of_bvarVec
#check @subst_bvarVec_eq_self

/-! ## Typed readings -/

#check @Semiformula.subst_bvarVec_val
#check @Semiformula.bvarVec
#check @Semiformula.subst_bvarVec
#check @Semiformula.castLE
#check @Semiformula.subst_bvarVec_eq_castLE

/-! ## The compiler-facing corollary -/

#check @srcBvars
#check @translate_emb_srcP_bvars
#check @translate_emb_srcP_bvars_eq

/-! ## Assumption audit -/

#print axioms isSemitermVec_of_bvarVec
#print axioms subst_bvarVec_eq_self
#print axioms Semiformula.subst_bvarVec_val
#print axioms Semiformula.subst_bvarVec_eq_castLE
#print axioms translate_emb_srcP_bvars
#print axioms translate_emb_srcP_bvars_eq

end LeanProofs.ZFCinPA.SubstIdentityAudit
