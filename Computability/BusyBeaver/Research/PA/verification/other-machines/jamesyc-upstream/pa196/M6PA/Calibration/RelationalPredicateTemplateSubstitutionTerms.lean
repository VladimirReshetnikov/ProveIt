module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateBinders
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
noncomputable def substTerms (w v : V) : V := termSubstVec L (len v) w v
noncomputable def substTermsGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “out w v. ∃ k, !lenDef k v ∧ !(termSubstVecGraph L) out k w v”
theorem substTerms_graph (out w v : V) :
    substTermsGraph.val.Evalb ![out,w,v] ↔ out=substTerms w v := by
  simp [substTermsGraph,substTerms]
theorem substTerms_length {k n v w : V} (hv : IsSemitermVec L k n v) :
    len (substTerms w v)=k := by simp [substTerms,hv.lh,hv.isUTerm]
theorem substTerms_nth {k n v w i : V} (hv : IsSemitermVec L k n v) (hi : i<k) :
    (substTerms w v).[i]=termSubst L w v.[i] := by
  simp [substTerms,hv.lh,nth_termSubstVec hv.isUTerm hi]
theorem substTerms_valid {k n m v w : V} (hv : IsSemitermVec L k n v)
    (hw : IsSemitermVec L n m w) : IsSemitermVec L k m (substTerms w v) := by
  simpa [substTerms,hv.lh] using hw.termSubstVec hv
theorem substEnvironments_valid {s n m b f w : V} (h : EnvironmentsValid s n b f)
    (hw : IsSemitermVec L n m w) :
    EnvironmentsValid s m (substTerms w b) (substTerms w f) := by
  exact ⟨substTerms_valid h.1 hw,by simpa [substTerms_length h.2] using substTerms_valid h.2 hw⟩
theorem termValue_subst {s : Nat} (t : Term s) {n b f w : V}
    (h : EnvironmentsValid (s:V) n b f) (hf : ∀i,t.FVar? i→(i:V)<len f) :
    termValue t (substTerms w b) (substTerms w f)=termSubst L w (termValue t b f) := by
  cases t with
  | bvar i => exact substTerms_nth h.1 (by exact_mod_cast i.isLt)
  | fvar i => exact substTerms_nth h.2 (hf i (by simp))
  | func fn _ => nomatch fn
#print axioms substTerms_graph
#print axioms substTerms_valid
#print axioms substEnvironments_valid
#print axioms termValue_subst
end M6.PA.RelationalPredicateTemplate

