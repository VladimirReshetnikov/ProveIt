module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateProofCoverage
@[expose] public section
namespace M6.PA.RelationalPredicateTemplate
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (targetShiftTerms)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language
private theorem bound_cast_max (a b : Nat) : ((max a b : Nat):V)=max (a:V) (b:V) := by
  rcases le_total a b with h | h
  · rw [Nat.max_eq_right h,max_eq_right (by exact_mod_cast h)]
  · rw [Nat.max_eq_left h,max_eq_left (by exact_mod_cast h)]

theorem sequentCovered_of_proofBound {Γ : LK.Sequent sourceLanguage} (d : LK.Derivation Γ)
    {f : V} (hb : (proofFreeBound d:V)≤len f) : SequentCovered Γ f :=
  sequentCovered_of_bound ((show (sequentFreeBound Γ:V)≤(proofFreeBound d:V) by
    exact_mod_cast sequentFreeBound_le_proofFreeBound d).trans hb)

theorem proofCovered_of_bound {Γ : LK.Sequent sourceLanguage} (d : LK.Derivation Γ)
    {f : V} (hf : IsSemitermVec L (len f) 0 f) (hb : (proofFreeBound d:V)≤len f) :
    ProofCovered d f := by
  induction d generalizing f with
  | identity r ts => exact ⟨sequentCovered_of_proofBound _ hb,trivial⟩
  | cut dp dn ihp ihn =>
    refine ⟨sequentCovered_of_proofBound _ hb,?_,?_⟩
    · apply ihp hf
      unfold proofFreeBound at hb
      simp only [bound_cast_max] at hb
      exact (le_max_left _ _).trans ((le_max_right _ _).trans hb)
    · apply ihn hf
      unfold proofFreeBound at hb
      simp only [bound_cast_max] at hb
      exact (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  | contraction dp ih =>
    refine ⟨sequentCovered_of_proofBound _ hb,ih hf ?_⟩
    unfold proofFreeBound at hb
    simp only [bound_cast_max] at hb
    exact (le_max_right _ _).trans hb
  | weakening dp ih =>
    refine ⟨sequentCovered_of_proofBound _ hb,ih hf ?_⟩
    unfold proofFreeBound at hb
    simp only [bound_cast_max] at hb
    exact (le_max_right _ _).trans hb
  | verum => exact ⟨sequentCovered_of_proofBound _ hb,trivial⟩
  | or dp ih =>
    refine ⟨sequentCovered_of_proofBound _ hb,ih hf ?_⟩
    unfold proofFreeBound at hb
    simp only [bound_cast_max] at hb
    exact (le_max_right _ _).trans hb
  | and dp dq ihp ihq =>
    refine ⟨sequentCovered_of_proofBound _ hb,?_,?_⟩
    · apply ihp hf
      unfold proofFreeBound at hb
      simp only [bound_cast_max] at hb
      exact (le_max_left _ _).trans ((le_max_right _ _).trans hb)
    · apply ihq hf
      unfold proofFreeBound at hb
      simp only [bound_cast_max] at hb
      exact (le_max_right _ _).trans ((le_max_right _ _).trans hb)
  | all dp ih =>
    refine ⟨sequentCovered_of_proofBound _ hb,?_⟩
    apply ih
    · have hs := NumericPAeqTerm.targetShiftTerms_valid hf
      simpa [NumericPAeqTerm.targetShiftTerms_length hf] using hs.adjoin (show IsSemiterm L 0 (qqFvar 0) by simp)
    · unfold proofFreeBound at hb
      simp only [bound_cast_max] at hb
      have hh := (le_max_right _ _).trans hb
      exact hh.trans (by simp [NumericPAeqTerm.targetShiftTerms_length hf])
  | @exs Γ p t dp ih =>
    refine ⟨sequentCovered_of_proofBound _ hb,?_,?_⟩
    · intro i hi
      have hi' : (i:V)<(termFreeBound t:V) := by exact_mod_cast term_fvar_lt_freeBound t hi
      unfold proofFreeBound at hb
      simp only [bound_cast_max] at hb
      exact hi'.trans_le ((le_max_left _ _).trans ((le_max_right _ _).trans hb))
    · apply ih hf
      unfold proofFreeBound at hb
      simp only [bound_cast_max] at hb
      exact (le_max_right _ _).trans ((le_max_right _ _).trans hb)
#print axioms proofCovered_of_bound
end M6.PA.RelationalPredicateTemplate

