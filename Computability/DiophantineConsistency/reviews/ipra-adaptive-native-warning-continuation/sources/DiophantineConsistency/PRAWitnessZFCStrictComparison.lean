import DiophantineConsistency.PRAStrictConReverse
import DiophantineConsistency.PRAWitnessZFCRefutationBound

/-! The exact Foundation ZFC consistency comparison in candidate PRA, given
an IΣ₁ proof for a particular finite no-zero equation. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessZFCStrictComparison
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRANoZeroUnary PRAStrictConReverse PRAWitnessZFCRefutationBound

theorem refutation_sigma_one : Hierarchy 𝚺 1 refutation := by
  simpa only [refutation, provabilityPred'_val] using
    (provabilityPred' (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)).sigma_prop

theorem zfc_boundCertificate : BoundCertificate refutation := PRA_proves_refutation_bound

/-- Every concrete IΣ₁ no-zero comparison to the actual Foundation ZFC
refutation predicate transfers to the exact comparison in candidate PRA. -/
theorem comparison (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n)
    (h : 𝗜𝚺₁ ⊢ (noZero n a b 🡘 ∼refutation)) :
    PRA ⊢ (Semiformula.lMap embedding (noZero n a b) 🡘
      Semiformula.lMap embedding (∼refutation)) :=
  comparison_if_bound n a b refutation refutation_sigma_one h zfc_boundCertificate
end DiophantineConsistency.PRAWitnessZFCStrictComparison
