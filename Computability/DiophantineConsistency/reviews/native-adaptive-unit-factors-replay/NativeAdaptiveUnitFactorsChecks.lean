import DiophantineConsistency.NativeAdaptiveUnitFactors

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.NativeAdaptiveUnitFactorsChecks
open NativeAdaptiveUnitFactors

example (q Z N U a c D f I V y : ℤ)
    (h : firstFactor q Z N*mainFactor U a c D*auxFactor a f V y*strongFactor a f I=1) :
    firstFactor q Z N=1 ∧ mainFactor U a c D=1 ∧
      auxFactor a f V y=1 ∧ strongFactor a f I=1 := (product_one_iff ..).mp h

-- Generic factors may be zero or negative; they are not assumed positive.
example : firstFactor 0 1 0=2 ∧ mainFactor 1 0 0 0=0 ∧
    strongFactor 0 0 0=4 ∧ auxFactor 0 0 1 0= -3 := by
  norm_num [firstFactor,mainFactor,strongFactor,auxFactor]

-- The factorization can have all four unit factors, including a zero strong index.
example : firstFactor 0 0 0*mainFactor 0 0 0 0*
    auxFactor 0 1 0 1*strongFactor 0 1 0=1 := by
  norm_num [firstFactor,mainFactor,auxFactor,strongFactor]

#print axioms first_ne_neg_one
#print axioms main_ne_neg_one
#print axioms strong_ne_neg_one
#print axioms aux_ne_neg_one
#print axioms product_one_iff
end DiophantineConsistency.NativeAdaptiveUnitFactorsChecks
