import IPRADerivations.Core.Basic
import IPRADerivations.Core.Semiring
import IPRADerivations.Core.Definitions
import IPRADerivations.Core.Monus
import IPRADerivations.Core.Order
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.Parity
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Search
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.MultiSums
import IPRADerivations.Core.Permutation
import IPRADerivations.Core.Division
import IPRADerivations.Combinatorics.Binomial

/-!
# Median theorems: object-language iPRA target

STATUS: uncompiled target scaffold, not a completed derivation.

The file has no `sorry` and declares no axiom.  `CertifiedTheorem` packages the
actual endpoint required by ProveIt: a closed formula together with a kernel-
checkable derivation in `Prf PRAAx`.  Constructing every field of
`MedianDerivationPackage` is the formal completion criterion.

The formulas to instantiate are listed below in division-free form.  All lists,
finite laws, traces, permutations, sorting networks, and samples are natural-
number codes decoded only through primitive-recursive projections.
-/

namespace LeanProofs.IPRA.MedianPlan

open LeanProofs.ConciseIPRA
open LeanProofs.IPRA
open Syn
open scoped Fm

abbrev ClosedFormula := Fm PTm 0

/-- A theorem of object-language iPRA, not merely a true ambient proposition. -/
structure CertifiedTheorem where
  sentence : ClosedFormula
  derivation : ([] : List ClosedFormula) ⊢[PRAAx] sentence

/-- Primitive-recursive symbols required by the median development.

Intended equations:

* `len(v)`, `nth(v,i)`, `valid(v)` for sequence codes;
* `ltCount(v,t) = Σ_{i<len(v)} [nth(v,i)<t]`;
* `gtCount(v,t) = Σ_{i<len(v)} [t<nth(v,i)]`;
* compare-swap, insertion, and insertion sort;
* permutation witnesses and sortedness checker;
* lower/upper middle projections;
* weighted prefix masses and absolute-deviation folds;
* binomial/multinomial sample-law folds.
-/
structure MedianSymbols where
  valid : PR 1
  len : PR 1
  nth : PR 2
  ltCount : PR 2
  gtCount : PR 2
  insert : PR 2
  sort : PR 1
  lowerMiddle : PR 1
  upperMiddle : PR 1
  twiceMedian : PR 1
  absDev : PR 2
  weightedAbsDev : PR 2
  oddMedianPMFNum : PR 3
  oddMedianCDFNum : PR 3

/-- Named closed theorem families after universal closure.  Each field must be
filled by an explicit `Prf PRAAx` derivation.

Core formulas, schematically:

`Median(v,t) := valid(v)=1 ∧ 2*ltCount(v,t) ≤ len(v)
                         ∧ 2*gtCount(v,t) ≤ len(v)`.

`TwiceMedian(v,M) := M = lowerMiddle(sort(v)) + upperMiddle(sort(v))`.

`MeanMedianBound(v,M) :=
  (2*S(v)-M*W(v))^2 ≤ 4*(W(v)*Q(v)-S(v)^2)`.

The exact sample law uses integer numerators over denominator `W^(2n+1)`, so no
field division is needed in the object theory.
-/
structure MedianDerivationPackage (S : MedianSymbols) where
  sequence_equations : CertifiedTheorem
  sorting_is_permutation : CertifiedTheorem
  sorting_is_nondecreasing : CertifiedTheorem
  middle_indices_in_range : CertifiedTheorem

  balance_iff_middle_interval : CertifiedTheorem
  twice_median_exists : CertifiedTheorem
  twice_median_functional : CertifiedTheorem
  odd_even_formula : CertifiedTheorem
  quantile_names : CertifiedTheorem
  monotone_transport : CertifiedTheorem

  absolute_deviation_pairing : CertifiedTheorem
  L1_minimizer_iff_median : CertifiedTheorem
  weighted_L1_minimizer_iff_median : CertifiedTheorem
  mean_median_bound_cleared : CertifiedTheorem

  rank_perturbation : CertifiedTheorem
  replacement_breakdown : CertifiedTheorem
  majority_interval : CertifiedTheorem

  finite_distribution_CDF_characterization : CertifiedTheorem
  finite_distribution_median_exists : CertifiedTheorem
  symmetry_center_is_median : CertifiedTheorem
  exact_odd_sample_PMF : CertifiedTheorem
  exact_odd_sample_CDF : CertifiedTheorem

  finite_Jensen_C_function : CertifiedTheorem
  ninther_rank_bound : CertifiedTheorem
  interpolated_median_identity : CertifiedTheorem
  conditional_median_L1 : CertifiedTheorem
  median_filter_correctness : CertifiedTheorem
  theil_sen_collinear : CertifiedTheorem
  one_dimensional_k_medians : CertifiedTheorem

/-!
Completion protocol:

1. Define every symbol with `recDef`, `sumF`, bounded search, pairing, and
   simultaneous recursion.
2. Prove its zero/successor equations at arbitrary terms.
3. Derive the universally closed formulas above using quantifier-free
   induction only.
4. Add the completed module to `IPRADerivations.lean` and the axiom audit.
5. Transfer each theorem through `pra_iff_native` to ConciseIPRA's native
   scalar core.
-/

end LeanProofs.IPRA.MedianPlan
