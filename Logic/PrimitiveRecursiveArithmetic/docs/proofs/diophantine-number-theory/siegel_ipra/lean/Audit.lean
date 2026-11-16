import Arithmetic
import FiniteSearch
import QuarticExample
import Specifications

#print axioms SiegelIPRA.positive_product_sum
#print axioms SiegelIPRA.factor_natAbs_sum
#print axioms SiegelIPRA.difference_of_squares
#print axioms SiegelIPRA.square_gap
#print axioms SiegelIPRA.quartic_factorization
#print axioms SiegelIPRA.quartic_bounds
#print axioms SiegelIPRA.no_square_between
#print axioms SiegelIPRA.mem_scan
#print axioms SiegelIPRA.scan_covers
#print axioms SiegelIPRA.mem_le_listBound
#print axioms SiegelIPRA.covers_bounded
#print axioms SiegelIPRA.list_iff_bound
#print axioms SiegelIPRA.prefix_always_bounded
#print axioms SiegelIPRA.bound_not_unbounded
#print axioms SiegelIPRA.quartic_seven_complete
#print axioms SiegelIPRA.sample_certificate_valid

-- Type checks of specifications do not assert proofs of these propositions.
#check SiegelIPRA.RungeBoundTarget
#check SiegelIPRA.RungeEnumerationTarget
#check SiegelIPRA.GenusFamilyTarget
#check SiegelIPRA.PositiveSiegelTarget
#check SiegelIPRA.CountSiegelTarget
