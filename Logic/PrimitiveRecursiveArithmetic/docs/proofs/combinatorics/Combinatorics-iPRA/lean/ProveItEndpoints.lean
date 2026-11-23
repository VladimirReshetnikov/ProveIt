/- Optional integration file. From the ProveIt repository root at
   b4de6f7a61a3fcf9740373b93089830f79e342f6, with IPRADerivations built:
   lake env lean /absolute/path/to/ProveItEndpoints.lean
   Names and signatures were inspected at that pin. This integration file
   was not included in the standalone kernel runs described in the report. -/
import IPRADerivations.Combinatorics.FiniteBijection
import IPRADerivations.Combinatorics.Vandermonde
import IPRADerivations.Combinatorics.Catalan
import IPRADerivations.Combinatorics.Fibonacci
import IPRADerivations.Combinatorics.RamseyBounds
import IPRADerivations.Core.Search
import IPRADerivations.Foundations.StrongInduction

#check LeanProofs.IPRA.fst_pair
#check LeanProofs.IPRA.sum_zero_elim
#check LeanProofs.IPRA.Search.search_found
#check LeanProofs.IPRA.strong_ind
#check LeanProofs.IPRA.Combinatorics.FiniteBijection.finite_bijection
#check LeanProofs.IPRA.Combinatorics.Vandermonde.vandermonde
#check LeanProofs.IPRA.Combinatorics.Catalan.cat_spec
#check LeanProofs.IPRA.Combinatorics.Fibonacci.fibonacci_lucas
#check LeanProofs.IPRA.Combinatorics.RamseyBounds.neighbor_split
