# Fixed-mask rank phase for the 80-operation graph

`TenPositive80RankPhase.graph_phase` proves `rankNat p v % 4 = 3` for every
positive zero of the actual 80-operation graph in every model of IΣ₁,
assuming the three explicit symbolic port equalities for β, the low mask,
and the shifted high mask. The port p₁ remains arbitrary. The theorem
is conditional on an actual graph zero; it is not a graph equivalence, halt
statement, literal PDF binding, or an internal iPRA theorem.

The proof uses the same witness supplied by `Direct80FixedDigits`: positive
N gives `q=2^(590069*N)` and the low window digit is 1. Therefore q is 0
modulo 4 and the window coordinate is 1 modulo 4. The model theorem for the
compact low-mask origin supplies lowNat = 2 modulo 4. The graph's transport
gap makes the natural subtractions valid. Applying the existing mod-4
homomorphism from the model difference ring to the exact natural rank formula
then gives the asserted phase. This adapts the argument in
`ArithmeticThirteenOuter.rank_mod_four`; it does not invoke the conjectural
fixed-minus Pell-phase argument. Its provider chain includes the previously
checked fixed-digit and population results and their stated boundaries.

The accepted guarded check is `observations/fixeddigits-attempt05/`. `observations/fixeddigits-attempt01/` through `fixeddigits-attempt04/`
are retained, including the elementary proof elaboration failures and an
intermediate diagnostic trace. The successful object is
`/tmp/tenpositive-80rankphase-al6srfn3/Direct80RankPhase.olean`, SHA-256
`eb82f42db709e064650b0da14bc719ed8d42af72fd474f2474ab0c935fce892d`.
The receipt records source/runner/tool, selected direct prototype and model
provider pins, output, and resources. This exploratory check inherits its
project/package providers; it does not independently audit every transitive
source-to-object edge or dynamic library, and the temporary object is not a
complete reproducible provider bundle.
