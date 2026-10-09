# Reference software

Only standard-library Python is used. All `partition` sequences use restricted-growth/canonical labels: the first block is 0 and subsequent new blocks are numbered consecutively. Inputs precede outputs.

`disk_algebra.compose(first, second)` computes `second o first`. `matrix_product(a,b)` uses ordinary algebraic order `a*b`. Therefore `matrix(compose(P,Q)) == matrix_product(matrix(Q),matrix(P))`, with a rejected actual product represented by the zero matrix. A dual number `x+y*epsilon` is packed as `x+2*y` in `{0,1,2,3}`. No tropical or Boolean substitution is used.

`compressed_search.solve` returns an all-cap representative table for a supplied homogeneous source. `Result.query` tests a specific cap and module charge subset; it does not check ambient geometry. `Result.certificate` records original generated-row indices. `Result.witness_statistics` evaluates additive counts on a retained witness DAG. Literal expansion requires an explicit output budget.

`checker.check(source, certificate)` requires the source independently and reconstructs every generated candidate. Its graph and feature kernels are independent of the producer's, but its compiler and record types are shared. Its certificate checker deliberately accepts any small source-subset certificate satisfying cost-dominating span inclusion; it need not match the producer's tie-breaking basis.

`mesh_oracle` is an independent finite triangulated-surface replay oracle. It does not import the producer's topology. It is intended for small audits, not binary-size expansion of huge witnesses.

`star_search` handles a different language: unbounded independent repetition with nonnegative costs and one control state. It is not used for fixed exponent queries.

Default solver/checker guards bound feature allocation, composition pairs and compiled syntax. Guard exceptions are inconclusive. The mathematical asymptotic algorithm is stated without those operational caps. This is research software, not a hardened parser for arbitrary hostile inputs or a replacement for native source validation.
