# Exact leading inverse correction and scope

The matching sharp arguments and this inverse consequence have passed independent review. Let

lambda=log(mu)=1.987312127568072176226565912666...,
C=(3pi^2 alpha^2/(2v))^(1/3)=2.232625307612844922179764700526... .

Their conclusion is

log a_n=lambda n-C n^(1/3)(log n)^(2/3)+o(n^(1/3)(log n)^(2/3)).

The sequence a_n is nondecreasing by appending the last letter, as proved in the frozen report. Define N(Y)=min{n:a_n>=Y} and L=log Y. Then

N(Y)=L/lambda
 +C lambda^(-4/3) L^(1/3)(log L)^(2/3)
 +o(L^(1/3)(log L)^(2/3)),

with

C lambda^(-4/3)=0.893568257650894909124642189453... .

Proof: for any fixed epsilon>0, substitute
n=L/lambda+(C lambda^(-4/3) +/- epsilon)L^(1/3)(log L)^(2/3)
into the logarithmic coefficient formula. Regular variation gives
n^(1/3)(log n)^(2/3)~lambda^(-1/3)L^(1/3)(log L)^(2/3).
Thus the minus/plus choices lie below/above the threshold for sufficiently large L, with an O(1) rounding error. Let epsilon tend to zero.

## Scope

The leading normalized deficit converges to an explicit positive constant, as established by the independently reviewed proof. This is stronger than the frozen Θ theorem.

It is not an asymptotic equivalent for a_n: the unquantified remainder in its logarithm may still diverge. It is not a multiplicative amplitude, a power-law prefactor, an all-orders transseries, a second-order logarithmic deficit formula, or an exact integer inverse rounding rule. No crossover threshold for old finite-data fits has been established.

A second-order calculation would need to resolve the integrated block-length entropy, factors depending on log log n, endpoint layers, the defective critical row mass, and fluctuations about the minimizing path. The leading-order proof intentionally discards these at o(F) precision and cannot supply them without further work.
