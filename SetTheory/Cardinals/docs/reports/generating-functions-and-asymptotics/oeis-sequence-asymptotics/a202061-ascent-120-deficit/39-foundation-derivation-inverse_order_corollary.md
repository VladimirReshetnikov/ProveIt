# Inverse-order corollary of the matching logarithmic deficit

Conditional only on the proof of the two-sided theorem in log_scale_refinement.md; no further analytic assumption is needed.

Let a_n=A202061(n), lambda=log mu, and define the integer threshold

N(Y)=min{n>=0:a_n>=Y}.

The sequence is nondecreasing: append a copy of the last letter to every nonempty avoiding ascent sequence. This preserves the ascent bound; a newly created 120 pattern using the repeated final letter would already exist using its prior copy. The map is injective. The growth lower bound ensures N(Y) is finite for large Y.

Put Phi(x)=x^(1/3)(log x)^(2/3), and suppose the established theorem gives

c Phi(n)-O(1)<=n lambda-log a_n<=C Phi(n)

for sufficiently large n, with c,C>0. Then

N(Y)=log(Y)/lambda+Theta((log Y)^(1/3)(log log Y)^(2/3)).           (I)

The correction is positive. This is an order statement, not an asymptotic equivalent, and does not identify a leading inverse coefficient.

Proof: set L=log Y. The coefficient upper bound first implies N(Y)>=L/lambda-O(1). Applying it at n=N(Y) then gives

lambda N(Y)-L>=c Phi(N(Y))-O(1)>=c' Phi(L)

for some c'>0 and all sufficiently large Y. For the reverse inequality choose

n=ceil(L/lambda+K Phi(L)).

Since Phi(n)/Phi(L)->lambda^(-1/3), any sufficiently large fixed K has

lambda n-C Phi(n)>=L

for all large L. The coefficient lower bound therefore gives a_n>=Y, and hence N(Y)<=n. This proves (I). The integer ceiling contributes only O(1), which is absorbed by the growing correction scale.
