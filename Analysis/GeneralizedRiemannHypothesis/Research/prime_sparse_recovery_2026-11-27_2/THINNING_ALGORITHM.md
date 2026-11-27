# Deterministic prime-set construction

Inputs: q≥2, rational 0<δ<1/2. List the characters of the finite unit group.
Choose integer m≥256 δ⁻² log(16 φ(q)) of that order. For integer X, list all
primes in (X,2X) coprime to q and integer weights v_p=(p-X)^3(2X-p)^3.
Increase X (e.g. doubling) until the window is nonempty and both exact tests pass:

1. |∑ v_p χ(p)|² ≤ (δ/4)² (∑v_p)² for all nonprincipal χ;
2. m max v_p ≤ ∑v_p.

Under the analytic lemma these checks terminate, at X=O(δ⁻² log(2q)
log(2q/δ)). For rational δ all finite bias comparisons are algebraic and
can be decided by root isolation. The initial scale can be 2, with doubling.

For each prime p set π_p=m v_p/∑v_p. For each real/imaginary character
coordinate a, set s_a=∑π_p a_p. Use t=δm/8 and λ=δ/16. For a partial
assignment of bits b_p, the conditional potential is

```
Σ_(a,σ=±1) exp(λ*(σ*(Σ_fixed a_p b_p - s_a)-t))
                * Π_unfixed ((1-π_p)+π_p*exp(λ*σ*a_p))
```

Iterate primes in increasing order. If π_p is 0 or 1 use the forced bit.
Otherwise evaluate the two resulting conditional potentials to absolute
error at most 1/(8N), N the candidate count, and choose the smaller estimate.
Exact ties in the estimates can be broken arbitrarily. This is a finite
algorithm because the arguments are computable real numbers; use certified
interval arithmetic rather than ordinary floats for this guarantee.
The starting potential is at most 1/4; the accumulated increase at most 1/4;
the final potential <1. Hence all coordinate deviations are <t, the retained
cardinality is between m/2 and 2m, and its uniform character bias ≤δ.

Output S={p:b_p=1}. To certify output independent of the construction, check
primality, coprimality, distinctness, and the exact character-sum inequalities
|∑_(p∈S)χ(p)|²≤δ²|S|². The recovery theorem then applies regardless of GRH.

The supplied Python experiment uses a simpler randomized thinning and exact
post-selection checks for q=24; it does not implement this large conservative
conditional-expectation construction. No efficiency claim for enumerating
φ(q) characters or certified exponential calculations is made.
