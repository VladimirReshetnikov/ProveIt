# A new route investigated, and why it is not yet an endpoint

The desired extra variable deletion would merge the first and main Pell roots
rather than the two auxiliary roots. With X=qw,Y=sq^3 supplied polynomially,
transport uses modulus q−1 and index recovery uses q^4, which are coprime.
A rational biquadratic norm of lambda*tau+D appears to merge the two positive
gaps r and gamma into a single positive witness. A weight
lambda=H(q−1)+1 is a unit modulo q−1 and is large enough to dominate the signed
main-root error in a positivity estimate. This initially suggests an
11-positive construction of far lower degree than the inherited degree958.

The missing condition is not a minor sign issue: the source requires
D = X+ac modulo H. The combined integral numerator only recovers the index
and transport congruences; with a unit weight lambda it does not retain that
main-root residue. If instead lambda is a multiple of H and the merged
coordinate is likewise scaled by H, the main-root residue is retained, but
transport is weakened to

    (q−1) divides H*Bt,

rather than (q−1) divides Bt. These are genuinely different. For example take
q=32,Y=q^3,X=192,H=4Y(X+1)+3. Then 31 divides H despite q=2 mod3,
q|X and q^3|Y. With toy K0=1,F=1,C=1 (alpha=30), Bt=192 and 31 does not
divide Bt. This is a counterexample to the proposed cancellation step, not
a claimed solution or counterexample to any full consistency polynomial.

One can force gcd(H,q−1)=1 by imposing (q−1)|Y, since H then equals3 modulo
q−1 and q=2 mod3. But the canonical half-binomial Y is determined by X,R,
not a free padded coordinate. No cofinal completeness theorem licenses that
extra congruence. It must not be inserted silently.

This failure exposes a concrete architectural obstruction: three residue
channels (first-root transport, main-root index, and main-root base residue)
cannot be collapsed into the naive two-root sum without losing a channel.
A future result could overcome it with a source construction guaranteeing
coprimality, or a nonlinear primitive norm that retains the main residue
without multiplying the transport quotient by H. Neither is established here.
