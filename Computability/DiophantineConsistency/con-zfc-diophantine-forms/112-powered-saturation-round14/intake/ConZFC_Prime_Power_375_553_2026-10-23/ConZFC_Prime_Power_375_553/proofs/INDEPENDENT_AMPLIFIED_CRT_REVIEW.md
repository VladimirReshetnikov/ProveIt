# Independent ordinary review of the amplified CRT argument

The reviewed source is `work_alt/AMPLIFIED_CRT_PROOF.md` and its final
linear-amplification interface: T=t!, K=2^23 R, N=B^K, with t>=1 and
the explicit raw guard B>=2. This is an independent mathematical review
performed during the same AI-assisted research session, not external peer
review or a proof-assistant certificate. It does not re-establish the
inherited C222-to-ZFC calibration.

## Prime-power range implication

The implication

    p^e divides binom(a,k)  =>  a mod p^e < k

is valid for a>=0, k>=1, e>=1. If a<k, the conclusion is immediate.
Otherwise, assuming that none of the k consecutive numerator factors is
divisible by p^e also rules out a multiple of every higher power p^j in
the same interval. The valuation summands with j>=e then vanish. At
most the first e-1 summands can contribute, and each is at most one.
This contradicts valuation at least e. If a multiple occurs at a-r with
0<=r<k, the least nonnegative residue of a modulo p^e is at most r.
The result is correctly stated only in this direction.

## Amplification and the index coordinate

For d_i=1+(i+1)t!, every prime divisor is greater than t. Distinct d_i
are coprime: a common prime would divide i-h, hence would be at most t,
and would divide t!, contradicting d_i=1 modulo that prime.

For p^m dividing d_i exactly, the amplified binomial condition gives a
small representative modulo p^(Km). The weaker index congruence modulo
B already says C=i modulo p. Because both the recovered index and i
belong to [0,t-1], which has length less than p, they are equal. This
justifies the passage from a modular local equation at C to the intended
equation at i. The exact-value step then uses p^(Km)>=2^K and the strict
local bound, as required.

## Completeness precision

The CRT choices modulo d_i^(2K) are compatible and can be taken positive
and at most B^(2K)=N^2. One falling-factorial term is divisible by
p^(2Km). Subtracting the denominator valuation loses at most
v_p(k!)<=k-1<=K-1<Km, so the binomial valuation remains at least Km.
This is the reason for the doubled precision. The proof does not make
the false assertion that ordinary small residues alone imply binomial
divisibility to the same precision.

## Product and radix bootstrap

The product identity is valid with

    Q=T^t(t+1)^t+2,

because the intended product is at most T^t(t+1)!<=T^t(t+1)^t<Q,
and its representative is below TQ-1 even at t=T=1. Both factors T^t
and (t+1)^t are already present in the source.

The raw B>=2 guard permits recovery of N=B^K before the product has
been interpreted. The factorial numerator V=(rho+1)^t dominates the
first exact-binomial digits. After that factorial graph is established,
Q<V follows from the integer gap between T(t+1) and rho+1; the t=1
case is checked separately in the proof. The second exact-binomial
digits are bounded by V^t and hence by the radix, since K>=t.

Finally, the aggregate representative bound gives n<=9N^2<=N^6 for
N>=2. All lower range indices are at most R. Thus all needed lower
digits are at most N^(6R), whereas the chosen radix exceeds
N^(K+1), with K=2^23 R>=6R. This is a valid strict inequality and
does not use prior range correctness. There is no circular factorial,
product, or range assumption in this order.

## Conclusion

No mathematical defect was found in the new amplified CRT reduction.
The signed compilation's earlier positivity recovery is compatible
with this argument: it establishes the true positive powers and the
positivity of the factorial candidate from its two ceiling rows before
using the full factorial identity. The separate finite verifiers bind
these ordinary arguments to the emitted quadratic graph.
