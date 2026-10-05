# Independent proof and finite-certificate review of the three-adic order range

PASS: the precise family q=B*3^k,R=2*3^e-3 cannot satisfy the authentic
repunit/divisor/window conditions when B=2^d and d=5^n with2<=n<=16.
This does not exclude all n, other q/R families or all direct-X83 zeros.

## Proof challenge

From3^k<=3B^3(B-1)<3*2^(4d), the exact inequality2^11<3^7 yields
11k<11+28d. Every certified modulus with2^h=1 and h dividing d divides
B-1. The literal repunit therefore forces its3-order to divide k.
If O is the lcm of the certified orders,11O>=11+28d is an exact
sufficient contradiction. No primality of the moduli is required.

The proposed orders450 and44848301000 have the complete factorizations
printed in the author proof. Root independently derived those prime
factorizations by trial division of the order integers, and used a new
square-and-multiply implementation to check both powers of2, both full
powers of3 and all eight proper-prime-divisor residues. The resulting
residues match the author's receipt exactly. Each proper order would
divide the proposed order divided by at least one of its prime divisors;
the non-one residues exclude every such case, proving both exact orders.

The independently recovered lcm is403634709000. Its criterion covers all
multiples of125 up to158570778535, including5^16. The smaller450-order
certificate handles d25. Root checked every exponent in3..16 and the
endpoint difference167520861489 using small integer arithmetic only.
Neither B=2^(5^16) nor any q,R,X,Y is materialized.

## Retained boundaries and correction

**Review remark 1.** At n17, k=403634709000 passes the two fixed order
requirements and the necessary size bound:3^k<2^(2k)<2^(3d)<3B^3(B-1).
The exponent comparison2k<3d checks exactly. This refutes an all-n
inference from just these finite tests. It does not establish the full
repunit, any index e, canonical divisibility, or a compiler zero.

**Review remark 2.** The pre-freeze prose summary said seven distinct
order primes. The exact set {2,3,5,41,107,10223} has six members.
The eight proper-power tests count2 and5 twice, once for each order.
The author corrected and retained this as numbered Remark2; its helper
already counted six. No certificate or theorem conclusion changed.

**Open question 1.** Additional moduli or a uniform order theorem could
extend the range, but n>=17 is not settled here. A finite search record
must not be promoted to an all-size order statement. Other canonical
relations and full83 soundness remain outside this theorem.

## Evidence scope

Root read the full author proof and helper inertly, bound the final trio
and all four dependency/read-span records, and independently checked the
mathematical chain above. The original reviewer scalar helper ran only
before freeze, with normal and optimized outputs byte-identical. Its
only computations are these two small modular certificates, factorization
of their orders, the lcm and endpoint inequalities. It neither imports nor
runs author or predecessor code. The frozen helper and receipt accompany
this review; they are not instructions to replay them.

No source array was evaluated or used for degree propagation, and no
native zero, enormous compiler numeral or whole compiler was run.
All source-level universality and outer premises are inherited at their
stated, previously reviewed interfaces. No operation bound changes.
