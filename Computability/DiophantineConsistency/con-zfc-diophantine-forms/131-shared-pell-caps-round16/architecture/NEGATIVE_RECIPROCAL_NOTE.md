# Negative reciprocal moduli and the remaining obstruction

This is a possible later direction, not an emitted Diophantine certificate or
a variable-count improvement in the current release.

For t>=4 and F=t!, define di=F^2/i-1 for 1<=i<=t. The following elementary
statements are proved:

1. Every di is positive and congruent to -1 modulo F, hence to 3 modulo 4.
2. Every prime divisor of di is greater than t. Indeed a prime <=t divides F
   and cannot divide a number congruent to -1 modulo F.
3. The di are pairwise coprime. A common prime of di,dj divides
   i*di-j*dj=j-i, contradicting item 2 when i!=j.
4. Their product is choose(F^2-1,t), directly by the falling-factorial formula.
5. Every di has a prime p congruent to 3 modulo 4 occurring to odd valuation,
   since a positive integer congruent to 3 modulo 4 cannot be a product solely
   of even powers of such primes and primes congruent to 1 modulo 4.
6. For a prime p congruent to 3 modulo 4 and integers x,y not both zero,
   vp(x^2+y^2)=2 min(vp(x),vp(y)). After dividing by the common power of p,
   any cancellation would make -1 a quadratic residue modulo p, impossible.
   Thus p^(2e) divides x^2+y^2 exactly when p^e divides both x and y.

This provides an anisotropic binary norm at a suitable prime factor for every
row modulus, unlike the current positive reciprocal family. Iterating binary
norms gives a way to force simultaneous zero congruences at a cost in degree
and multiplication gates.

It does not by itself bound the decoded variables or justify merging their
range graphs. Positivity does not survive a nonzero modular target: for
example (p-1)+2 is congruent to 1 modulo p, so a small sum residue does not bound
either summand. A p-adic norm identity with a small nonzero target likewise is
not a natural-domain inequality. Removing a beta quotient range would leave
its modular equation freely solvable whenever that denominator is invertible.

Replacing the current binomial by choose(F^2-1,t) would also require a complete
new factorial recovery and raw-bootstrap argument. A floor fixed-point
variant was considered, but it has not been integrated, checked, or claimed
in this release. The completed 249-variable and 278-variable equations retain
the positive reciprocal product and its established factorial identity.
