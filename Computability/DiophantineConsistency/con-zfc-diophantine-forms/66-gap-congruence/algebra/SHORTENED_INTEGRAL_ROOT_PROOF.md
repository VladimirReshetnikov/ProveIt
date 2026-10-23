# Shortening the integral-root equations

## Status and precise claim

This is a modest, independently checked composition with the new integral-root
construction, not a new low-degree mechanism. The incoming 15-positive-variable
polynomials have operation/degree pairs 90/24, 88/26 and 79/30. The circuits here
have **88/24, 87/26 and 78/30**, respectively. All arithmetic operations,
including multiplication by two or by any fixed coefficient, remain charged.
No variable-count improvement or global minimum is claimed.

The JSON files retain the entire authentic coefficient tuple of the incoming
Integral_Root package, with beta=2^590069-1 and its already shifted MF port.
They do not mix ports with another native instance. Their bound source JSON
SHA256 digests are recorded in RESULTS.json. Ordinary mathematical soundness
and completeness inherit that package's integral-root theorem, ordinary strong
rank theorem and native compiler/refutation calibration. No new proof-assistant
certificate is claimed.

## 1. Sharing the auxiliary gap

All three source equations already compute y0=V+u and subsequently compute
2V+u. Replace the latter two-operation expression by V+y0, using one addition.
The identity 2V+u=V+(V+u) holds over every commutative ring. Nothing else in
these two degree-26/30 polynomials changes, so their output polynomials and
exact degrees are literally unchanged. No positivity or semantic assumption
is used in this step.

## 2. Positive transport shift in the degree-24 equation

The degree-24 source separately imposes

  A_t = q[K0 C+(q-F)-z_old(q-1)]+XC-q = 0.

Replace the supplied positive transport variable by z=z_old-1 and compute

  A_t' = q[K0 C-F-z(q-1)]+XC.

This takes seven operations rather than eight. The exact all-value identity is

  A_t'(z) = A_t(z+1).

All other residuals are independent of this transport variable. Consequently
the new degree-24 polynomial P24' satisfies P24'(z)=P24(z+1), as a polynomial
identity, not just at its zeros. A positive new zero maps directly to a
positive old zero by z_old=z+1.

For completeness, the old integral-root construction starts with canonical
ordinary compiler witnesses, and changes neither their z_old nor the recovered
w. The inherited ordinary proof, Section 7 of ORDINARY_KERNEL.md, establishes

  w=2^R/q > q > F, C>0,
  (K0+w)C-F = (z_old-1)(q-1).

Its left side is strictly positive. Since q>1 and z_old is an integer,
z_old>=2. Thus z=z_old-1 is positive on those canonical witnesses, and all
integral-root reconstructions remain valid. No claim is made that an arbitrary
positive tuple has z_old>=2; the claim is only needed on the canonical
completeness witnesses and is supplied by the inherited theorem.

## 3. Exact degree and metric audit

Translation by a constant preserves the highest homogeneous component of a
nonzero polynomial. Therefore P24'(z)=P24(z+1) has the source's exact degree24
and the same highest form

  4 X^4 Y^6 f^8 u^2 ((eta+zeta)T+hX)^2.

The degree26/30 circuits are the same polynomials as their source circuits,
so their exact degree certificates carry over without a new leading-term
calculation. The transformation script removes dead producers, verifies every
input is live and every producer name is unique, and counts the literal
binary operations after the rewrite. The resulting counts are 88,87,78.

The checker reads upstream JSON as inert data and executes no upstream code.
It checks 360 exact signed full-circuit assignments, 360 modular full-circuit
assignments, and 6000 local identity assignments in total. These finite tests
are regression checks, not the proofs of the identities or of the inherited
semantic theorem. The universal identities and completeness argument above
are the mathematical proof.

## 4. Explored but unclaimed alternatives

A tempting deletion of J=3j+1 would save two more gates. It is not justified:
that congruence forces gcd(q,3)=1 in the main-root divisibility argument.
Changing the native radix exponent to even may destroy the native padding
and multiplicative-order hypotheses. No such deletion is used here.

A free auxiliary coordinate Z=cT-R can be combined with a rational-root
carrier because the strong equation gives gcd(c,U-1)=1. However clearing its
c-denominator increases the degree of the auxiliary residual in the immediate
construction, rather than improving this frontier. It is not included as a
new candidate.
