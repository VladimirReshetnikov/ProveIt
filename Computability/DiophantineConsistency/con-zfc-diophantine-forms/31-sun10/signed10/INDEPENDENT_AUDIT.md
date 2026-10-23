# Independent review of the ten-integer equation

## Finding and scope

The primary packet `generated/signed10.json` passes the independent review
and finite checks described here. It has exactly ten unrestricted integer
unknowns, **1442 binary arithmetic operations** (851 multiplications, 566
additions, 25 subtractions), and exact total degree

\[
126496\,5^{31}+27064
=589042901992797851562527064.
\]

The independent auditor is `audit_signed10_independent.py`. It imports only
the Python standard library; it imports neither the builder, the ordinary
verifier, nor the shared circuit implementation. Its recorded result is
`INDEPENDENT_AUDIT.json`. Run it from any working directory by giving the
path to that script. All assertions essential to its checks use explicit
exceptions, so the audit remains active under `python3 -O`.

This is an ordinary mathematical review plus finite exact arithmetic
verification. It does not replace the inherited compiler theorem, constitute
an end-to-end proof-assistant certificate, or test whether ZFC is consistent.
The ten-variable universal reduction is Sun's result, including its 2026
preprint dependency. The locally changed mergers and weights are reviewed
separately below.

## 1. Source normalization and the actual fixed coefficients

The review used the primary sources:

* Zhi-Wei Sun, *Further results on Hilbert's Tenth Problem*,
  arXiv:1704.03504v7, Theorem 3.1 and its proof:
  <https://arxiv.org/html/1704.03504v7>.
* Zhi-Wei Sun, *Ten unknowns for Hilbert's tenth problem over the integers*,
  arXiv:2609.01594v2, Sections 3, 4, 6, and 7:
  <https://arxiv.org/html/2609.01594v2>.

The parent residual file has SHA256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.
These are the exact upstream bytes, without an added terminal newline.
The active coefficient tuple is the complete
`wang943-mixed-121x8801` instance. The audit compares all four local payloads
with `../coefficients/COEFFICIENT_BINDING.json`, checks their compressed and
uncompressed hashes, and verifies their bit lengths. Historical coefficient
references inside the parent source are not used to specialize the equation.

The polynomial supplied to Sun's source construction is

\[
P(a,n)=\sum_{j=1}^{22}r_j(n_1+1,\ldots,n_{31}+1)^2,
\]

independent of the dummy input a. This is a direct fixed Diophantine
definition, so setting a=0 requires no choice of an unspecified enumeration
index. The shift changes nonnegative source witnesses into the positive
parent witnesses. The fifth residual at all parent variables equal to one
is 1, independently of the ports. Hence the constant term of P is positive,
as required by Sun's normalization, without adding another witness or
increasing its degree.

The independent audit expands all 22 shifted squares symbolically, with the
four coefficient ports retained as indeterminates. It reconstructs every
one of the 402 factorial-weighted coefficient recipes and checks every
reversed-base exponent. All records have dummy-input exponent zero; the
source has 31 witness variables and degree 4. Every coding exponent is
nonnegative because
\(e(\alpha)\le4\,5^{31}<5^{32}\).

For the actual tuple the audit independently verifies
\(|c_\alpha|+1<2^{4269855}\). Since each factorial multiplier is a positive
integer, this also bounds the ordinary coefficient magnitudes. The source
radix is the fully specified even power
\(\beta_S=2^{4269882}\); its delivered bytes are authenticated separately.
The numerical inequality

\[
2\cdot4!\cdot33^4=56924208<2^{27}
\]

therefore establishes precisely the strict coefficient bound in the proof
of Sun 2021, Theorem 3.1, for p=2, degree 4, and 31 source witnesses.

A formula-by-formula comparison with that proof confirms the expressions
for the digit mask, the factorial-weighted reversed polynomial, N0, N1,
N, T, J, the intermediate S and R, and the resulting X and Y. In particular,
the mask's largest position is included, the geometric sum has 9t+1 terms
before multiplication by the base, and p=2 makes the denominator p−1 equal
to one. No variable exponent occurs. The shared-power implementation is
checked against the literal 402-term reversed sum with the actual fixed
coefficients.

## 2. The Lucas and binomial bridge

The bridge formulas match Sun 2026 (6.1)–(6.7), and the modified Lucas
expressions match (3.1)–(3.7). The substitution \(\xi=zx\) is exactly the
witness sharing used in Section 7. The introduced abbreviation
\(P_n=U^2V\) only shares repeated arithmetic.

The positive direction uses the bridge followed by the full residue-class
interpolation theorem, Section 4. It is essential that the theorem supplies
one suitable positive \(\xi\), divisible by the prescribed positive z,
and then permits every residue class for y modulo that same \(\xi\).
The construction uses the quantifiers in this order. It never selects a
new \(\xi\) after choosing the congruence required by the divisibility merger.

The reverse direction invokes the bridge only after recovering all of its
hypotheses: b a square, O positive, \(\xi\ne0\), both remaining square
conditions, and S dividing T. The positivity argument supplies the strict
inequalities used by the source construction. Arbitrary negative inputs
to the final polynomial are allowed; they are not assumed positive in this
reverse direction.

## 3. Quintic merger

The replacement

\[
\pi(v)=(v^3-v-1)(v^2+23)
\]

has no rational zero and has a zero modulo every nonzero integer. A cubic
rational zero would have to be 1 or −1, neither of which works; the quadratic
has no real zero. For an odd prime other than 23, the cubic is separable
with discriminant −23. If it has no linear factor, its Frobenius permutation
is a 3-cycle, so its discriminant is a square. Thus either the cubic or the
quadratic has a simple root. At 23, the cubic root 3 is simple. At 2, the
quadratic has roots to all powers because −23 is 1 modulo 8. Hensel lifting
and the Chinese remainder theorem prove the claim for arbitrary moduli.

With \(r=T+Sy\), its homogeneous form is

\[
\Theta=(r^3-rS^2-S^3)(r^2+23S^2),\qquad
\Sigma=\xi S^5.
\]

The integer S is odd and hence nonzero. Thus Theta is nonzero for every
integer assignment, since a zero would give a rational root of pi.
If S divides T, a root of pi modulo \(|\xi|\) specifies precisely a residue
class of y in which Sigma divides Theta. Conversely, if a prime divides S
to order alpha and T only to order beta<alpha, then the two homogeneous
factors have respective orders 3beta and 2beta. Consequently S to the fifth
power cannot divide Theta. This proves the reverse divisibility implication,
including primes 2 and 23; no exceptional prime is omitted.

## 4. Coprime square merge and its boundary case

Write

\[
q_0=1+(3O-4)b^2z^2,\qquad r_0=bq_0,\qquad b=1+3f.
\]

For z nonzero, the actual bridge expression \(O=f^2l^2\Delta\) makes
\(|r_0|>1\). If b=1 then f=0, so O=0 and
\(r_0=1-4z^2\le-3\). Otherwise \(|b|\ge2\), and
\(q_0\equiv1\pmod{b^2}\) excludes zero. Hence \(|r_0|\ge2\).
The missing possibility b=−1 is excluded by b=1 modulo 3.

Since \(\gcd(b,q_0)=1\), a square r0 makes the two factors signed squares
of the same sign. A negative square cannot be 1 modulo 3; thus b and q0
are positive squares. If O were nonpositive, q0 would be negative, so O
is positive. This proves the needed soundness without any prior sign
assumption on f, l, or Delta.

Completeness needs a little more than the abstract assertion O>0. The
unqualified assertion that the scaled Pell condition works for every
positive O would be false at O=1 and b=4. Here the actual positive bridge
witnesses have f>0, b≥4, and g≥b. The positive integer Delta is divisible
by g, so \(O=f^2l^2\Delta\ge4\). Hence \(d=3O-4\) is a positive nonsquare
(it is 2 modulo 3). A positive Pell unit for d has a power whose second
coordinate is divisible by b: reduce the norm-one unit modulo b and use
the finite order of its class. Writing that coordinate as bz supplies the
required positive z. It remains available as the prescribed divisor in
Sun's interpolation theorem. The final proof explicitly includes this
boundary-case argument.

## 5. Structural weights and exact norm

Let \(r_1=(P_n^2-4)K^2+4\) and \(r_2=DFI^*\). For every integer assignment,

\[
|r_1|\le(P_n^2+4)K^2+4\le(P_n^2+K^2+2)^2.
\]

The second inequality follows by subtraction: its difference is
\(P_n^4+K^4+P_n^2K^2+4P_n^2\), a sum of nonnegative terms. Thus, once
z is known nonzero, the signed integer weights

\[
w_0=1,\quad w_1=r_0,\quad
w_2=r_0(P_n^2+K^2+3)
\]

satisfy strict successive separation of the absolute root magnitudes.
In a multiquadratic splitting field, an automorphism changing any root
has a largest changed index. That changed term dominates all earlier
changed terms, so it cannot fix their weighted sum. A rational weighted
sum therefore implies that every nonzero square root is rational and hence
integral. Complex absolute values handle negative radicands; zero radicands
already are integer squares. Signed weights do not change the argument.

The auditor independently multiplies all eight signed linear factors in
four formal indeterminates. After the odd radical powers cancel it obtains
35 terms. It then cuts the delivered graph at `norm_center` and the three
`scaled_A` ports and expands that part of the delivered circuit separately.
The two exact integer polynomials agree.

If Sigma is zero, the norm is Theta to the eighth power, which cannot
vanish. Hence every zero of the final polynomial has \(\xi=zx\ne0\),
justifying the preceding separation argument. A vanishing factor divided
by Sigma makes the weighted root sum rational. The roots are therefore
integers and Sigma divides Theta. The reverse merger, coprime square
argument, and Sun's reverse bridge now apply in the correct order. The
positive direction uses the same residue-class interpolation to realize
the divisibility condition and chooses the integer m from the resulting
integer roots. No extra unknown is introduced in either direction.

## 6. What the executable audit establishes

Beyond the source and norm identities, the audit verifies that all 1570
graph nodes are live, that its only variable leaves are the ten declared
unknowns, and that every operation is binary addition, subtraction, or
multiplication. It independently transcribes every named formula and
compares all 53 named nodes on 27 assignments at each of three primes:
**4293 named-node comparisons** with the actual fixed coefficients.
The assignments include all-zero, all-one, all-negative, individual zero
coordinates, and further signed assignments. The cases f=0 and either
x=0 or z=0 receive explicit specialization checks.

The graph supplies a total-degree upper bound. Setting all ten variables
equal to one common indeterminate and computing the coefficient at that
degree gives nonzero residues 955, 398752, and 574080 modulo 1009, 1000003,
and 1000033 respectively. Any one proves that the reported upper bound is
attained. These computations use only delivered graph data and independently
authenticated fixed leaves.

Finite regressions also exercise the structural positivity boundary,
the root bound, and prime-power roots of the quintic. Their scope is
deliberately finite; the proofs in Sections 3–5 establish the universal
claims. No gap was found in the local simplifications or in their interface
with the cited source reductions.
