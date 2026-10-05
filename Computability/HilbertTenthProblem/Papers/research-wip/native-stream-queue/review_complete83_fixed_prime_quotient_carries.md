# Independent review: fixed-prime quotient carries

**PASS; no correction requested.** The complete frozen author proof, helper
and receipt were read inertly. The quantified proof and source interface
pass the independent challenge below. The new reviewer separately checks
finite arithmetic, source polynomials and every dependency pin.

| Author artifact | SHA256 |
|---|---|
| `complete83_fixed_prime_quotient_carries.md` | `53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46` |
| `complete83_fixed_prime_quotient_carries.py` | `210506dc2ff70393a975d1768bea748a733f5f6c9b3b7790052c73336315912c` |
| `complete83_fixed_prime_quotient_carries.json` | `59ef0669c6708c820c67332667b288ac71c27d362e9793847dc7accd3d3b07d6` |

## Mathematical conclusion and scope

For every fixed authentic original compiler, the construction removes the
odd-primary carry hypotheses on the specified infinite subsequence. It
provides positive outer/input choices whose prescribed half-binomial value
Y is divisible by the cube of the odd part A of q. The enlarged selector z
has no proved binary population bound. Thus a full positive 83-source zero
is still conditional on the stated binary condition. Neither a rejected
ordinary input nor an unconditional universal 83-operation bound follows.

The set S of selected primes is fixed by the compiler, but their exponents
in A are not fixed. That distinction is essential: the S-supported part
grows linearly in the subsequence parameter and provides the quadratic
aggregate saving needed to fit the input interval.

## Independent proof challenge

**Subsequences.** In the plus shape n=9^j is odd and 1 modulo 4. For every
p dividing B+1, odd-prime lifting gives
`v_p(B^n+1)=v_p(B+1)+v_p(n)`. Since only the prime 3 divides n, and 3
already divides B+1, the complete S-part is exactly `(B+1)n`.
In the minus shape m=9^(phi(d)j) is 1 modulo d and modulo 4;
`n=((d+1)m-1)/d` is integral and 1 modulo 4, and `D+1=(d+1)m`.
Applying lifting to `(2B)^m-1` gives exactly `(2B-1)m` as the S-part.
Both sets S exclude 5 and both satisfy `Bn<A_S<=(2B-1)n`.
The choices retain the source's required congruence class, not merely
the approximate sizes q~Q^2.

**Carry forcing.** Write `b_p=a_p+tau_p` and
`e_p=max(1,2a_p-tau_p)`. Imposing
`R+1=-2p^b_p mod p^(b_p+e_p)` is equivalent to the quotient of
`r+1=(R+1)/2` being -1 modulo `p^e_p`. The factor 2 is necessary.
This simultaneously fixes the exact denominator depth b_p and places
e_p terminal digits p-1 in the positive quotient. Adding the quotient
to itself supplies at least e_p carries. Independently, the binomial
identity at `N=r+1` gives

`v_p(binomial(2r,r)) = b_p + v_p(binomial(2eta_p,eta_p))`.

Consequently the central valuation is at least `b_p+e_p>=3a_p`.
The maximum with 1 handles `tau_p>=2a_p` while still giving
`e_p<=2a_p`. This changes quotient carries without deepening every
denominator resonance, so the earlier all-prime depth obstruction is
not being bypassed by a hidden contradictory assumption.

**CRT and the outside-prime search.** The total added modulus is
`Cextra=product_(p in S) p^e_p<=A_S^2`. All prime-power congruences are
compatible with the original m0 class because m0 has only primes 2 and 5
and G0 is a unit at each prime of A. The residue is chosen modulo
`M=m0*A*g*Cextra`. Along this residue class, the quotient
`(r+1)/(Ag)` has an affine slope that is a unit at every outside prime.
It generally is not a unit at S; the proof correctly does not require
that. The S-unit conditions have already been fixed by the quotient
congruences. Inclusion-exclusion on A_out finds an outside-unit value
within `floor(sqrt(3A_out))+1` consecutive representatives; the case
A_out=1 is separate and immediate. The lower bound
`phi(A_out)/2^omega(A_out)>=sqrt(A_out/3)` correctly uses the exclusion
of 5. It is not the same inequality with unrestricted odd factors.

**Positivity before positive-quotient arguments.** Initial affine
congruences can give signed R. The proof first bounds
`z<=m0*A*g*Cextra*(floor(sqrt(3A_out))+1)` and then applies its explicit
threshold. Since `g<=D+1`, `A<2Q` and `A_S=O(n)` for this fixed
compiler, the upper bound is `O(n^3 Q^(3/2))`, below q of order Q^2.
The sparse minus subsequence causes no difficulty: an inequality true
for all sufficiently large n is true for its sufficiently large
members. Only after positive slack and the direct packed-index bounds
are obtained is the positive-quotient carry argument used. There is no
reuse of the old `z<=4d` restriction.

The exact source slack is `alpha(k)=S0-ell*k`, with `S0>q/2`.
Its nonnegative allowed interval is
`k<=floor((S0-1)/ell)`. The fixed packed R does not change when the
ordinary input representative changes. The input exponent remains at
least `10D+b`, and the transport period is preserved. The same direct
positive-slack argument gives `3q+1<R<q^4-q^3`, hence the inherited
near-power and half-binomial domain.

**All remaining odd primes fit.** At outside primes the exact depth alone
supplies `c_p>=b_p>=a_p`, so each needed local precision is at most 2a_p.
At S no local input condition remains. Therefore
`Hreq<=A_out^2=A^2/A_S^2` without any unproved carry hypothesis.
For d>=25, the elementary bound `4^d>12d(d+1)` implies
`A_S^2>6ell`. Both shapes satisfy `q>=A^2/3`. These give the strict
margin

`ell*Hreq < A^2/6 <= q/2 < S0`.

Every least CRT representative fits the positive interval, including
the empty-CRT case Hreq=1, k=0. There is no endpoint error from replacing
the sharp interval by this sufficient stronger bound.

At each deficient outside prime, the normalized quadratic polynomial
is `eta_p-y` modulo p, with derivative -1 modulo p. Its root is unique
and a unit, including at p=3. The actual input exponential map is a
residue isometry at every precision, so it attains that root in one
class of k. The new proof can require precision `a_p<h<=2a_p`;
this is justified by the all-precision lemma, not by the old restricted
input budget. CRT combines the classes without changing R, q, z, the
fixed ports, or the transport congruence. Thus the odd cube divisibility
is proved on the permitted ordinary input progression.

**Open binary condition.** The large starting input still separates the
binary denominator valuations from u(k), so the inherited exact binary
criterion is independent of the chosen odd-prime lift. However, its
truth for this new z is unproved. The previous small-z binary theorem
cannot be substituted here. Until that condition holds, the argument
does not supply the integer witness `s=Y/q^3` or a full positive Pell
completion. The author preserves this boundary.

## Read and evidence scope

The complete author proof, helper and saved receipt were read. The
author helper's synthetic A0 is explicitly not a computed compiler mask
constant, and its relaxed small-d LTE tests are not actual compiler
instances. Its bounded evidence supports precisely the recorded scope.
No author helper was replayed. All seven named dependency hashes and
byte counts are independently authenticated by the fresh reviewer.
The accepted source-coupled lifting
proof and the aggregate input-budget proof and independent review were
also read completely. The exact quotient-carry identity was checked
directly, in addition to the accepted carry-budget dependency. The
native/Pell/half-binomial/actual compiler theorems remain inherited at
their pinned scope; this is not another full audit of all their
ancestors.

The fresh reviewer authenticates the unchanged 83-source JSON and
independently expands a selected 23-row interface as sparse integer
polynomials. It proves C=z, W=0, u=2dx+b, the exact affine R with its
constant z term retained, and the transport expression. The full
83-row/18-witness ledger is guarded, but no full source zero or new
degree claim is tested. The source chart remains 46 multiplications
and 37 additions.

Fresh finite arithmetic independently checks:

- 480 forced-quotient carry cases, including saturated tau, with 40
  direct integer binomial comparisons; carries are counted by literal
  base-p digit addition.
- 64 synthetic enlarged-CRT systems, checking the factor 2, the fixed
  S quotient tails, exact outside depths, and the bounded coprime search.
  Their intermediate R may be signed; they are not compiler instances.
- 24 normalized input permutations at precisions through 2a, comprising
  5,976 residue values, each composed with the unique local unit root.
- Ten plus/minus subsequence checks. Large minus exponents are kept as
  exact index/valuation identities rather than materializing enormous
  powers. The small numeral cases are not represented as authentic
  compiler programs.

These checks corroborate the all-size proof; they do not establish
infinite claims by testing. No author, predecessor, archived, frozen,
or supplied program is executed or imported. Only the fresh reviewer
code runs before freeze. Fresh writer, normal exact replay, and optimized
exact replay from `/` passed. The companion JSON binds the reviewer's own
source bytes, the author trio, the seven dependency pins, and each finite
check's explicit scope. The MD is a proof review, not an assertion that
these finite checks alone establish the infinite theorem.
