# Congruence certificates: positive and integer peer review

Accepted for ordinary arithmetic research, with no new semantic gap found
in the positive or integer components reviewed here. The arrival is
`docs/incoming/ConZFC_Congruence_Certificates_2026-10-24.zip`, SHA256
`f4119b01e56f586558f0910c6deb21b83c82dfc324f884d7d95d28500ef09e63`:
205 members, 5,899,098 uncompressed bytes. All 204 content-manifest entries
were authenticated. The unchanged native/compiler calibration and the
internal object-ZFC derivation retain their existing boundaries.

| Domain | Variables | Exact degree | Live binary operations |
|---|---:|---:|---:|
| positive integers | 12 | 70 | 98 |
| positive integers | 13 | 51 | 88 |
| unrestricted integers | 13 | 1,072 | 195 |
| unrestricted integers | 14 | 414 | 148 |
| unrestricted integers | 15 | 218 | 130 |
| unrestricted integers | 16 | 124 | 118 |

The positive equations delete two gates and promote J to a free positive
input. They are ordinary existence equivalences with the old restricted
positive domains; they are not polynomial identities with the old j
coordinate left unchanged. A separate exact polarization gives a new
**12-positive / degree70 / 96-operation** circuit in
`candidates/free-j-polarized-positive/`. This modest circuit improvement
does not warrant replacing the established canonical 90-operation,
degree51 printed page under the user's current policy.

## Positive-domain proof

The free-J argument legitimately carries the possible factor three until
it is excluded. It does not silently reuse gcd(q,H)=1 from the restricted
parent. From q^3 dividing Y and H=4Y(X+1)+3, the exact identity is

```
gcd(q,H)=gcd(q^5,H)=gcd(q,3) in {1,3}.
```

If three divides q, Y is divisible by 27 and H is three modulo27, so
H has exactly one factor of three. Every other prime of q is prime to H.
The available divisibility q^5 | H(qE-v) therefore gives
q^5/gcd(q,3) | qE-v. This modulus is a multiple of q^4, and q^4|qE,
so q^4|v follows before coprimality is recovered.

The early norm/unit and carrier conclusions are used in their correct
order. A product equal to one has factors ±1, and the complete modulo-four
arguments exclude minus one without assuming q even. The positive
carrier bounds give q>=16, 3q<R<q^4-2, large Y and positive Dstar. The
first/main Pell classification and early index congruence then give the
same large-index bounds as the parent. The ordinary strong-rank and
auxiliary results supply p=R before q|X is needed. The parent lemmas are
still explicit dependencies; the new gcd argument does not purport to
replace the full ordinary source proof.

The resulting projection is X=2^R modulo H/g with g in {1,3}, not
initially modulo H. The new growth estimate is sufficient:

```
X(2A-1)^2-2P0(X+1)^2
  =12XY(X+1)+9X-2(X+1)^2 > 0.
```

For X>=2 the ratio lower bound and r0>=24 give Y>2^R. Thus X and2^R
both lie strictly between zero and a, whereas H/g>=H/3>a, proving
equality. For X=1, Y>=2^(R-2) puts 0<2^R-1<H/2. The only possible
nonzero multiple of H/3 in this interval is H/3, but its equality would
give 8Y=3*2^R-6, contradicted modulo eight. This closes the exceptional
case without assuming the desired power equality.

Now q|3*2^R makes q either a power of two or three times one. For the
authentic beta=2^590069-1, the congruence beta|q-1 rules out the latter:
reduce the exponent modulo590069 and bound the residue of3*2^r. The
two endpoint cases in the written argument are valid for every d>=4.
Only at this point is q|X concluded and the old source quotient restored.
Canonical completeness simply retains the already positive J.

The leading selected coefficients are 64*beta^18 and -32*beta^15, so
the degrees70 and51 persist at the actual nonzero whole tuple. The
explicit coefficient tuple is compact44, with MF already shifted once;
all four raw payloads match the earlier retained compact57 tuple byte
for byte. It is not mixed with the integer family's larger source34 tuple.

## Integer-domain proof

The valuation composition respects the unrestricted integer domain.
Unconditionally q=2 modulo3, H is odd and nonzero, Delta=0 modulo3,
and delta=Q-1=-1 modulo3. Thus the auxiliary denominator never vanishes,
even before any guard or radical is interpreted. The raw radicands are
nonzero three-adic units. Their squared weights have the stated distinct
even valuations. Grouping radicals by rational square class and using
the unique least valuation excludes every nontrivial class, including
negative raw radicands. This establishes rational roots before any
Archimedean positivity is used.

In the retained-root family, modulo-four unit products are valid on every
integer assignment. M and U are divisible by eight. Every nonleading
cleared-norm monomial contains a radicand numerator divisible by64;
the only radicand-free term has even powers of delta and the center.
Therefore the cleared norm is zero or one modulo four, even if delta is
even. None of the displayed unit factors can be minus one. Consequently
the actual polynomial zero recovers all required retained equalities
before radical interpretation. The independent Laurent calculation
checks precisely this structural premise.

The guard square then gives N>0, hence G>0 and eta*zeta>0. If c=0,
eta*zeta=-Y(Y+1)k^2<=0 for every integer Y, a contradiction. The literal
affine forms give Delta>=3 even off source: v=0 gives a=0; otherwise
the minimum absolute q,W,Y scales force |a|>=1008. Thus the strong
equality makes Q>1. Only now is the adjacent-coefficient rational Pell
descent applied. Its transformed integer V has smaller absolute value,
and its rational companion preserves the reduced denominator because
2Q-1 is one modulo that denominator. This proves the auxiliary root
integral without a circular positivity assumption.

The signed root relation modulo M=2q^2 gives
v=q^2(2*v_old+1); modulo H it gives gamma=(d-b0)/H integral, since
gcd(H,M)=1. These are the full required source scale and quotient,
not weaker divisibilities. The formulas I_old=Delta*I and
r_old=(Delta*(2r+1)-1)/2 are integral because Delta is odd. The two
auxiliary quotients are integral from f^2=1 modulo c. These maps allow
signed roots and signed restored coordinates exactly as the inherited
normalized source does.

Completeness uses the retained source's explicitly reconstructed
normalized strong witness, not division of an arbitrary old strong
index by Delta. The inherited `NORMALIZATION.md` constructs this
witness at m=R*c and reconstructs the squared-modulus auxiliary witness.
The free n formulas in the new proof have the right signs and weights.
The three-generalized-pentagonal representation is an unchanged
explicit mathematical dependency. No finite check supplies that
unbounded theorem or the native calibration.

I checked the degree arguments, including the unique dominant root for
14 and15 variables and the cancellation p=UV+s for16. The displayed
selected coefficients remain nonzero at the actual beta:

```
13:  2^1000 * 3^696 * beta^480,
14: -2^402  * 3^302 * beta^196,
15: -2^209  * 3^151 * beta^104,
16:  2^113  * 3^77  * beta^58.
```

Their monomial exponents sum to the claimed degrees. The source34 four
ports and both determinant scales match the previously reviewed
`fixed-prime-compact-norms` payloads byte for byte. MF is shifted exactly
once. The exploratory 14-variable degree558 file is explicitly dominated
and is not included in the released four-point family.

## Replays and exclusions

`congruence-certificates-peer.py` authenticates the original ZIP and every
manifest entry, compares all ten fixed payloads to earlier whole-tuple
bytes, then works only in scratch directories. Normal and optimized
replays pass the positive checker, independent integer norm checker and
literal four-graph integer regeneration. All four regenerated graph
files match byte for byte. The original pure finite integer checker
functions additionally pass72 signed conjugate-product controls per
graph and actual-tuple univariate degree attainment. The independent
norm oracle checks exact rank-two/three/four Laurent identities with
6/35/495 terms and denominator clearance.

The positive checks cover896 complete unit-residue cases,6336 gcd
diagnostics,15132 Mersenne diagnostics, the exact growth identity,
topology/liveness and the nonzero selected coefficients. The diagnostics
supplement the unbounded proof reviewed above. Normal/-O driver receipts
are `congruence-certificates-peer.json` and
`congruence-certificates-peer-optimized.json`.

No archival coefficient generator was executed: unchanged whole payloads
were authenticated and byte-compared instead. No old H10 emitter, direct
component, Lean or other proof assistant was run. The direct oriented
power component is outside this review and can be queued separately.
Neither these checks nor the ordinary reduction constitutes an encoded
object-ZFC proof or a proof that the equation lacks solutions.
