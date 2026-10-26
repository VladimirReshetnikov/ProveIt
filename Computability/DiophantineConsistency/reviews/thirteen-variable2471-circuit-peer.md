# Independent review of the thirteen-variable carrier and circuit construction

Reviewer: `/root/circuit_reduction`. ROOT authored the ordinary proof.
I reviewed the complete proof, its inert source proof and entire source
graph, and independently checked the proposed graph transformation and
degree calculation. I did not author this carrier proof or its forthcoming
materialized graph/auditor.

Final reviewed proof:
`research/thirteen-variable-independent/PROOF.md`, SHA256
`d2e40a04fdc670a5f5a05d2c8e7e762e07ef559eb051e5ff6f5c82e7e3e8f6a8`.
Its complete native binding is the accepted phase-split2471 proof
`934c7984038b578a68b1396fffdb8db71a9039b01a86455a74c8639264a1b966`
and certificate
`f6c576194bfd60d10457c6ba9c43c0b7a8537639588c4f022e7a0362b9051bef`.
The four whole ports total 58125 bytes. The Carrier65 proof used in the
maps is `53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749`.

The complete inert sources read were source192's `compact13/PROOF.md`,
SHA256 `5d210d457196c40bec061ecd79b86eeb1aeabb46a3d5e037d88bc34773fba07f`,
and `compact13/positive13_square.json`, SHA256
`9574f3db6cfc549d565d278f84d7d9f0a53fec92cdcc05762c95d1e54db49c7c`.
The JSON was parsed as data only. No incoming executable was imported or
run, and its older coefficient tuple was not adopted.

## Correction found during review

The originally reviewed proof had SHA256
`3eb77199b3961be024ec1f170d843f939ecbabb8b2af33adad6d6f66bb181af1`.
Section 4 stated initial values `1,3-4*A^2` for the signed odd ordinate
subsequence. I reported the second value as a typo. Since
`psi_A(3)=4*A^2-1` and `Q1(1-A^2)=4*(1-A^2)-3`, the correct second value
is `1-4*A^2`. ROOT corrected it to `1,1-4*A^2`; I reread that change in
the complete final proof identified above. The stated recurrence identity,
theorem, witness maps and polynomial are unchanged. The final version
passes this review; the earlier hash does not identify the corrected text.

## Full positive-domain maps

PASS. The descent for the Pell discriminant `S^2-1` covers every positive
nontrivial solution and terminates at `(S,1)`. Divisibility of its abscissa
by `S` forces an odd index. The full odd-ordinate residue is modulo
`4*S^2`, including either sign of the derived `y`. Together with the
literal congruence `y=1 mod 4`, it forces `4*S^2 | y-1`. The bound
`abs(y)<2*abs(V)` follows directly from the norm equation.

At every zero of the unscaled thirteen-variable equation, cancellation
of positive `Delta` gives four integer units. The inherited consecutive
Pell obstruction excludes `P=-1`; the displayed modulo-four arguments
exclude minus one for the other three units. Thus all four normalized
factors are one without first interpreting the rank, alignment or signs
of `C`, `G`, `R` or `tau`.

Since `b|S`, the full ordinate residue implies `b|G` even when `b` is
composite or even. If `G<=-1`, the literal derived ordinate is larger
than `4*abs(V)`, contradicting the Pell bound. Hence `G>=0` and
`z=G/b+1` is a positive integer restoring the deleted transport factor.
The map to the parent uses its `i=b*i`, positive ordinate `abs(y)`, and
this `z`, retaining the other coordinates. It therefore covers every
positive zero, including noncanonical ones, before invoking the accepted
parent soundness theorem.

For completeness, the actual2471 outer data supply `R=3 mod 4`, the
required first-root Pell pair and `b|G`. Their rank bound gives `w>q`,
so `G>0`. Taking a positive power of the norm-one unit in the finite
quadratic ring modulo `b*c^2` gives a positive Pell ordinate `I`
divisible by `b*c^2`; this step does not require primality or a field.
The resulting `i=I/(b*c^2)` produces the new strong factor exactly.

The corrected odd-index recurrence gives both congruences for `Vstar`:
`Vstar=-c mod f^2` and `Vstar=-R mod c`. With `f^2=1 mod c`, the
displayed numerator for `T` is divisible by both coprime denominators
and is positive. The choice `y=-psi_S(R)` and the displayed formula
for `m` are integral; `G/b>=1` and the Pell bound make `m` positive.
The evaluated polynomial abbreviation `y` is exactly that signed target.
These are witness-construction divisions only. The completeness map
legitimately selects a fresh strong seed; it is not asserted to identify
the whole thirteen- and fourteen-variable zero sets coordinatewise.

## Scaled factor and exact degree

PASS. At a zero of either thirteen-variable polynomial, the normalized
strong factor is an integer unit and its modulo-four residue rules out
minus one. Consequently `Z=Delta` on both zero sets. The exact ring
identity

    p-pold = P*Q*Z*(Z-Delta)*(V^2-y^2)

then proves equality of their entire positive zero sets by the identity
map. This reasoning does not assume a sign for the new auxiliary factor
before establishing the identity, and it introduces no extra premise
about a native packed witness.

I recomputed the leading forms of `y`, `Theta`, `U` and `Z`, of degrees
19, 14, 52 and 48. The main norm has exact degree18 after the stated
degree22 cancellation; the first norm has degree22. Their product is

    -128*q0^77*gamma*i^2*k0^11*w^12*s^21*f^10*T^4*C0^2.

Its specified monomial coefficient is `-128*beta^79`, nonzero at the
actual positive fixed beta. Thus the degree is exactly140, while the
unscaled construction has degree174. These are different polynomials
with equal positive zero sets, not a pointwise polynomial identity.

## Literal schedule and domain scope

The full inert 69-row source graph has 39 multiplications, 16 additions
and 14 subtractions. I independently parsed its dependency graph as data,
moved the existing `scaled_f2` producer before its new use, inserted
`Theta=scaled_f2-Delta`, and replaced only the auxiliary multiplication's
`S^2` input by `Theta`. The resulting in-memory schedule has 70 rows:
39 multiplications, 16 additions and 15 subtractions. Every row, all
thirteen inputs and all four fixed ports remain live. In particular `S^2`
is still required by `Z`. Degree propagation with the separately checked
main-norm cancellation agrees with the degree174 and degree140 claims.

This review verifies that construction, not a yet-to-be-reviewed
materialized70-row packet with current whole-port bindings. A complete
graph/auditor and its receipt still require separate finite review.

The positive-integer parametrization `1+u^2+v^2+w*(w+1)` is surjective
by the three-square theorem for `4*N+1`, including `N=0`; its three
squares have exactly one odd member. It is always positive on integers.
The direct substitution uses seven operations per original variable,
giving 39 unrestricted variables and 161 operations. The nonzero highest
form survives the disjoint quadratic substitutions, so degree280 is exact.
The proof accurately states that no full lifted graph is supplied.

No further mathematical correction is requested. The result retains
the accepted native and syntactic-calibration contracts and the ordinary
proof boundary; this review does not claim a new formal-kernel replay,
actual unsolvability or a global minimum.
