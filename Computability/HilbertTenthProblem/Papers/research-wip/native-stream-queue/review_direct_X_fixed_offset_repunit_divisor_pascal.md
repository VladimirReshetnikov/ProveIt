# Independent review of the fixed-offset repunit-divisor obstruction

**PASS.** I independently checked the complete integer-divisibility proof,
the denominator clearing for every integer offset, the nonzero-remainder
argument, and the exclusion of the authentic lcm progression. No
mathematical correction is requested. The final author wording explicitly
requires an authentic odd exponent in its displayed progression, adopting
the optional scope clarification raised during this review.

The frozen author pair is
`/tmp/direct_X_fixed_offset_repunit_divisor_root.md`, SHA256
`8e54b2963256a1a239e91a495f22c6c43c26d439c287f724b0e2679f96827717`,
and the same stem with `.json`, SHA256
`dcf3b417cb6392b6f2c3b3ef8a481d081b4d8e4ec547c76f4537a0c8c9764470`.
The accompanying reviewer receipt authenticates both files and all five
declared dependency byte/read-span pins. The complete author proof and
receipt were read as inert text/data. Relevant dependency reads are listed
exactly in that receipt; their authentication does not broaden proof scope.

## 1. The polynomial obstruction needs no denominator cancellation

The literal equations give `q-1=(B-1)J`, so J divides both `q^2-1` and
every summand of the packed R. Hence J divides R for arbitrary integer
U,Z and mask values. In particular, no positivity of those quantities
is required; only J>0 enters the finite size bound.

If `D*R=P(q)` with fixed nonzero integer D and fixed integer polynomial
P, divisibility of R gives divisibility of P(q). Since q=1 modulo J,
J divides P(1). This does not cancel D, even if D and J have common
factors. When P(1) is nonzero, the positive divisor J is at most
`abs(P(1))`; substituting into q=(B-1)J+1 proves the stated explicit
finite bound. The conclusion is necessary, not sufficient for any of
the remaining compiler equations.

## 2. Every integer offset is covered

For `c=a-h`, where a=max(c,0) and h=max(-c,0), direct multiplication
of `R=2*3^(3k+c)-3` by `D=3^h B^3` gives exactly

    D*R=2*3^a*q^3-3^(h+1)*B^3.

This works also when c is negative; the explicit premise 3k+c>=1
keeps the original R an integer of the intended form. No rational
coefficient is treated as an integer congruence without first clearing
its denominator.

For B=2^d and d>=1, the resulting remainder
`N=2*3^a-3^(h+1)*B^3` never vanishes. If a=0 its two terms differ
modulo3. If a>0 then h=0, and equality would imply
`3^(a-1)=2^(3d-1)`. The right side has a positive binary exponent
at least2 and cannot be a power of3, including the a=1 endpoint.
Thus the finite bound is valid for every fixed integer c. It is not
uniform when c varies with k.

## 3. The authentic progression has no remaining finite exceptions

For the inherited odd d with25|d, the divisor31 of2^5-1 also divides
B-1. The elementary residues used to prove order30 can be checked from
`3^5=-5 modulo31`: squaring gives `3^10=25`, cubing gives
`3^15=-1`, multiplying by3 gives `3^6=16`, and squaring the fifteenth
power gives `3^30=1`. The proper prime-divisor tests at15,10,6 prove
that no proper divisor of30 is the order.

It follows that30 divides the unit order modulo B-1. With
`c=2^(3d+1)`, the lcm in the author progression is consequently a
multiple of15c. Every positive k in the progression exceeds c, and

    J-3^k=(3^k-1)/(B-1)>0,
    3^k>=3^(c+1)>2*3^c.

Also c>3d makes `N=2*3^c-3B^3` strictly positive. Hence
`0<N<2*3^c<J`, contradicting J dividing N. This excludes every
member of the specific progression using the literal packed index
alone. The earlier canonical scale, repunit, and numerical-window
theorems remain valid at their separate scopes.

## 4. Retained boundary and exact review limits

**Review remark 1 (the nonzero remainder is indispensable).** The
unqualified extension to every fixed polynomial ansatz would be false.
For `P(T)=T^2-1,D=1`, the author's integer assignment
`U=1,Z=q-1,MC=MF_source=0` gives R=q^2-1 for every positive J and
q=(B-1)J+1. I checked its substitution: qU-Z=1, and the second packed
summand vanishes. These are not authentic masks or compiler zeros.
They refute the stronger divisor-only claim precisely because P(1)=0.

The author also retains the failed fixed-offset infinite-completion
proposal with its explicit obstruction. Neither proof claims to rule
out all variable offsets, settle the direct-X83 divisibility obligation,
or improve the accepted universal84 bound. No old canonical valuation
or native theorem was independently re-audited here beyond the stated
dependency interfaces.

This is a proof-only review with fresh metadata authentication. No
scientific helper, supplied or predecessor program, frozen helper, or
source array was executed, imported or evaluated. No source degree was
propagated and no large compiler parameter or native witness was
materialized. Only `/tmp` review artifacts were written; no repository
or Git mutation occurred.
