# Root review of the direct-X83 wrap isolation

**PASS within the stated scope.** The all-size parity, nonsquare and
width-less-than-one statements are supported. The finite exclusion stops
at even q<=64; universal83 and exclusion of every wrap remain open.
The frozen author note and metadata have SHA256
`1245a351ba1849b423570c7cbf37273cd0f96a360dbf8a5a6f0c01bdf988ac42`
and `4e3be7bd31b9cec5b755bad2d7d135f03752ab9abc424eb9d15ee44394aa7bb4`.
I read the entire note and helper inertly, the full direct-X83 boundary,
and the half-parameter proof's auxiliary-polynomial and signed-step-down
argument, including the stronger plus-sign period at lines154-158.

R odd follows from psi_A(R)=R modulo2, c|m and the odd auxiliary index.
For the stronger result, the plus chi congruence with comparison2R<m
gives ell=eR+2mt. In the quadratic ring modulo f, the unit to power2m
is -1, so the coefficient shifts by e(-1)^t. The two unsquared Q_j
congruences, with c>2R and f>2c, force e(-1)^j=e(-1)^(j+t)=-1.
Thus t is even, and the two cases e=+1,-1 both give R=3 modulo4.
No division in an even residue ring or assumption q|X is used.

The authentic outer formula excludes odd q before any dyadic typing.
Then Y is divisible by8, so H=3 modulo8. The main projection
X=2^R modulo H makes X coprime to H with Jacobi symbol -1. This
excludes every square, and more generally forces an odd exponent of2
when X is a power of2 times a square. These are necessary conditions
rather than a classification of all remaining X.

For the logarithmic interval I independently checked the exact Pell
formula and both error signs. The negative error in replacing the
fundamental-unit logarithm by log(2C) has magnitude less than
(t-1)/C^2, and the nonnegative geometric correction is less than1/C^2.
Substituting2n=R+epsilon+vXY into the strict ratio bounds yields the
stated endpoints with L=log(2A^2/P). The identity A^2-2P>0 gives
L>log4. A>=2Y, P>2Y^2 and Y>=q^3 give exactly the displayed uniform
width bound; it is below1 for q>=16. This proves at most one possible
integer for each tuple, not existence or full Diophantine soundness.

The fresh helper uses outward-rounded integer intervals for logarithms.
Its atanh argument is at most1/3; the70-term omitted tail is strictly
below3^(-140). Directed multiplication and division preserve the
required enclosure, and the positive numerator/denominator bounds
justify the interval division. The inclusive integer ranges cover the
whole stated necessary-condition superset. The receipt's three integer
survivors all violate the authentic outer upper bound; none is claimed
to be an actual Pell solution. The separate512 scalar controls test
only the elementary logarithmic estimate.

Root authenticated all four frozen artifacts without replay. Their
helper and receipt pins are `f14a95b26cd42934d5b9491be73fcb2b6cbefc5581df7636ec5f9e595e5eda96`
and `6f4846bd7d1bd7e74e1665ecb918b1d4a4c10f0df91824e83dd50a659dc116d0`.
No saved helper or array was executed or evaluated. The finite result
is accepted on inspected arithmetic code and its bound receipt, not
presented as an independently rerun experiment or a compiler fixture.
