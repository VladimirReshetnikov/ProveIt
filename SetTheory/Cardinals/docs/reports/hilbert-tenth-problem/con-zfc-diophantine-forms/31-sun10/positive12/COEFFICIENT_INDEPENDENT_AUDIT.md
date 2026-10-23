# Independent audit of the 121 by 8801 coefficient adapter

The reviewed files are `research/coefficients/new/COEFFICIENT_PROOF.md`,
`build_coefficients.py`, `COEFFICIENT_BINDING.json`, and the stated package-24,
package-25 and package-27 upstream proofs. Source pin is
`8c6eec9d19ef80538c8e61ff6e0180040583446a`.

## Finding

No mathematical obstruction was found in the new joint choice
rho=2^121, L=8801, d=1064921, lambda=2341. The new coefficient bytes, their
finite convolution geometry, and the unit hypotheses were independently
recomputed without importing or executing the proposed builder. The Boolean
coverage argument is valid for every sufficiently large chosen physical length,
not merely the finite lengths checked by the diagnostic script.

## Geometry and the two clause targets

The native support has 989 elements and maximum exponent 3296. The two targets
are 4393 and 5495. Their difference 1102 is absent from E-E; the relevant anchor
difference 1101 occurs only as 3296-2195. Because 8801>2*3296, reducing these
differences modulo 8801 cannot introduce additional collisions.

The independent reconstruction checks all 69,230 scalar overlap identities,
including contributions from every term of the reflected-clause coefficient.
This matters because, unlike some earlier long-target layouts, the smaller
first target does not permit a blanket claim that all reflected-clause terms
lie above all overlap targets. Exact coefficient checks are the proper argument.
They all pass, including the source-preserving targets 1013+j,1065+j,2195,3296
and both clause targets.

The maximum exponent of an unshifted computational convolution is exactly
5495+3296=8791. Thus population padding at exponents 8792 through 8799 is
outside the computational support and below L. This remains true after every
allowed dummy choice, since dummy positions are already included in E. The
strict global no-carry bound is unchanged apart from replacing rho; its threshold
is between 2^119 and 2^120, hence below 2^121. The largest padding digit separately
satisfies 2*(2^119-1)+4<2^121. The native masks have the stated populations and
low-bit congruences when recomputed as actual integers.

The underlying binary-alignment proof uses only the low support digits and the
exceptional upper dummy spill, not the primality or power-of-five nature of 125.
Changing this width to 121 replaces the exceptional binary remainder 124 by120.
Two occupied anchors still rule it out. The smaller circumference retains the
necessary modular support intersections. Additional external zero tests restrict
solutions and vanish on canonical aligned witnesses, so they introduce no new
soundness branch and no completeness restriction.

## Unit multiplier for every allowed physical dimension

Factor d=11^2*13*677. The orders of B modulo121,13,677 are10,12,52, with lcm780.
The prime lambda=2341 has lambda-1=2340 divisible by780; the order of B modulo
lambda is60, also dividing2340. Thus, for every spatial width w=lambda^a and
physical cell count N=lambda^n,

    B^w congruent B and B^N congruent B modulo d*lambda.

This is a congruence statement, not an equality of integers. It holds for every
a,n, because lambda is1 modulo all the relevant orders. The table gives
nonzero residues of both B^2-1 and1+B*DC+B^2(DR+1) at every prime dividing d*N.
It therefore proves that the actual rank-change multiplier Gamma is a unit
modulo d*N for all the chosen sizes, including every higher power of lambda
and the fixed prime power11^2. Unit status only requires nonzero reduction at
the underlying primes.

The independent checker verifies the literal valuation-one certificate

    B^2340 = 1+1092*2341 modulo2341^2.

Since2341 does not divide1092, ordinary binomial lifting gives
ord_(lambda^n)(B^2340)=lambda^(n-1).

## Boolean coverage, including the factor d

Let N=lambda^n, T=N/lambda and C0=d*lambda. The hypotheses N>d*lambda^2 imply
T>C0. Powers of B^2340 are1 modulo d and generate all principal units1modlambda
modulo lambda^n. By CRT their T orbit values modulo d*N are exactly

    {1+C0*z : z modulo T}.

The CRT conclusion requires gcd(d,lambda)=1, which holds and is checked.
Normalize the desired target by the unit B^2. Subtract either0 or B to obtain
a residue nonzero modulo lambda, and call its least residue modulo C0 'a'.
Then1<=a<C0<T and gcd(a,T)=1. Every target of the form a+C0*u is a sum of a
distinct orbit elements: choose z0 with

    a*z0+a*(a-1)/2 = u modulo T,

and use additive coordinates z0 through z0+a-1 modulo T. They are distinct
because a<T. The optional subtracted B corresponds to the extra distinct
physical cell index3 after restoring B^2. This proves coverage of every residue
without repeated control bits.

The largest available orbit cell is N-N/lambda-lambda+3. The independently
chosen height h>lambda implies w=N/h<N/lambda, so its translates by1 and by w
remain below N. The extra cell3 obeys the same bounds. The required smallest
control index is2, so the distinguished initial cell is untouched. The argument
uses the inherited independent rectangular padding theorem; sufficiently large
powers of an arbitrary fixed odd prime are available because that theorem allows
every sufficiently large independent width and height.

The independent code additionally constructs32 Boolean subsets at the **actual**
d,B,lambda and physical sizes lambda^4 and lambda^5. It computes the inverse
orbit indices by lambda-adic lifting, checks that no index is repeated or wraps,
and verifies the complete selected subset sum modulo d*N. These examples check
the transcription but are not the proof of universal coverage.

## Rank, parity, and remaining semantic dependency

The exact dummy rank formula is unchanged because the native support and dummy
location are unchanged. The target residue R=d*w modulo d*N is therefore
attainable. The new d and all dimensions remain odd, so the existing population,
odd-rank and canonical Pell parity arguments transfer with their stated premise.
The adapter still relies on the imported Wang-language, native-window/Pell and
K215 calibration theorems. The finite checks do not reprove those unbounded
semantic results or supply a new Lean/Rocq endpoint.

## Reproduction

Run `python3 audit_coefficients_independent.py` from this directory; it uses the
adjacent `../coefficients` package. The result is
`COEFFICIENT_INDEPENDENT_CHECKS.json`. The checker compares all four reconstructed
integers with the delivered gzip bytes and their SHA-256 hashes. It uses only
the Python standard library and does not modify the coefficient source directory.
