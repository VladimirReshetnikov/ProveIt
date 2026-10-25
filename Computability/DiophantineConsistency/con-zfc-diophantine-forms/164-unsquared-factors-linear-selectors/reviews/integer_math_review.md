# Independent review: linear binomial radius and residue-class radix

## Verdict and scope

**PASS, with the inherited arithmetic/formalization boundary stated below.**
No blocking mathematical or literal-interface defect was found in the reviewed
`round20/integer/PROOF.md`, the four endpoint source edits, or their affine
restriction/restoration claims.

Reviewed proof SHA-256:
`71c65b99178fc512ee39d754586682bc2a37d8dac2c38892b4237d41a90cdc47`.
The inspected comparison checkout is
`7a8da414376a80b90ecf799f37ceb26fb9ac674e` and was clean at inspection.

This review independently checks the new ordinary arguments and their interface
to the retained factorial-free source. It does **not** claim a rebuilt
end-to-end Lean/Coq proof, prove consistency, or treat finite tests as proof of
unbounded zero-existence equivalence. The signed Pell frame/orientation theorem,
the numerical C222 calculus and its ZF/ZFC calibration remain the explicitly
identified inherited boundary.

## 1. Lcm bound and the linear radius

The supplied elementary recurrence is correct. If
`k=ceil(n/2)` and `p^a<=n` is the highest relevant prime power, the only case
not already covered by `Lambda_k` has `k<p^a<=n`. Then
`p^(a-1)<=n/2<=k`, so exactly one additional factor of p is needed. The
`p^a`-level of Legendre's binomial valuation is one, since both k and n-k
are below p^a and n<2p^a; all other levels are nonnegative. Therefore

    Lambda_n | Lambda_ceil(n/2) * binom(n,ceil(n/2)).

For even n=2m, the binomial is at most 4^m. For odd n=2m+1, the two equal
middle coefficients together are at most 2^(2m+1), so each is at most 4^m.
Strong induction gives Lambda_n<=4^n. No unproved asymptotic estimate is needed.

Consequently, for t=16+h² and F=[2(t+1)]^t,

    F >=34^t >16^t >=Lambda_t².

The incoming theorem with radius threshold `R>=Lambda_t²` is genuinely
available in `inherited_factorial_free/report/main.tex`; the older review
with a factorial-square hypothesis is not the theorem being used.

I also checked both arithmetic directions of that incoming selector:

* For a fixed row i, R+i>Lambda_t² yields a prime with v_p(R+i)>2a,
  where a=v_p(Lambda_t). All other shifted factors have valuation
  v_p(j-i). Hence v_p(B)=v_p(R+i)-d, with
  d=v_p(t*binom(t-1,i-1)) in [0,a]. This is a full prime power exactly
  dividing B, divides R+i, and exceeds t.
* For any full prime power p^e exactly dividing B, let v be the maximal
  valuation among R+1,...,R+t. The binomial valuation is a sum of zero-one
  terms supported on levels at most v, so e<=v. A maximizing row is
  compatible. This covers every prime of B, not only primes chosen as
  isolating row selectors.

Thus the reduction R=F² -> R=F satisfies the precise two-sided CRT theorem.

## 2. Signed bootstrap, including all exceptional bases

The dependency order is sound, and no application to base zero is hidden.

1. The retained request at d=2(t+1)>1 and positive t authenticates F first.
   The beta odd-square multiplier then gives y>=F>0.
2. The residue constraint q=4z+1 rules out q=0 and q=-1 without a sign
   assumption.
3. At q=1, base q+1=2 forces the nine actual CRT upper representatives to
   be nonnegative. Hence H>=2, C0>=0, and the raw index row
   B*mu=C0+R+1 rules out B=0. Base BH has absolute value at least two.
   Its power request gives q=(BH)^x and x>=0, so q=1 forces x=0.
   The last beta endpoint would require
   [1+(t+1)y]*u_t=-1, impossible.
4. For every remaining q in this residue class, |q|>=3 and |q+1|>=2,
   including q=-3. The same signed-power lemma establishes nonnegative
   actual upper representatives, H>=2 and B!=0. It applies to BH before
   the sign of B is known. It gives x>=1.
5. The first endpoint and y>=F exclude u0<=-1, giving x>=F+1. The last
   endpoint then gives u_t>=1 and x>=2+(t+1)y.
6. With Q=|q|, the genuine self-power now yields
   Q>=2^x and Q>=4B². Since |B| is a positive integer, Q>=4|B| also
   follows, proving the quoted |B|<=Q/4 bound.

The bases q, q+1 and BH are nonzero when used. B's request is postponed until
the binomial is authenticated and B>=2. d was positive from the outset.
The retained signed power lemma covers the possible negative q, q+1 and BH
and does not infer positivity prematurely.

The common-normalization step is also valid at negative q. For every low
denominator L, its nonnegative exponent is at most x; therefore L is a
nonzero power of q and its ratio v=M/L is an integer and nonzero. The
scaled row vU=M*Q_i+R_i implies v|R_i. Dividing gives an integer remainder
r_i and U=L*Q_i+r_i. The common norm yields |r_i|<|L|/2, without
requiring the signs of M, L or v. The uniqueness comparison with a
canonical signed lift smaller than |L|/32 is valid.

## 3. Binomial authenticity before sign recovery

Section 4's signed extraction is correct. In the actual parameter range
R>=F>=t, the coefficients C_j=binom(R+t,j), j<=t, satisfy

    C_j<=C_t=product_(i=1)^t (R+i)/i <=(R+1)^t <=(F²+1)^t.

This supplies a short explicit justification for the displayed majorant;
the weaker statement R>=1 alone need not be used in its derivation.
For F>=7, F²+1<=2^(F-1). Combining this with
x>=2+(t+1)F and Q>=2^x gives

    V/Q<=2^(-F-t-2),    V/(Q-1)<1/32.

The signed polynomial r0=sum_(j<t) C_j*q^j has absolute value
less than Q^t/32 and is congruent to (q+1)^(R+t) modulo q^t, regardless
of q's sign. The norm-selected lift therefore equals r0. Reducing the
remaining quotient modulo q gives B congruent to C_t. Since
|B|<=Q/4 and 0<C_t<Q/32, their difference has magnitude below Q,
so B=C_t>0.

Only now is q=(BH)^x declared positive. Thus the negative-radix branch is
actually ruled out arithmetically; it is not omitted. The power N=B^x
is authenticated only after B>=2. There is no B-sign circularity.

The subsequent inherited digit/local bounds still apply:

* Ordinary coefficients are at most max(1,a)^k<=H^x, including a=0.
* The polynomially derived label is at most H^ell, ell=2^22, and
  ell(t+1)<x follows from the retained huge endpoint lower bound.
* q=B^x H^x, B>=2, supplies the strict tail budget.
* The local bound L<(2x)^(2^23)<2^x uses x>2^32 and is unaffected by
  reducing the separate binomial radius.
* The upper indices and all four denominator groups are unchanged except
  for the smaller front index R+t.

These give the same range congruences and local-polynomial evaluation
bound as the predecessor. The every-row selector then recovers all local
rows. In the converse direction, CRT is imposed at p^(2xe) for **every**
prime p of B. Dividing each range falling factorial by k! loses fewer
than x<=xe powers of p, so the required p^(xe) divisibility survives.
The derived-label polynomial respects these same CRT congruences.

## 4. Boundary y=F and proof-label multiplicities

The y=F exception is handled at the correct stage: only after local
beta-row recovery. Its first ordinary beta remainder is zero, whereas the
last is one. Positive update weights propagate a zero initial accumulator
to the last accumulator, contradicting that last remainder. Thus y>F at
a complete zero, and the genuine initial remainder is F+1.

The evaluated-product argument recovers exact multiplicities, not merely
prime support. The conclusion side has at most t nonunit factors. If the
two nonunit counts differ, their smaller count d is at most t, while the
larger side is at least (F+1)^(d+1) and the smaller at most
t^d(F+1)^d. This contradicts F+1>t^t. Hence the counts agree and are
both at most t.

The two formal products of factors 1+jX now have coefficient sums at most
(t+1)^t<F. A nonzero difference polynomial with coefficient magnitudes
below F cannot vanish at F: divide by its least occurring power of F
and reduce modulo F. The resulting polynomial identity determines each
positive-label multiplicity by its distinct rational root -1/j.
Unit label zero contributes nothing. The inherited single-conclusion
Horn closure argument then excludes circular spurious refutations.

## 5. Constructive completeness and parity/canonical choices

The construction has a noncircular parameter order:
finite refutation -> padded t -> F,R -> sufficiently large y -> even x ->
B,N -> CRT representatives/H -> q -> the common Pell frame.

The odd-square beta choice is cofinal. If O is the odd part of t!, an
arbitrarily large odd multiple a_beta of O gives y=F*a_beta² divisible
by t!, because v_2(F)>=t>v_2(t!). It is even. The beta moduli
1+(i+1)y are odd and pairwise coprime. A sufficiently large beta code
can therefore be chosen even by adding their odd product.

For R=F (and also R=F²), v_2(R)>v_2(i) for every 1<=i<=t, so
v_2(R+i)=v_2(i). The binomial B is odd. Hence N² is odd, and adding
N² changes a representative's parity while preserving all full-precision
CRT congruences. Concretely, the other eight representatives can be
chosen positive even and at most 2N², and the dominant a positive odd
in [2N²,4N²). The interval contains two consecutive representatives of
each residue class, of opposite parities. This preserves the earlier
dominance construction, makes H odd, and makes the semantic anchor even.

The front index is smaller, not larger: R+t<=B<B²<N². The other front
indices x,y+1,t are also below N². The anchor lower bound 2a² dominates
all nonanchor requested indices. Since BH is odd and x is even,
q=(BH)^x is an odd square and hence 1 modulo 4. Thus z=(q-1)/4 is an
integer. This is an existence construction, not a square-root recovery
claim for every edited tuple.

The eleven canonical tails are nonnegative and <M/32, so their norm gap
is a nonnegative integer. The stated ternary representation of that gap
by a²+b²+c(c+1) is valid via the three-square representation of 4g+1.
The retained constructive Pell completion then provides all private
coordinates. Factorials here occur only in choosing y in the existence
proof; no factorial-authenticity equation is restored.

## 6. Literal source and restoration audit

The independently inspected sparse schema is
`finite_quadratic_residuals_v1`, with coefficient/monomial pairs in
`residuals[].terms`. At every inherited stage from the raw factorial-free
source through its factored, projected, translated and two balanced
endpoints, F is coordinate 3, R is coordinate 4, and row zero is exactly

    [[-1,[3,3]],[1,[4]]]  = R-F².

F and R are not deleted by the earlier projection, their coordinate
translations are zero, the factoring edits do not alter/delete row zero,
and no preceding/final residual-row operation uses row zero as either
target or source. No coordinate shear targets either coordinate. Thus
changing that retained row to R-F is the stated semantic change, not a
change to an unrelated translated gate.

The source copies are byte-identical to the inherited balanced equations:

| Source | SHA-256 | stored q coordinate | private z | radix row |
|---|---|---:|---:|---:|
| 241 | 4ac1f58659deee06fdd8d956ebc1f38f72543135759f1174b145e3d8f5b4f9fb | 103 | 238 | 175 |
| 242 | 3970268165d2dea4914550913d1e882f9c6f108008de677a919fc2a01b8740a5 | 104 | 239 | 176 |

The earlier translation is old=new+shift with shift -1 at the q
coordinate. Accordingly actual q=stored q-1. The old stored guard is

    stored_q-2-4z-4z²,

not stored_q-1-4z-4z². After the semantic edit, the correct restoration is

    stored_q=4z+2,    R=F.

The checker independently pulls every surviving source residual back through
these restorations and checks both deleted affine rows vanish identically.
Restriction and restoration are inverse maps between the **edited** source
and the projected endpoint.

The old private-root map z_new=z_old(z_old+1) proves only a one-way guard
implication when R is fixed. The separate linear-radius change is justified
by soundness/completeness above, not by a pointwise witness map. The proof,
certificate text and review keep these distinctions explicit.

## 7. Executed finite checks and exact endpoint census

External checker code and its relevant imports were inspected before execution.
The following checks passed:

* New endpoint `check.py`, normally and with Python -O: all four endpoints,
  every pulled-back residual/restored coordinate, collected quartic,
  coordinate liveness, metrics, and six rejected corruptions per endpoint.
* Inherited independent power-interface audit: all eighteen requests,
  fourteen principal pairs, one derived consecutive pair, all five base
  moduli and all 37 distinct frame atoms.
* Inherited factorial-free checker with `--skip-parent --affine-only`:
  full immediate source reconstruction, eighteen Horn-factor edits,
  202 monic projections, 114 unused-coordinate removals, translations,
  both balanced endpoints and seven rejected corruptions. The older
  transitive parent verifier was intentionally not claimed rerun here.
* Separate literal bindings inspection summarized in
  `integer_math_source_bindings.json`.

| Endpoint | Variables | Rows | Degree | Monomials | Height | Row height |
|---|---:|---:|---:|---:|---:|---:|
| linear_integer239 | 239 | 175 | 4 | 12,749 | 7,968 | 64 |
| linear_integer240 | 240 | 176 | 4 | 5,023 | 7,968 | 64 |
| mod4_integer240 | 240 | 176 | 4 | 12,812 | 7,968 | 64 |
| mod4_integer241 | 241 | 177 | 4 | 5,067 | 7,968 | 64 |

Receipts are in `integer_math_checks_normal.json`,
`integer_math_checks_optimized.json`,
`integer_math_power_interface.json`,
`integer_math_inherited_finite.json` and
`integer_math_source_bindings.json`.

Later optimizer row bases are outside this frozen numerical census unless
independently replayed. Invertible integer row operations preserve the common
zero set, so they do not change the ordinary arithmetic argument; any new
metrics must nevertheless be recomputed from their actual frozen artifacts.

## Conclusion

The new radius and radix arguments close the signed bootstrap, the output-sign
cycle, every-prime CRT completeness, the y=F boundary and exact label balance.
The literal semantic edits are correctly bound to their translated sources,
and the subsequent affine deletion is an actual integer zero-set bijection.
No repair is required for the reviewed version. A final report may use the
coefficient-bound derivation in Section 3 and explicit CRT parity intervals
in Section 5 to make its already-valid compressed arguments easier to audit.

