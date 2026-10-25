# Four symmetric digit caps replace eleven interval-product guards

This note proves a new transformation of the current signed C222 compiler.
It is independent of finite testing. It composes with the selective nine-term
linear orientation pool and the deterministic comparison center. It changes
neither a semantic front coordinate nor a power request. The final polynomial
and its measured size must be obtained from the actual finite transformation;
the proof does not infer final counts by informal subtraction.

## 1. A general signed-residue cap

Let `L>=1` and let integers `p_i` have canonical residues `a_i` modulo L,
for `1<=i<=m`, with

    0 <= a_i < L/8,       1 <= m <= 5.

Suppose unrestricted integer coordinates `r_i` satisfy `r_i=p_i mod L`.
Replace separate interval guards on every `r_i` by the single equation

    L^2 - 4*sum_i r_i^2 - 1 = u^2+v^2+w(w+1),                (SC)

where `u,v,w` are new unrestricted integers.

For every integer w, `w(w+1)>=0`, so (SC) implies

    4*r_i^2 <= 4*sum_i r_i^2 < L^2.

Thus `-L/2<r_i<L/2`. The only integer in that interval congruent to
`a_i in [0,L/8)` is a_i itself. Indeed `a_i+L>L/2` and
`a_i-L<-7L/8<-L/2`. Therefore every r_i equals its canonical residue.

Conversely set `r_i=a_i`. Then

    4*sum_i a_i^2 < (m/16)*L^2 <= (5/16)*L^2 < L^2.

Consequently the integer `L^2-4*sum_i a_i^2-1` is nonnegative and has
a representation `u^2+v^2+w(w+1)`. For completeness, the latter standard
representation follows from Legendre's three-square theorem applied to
`4n+1`. Since `4n+1` is not of the form `4^a(8b+7)`, it is a sum of
three squares; exactly one summand is odd. Writing the others as `(2u)^2`
and `(2v)^2` and the odd one as `(2w+1)^2` yields the required identity.

The cap does not merely assert nonnegativity of r_i. It selects a signed
representative in a short symmetric interval; correctness comes from the
separately proved location of the true residue. The factor 4 is a fixed
integer coefficient and every residual in (SC) is quadratic.

## 2. A low-digit lemma with a fixed spare-radix margin

Let `q>=2`, `k>=1`, `n>=0`, `L=q^k`, and suppose

    binom(n,j) <= q/16      for all 0<=j<k.

The binomial theorem gives the low residue

    a = sum_(j=0)^(k-1) binom(n,j)*q^j.

It is nonnegative, is congruent to `(q+1)^n` modulo L, and satisfies

    a <= (q/16)*(L-1)/(q-1) < L/8.

The last step uses `q/(q-1)<=2` and `L-1<L`. In particular a<L,
so it is the canonical residue. The argument includes n=0: its low
residue is one, because `binom(0,0)=1` and all higher coefficients vanish.

No variable exponent or binomial operation is added to the equation.
These are proof expressions for the values of the already-certified
power coordinates and their ordinary integer residues.

## 3. The exact current source and the four groups

The existing signed front, after the Pell orientation/power stage and
before any remainder-sign interpretation, supplies

    t>=16,
    V0=(F^2+1)^t,
    FB=V0+s,    B=r+s+1,    q=B+o+1,
    r,s,o>=0,
    y=V0(V0-1),
    x=F+1+(y+1)u0,
    x=1+[1+(t+1)y]*ut,
    N=B^x,    q=(B H0)^x,
    H0=1+a+b+c+d+S+Sp+u+vq+C0.

The nine actual CRT representatives in H0 are nonnegative. Their shifted
stored coordinates need not be. The selective-orientation proof gives
all eighteen powers exactly without assuming the signs of any of the
eleven digit remainders or slacks addressed here. In particular the
positive output of `q=(B H0)^x` first supplies x>0 and its canonical pair.

The raw ceiling forces `F>=1`, `B>F`, hence `B>=2` and `q>=3`.
It also gives `y>F+2`, so `u0>=0`, `x>=F+1>=2`, `ut>=1`, and

    x >= 2+(t+1)y >= 2t+4.                                  (1)

All of this precedes the factorial interpretation. The initial possibility
F=0 is handled by the already-oriented t pair: its base-one power would
give V0=1, contradicting `FB=V0+s` with s>=0. No digit cap is used to
establish this early fact.

There are exactly four common denominators after K=x:

| Group | Upper indices n | Common L | Number of remainders |
|---|---|---|---:|
| T | F^2+t, C0 | q^t | 2 |
| A | a,b,c,d,h | q^(t+1) | 5 |
| S | S,Sp | q^(y+1) | 2 |
| X | u,vq | q^x | 2 |

Here h is the derived-label upper index. Equation (1) implies that every
lower index `k in {t,t+1,y+1,x}` satisfies `1<=k<=x`.

Replace the eleven old nonnegative-product graphs `r_i*s_i>=0` by one
instance of (SC) for each row of this table. Keep the eleven linear rows

    L=r_i+s_i+1,                                             (2)

and all digit-output and quotient equations. The old slacks s_i may be
eliminated later by certified monic substitution; mathematically (2)
continues to define them exactly.

## 4. The ordinary representatives have tiny low digits before F=t!

Let n be any one of the nine actual CRT representatives. With
`H0=1+sum(representatives)`, we have

    max(1,n) <= H0.

For every `0<=j<=k<=x`, including n=0,

    binom(n,j) <= max(1,n)^j <= H0^x = q/B^x <= q/16,          (3)

because B>=2 and x>=4. This proves the needed coefficient bound without
any factorial identity, any choice of CRT representative size, or any
assumption that the actual representatives are strictly positive.

The case j=0 is explicit: `binom(n,0)=1`, so no invalid use of `0^0`
or the estimate `binom(0,0)<=0^k` occurs.

## 5. The factorial low digit is tiny before the factorial is known

Set `b=F^2+1` and `n0=F^2+t`. Since F>=1 and t>=1,

    b^t >= 1+tF^2 >= F^2+t = n0.

The second inequality is equivalent to `(t-1)(F^2-1)>=0`.
Together with the raw ceiling and B>F,

    n0 <= V0 <= BF < B^2.

For every `0<=j<=t`, therefore,

    binom(n0,j) <= n0^t < B^(2t)
       <= B^(x-4) <= q/B^4 <= q/16.                          (4)

The exponent comparison is (1). This is a bound through position t,
not merely below t, so it also controls the digit whose intended output
is B. It uses none of `F=t!`, the value of the factorial binomial, or a
decoded range predicate.

After the exact power `(q+1)^n0` and `L=q^t` are known, its retained
digit equation is

    (q+1)^n0 = (B+q*z)*L + r_T.

The T-group symmetric cap gives `|r_T|<L/2`; (4) and the low-digit lemma
give the canonical residue `0<=a_T<L/8`. Hence r_T=a_T. The next digit
is `binom(n0,t)<q`, whereas the unchanged output bound gives
`0<B<q`. Reducing the exact quotient modulo q therefore yields

    B=binom(F^2+t,t).

The unchanged raw ceiling now invokes the inherited factorial fixed-point
lemma to give `F=t!`. This step is noncircular: the very cap needed for
this first binomial is justified by (4), proved without that identity.

The other T-group member C0 satisfies (3), so its remainder can be
recovered at the same stage. Its later range interpretation may still be
postponed until the factorial has been identified.

## 6. The derived-label digits are tiny after F=t!

The retained reciprocal-index condition is

    B divides C0+F^2+1.

The interpreted factorial binomial, t>=16 and F=t!, give B>F^2+1.
Thus C0=0 is impossible, and C0>=1. Consequently H0>=2.

Let `n=max(a,b,c,d)` and `n*=max(1,n)`. The inherited, explicitly
certified monotone constructor majorant is

    h <= (n*+1)^ell,       ell=2^22=4194304.

Because C0 is a separate representative and C0>=1, `H0>=n+2`.
Thus `n*+1<=H0`, including n=0, and

    h <= H0^ell.

For all integers t>=16,

    ell*(t+1) < 2*t!.

This inequality is verified at t=16 and preserved on increasing t because
`(t+1)^2>t+2`; no asymptotic claim is needed. The endpoint bound gives
`x>2F=2*t!`, so `ell*(t+1)<x`. For every `0<=j<=t+1`,

    binom(h,j) <= max(1,h)^j <= H0^(ell*(t+1))
       <= H0^x = q/B^x <= q/16.                             (5)

This proves the bound for the only upper index that needed the factorial
identity first. No A-group digit or interval sign is used to prove (5).

## 7. Soundness and exact restoration of the old guards

The proof order is now fully acyclic.

1. Apply the unchanged square frame, modified anchor, selective orientation
   pool, and signed-power lemmas. Obtain exact power values and the early
   front inequalities of Section 3. The eleven removed product guards are
   not used by those lemmas.
2. Recover the T-group factorial remainder by (4), identify its binomial
   digit, and use the inherited fixed point to obtain F=t!.
3. Establish C0>=1 and the derived-label margin (5).
4. Apply (3), (4), and (5) together with the four symmetric caps. Every
   retained remainder is its canonical `r_i in [0,L_i/8)`.
5. The retained linear rows (2) therefore give

       s_i=L_i-r_i-1>=0.

   Hence `r_i*s_i>=0`. Choose fresh triples representing each of these
   eleven products by `u_i^2+v_i^2+w_i(w_i+1)`. These restore the eleven
   old product-guard rows. Their witnesses were private, so no other row
   changes. All other coordinates, including signed digit quotients,
   are retained exactly.
6. The complete parent arithmetic graph is now restored. Its range tests,
   Horn-flow interpretation, C222 calibration, and ZFC refutation bridge
   apply exactly as before.

There is no need to constrain a digit quotient or a high-digit coordinate
to be nonnegative in order to prove congruence or unique residue selection.
When their old semantic interpretation requires nonnegativity, it follows
after the actual positive numerator and canonical remainder are known.

## 8. Completeness and the reverse witness construction

Start from a finite C222 refutation and any of the canonical witnesses
supplied by the parent construction. Its semantic front satisfies all
the exact relations in Section 3 and F=t!. Its canonical remainders obey
(3)--(5), so for each group of size m<=5 they satisfy `r_i<L/8` and

    L^2-4*sum_i r_i^2-1 >= 0.

Choose one ternary representation of this nonnegative integer for each
group. Delete the eleven old private product-guard triples. Every remaining
source coordinate, every quotient, and every old linear remainder row is
unchanged. This constructs a zero of the new graph.

One can equally start from an arbitrary zero of the fully interpreted
parent graph: its exact semantics prove these same bounds. Thus the
change is an existence equivalence with explicit witness restoration,
not a heuristic expectation that sufficiently large bases should work.

## 9. Literal bindings for the current implementation

For `new_direct/equations/linear9/source.json`, before deleting/remapping
coordinates, the exact table is:

| Group | L coordinate/name | Remainder coordinates |
|---|---|---|
| T | 181 / pow4.output | 183 / choose0.remainder; 236 / range8.remainder |
| A | 189 / pow6.output | 191,197,202,207,242 / range0,1,2,3,9.remainder |
| S | 211 / pow11.output | 213,219 / range4,5.remainder |
| X | 223 / pow14.output | 225,231 / range6,7.remainder |

Delete exactly `domain_guard.3` through `domain_guard.13`, eleven
rows. Their 33 private witness coordinates are 547 through 579 inclusive.
Keep the three early scalar graphs `domain_guard.0`, `.1`, `.2` and the
squared-anchor graph `domain_guard.14`. Keep all eleven rows with labels
ending in `.remainder_bound` for these requests.

Append twelve fresh signed coordinates, three for each of the four new
rows. For each group the literal residual is

    +L*L - 4*sum(r*r) - 1 - u*u - v*v - w*w - w.

The sum-of-squares wrapper still has degree at most four. The raw
transformation removes 21 coordinates and 7 residuals before exact
projection. Final liveness, integral restoration, collected coefficients,
degree and size must be measured by the implementation and independent
checker; no final metric is asserted here.

## 10. Verification and attribution boundary

The conceptual input is the existing natural-domain pooled low-digit
budget in `conzfc_graph_digits/direct/PROOF.md`. That theorem used a
nonnegative sum cap and a different radix `q=N^(2R)`; its soundness did
not need a pre-factorial low-digit estimate. The new work is the symmetric
signed cap, the actual self-radix `q=(B H0)^x` bounds, the pre-factorial
estimate (4), and the staged witness restoration for unrestricted integers.

The inherited inputs are Pell classification and power compilation, the
factorial fixed-point theorem, the literal constructor majorant, Legendre's
three-square theorem, and the parent C222/ZFC calibration. Finite checks
must verify the actual deletion boundary, the four denominators, the
remainders and private witnesses, every remaining row, every projection,
and every collected quartic coefficient. They do not prove the unbounded
number theory by sampling.
