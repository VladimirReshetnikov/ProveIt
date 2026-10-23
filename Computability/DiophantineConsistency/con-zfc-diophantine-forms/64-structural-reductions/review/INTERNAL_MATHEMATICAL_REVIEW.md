# Independent internal review of the proposed reductions

Review date: 23 October 2026. Comparison snapshot:
`VladimirReshetnikov/ProveIt@beb0192cb8dc36f78c369c080f2adfbc1887a486`.

## Finding and scope

I found no blocking mathematical gap in the new 41-integer quartic or
14-positive degree-30 construction after an independent adversarial reading
of their proofs, literal equations, and the relevant inherited Pell
arguments. This is an internal AI-assisted mathematical review, not external
peer review, a proof-assistant certificate, or a proof that either equation
has no solutions.

The review covered:

- `integer41/PROOF41.md`, `PROOF44.md`, and the literal
  `quartic41.json` and `quartic44.json`;
- the inherited signed-domain, odd-scale, ordinary strong-rank, and signed
  auxiliary-index arguments, including their quantitative hypotheses;
- the source34 whole-tuple contract and canonical parity statements;
- `positive14/build.py`, `PROOF.md`, the ordinary kernel and
  squared-modulus proof, and the compact native coefficient binding;
- independent reading and hashing of all eight supplied fixed coefficient
  payloads, and independent checks of their numerical mask contracts.

The review did not independently reconstruct the entire machine-to-tableau
compiler proof or the K215/refutation calibration. These remain the named
inherited mathematical dependencies. The proposed sextic and octic
companions were outside this review's requested scope.

## 1. The 41-integer quartic

### Literal arithmetic agrees with the proof

The first seven lifted rows recover, without division by a potentially zero
quantity,

    L=q^2-1, N=q^3, X=4q w_scale,
    Y=(2 v_scale+1)q^3, a=E+Y, E=XY,
    c=(eta+zeta)Y+eta,
    P=(eta+zeta)(XY^2+1).

Consequently the first norm really is

    tau^2-XY^2(XY^2+1)(eta+zeta)^2=1.

The main-root, strong, and exposed quotient rows similarly give precisely
the equations used in the proof. In particular the two exposed congruences
are `V=of-c` and `V=jc-R`; neither requires inventing an integral quotient
from a rational expression. Substituting `w=4 w_scale` preserves quadratic
residual degree. There are 41 coordinates and 26 residuals, and the isolated
`tau^4` term has coefficient one in their sum of squares.

### No early sign is assumed for the radix

The two retained common-sign guards force `F,alpha,C=q-F-alpha` to share a
nonzero sign. Thus `q` has that sign, `J` is nonzero, and
`Q=|q|>=beta-1>=16`. The separate positive- and negative-radix estimates in
PROOF44 correctly establish

    Q(Q^2-1)<R<Q^4-2

before any sign conclusion about `q,w_scale,Y,eta,zeta`. For negative q the
mask summand becomes `(Q MF-MC)(Q+1)/beta`, which is positive under the actual
shifted-mask bounds. Using an unshifted MF in that estimate would be a real
error; the supplied polynomial uses the shifted port.

The main norm excludes `X=0` by reduction modulo `H=4Y+3`, whose absolute
value exceeds one. Therefore `X=4q w_scale>0` gives `X>=4Q`. Since the cubic
scale is a nonzero odd multiple of `q^3`,

    |E|>=4Q^4>3R+1.

This stronger bound is obtained before the eta/zeta signs are recovered.

### The negative common-sign contradiction is valid

The single guard on `eta*zeta` leaves just two common-sign possibilities.
For the negative one, write `K=-(eta+zeta)>0`, `Z=|Y|`, `c0=|c|`, and
`B1=|a+2|`. Direct substitution gives either

    KY<c0<K(Y+1)                  (Y>0)

or

    K(Z-1)<c0<KZ                  (Y<0).

Hence `c0>K`. Also `P0=2XY^2+1>B1>=2`. The first and principal Pell
classifications give `K=2 psi_P0(n)` and `c0=psi_B1(p)`, so monotonicity
forces `p>n`. The signed index row gives

    2n=-(R+1) modulo |E|.

The positive representative is at least `|E|-R-1>2R`, so `n>R`. This is the
key point where the factor four is needed: the earlier bound
`|E|>R+2` alone does not produce this contradiction.

Pell growth now proves `c0>B1(B1^2-1)^2`, `c0>2p`, and `c0>2R`. Thus the
ordinary strong-rank theorem's large-coordinate hypothesis is available
before it is invoked. It yields `p|m`, `c0|m`, and `m>2p`.

The signed auxiliary-index argument remains valid for either sign of c.
The congruence modulo f is squared, and the other is modulo `|c|`; its
conclusion is `R=+p` or `-p` modulo c0. Since `0<R,p<c0/2`, this gives
`p=R`, contradicting `p>n>R`. Thus the new product guard really recovers
both separate positive signs.

### Restoration to the 44-variable intermediate and compiler endpoint

Once eta and zeta are positive, the omitted separate ternary guards can be
supplied, so the intermediate proof applies. I checked its negative-Y ratio
argument and both possible principal-root signs against the inherited
odd-scale proof. The required hypotheses are the absolute-radix bounds,
`X>=Q`, and `|Y|>=Q^3`, all already available. The proof recovers `Y>0` and
then `X=2^R` without assuming a sign for q.

Only then is `q|2^R` used to give `q=+2^t` or `-2^t`. The Mersenne lemma
excludes the latter: modulo `2^d-1`, every `2^t` has residue `2^r` for
`0<=r<d`, which cannot equal `2^d-2` when `d>=3`. This sign argument does
not require d to be odd.

The post-power compiler can now be applied directly. It would be incorrect
to claim that an arbitrary new solution already has the old separate
square-w and twice-square-q restrictions. PROOF44 explicitly avoids that
claim and instead decodes through the post-power compiler; fresh canonical
old witnesses may subsequently be chosen.

### Completeness uses the actual parity interface

Source34's coefficient proof supplies canonical `q=2^t` with odd t,
`R=3 mod 4`, and `R>t`. Therefore `w_source=2^(R-t)` is divisible by four,
and `w_scale=w_source/4` is an integer. Also `X=2^R=2u^2` with
`u=2^((R-1)/2)`. Its ordinary strong multiplier and cubic scale are odd, as
required by the retained affine parametrizations. These statements are
properties of the complete source34 adapter, not consequences of numerical
mask bounds alone.

## 2. The 14-positive degree-30 construction

### Unit recovery does not assume a Pell solution in advance

For f=1 the residual `W=I^2` is already too large for the outer sum of
squares to equal one. For f>=2, write `Aaux=Delta(f^2-1)>1`. If Na were
zero, `Aaux V^2=(Aaux-1)(V+e)^2` would make `Aaux(Aaux-1)` a rational
square. Neither factor on the right can vanish because e is positive.
The integer lies strictly between consecutive squares, a contradiction.
Thus `Na^2>=1`. The outer equation forces all other residuals to vanish;
then `W=0` makes Na a Pell norm whose residue modulo four excludes -1.
This establishes the claimed tuplewise reduction to five exact equations.

### The adaptive modulus is large enough before the rank is known

The first integral-root carrier gives `q^3|Y` without a size assumption on
an unknown index. Therefore `Y>=q^3`, and the shifted transport equation
gives `C>0`. The actual native bounds imply `R<q^4-2`.

Since `H=4Y(X+1)+3`, the relation `gcd(Y,H)|3` implies
`gcd(Y^2,H)|9` by a prime-valuation argument. For `U=Y^2` and
`mu=U/gcd(U,H)`,

    mu>=Y^2/9>=q^6/9>q^4>R+2.

At the same time `U|4XY^2` holds identically. These deductions precede any
use of the missing quotient h or the principal rank, so the new modulus
choice has no circular dependency.

The principal rational root `Dstar/U` is integral because its square is an
integer. Its positivity follows from `r=k-R-1<k`, positive gamma, and

    b0/H>c/5>kY/5>k/Y^2=k/U.

This uses only the already established large Y. Thus positive Pell
classification is justified at the claimed point in the proof.

### The order of strong-rank, no-wrap, and quotient restoration is sound

From the first Pell congruence and `U|H r`, one gets
`2n=R+1 mod mu`, hence an early lower bound on n. This proves the strict
large-c hypothesis required by the inherited ordinary strong-rank theorem.
That theorem is then used to obtain `c|m`, `m>2p`, and
`c^2|(f^2-1)`; none of those divisibilities is obtained by an illicit
cancellation of Delta.

The auxiliary step-down uses the actual new V through
`T_old=fT`, yielding `V=-c mod f` and `V=-R mod c`. It gives `p=R`
without needing h or the main congruence. Only now does
`n<p=R` remove the multiple of mu and give `2n=R+1`.

The first Pell recurrence then makes `r=k-2n` a positive multiple of the
full `4XY^2`. This restores both `h=r/E` and integral
`gamma_old=gamma-r/U`. Finally `g>(a+1)c` and `c>X` prove
`gamma_old>0`. The proof correctly distinguishes divisibility by mu, known
early, from divisibility by the full U, known only at this later stage.

### Canonical positivity and the squared-modulus quotient check out

For completeness, the standard canonical witnesses make r divisible by U,
so the new gamma is positive. The first new gap is positive because

    tau-ell=(ell k+1)/(tau+ell)>k/3>s.

Here `ell>k`, `tau<ell+k`, `k>XY`, and `X>=q` justify each inequality.
Thus `rho=tau-ell-s` is a positive integer. The shifted transport variable
is positive since `w>q>F` forces the old transport coordinate to exceed one.

The new T is not obtained by dividing an arbitrary old quotient by f.
It is chosen explicitly using the auxiliary Chebyshev quotient at odd
`R=3 mod 4`. The stated polynomial identities give
`V=-c mod f^2` and `V=-R mod c`. Canonical normalized strong witnesses give
`f^2=1 mod c` and `gcd(c,f)=1`; hence

    T=(V+c+R f^2)/(c f^2)

is integral and positive. The auxiliary ordinate exceeds V, making
`e=y_old-V` positive. These arguments establish completeness of the new
quotient and gap parametrizations rather than assuming surjectivity.

### Exact degree is 30, with a 14-degree principal residual

I checked the cancellation identities and leading forms against the literal
builder. The residual degrees are `12,14,10,15,2`, not an upper bound
obtained by blindly propagating syntactic degrees. In particular M has the
nonzero degree-14 leading form

    8 X0^2 Y^2 R0(k0 Y^3+2R0).

The unique degree-15 residual is Na. Thus the polynomial has degree 30 and
leading form

    4 beta^10 J^10 w^4 Y^4 f^8 e^2 (beta J-F)^2.

This is nonzero for the authentic beta. The literal builder's 83 binary
operations agree with its ledger: 44 multiplications, 23 additions, and
16 subtractions. The four fixed leaves are constants, not existential
unknowns. The domain here is strictly positive integers; this count must
not be advertised as 14 unrestricted integer variables.

## 3. Independent fixed-data checks

I independently decompressed every supplied coefficient, recomputed its
raw SHA256, and compared it with the inherited binding. All eight matched.
I also checked the exact Mersenne beta, `K>=0`, `0<MC<beta`,
`beta<MF_source<2 beta`, the native low-mask residue 2 modulo 4, the
unshifted high-mask residue 4 modulo 8, and the native mask population sum.
Every check passed for both complete tuples:

| Construction | Native tuple | beta bits | K bits | MC bits | MF_source bits |
| --- | --- | ---: | ---: | ---: | ---: |
| Q41/Q44 | mixed-parity-unrounded-1064921 | 1,064,921 | 1,065,043 | 1,064,921 | 1,064,922 |
| Fourteen positive | wang943-complement67-shared-anchor-length8807-prime581197 | 590,069 | 592,884 | 590,069 | 590,070 |

These are different coherent tuples. The fact that another older tuple has
the same beta exponent as source34 would not justify mixing their other
ports. The supplied packets and proofs keep the tuple boundaries intact.
Exact numerical checks confirm the required coefficient hypotheses; they
do not replace the native semantic and canonical-completeness theorems.

## 4. Corrections and qualifications preserved in the final proofs

The review found no additional blocking correction to make. The following
earlier corrections are material and must survive report integration:

- The literal quartic transport equation is
  `(K0+w)C=z(q-1)+F`. The unshifted source coordinate is `z_source=z+1`.
  The old prose's `(z-1)(q-1)` is not the literal equation.
- New quartic soundness recovers the sign of q after recovering `X=2^R`.
  It does not assume the old separate square restrictions for an arbitrary
  new zero.
- In the fourteen-positive proof, M has degree 14. The outer polynomial
  still has degree 30 because Na has degree 15.
- The positive-only and unrestricted-integer domains are different claims.
  The 14-positive construction is not an unrestricted 14-variable equation.
- All existence equivalences depend on the stated ordinary native/Pell/K215
  mathematics. Finite validators authenticate data, algebra, liveness and
  degree; they do not prove the whole unbounded semantic reduction.

The separate nine-positive candidate at degree 1,781,068 with 470 gates is a
modest finite packing improvement over the pinned 1,910,404/473 point.
Its novelty is principally a better row/weight/target arrangement and
recalibrated threshold. The 41-integer and fourteen-positive constructions
make structural changes to the signs and quotient parametrization. None of
these comparisons establishes a global optimum or historical novelty
outside the inspected repository frontier.

## 5. Final LaTeX transcription review

The later expanded proof in `positive14/section.tex` was
reviewed separately, focusing on the newly reproduced ordinary strong-rank
and signed auxiliary step-down details. No new mathematical or
transcription error was found. Specifically, the added lower bound on
`psi_F0(gcd(u,dp))` follows from the stated gcd divisibility; the
composition and recurrence argument gives `c|m`; the polynomial recurrence
for the odd Chebyshev quotient is correct; and the signed reduction of
the abscissa index modulo `2m` has the strict inequalities required for
uniqueness.

I also independently transcribed all 26 displayed residuals from
`integer41/section.tex` into polynomial expressions and compared
their exact expansions with the 26 rows of `quartic41.json`. Every row
agreed identically. Each displayed row has witness degree at most two after
expanding only the stated affine abbreviations. In particular the packing
row

    k-1-hE-(q-F)(N-q)+CL-(MC+qMF)J

is exactly the JSON row, not merely a consequence of other rows. Here N
remains an independent lifted coordinate; replacing N by q cubed inside
the literal quartic would instead raise its degree and is not done. This
check used exact sparse polynomial arithmetic with symbolic coefficient
ports, not numerical sampling.
