# Odd half-binomial scale: 27 unrestricted integer variables

Research note, 22 October 2026. Source snapshot:
`VladimirReshetnikov/ProveIt@f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

## Result and interface

Retain the normalized P67/P68 or ordinary-strong P69 blank-machine circuits
and a single authentic coefficient tuple `(beta,K,MC,MFsrc)` from the existing
compiler. Positivity is required only for

    J,F,alpha,z,eta,zeta.

Set

    i = 2r+1, s = 2v+1, w = u^2

and allow `r,v,u,f,h,T,tau,y,gamma` to be arbitrary integers. The resulting
domain has the same existence of zeros as the positive source circuit. The
usual three-variable positive surjection on those six guarded coordinates
therefore gives `6*3+9=27` unrestricted integer unknowns. This improves the
29-integer construction in package 14 by two variables and five gates.

The new mathematical ingredient is that a negative nonzero half-binomial
scale `s` is incompatible with the arithmetic equations. Completeness uses
an exact population identity to show that the authentic positive scale is
odd. This is an ordinary mathematical proof; it is not kernel checked.

## 1. Common abbreviations and easy sign facts

Use precisely the source abbreviations

    q=beta J+1, C=q-F-alpha, X=wq, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, A=a+2,
    H=4a+3, Delta=a^2+H,
    D=X+ac+gamma H,
    G=(q-1)(q-F)+alpha,
    R=G(q^2-1)+(MC+q MFsrc)J,
    V=c(Tf-1)-Rf^2.

Here `q>=16`, `k>=2`, and `s` is odd, so `Y` is nonzero and `|Y|>=q^3`.
Initially `X>=0`. Since `a=(X+1)Y`, one has `|a|>=q^3`, so `Delta>0` and
`|H|>1`. As always, `Delta` is 0 or 3 modulo four, independently of the sign
of `a`.

For P67, cancelling the nonzero Delta gives the six-factor unit equation

    N0 N1 Naux Nk Nt Ns=1,
    Ns=f^2-Delta i^2 c^4.

The familiar mod-four arguments exclude negative main and strong units.
The auxiliary coefficient `(i Delta c^2)^2` is a square, so its negative
unit is impossible too. The consecutive-product negative-Pell descent
excludes `N0=-1` when `X>0`; when `X=0`, `N0=tau^2`, which is also not -1.
Thus `N0=N1=Naux=Ns=1`, `Nk=epsilon`, `Nt=nu`, with `epsilon,nu` in
`{1,-1}` and `epsilon nu=1`.

The same conclusion applies to P68 after recovering `Ns=1`, since its
auxiliary coefficient then agrees with the square coefficient of P67.
For ordinary P69, recover `1+(ic^2)^2-Delta(f^2-1)=1` first: its negative
unit would require the difference of two residues from `{0,1}` to be 2
modulo four. This gives the ordinary strong equation and a square auxiliary
coefficient. The subsequent argument is identical. Systems assert their
individual norms equal to 1 directly.

If `X=0`, the main root equation says `D=ac+gamma H`. Reduction of
`D^2-Delta c^2=1` modulo H, using `Delta=a^2+H`, gives `0=1 (mod H)`.
This is impossible because `|H|>1`. Consequently `w>0` and `X>=q`.

Weak transport with the six still-positive guarded coordinates is unchanged.
For the product, it yields `C>=0`; the shifted ordinary system gives `C>0`.
In either case `q-F=C+alpha>0`, and the source mask bounds give

    q(q^2-1)<R<q^4-2, R-2>3q+1, |E|>=q^4>R+2.       (1)

These deductions have used neither the sign of s nor the sign of h.

## 2. Assume s<0 and recover the Pell rank

Put

    Z=-Y>=q^3, B=-A=(X+1)Z-2,
    c0=-c=kZ-eta, P0=2XZ^2+1.

Then `B>=2`, `Delta=B^2-1`, and

    k(Z-1)<c0<kZ,  P0>B,  c0>k.                    (2)

The first and main norm classifications give

    |tau|=chi_P0(n), k=2 psi_P0(n), n>=1,
    |D|=chi_B(p), c0=psi_B(p), p>=1.

Since `P0>B` and `c0>k`, strict growth gives `p>n`. Also `P0=1 (mod |E|)`,
so the first Pell recurrence and index factor give

    2n=R+epsilon+v0 |E|, v0>=0,
    n>=(R-1)/2>=24.                                (3)

Nonnegativity of `v0` follows from `2n>0` and `0<R+epsilon<|E|`, and not
from a sign assumption about h. Thus

    c0>B Delta^2, c0>2p, c0>2R.                     (4)

For the last inequality, `p>=25` and `B=|E|+Z-2>R`, so
`c0>=psi_B(2)=2B>2R` suffices. The stronger ordinary-rank bound in (4)
follows from `psi_B(p)>=(2B-1)^(p-1)` and `p>=25`.

For normalized strong, `f^2-Delta i^2 c0^4=1` and odd i give

    |f|=chi_B(m), psi_B(m)=|i|c0^2,
    p*c0 divides m, hence m>2p.                    (5)

Indeed strong divisibility gives `p|m`; writing `m=pt`, the Pell binomial
expansion modulo `c0^2` gives `c0|t`, since `gcd(chi_B(p),c0)=1`.
For ordinary strong, the existing relaxed-rank lemma applies by (4) and
gives `p|m`, `c0|m`, `m>=c0>2p`, and `c0^2 | f^2-1`. In both versions,
letting rho be the positive square root of the auxiliary coefficient,

    rho^2=Delta(f^2-1), c0^2 divides rho,
    rho^2 V^2-(rho^2-1)y^2=1.

The auxiliary equation excludes zero V and y. Its Pell classification and
odd Chebyshev quotient give an odd index ell and sign sigma such that

    V=sigma Q_j(rho^2), ell=2j+1,
    Q_j(1-B^2)=(-1)^j psi_B(ell),
    Q_j(0)=(-1)^j ell.

The defining V gives `V=-c=c0 (mod |f|)` and `V=-R (mod c0)`. Squaring the
first congruence, and then applying the source signed step-down lemma with
`0<2p<m`, yields `ell=+p or -p (mod m)`. Reducing the second congruence
modulo c0 gives `ell=+R or -R (mod c0)`. Therefore
`R=+p or -p (mod c0)`, and (4) forces

    p=R.                                          (6)

The change from `c>0` to `c<0` changes a congruence sign which is discarded
when squaring. It does not alter this rank argument. No claim about the
sign of V, f, T, or gamma is needed.

## 3. Recover the index sign and obtain a large negative scale

Equations (1), (3), and `n<p=R` force `v0=0`. If `epsilon=-1`, then
`R=2n+1`. However, `Q=chi_B(2)=2B^2-1>P0` and `B>Z`, so

    psi_B(2n)=2B psi_Q(n)>=Bk,
    c0=psi_B(2n+1)>Bk>kZ,

contradicting (2). Hence `epsilon=nu=1`, `R=2n-1`, and transport now gives
`C>0` in the product case as well. Write `R=2r0+1`, `n=r0+1`; here `r0>=23`
(the weaker bound `r0>=2` is all that is used below).

The elementary Pell growth bounds give

    Z>c0/k
      >= (1/2) [ (2B-1)^2/(2P0) ]^r0
      > X^r0/2
      > 2^(2r0+1)=2^R.                            (7)

For the strict middle inequality, after multiplying by positive denominators,

    (2B-1)^2-2P0 X
      =4(2X+1)Z^2-20(X+1)Z+25-2X >0.

For `X>=16` and `Z>=4` this expression is positive: its value at `Z=4`
is `46X+9`, and it is strictly increasing thereafter. The final inequality
uses `X>=16` and `r0>=2`. The elementary facts `Q>P0` and `B>Z` used above
also hold directly for `X>=16`, `Z>=4`.

## 4. Both signs of the main root are impossible

The integer Pell polynomials at the original negative parameter `A=a+2=-B`
satisfy, for every integer index j,

    chi_A(j)-a psi_A(j)=2^j (mod H),
    chi_A(j)+a psi_A(j)=2^(-j) (mod H).

Here 2 is invertible modulo the odd integer H. These recurrence identities
are valid for negative A and negative H as well. Since R is odd,

    chi_A(R)=-chi_B(R), psi_A(R)=psi_B(R),
    c=-psi_A(R).

If `D=+chi_B(R)`, the defining `D-ac=X+gamma H` therefore gives

    X=-2^R (mod H).

But `0<X+2^R<X+Z<4(X+1)Z-3=|H|`, by (7). This is impossible.
If instead `D=-chi_B(R)`, the same identity gives

    X=2^(-R) (mod H), hence X 2^R=1 (mod H).

Again (7) gives `1<X 2^R<XZ<|H|`, impossible. Main norm already excludes
`D=0`. Therefore `s<0` cannot occur. Because s is odd, this proves `s>0`.

At this point every remaining equation lies in the already proved signed
domain of package 14 (or package 12 with the odd multiplier and square scale).
Its compiler soundness applies without any further change.

## 5. Completeness: the canonical scale is odd

Use the canonical positive witnesses of package 14: these already permit
odd i and `w=u^2`, by choosing the strong index `m=cR` and spatial/temporal
padding by powers of five. Only odd s remains to be checked.

Write `q=2^t`, `M=q^2`, and

    S=(C-1)+qF,
    Tmask=(MC J+1)+q(MF J-1).

The native masks give `S AND Tmask=0`; both numbers lie below M. Consequently
their sum lies below M and has population equal to the sum of their
populations. Since `MC=2 (mod 4)` and `MF=4 (mod 8)`, where MF is the
unshifted high mask, and `popcount(MC)+popcount(MF)=d`, the repeated masks give

    popcount(Tmask)=dN+2=t+2.

The exact packing formula is

    R=(M-S)(M-1)+Tmask
     =(M-1-S)M+(S+Tmask).

The high and low blocks have no overlap, and the M-bit complement has
population `2t-popcount(S)`. Therefore

    popcount(R)=2t+popcount(Tmask)=3t+2.

The authentic half-binomial kernel supplies

    v2(Y)=popcount(R)-2=3t.

Since `Y=s q^3`, this says `v2(s)=0`: s is a positive odd integer. Put
`v=(s-1)/2`. The unchanged positive witnesses now satisfy the new domain.
This proves completeness. In fact this parity conclusion holds for every
positive source solution after compiler recovery, not merely the canonical
ones.

## 6. Exact size and reproducible artifacts

For each of the six guarded ports use the positive surjection

    Pos(x,y,z)=1+x^2+y^2+z(z+1).

It costs seven binary arithmetic gates and is onto the positive integers
by the three-square theorem applied to `4n-3`. The two odd maps cost two
gates each and the square map costs one. The entire substitution therefore
costs `6*7+2+2+1=47` gates.

| Source | Integer unknowns | Equations | Exact degree | Binary gates |
| --- | ---: | ---: | ---: | ---: |
| normalized P67 | 27 | 1 | 274 | 114 |
| normalized P68 | 27 | 1 | 216 | 115 |
| ordinary P69 | 27 | 1 | 172 | 116 |
| ordinary shifted system S60 | 27 | 6 | 46 | 107 |
| sum of squares from S60 | 27 | 1 | 92 | 124 |

Degree uses weight two on `J,F,alpha,z,eta,zeta,w`, and weight one on
`s,i,f,h,T,tau,y,gamma`. For the normalized P67 six factors the exact
weighted degrees are `(40,32,104,12,4,82)`; for P68 replace 104 by 46; for
P69 they are `(40,32,46,12,4,38)`. The main-norm leading cancellation is
accounted for by `N1=2ac(X+gamma H)+(X+gamma H)^2-Hc^2`. The ordinary sum
of squares has exactly twice the degree 46 of its unique highest residual.

These degree claims hold uniformly for every fixed `beta>0`, not only for
the small tuple used in the numerical specialization check. Here is an
explicit nonvanishing certificate. For a substituted port p write `p_*`
for its highest homogeneous part. Thus every positive guarded port has
`p_*=u_p^2+v_p^2+r_p^2`; these forms use disjoint triples of variables. Set

    Q_*=beta J_*, k_*=eta_*+zeta_*, w_*=w_integer^2,
    s_*=2s_integer, i_*=2i_integer,
    C_*=Q_*-F_*-alpha_*,
    Nt_*=w_* C_*-z_* Q_*.

The polynomial `Nt_*` is nonzero for every `beta>0`: setting
`w_integer=0` leaves `-z_* Q_*`, a nonzero polynomial. The other displayed
factors are likewise nonzero. In this notation the highest homogeneous
parts of the three product polynomials, after the actual 27-variable
substitution, are respectively

    P114_* = -8 Q_*^91 h gamma i_*^4 k_*^13 w_*^13 s_*^26
                T^2 f^2 Nt_*,
    P115_* = -8 Q_*^71 h gamma i_*^2 k_*^9 w_*^11 s_*^20
                T^2 f^4 Nt_*,
    P116_* =  8 Q_*^55 h gamma i_*^2 k_*^9 w_*^7 s_*^16
                T^2 f^4 Nt_*.

Their degrees are exactly 274, 216, and 172. In particular the only leading
term left in the main norm after cancellation is
`8 gamma a_*^2 c_*`; here `a_*=w_* s_* Q_*^4` and
`c_*=k_* s_* Q_*^3`. The unique highest ordinary-system residual has
highest part `a_*^2 c_*^2 T^2 f^4`, of degree 46. Its square is the
nonzero highest part of SOS124, of degree 92. The integral polynomial ring
has no zero divisors, so none of these products can vanish identically.
This proves exact degree for the original authentic tuple and for the new
5263-tile tuple, independently of the values of `kappa`, `MC`, and `MF`.

The circuit builder records exact operation ledgers, rational/integer
identity checks, liveness, weighted upper bounds, and independent univariate
specializations attaining every stated degree. These are finite checks of
arithmetic statements, not a formal verification of the compiler, the Pell
rank lemmas, or Con(ZFC). The ordinary mathematical reduction is the proof.

## 7. Dependencies and precise scope

All source paths below are inside the pinned collection.

* `14-integer29/proofs/signed_domain_proof.md`: existing signed domain,
  odd strong multiplier, square scale, and canonical completeness.
* `11-t4/comparison/sources/06-blank67/proofs/fixed_blank_67_proof.md`:
  polynomial formulas, weak transport boundary, index bootstrap, packing.
* `11-t4/comparison/sources/06-blank67/proofs/blank_helical_proof.md`:
  canonical powers-of-five padding and finite-window semantics.
* `12-gap-norm14/proofs/ORDINARY_BLANK_PROOF.md`: ordinary rank, signed
  auxiliary step-down, shifted S60 and SOS77.

Composing with an authentic compiler tuple and the established K215
blank-halting/refutation endpoint gives the ZFC-provable equivalence between
unsolvability of each listed construction and Con(ZFC). This note supplies
no proof of Con(ZFC), no claim of global minimality, and no new Lean/Rocq
build. Universal-polynomial small-variable bounds are a different comparison.

