# Independent review of the product-square and Pell-doubling reduction

## Scope and verdict

The proposed product-square reduction is sound under the explicitly
retained ordinary ten-positive source, indexed folding, and auxiliary
completeness interfaces. Both the original `A D` saturation version and
the stronger Pell-doubling version pass this mathematical review.

The Pell-doubling version is the preferred mathematical construction:
it arranges coprimality by making the adjacent-Pell coefficient a multiple
of the tested product. It needs no extra saturation by `A D`. There is
no hidden restriction on the parity of the strong index; the inherited
auxiliary-completeness theorem explicitly accepts every strong pair
satisfying its stated norm and divisibility conditions.

This review is pinned to the final literal evaluators below and to the
complete `PROOF.md`, including fresh-seed completeness. The operation
counts are for the supplied topological lists and their stated binary
operation convention. The degrees are also established independently by
the highest homogeneous forms in Section 8 below.

| Final evaluator | Positive unknowns | Products | Sums | Differences | Total | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| `equation_84.json`, weight V^2 | 10 | 50 | 19 | 15 | 84 | 436 |
| `equation_85.json`, weight bV | 10 | 51 | 19 | 15 | 85 | 328 |

`REVIEW_PINS.json` gives SHA-256 hashes for the two literal equations and
proof reviewed. No new end-to-end proof-assistant certificate or global
simplicity minimum is asserted.

## 1. Definitions for the stronger version

Keep the parent's positive outer inputs and its polynomials
`A, Delta=A^2-1, c, E, R, b=c(T+alpha)-R, B, M, Kpos`, with

    U=i c^2,
    a=Delta U^2 E,
    F0=1+a,
    G=E F0,
    d=4aF0,
    Df=1+d,
    Q=Delta d,
    delta=Q-1,
    V=Df b-c,
    Dy=QV^2-1.

The integer `f=1+2a` is a proof abbreviation; it need not be a computed
gate. Identically `Df=f^2`. The complete equation is

    delta Z^2-M^2 G Dy=0.

The shipped finalizers set `RG=M^2 G` and use the exact identity

    Q(Z^2-RG V^2)+(RG-Z^2)
       = (Q-1)Z^2-M^2 G(QV^2-1).

This removes one literal binary operation relative to materializing both
`delta` and `Dy`. The 84/85 counts include this sharing; the identity does
not add a witness or an assumption.

For a polynomial transport weight `L`, the same cleared carrier gives

    z=Z/M=n+kappa+s-(1+hL)t-rho,

where `h=q-1`, `t=B/h`, `s=Y/q^3`, `rho=e/mu^2`, and
`kappa=Kpos/H`. The reviewed weights are `L=V^2` and `L=bV`.
These fractions are used only in the proof; the supplied equation is
an integer polynomial.

## 2. Root extraction over the rationals

Before any transport sign is known, the raw positive inputs imply
`E>1`, `U>=c^2`, `Delta>=3`, `Df>c+1`, `Q>1`, and `M>0`.
Since `b` is integral, either `b=0` and `V=-c`, or
`|V|>=Df-c>1`. Thus `Dy>0` and `delta>0` unconditionally.

The key identity is

    Q=4 Delta^2 U^2 G.

Therefore `delta=-1 mod G` and `Dy=-1 mod G`, so

    gcd(G,delta Dy)=1.

At a zero let `z=Z/M`. The equation reads `delta z^2=G Dy`.
For every prime `p` dividing `G`, the valuations of `delta` and `Dy`
are zero. Hence `v_p(G)=2v_p(z)` is even. This argument remains valid
when `z` is rational: the valuation of a rational square is even.
There is **no assumption that M is coprime to G**. Thus `G` is a
positive integer square.

Since `F0=1 mod E`, its positive factors are coprime. We recover
positive integers `tau,f0` with

    E=tau^2, F0=f0^2, g=tau f0, G=g^2.

Set `y=|z|/g`. This is a positive rational satisfying

    QV^2-(Q-1)y^2=1.                                  (A)

## 3. The rational adjacent-Pell descent is valid

For arbitrary integer `Q>1`, nonzero integer `V`, and positive rational
`y` satisfying (A), put `v=|V|` and write `y=a0/m` in lowest terms.
Clearing denominators and using coprimality gives `m^2 | Q-1`.
For `v>1` the equation implies

    v<y<Qv/(Q-1).

The exact transformation

    v'=(2Q-1)v-2(Q-1)y,
    y'=(2Q-1)y-2Qv

preserves the norm. The first coordinate is integral because
`m | Q-1`. The reduced denominator of `y'` remains `m` because
`2Q-1=1 mod m`, and `a0` is coprime to `m`. The strict inequalities
give `-v<v'<v`. The first coordinate cannot be zero since its norm
would be nonpositive. Taking absolute values therefore permits descent
on the positive integer `v`. At `v=1`, equation (A) gives `y=1`.
The preserved denominator is consequently one. Thus `y` and
`z=epsilon g y` are integers.

There is no assumption of an initial sign for `V` or `z`, and no
unjustified inference that an arbitrary rational Pell coordinate is
integral. The adjacent form of (A) supplies the particular descent.

## 4. Doubling restores the exact inherited strong interface

Define

    I=2U g, f=1+2a.

Then, identically after the extracted root `G=g^2`,

    f^2-Delta I^2
      =1+4aF0-4Delta U^2G=1,
    Q=(Delta I)^2,
    V=f^2[c(T+alpha)-R]-c.

Moreover `I>0` and `c^2 | I`. These are exactly the retained strong
and auxiliary interfaces. The main-index folding argument therefore
applies and yields `c=psi_A(p)` for an odd positive index `p`.
The first norm `E=tau^2` has the same meaning as in the parent.
It excludes its first index and gives the unchanged inequalities

    k>=8V0+4,
    c>kY>=k>8q^5,
    c>X,
    kappa>0.

Using the inherited unconditional bound
`R<q^4+(alpha+2)q^2` now proves `b>c` before any assumption on `B`.
Consequently `V>0`. No square root, rank, or sign has been obtained
from a condition whose interpretation depends on the carrier sign.

## 5. Both transport weights exclude negative B

Write `W=1+hL`. At any zero,

    n=epsilon g y-kappa-s+Wt+rho,
    rho<b/mu^2<V/mu^2.

The latter is only a one-sided inequality; it does not assume `e>=0`.
Since `Q>1`, equation (A) gives `y<3V/2`.

### The existing square L=V^2

Here `Df-1=Delta I^2=4Delta U^2g^2>g`.
The inequality `b>c>=3` gives

    V>(Df-1)b>3g,
    gy<V^2/2.

If the integer `B<=-1`, then `Wt<-L`, and hence

    n< L/2-L+V/mu^2<0,

contradicting the positive input `n`.

### The lower-degree weight L=bV

Since `c>=3`, the folded odd index satisfies `p>=3`. Thus
`c>=psi_A(3)=4Delta+3`, and

    V>(Df-1)c>4Q.

Put `S=Delta I`, so `Q=S^2`. Positive Pell classification in (A)
gives `SV=chi_S(v)` for an odd index `v`. The first two odd choices
produce `V=1` and `V=4Q-3`, both excluded. Hence `v>=5` and

    V>=16Q^2-20Q+5>8Q^2.

Using `Df=1+Delta I^2<2Delta I^2`,

    b=(V+c)/Df>4Delta^3 I^2>4g.

The last inequality follows directly from `I^2=4U^2g^2`.
Consequently `gy<3bV/8<L/2`. The same contradiction proves `B>=0`.
The definition of `B`, with positive `F` and positive multiplier of
`C`, then forces `C>0`.

## 6. The later decoding really has the same prerequisites

The changed root relation is `z=epsilon g y`, rather than a signed
sum of two roots. The later arithmetic arguments only need the
following already recovered facts: `E=tau^2`; the strong norm;
`c^2|I`; the adjacent auxiliary norm; the literal residues
`V=-c mod f` and `V=-R mod c`; and integrality of the carrier `z`.
All have been supplied.

Transport positivity gives the same mask bounds on `R`. The retained
rank argument identifies `p=R`, then proves the needed parity before
cancelling the `mu^2` denominator. The replacement of the center and
transport contributes only integer terms; `1+hL=1 mod h` remains true.
Thus the subsequent first-index congruence, whole-product projection,
remaining denominator cancellations, and fresh unscaled native-source
reconstruction have the same hypotheses. In particular, no composite
modulus unit is newly or silently cancelled.

## 7. Complete witnesses and the absence of a parity obstruction

Start with the retained canonical outer/first/main witnesses of an
arbitrary refutation. They fix `E=tau^2`, `c`, and `A`. Choose a seed
Pell pair `(f0,I0)` at a positive period of the determinant-one Pell
matrix modulo `c^2 tau`. Then `c^2 tau | I0`, and

    i=I0/(c^2 tau)>0,
    U=I0/tau,
    a=Delta I0^2,
    F0=f0^2,
    G=(tau f0)^2.

Doubling the seed pair gives the actual strong pair

    f=2f0^2-1,
    I=2f0I0.

The actual strong index is even. This is permitted: the retained
auxiliary-completeness theorem requires the strong norm and `c|I`,
not an odd strong index or an odd value of `I/c^2`. Its explicit
auxiliary construction supplies `T>0`, `V>0`, and `y>V` for this
fresh doubled pair.

The canonical outer data supply integer `t>=0`, `rho>=0`, `s>0`,
and `kappa>0`. Also `tau>Y>=s`, while
`f0>(A-1)I0>Xc>kappa`; the seed can be enlarged if needed.
Thus `g=tau f0>kappa+s`. Define

    n=gy+(1+hL)t+rho-kappa-s.

It is a strictly positive integer, and the normalized carrier equals
`gy`. This supplies a zero of the new equation for either weight.
The new seed and doubled strong pair are chosen afresh; no arbitrary
pre-existing strong witness is presumed to have the required form.

## 8. Independently derived degree forms

Let `q0=beta J`, `k0=eta+zeta`,
`A0=q0^3 wY`, `U0=i k0^2Y^2`, and
`E0=q0^10 w^2Y^4k0^2`. For the `bV` carrier, the right-hand product
has degree 328 and strictly exceeds the degree-284 left term. Its
leading homogeneous part, with the final subtraction sign, is

    -2^10 q0^156 w^34 Y^78 i^14 k0^44 (q0-F)^2.

In particular the coefficient of
`J^156 w^34 Y^78 i^14 eta^44 F^2` is
`-1024 beta^156`, which is nonzero for the actual positive beta.

For the `V^2` carrier the left term dominates in degree 436, with
leading homogeneous part

    2^14 q0^200 w^46 Y^104 i^20 k0^60
      (q0-F)^4 (q0-F-alpha)^2.

These are degree calculations for the complete polynomial, independent
of any claim that a particular input lies on its zero set.

## 9. Original A D saturation version

The previously materialized 87-operation, degree-436 version has
equation SHA256
`8cdb9f9664861bcaa4db27987c3a33721869dad46157daef9a5fc46e11766f70`.
Its `U=i c^2 A D`, `D=1+Delta c^2` arrangement is also sound:
`Df=1 mod A D`, `delta=-A^2 mod Df`, and `Dy=-D mod Df` imply
`gcd(E Df,delta Dy)=1`. The same rational valuation and adjacent
descent arguments apply. The fresh strong period must then be chosen
modulo `c^2 A D tau`. That version is a checked predecessor, not an
additional assumption needed for the stronger doubling theorem.

## 10. Bounded novelty comparison

The copied `provenance/prior_product11_proof.md`, Sections 1 and 3,
already uses a single product-square equation and prime-factor
coprimality. Its strong ordinate contains the saturation `A(1+Delta c^2)`;
its equation is in eleven unrestricted integers with different fixed
source ports. Product-square extraction and classical Pell doubling are
therefore not new concepts in this corpus.

The concrete distinction reviewed here is to replace the strong trace
by the doubled seed trace *before* eliminating roots. This makes
`Q=4 Delta^2 U^2 G` divisible by the entire tested radicand `G` and removes
the saturation factor while retaining ten positive unknowns and the
parent's whole four-port coefficient tuple. The finite changes give
84/436 and 85/328, against the pinned parent's 89/288. The comparison
supports those particular operation/degree tradeoffs. It is not a
historical priority claim or a general minimality result.

## 11. Final verdict

No unresolved mathematical defect was found in root extraction,
rational adjacent-Pell descent, the doubled strong-pair interface,
transport sign recovery, later denominator inheritance, or positive
completeness. The order of the proof does not presume the decoded
transport sign, main rank or parity while establishing the early bounds.
The doubled even strong index is allowed by the retained auxiliary
completeness interface. These conclusions concern the written arithmetic
reduction and the explicitly retained calibration; finite evaluator
checks do not constitute a new proof-assistant verification of ZFC
consistency equivalence.
