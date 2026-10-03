# Independent mathematical review of retained-a,c asymmetric scales

**Provisional status: mathematics only; no emitted-source audit yet.** The
bootstrap below passes independent challenge. It supports changing
`X=w*q^3` to `X=w*q` while retaining `Y=s*q^3`, all raw gap equations,
positive supplied coordinates, and the existing fixed compiler hypotheses.
It also supports the proposed unit groupings. It does not authenticate a new
emitted circuit, operation ledger, formal degree, public API, or receipt.

Relative links below assume this note is placed beside the research-wip
compiler notes. The mathematical inputs read for this review are:

|Proof source|SHA256|
|---|---|
|[Relaxed auxiliary rank](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)|`9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90`|
|[Half-parameter auxiliary identities](../../1980/HALF_PARAMETER_PELL_92_PROOF.md)|`c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b`|
|[Fixed-minus congruences and step-down](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)|`47a2c5b69f3c87b7a1ddc61ef84757023de291b63d1330e2c8dc9b40e811ab8b`|
|[Half-binomial kernel](pell_kernel_half_binomial42.md)|`0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992`|
|[Actual weak raw packing bounds](complete75_signed_projection_elimination101.md)|`55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d`|

Only the applicable generic rank, polynomial congruence, step-down, and lower
ratio lemmas are used before restoring the old scale. The old whole native
kernel theorem is not invoked with an unverified scale hypothesis.

## 1. Unit restoration and its exact domain

Put `H=4a+3`, `A=a+2`, `Delta=A^2-1=a^2+H`, and `t=i*c^2`. The four
candidate factors are

    N0=g^2+L*(2g-k),       L=X*Y^2*k,
    Nm=d^2-Delta*c^2,
    Ni=mu^2-Delta*kappa^2,
    Na=t^2*(U^2-y^2)+y^2.

For every integer a, Delta is0 or3 modulo4. Each of Nm and Ni is therefore
either a square or a sum of two squares modulo4, and cannot equal−1. Also
`t^2` is0 or1 modulo4, so Na is respectively `y^2` or `U^2` modulo4.
Thus Na cannot equal−1, without using the strong equation or any typing.

Consequently grouping Nm*Ni, or Nm*Ni*Na, into a product required to equal1
restores every grouped factor to+1 on **all integer tuples**. In the proposed
two-pair arrangement, `N0*Nm=1` first forces Nm=+1 by its own modular
protection and hence N0=+1. Likewise `Ni*Na=1` forces both to+1. Thus this
two-pair grouping also preserves the entire integer zero set of its ungrouped
asymmetric polynomial. It needs no independent sign theorem for N0. This is
separate from the positive-domain scale change proved below.

For completeness, N0 also independently excludes−1 on the actual positive
cone. Let `V=XY^2>1`, `D=V(V+1)`, `T=L+g`; then

    N0=T^2-D*k^2.

If this were−1, put `P=2V+1`, `k'=Pk-2T`, and `T'=PT-2Dk`.
Because `P^2=4D+1`, one has `Pk>2T` and hence k'>0. Since
`T^2-V^2*k^2=V*k^2-1>0`, T>Vk and k'<k. The transformed pair still has
norm−1, and |T'|>0. Choosing a solution with least positive k gives a
contradiction. This optional descent requires V>1; it is not an unrestricted
signed-domain claim. V=1 admits the familiar negative norm solution. The
actual positive source has q>=16, X>=q, Y>=q^3, so V>1 before equations.

## 2. Actual raw packing, including the weak boundary

At a positive zero, first restore all grouped unit equations as above, if
applicable. Restore the six positive graph coordinates and the first root
`tau=L+g` as in the [selected113 parent](complete74_gap_selective_projection113.md).
These are positive definitions on the new grid too. Their algebraic
restoration does not require the old q^3 scale for X.

Let B be the fixed dyadic base, q=(B−1)J+1, and let MF0 denote the unshifted
mask, so the actual fixed port MF is MF0+B−1. The retained mask hypotheses
include `0<MC,MF0<B−1`, `MF0>=4`, B>=16, and J>0. Write

    S'=Z+qF-1,
    TC=MC*J+1, TF=MF0*J-1, T'=TC+q*TF,
    R=(q^2-S')*(q^2-1)+T'.

Then `0<TC<q`, `3<=TF<q-2`, and `3q+1<=T'<q^2-1`.
Since R is supplied positive, S'>q^2 would make R negative. Since F,Z are
positive, S'>=q. Therefore

    q>=16,  q<=S'<=q^2,  3q+1<=R<q^4.

The allowed endpoint S'=q^2 is not discarded: it can correspond to the
untyped value `q^2-Z-qF=-1`. In particular, this proof does **not** import
`F+Z<q` or the stronger R bounds from the different normalized87 source.
The new scales give `X>=q`, `Y>=q^3`, `E=XY>=q^4>R`.

## 3. Rank recovery before power decoding

The restored first norm is
`tau^2-V(V+1)k^2=1`, where V=XY^2. Its fundamental positive unit has
coordinates `(2V+1,2)`. Thus, for some n>=1,

    k=2*psi_P(n), P=2XY^2+1.

As P=1 modulo E and the retained index equation is `k=R+1+hE`,

    2n=R+1+vE, v>=0.

Here `0<R+1<=E`. The boundary R+1=E is allowed: v<0 would give2n<=0,
so nonnegativity of v still follows. In particular n>=25.

The retained main norm gives `c=psi_A(p), d=chi_A(p)`. The retained equations
force `a=Y(X+1)` and `kY<c<k(Y+1)`. Since P>A and c>k, Pell monotonicity
gives p>n. Hence elementary growth gives `c>A*Delta^2` and c>2p, while
`c>kY>Y(R+1)>2R` independently bounds the target index.

These are precisely the independently available hypotheses of the relaxed
ordinary strong-rank lemma. Applying it to

    (i*c^2)^2=Delta*(f^2-1)

gives `f=chi_A(m)`, p|m, c|m, m>=c>2p, and
`t=i*c^2=Delta*psi_A(m)`. It does not assume that X is a power, that q is
typed, or that p=R. Since m>2p, f>2c, and `U=of-c>0`.

The retained auxiliary norm is `(tU)^2-(t^2-1)y^2=1`. It has an odd positive
Pell index ell. The odd-index polynomial identities give

    U=(-1)^((ell-1)/2)*psi_A(ell) modulo f,
    U=(-1)^((ell-1)/2)*ell       modulo c.

Together with `U=-c mod f`, squaring and doubling imply
`chi_A(2ell)=chi_A(2p) mod f`. The strict range m>2p makes the usual
nearest-multiple step-down valid. Explicitly, reduction to
`0<=r<=m/2` gives a signed `chi_A(2r)`; the endpoint2r=m is zero modulo f
and impossible, and otherwise both compared positive values are at most
`chi_A(m-1)<f/3`. The negative representative is impossible and equality
forces r=p. Hence ell=±p modulo m, and therefore modulo c. Combining with
`U=-R mod c` gives R=±p modulo c. Since `0<R,p<c/2`, this forces p=R.

If v>=1 in the first-index relation, then
`2n>=R+1+E>=2R+2`, contrary to n<p=R. Thus `2n=R+1`. This step uses only
E>R, not the unavailable stronger E>2R.

## 4. Lower ratio, exact power, and only then inheritance

Set r0=(R−1)/2>=1 and `xi=(X+1)^(2r0)/X^r0`. The elementary lower Pell
ratio estimate gives

    c/(k/2) >= xi*(1+3/(2a))^(2r0)
                   *(1+1/(2XY^2))^(-r0) > xi.

The strict inequality uses only `6XY^2>a`, valid here. It does not use an
upper approximation error, population decoding, or X>=q^3. The retained
upper ratio yields

    Y>xi/2-1>X^r0/2-1>X^r0/3,
    a>X^(r0+1)/3>2^(2r0+1)=2^R.

These estimates already hold for X>=16 and r0>=1. Also X<a. The recurrence
of `chi_A(j)-a*psi_A(j)`, whose first values are1 and2, gives2^j modulo
H=4a+3. The retained main-root projection therefore gives `X=2^R mod H`.
Both representatives lie strictly between0 and a<H, so X=2^R exactly.

Now q|X forces q=2^ell0, with ell0>=4. Since R>=3q+1>3ell0,
q^3 divides X. Therefore

    w_old=X/q^3=w_new/q^2

is a positive integer. Every other supplied coordinate is unchanged. Only
at this point does the rational all-register substitution become a positive
integer restoration of the frozen symmetric parent. Its full ordinary-input
universal theorem, masks, and input decoding may now be invoked. Conversely,
`w_new=q^2*w_old` takes every positive parent zero to a positive new zero.
The maps are inverse on these positive zero sets.

This scale inverse is not defined as an integer map on arbitrary signed or
positive off-zero tuples. Unit grouping may preserve all integer zero tuples
within one scale, while the asserted comparison between scales remains a
positive-zero bijection. Those two scopes must stay distinct in the new
source metadata and proof.

No new finite test suite or emitted-source claim accompanies this note.
Operation counts, exact degrees, source privacy, and all guarded interfaces
remain obligations of the separate authenticated source review.
