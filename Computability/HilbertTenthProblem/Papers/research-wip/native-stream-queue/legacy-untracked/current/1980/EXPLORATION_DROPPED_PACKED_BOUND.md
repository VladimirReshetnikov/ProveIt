# Excluded route: dropping the packed upper bound

This note concerns the proposed deletion of `Y+alpha=q^2` from the
positive-coefficient encoding, without a replacement upper bound. It gives
an exact counterfamily for the retained coding equations and the final
central-binomial divisibility condition. It does not assert that every
member has already been extended to a solution of all auxiliary Pell
equations: such an assertion would additionally require applying their
full necessity construction to these altered coding data.

The family proves that positivity of the computed coefficient and third
block, the packed congruence, and the final binomial divisibility do not
by themselves enforce the intended code range or quadratic equations.

## Fixed data

Fix any admissible 109/108 homogeneous encoding, with its powers of two
`b,B,q=B^L,n=q^8`, `theta=B-Z`, and
`lambda=(q^2-1)/(B-1)`. Take the intended coefficient value `e=e_0(B)`.
Choose any small allowed coordinate values for `C=x+g`, with the encoded
unit coordinate `delta=1`; these need not satisfy the ordinary quadratic
rows. For example the underlying rows may include the unsatisfiable
constant equation 1=0. After homogenization its target is `2delta^2=2`,
so it really does fail when `delta=1`.

Take `b` sufficiently large to bound the chosen coordinate values. The
fixed support and radix margins give

    e<q,    lambda>q,    ZC^2<q,
    Omega=Zlambda-2e>0,
    S_3=(2e-Zlambda)C^2+Blambda(1+q)>0.

For the canonical mask `ell_0=ell_0(B)`, the packed code is

    Y_0=ell_0+eq=V+t_0 theta

with a positive integer `t_0`. Its numerical packing has positive `r_0`
and the ordinary block bounds even if its zero-target tests fail.
Write

    r_0 = [g+q^2(ell_0+eq+q^2S_3)](n^2-n)
          +[q^2(1+theta lambda)-(b-1)ell_0
                           +(B-4)ell_0 q^4](n^2-1).

The coefficient of `ell` in this formula is the strictly positive integer

    K_r = q^2(n^2-n)
          +[(B-4)q^4-(b-1)](n^2-1).

All quantities in this paragraph are now fixed.

## Exact unbounded family

Choose a positive integer `A` such that

    P=theta*A*K_r > r_0,
    D=P-r_0 >0.

For every positive integer `M` with `2^M>D`, put

    ell_M=ell_0+theta*A*(2^M-1),
    t_M=t_0+A*(2^M-1).

Then the packed congruence is preserved exactly:

    ell_M+eq=V+t_M theta.

The positive coefficient `Omega`, the positive `S_3`, and all retained
geometric and power equations are unchanged. The value computed for `r`
is exactly

    r_M=r_0+K_r(ell_M-ell_0)=P*2^M-D.

Both `ell_M` and `r_M` grow without bound. The deleted upper bound fails
for every sufficiently large `M`.

## The binomial filter eventually passes

Let `s_2(v)` denote the binary digit sum of the nonnegative integer `v`.
The two parts in

    r_M=(P-1)2^M+(2^M-D)

have disjoint binary supports, and the low part is the `M`-bit complement
of `D-1`. Therefore

    s_2(r_M)=s_2(P-1)+M-s_2(D-1).

This identity is exact, and its right-hand side grows linearly with `M`.
The elementary factorial-valuation identity gives

    v_2(binomial(2r_M,r_M))=s_2(r_M).

As `n` is a power of two, the desired condition
`n^2 | binomial(2r_M,r_M)` holds whenever

    M >= 2log_2(n)+s_2(D-1)-s_2(P-1).

Thus arbitrarily large members of the family pass the central-binomial
divisibility filter while retaining the same failed quadratic target.
The bounded-block proof previously gave
`s_2(r)=2log_2(n)-tau_2(S,T)`, which makes that divisibility force zero
carry. Once the packed upper bound is removed, the hypotheses for that
identity disappear, and large high blocks create enough binary ones to
pass the divisibility test for unrelated reasons.

## Scope of the exclusion

This is a complete counterexample to deriving the missing packed bound
or the quadratic target tests from the remaining coding equations plus
central-binomial divisibility. The note deliberately makes no stronger
claim about a fully instantiated false positive for every auxiliary
Pell equation. Any proposed replacement must supply a new range
argument or explain which other constraint rejects this explicit family.
