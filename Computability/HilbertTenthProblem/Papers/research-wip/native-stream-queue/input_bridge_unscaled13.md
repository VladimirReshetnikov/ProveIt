# A conditional 13-operation bridge at the unscaled input index

Replacing the established bridge's index `u=2d*x+b` by the ordinary input
`u=x`, and its index modulus by `a+1`, gives an exact **13=6M+7A**
conditional arithmetic module. Under the interface below, its positive
existential projection is precisely `W=2^x` **and `x>=2`**. It has no
positive solution at `x=1`. Moreover, the existing disjoint End-marker
architecture cannot accommodate every input phase by reserving finitely
many fixed End positions while retaining a nonzero remainder word.

These are two separate, proved limitations of this particular proposal.
There is no full 75-operation compiler here, and the established complete
bound remains [76](../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md). The
[checker](input_bridge_unscaled13.py) and
[receipt](input_bridge_unscaled13.json) preserve the exact source and
finite checks. The author audit and two independent mathematical reviews
pass. A separate root source review and fresh default replay also pass;
the saved receipt matches. No formalization is claimed.

## Conditional interface and exact projection

For an integer `A>=2`, write

    chi_A(v)+psi_A(v)*sqrt(A^2-1)
      = (A+sqrt(A^2-1))^v.

Fix strictly positive integers `a,q,J0,C,alpha,x,W` such that

    A=a+2, Delta=A^2-1, H=4a+3, M=a+1,
    c=psi_A(J0),
    C+alpha+x=q,
    0<W<C<q<J0<M,
    2^q<a.                                                (1)

The quantities `Delta`, `H` and `bounded=C+alpha` are registers already
paid by the containing kernel and outer source. In the actual established
kernel, the stronger facts `X=2^J0<a` and `q<J0<a+1` supply the two
size conditions involving `a` in (1). We use only (1) in this note.
Exponentiation in (1) is an interface hypothesis or a proved consequence
of a containing kernel; it is not a free source instruction.

Consider the four additional equations

    kappa=x+delta*M,
    c=kappa+phi,
    mu^2=1+Delta*kappa^2,
    mu=W+a*kappa+rho*H,                                   (2)

where `kappa,delta,phi,mu,rho` must all be strictly positive integers.
Together with the bound equation in (1), these are the five comparisons
implemented by the source below.

**Conditional projection theorem.** For every choice of fixed interface
values satisfying (1), equations (2) have strictly positive witnesses
if and only if `x>=2` and `W=2^x`.

For necessity, the positive Pell classification gives a positive integer
`v` with

    kappa=psi_A(v), mu=chi_A(v).

Strict monotonicity of `psi_A` and `c=kappa+phi` imply
`v<J0<M`. Reduction of its recurrence modulo `M=A-1` gives

    psi_A(v)=v modulo M:                                 (3)

the initial values are 0 and 1, and `psi_A(v+1)=2A*psi_A(v)-psi_A(v-1)`
reduces to the recurrence for the integers. Thus the first equation in
(2) gives `v=x modulo M`. The bound in (1) gives `0<x<q<M`, so `v=x`.
This argument covers both index parities; no parity restriction on the
ordinary input is made.

Similarly,

    chi_A(v)-a*psi_A(v)=2^v modulo H.                       (4)

For an elementary verification, the left side has initial values 1 and 2
and obeys the Pell recurrence. The sequence `2^v` obeys the same recurrence
modulo `H=4A-5` because `2^2-2A*2+1=-H`. The last equation in (2) now gives
`W=2^x modulo H`. Both values lie strictly between 0 and `H`:

    W<q<H,             2^x<2^q<a<H.

Consequently `W=2^x` as an integer. If `x=1`, however, `v=1` gives
`kappa=1`, and the first equation in (2) becomes

    1=1+delta*(a+1),

which contradicts `delta>0`. Equivalently, its residual is exactly
`-delta*(a+1)`. With the forced `W=2`, the last equation also gives
`rho=0`, since `mu=A=a+2` and `kappa=1`. The failure is therefore an
actual positive-domain obstruction, independently of compiler phases.

For sufficiency assume `x>=2` and `W=2^x`, and set

    kappa=psi_A(x), mu=chi_A(x),
    delta=(psi_A(x)-x)/M,
    phi=psi_A(J0)-psi_A(x),
    rho=(chi_A(x)-a*psi_A(x)-W)/H.                         (5)

Congruences (3)--(4) give integer quotients. Since `x>=2`, strict growth
gives `psi_A(x)>x`, hence `delta>0`; and `x<q<J0` gives `phi>0`.
Finally, writing `psi_A(0)=0`,

    chi_A(x)-a*psi_A(x)
      =2*psi_A(x)-psi_A(x-1)
      >psi_A(x)>=psi_A(2)=2A>W.

The last inequality follows from `W=2^x<a`. Thus `rho>0`, proving the
positive converse with explicit witness formulas and bounds.

## Exact source ledger

The source consumes the borrowed paid registers stated above; charging
their production again would describe a different module boundary.
Each row below is one binary arithmetic operation. All equality
comparisons are free.

| Register | Instruction | Cost |
|---|---|---|
| modulus | `a+1` | A |
| raw_bound | `bounded+x` | A |
| index_product | `delta*modulus` | M |
| index_rhs | `x+index_product` | A |
| gap | `kappa+phi` | A |
| kappa2 | `kappa*kappa` | M |
| scaled_kappa2 | `Delta*kappa2` | M |
| norm_rhs | `scaled_kappa2+1` | A |
| mu2 | `mu*mu` | M |
| modulus_multiple | `rho*H` | M |
| difference_multiple | `a*kappa` | M |
| exponent_partial | `W+difference_multiple` | A |
| exponent_rhs | `exponent_partial+modulus_multiple` | A |

The five comparisons are

    raw_bound=q, kappa=index_rhs, c=gap,
    mu2=norm_rhs, mu=exponent_rhs.

Relative to the established 14-operation bridge, delete the input-scaling
multiplication and offset addition, and add the computation `M=a+1`.
The net saving is one multiplication. The six usual bridge coordinates
remain `W,kappa,mu,delta,phi,rho`; in the conditional statement `W` is
fixed by the containing interface, and the other five are quantified.

The literal source at `u=x` cannot certify all positive ordinary inputs.
Changing the index to `u=x+1` would put its first value at 2 and avoid
this particular zero-quotient failure, but computing that index adds an
addition to this schedule. It also changes the endpoint to `W=2^(x+1)`
and leaves the phase problem below. No free finite-exception repair or
unpaid shift of the input is claimed.

## Capacity of fixed disjoint End variants

The established compiler uses `B=2^d` and a fixed cell origin, and obtains
its unique End selector by `C=Z+W`: a periodic mask forbids End in `Z`,
then the single-bit power `W` inserts it. Its actual endpoint is
`W=2^(2d*x+b)`, at one fixed inner-cell phase `b`. The proposed unscaled
power `2^x` visits every inner-cell phase as the ordinary positive input
varies.

Here is a precise obstruction to adding fixed End variants within that
architecture. Fix an arbitrary finite width `d>=1`, a set of End phases
`E` contained in `{0,...,d-1}`, and `q=B^N`, where

    B=2^d, J=(q-1)/(B-1),
    mask_E=J*sum_(j in E) 2^j.

Suppose an End at exponent `x` must have phase `x modulo d` in `E`, and
suppose uniqueness is enforced by the same disjoint insertion rule

    0<Z<q,             Z AND mask_E=0.                    (6)

**Phase capacity lemma.** No such fixed `E` covers every positive input
while allowing a positive remainder `Z`.

Indeed, every residue modulo `d` occurs among positive integers
(and among integers `x>=2`), so covering all inputs forces
`E={0,...,d-1}`. Its cell mask is then `B-1`, hence `mask_E=q-1`.
For every integer `0<Z<q`, one has `Z AND(q-1)=Z>0`, contradicting (6).
If `E` is proper, choose a missing phase `j`; the infinitely many inputs
`x=j+kd>0` have no permitted End phase. Enlarging the fixed cell width
does not change this argument.

This lemma concerns only a periodic forbidden mask and disjoint
single-bit End insertion in one fixed cell field. It is not a lower
bound for arbitrary computation compilers. A construction with a
different global marker invariant, phase-dependent interpretation,
overlapping controls, a paid conversion, or a different encoding would
need a new soundness/completeness proof. The existing proof cannot obtain
an arbitrary phase merely by moving its cell origin: the origin Start
selector is fixed at binary bit zero and recovered from oddness of `Z`.
No impossibility theorem about redesigned origin encodings is asserted.

## Evidence and reproduction

Run with the repository's pinned environment:

    python input_bridge_unscaled13.py

The checker symbolically compares all five schedule residuals with the
displayed source equations, verifies the 13-operation ledger, and checks
the exact `x=1` index residual. It tests 12 canonical Pell tuples: nine
have positive bridge coordinates at `x>=2`, while the three `x=1` tuples
have `delta=rho=0` and are explicitly rejected by the positive domain.
It additionally checks 300 index congruences and every End-phase subset
for widths 1 through 8: 502 partial sets have a missing input phase, and
the eight full sets give the all-ones forbidden mask at each of three
padding lengths.

The finite Pell fixtures use `a=2^(q+1)` and `J0=q+3`, so they satisfy
`2^q<a` but have `2^J0=4a>a`. They test the weaker conditional interface
(1), not the actual full main-kernel parameter relation. They are neither
full compiler witnesses nor a universal representation check. The
parametric statements in this note are mathematical proofs; symbolic
and finite checks provide separate source and example evidence.
