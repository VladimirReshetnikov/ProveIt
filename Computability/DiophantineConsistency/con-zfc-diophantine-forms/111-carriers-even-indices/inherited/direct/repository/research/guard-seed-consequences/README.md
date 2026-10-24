# Five more guard signs follow from original rows

This packet proves five universal sign consequences of the original
1259-coordinate equations, before any Pell or power interpretation.
It does not yet materialize a new complete quartic. Its input is the
frozen107-guard mixed988 packet. Its remaining102 guards suffice to
recover all107 old guarded signs.

| Raw coordinate | Contracted coordinate | Removed guard role | Proved bound |
|---:|---:|---|---:|
| 32 | 29 | endpoint.ut | >=1 |
| 87 | 66 | factorial0.output | >=0 |
| 107 | 77 | factorial1.output | >=0 |
| 130 | 91 | moduli_product.quotient | >=0 |
| 517 | 218 | crt.nonnegative_quotient | >=0 |

The coordinate correspondences use complete metadata equality, checked
against every retained raw coordinate. All other102 guard roles are
unchanged. In particular, endpoint.u0, both factorial power outputs V,
the factorial remainders/slacks, t0 and base0.T remain guarded.

The unbounded proof below is accompanied by `CERTIFICATE.json`: four
initial bound certificates,975 sequential exact sign-row inferences and
five polynomial ideal certificates containing47 original-row terms.
`check.py` imports no producer. It independently collects all polynomial
identities and verifies every sign dependency in order. Neither numerical
sampling nor a semantic assertion that a free variable is a power occurs
in this proof.

## A generic integer lower-bound rule

Suppose the original rows imply `x*F=G`. Suppose earlier established
signs and integer lower bounds imply

    F>0,  G-(L-1)*F>0.

For an integer x<=L-1, the first inequality gives
`x*F<= (L-1)*F<G`, a contradiction. Hence x>=L. Here L is0 or1.
The checker shifts each earlier lower bound to a new nonnegative
variable. It verifies that the two polynomials have positive
coefficients and a positive constant, and that each odd-power operand
is already nonnegative. Even powers need no sign premise.

First apply the unchanged four preliminary certificates from mixed988:
t>=1, n>=2, A>=2 and D>=2. They require only the retained t0/T guards.
Then apply the following five stages, in the displayed order. Every
intermediate sign inference is an actual row `c*x=P`, c>0, with either
nonnegative coefficients and previously nonnegative odd operands or an
explicitly verified affine square. A sign is never assumed because a
variable is described as a power output or a gate.

## 1. Both factorial outputs

For either factorial block, write f for its output, C for its binomial
input, V for its power-output input, r for its remainder and s for its
slack. The exact ceiling and remainder rows, with their defining gates
substituted locally, give

    E = C+V-f*C-r-1 =0,
    H = C-r-s-1 =0.

The factor and numerator for the new bound are

    F=r+s+1,
    G=V+s.

The complete ideal identity is `f*F-G = -E+(1-f)*H`. Since r,s,V>=0
are retained guards, F>0 and G+F=V+r+2s+1>0. The integer rule with L=0
therefore gives f>=0. In fact G>=0 already gives the result directly.

The first block uses raw(f,C,V,r,s)=(87,91,93,94,95), with semantic
rows82/85. The second uses(107,111,113,114,115), rows97/100. All defining
row multipliers are stored explicitly in the certificate.

The fact that other defining gates use f does not create a cycle. No
sign or combinatorial meaning of C is assumed: H itself proves C>0.
The independently guarded V input is not interpreted as a power. Both
factorial output signs are proved before they are used in later stages.

## 2. The moduli-product quotient

Let q=raw130, d=raw126, R=raw129 and s=raw131. Put

    N=raw123*raw106*raw107,
    M=1+raw87*(raw59+1).

The actual product division, remainder bound and canonical-index rows
give, after substituting their defining gates,

    E=N-R-d*q=0,
    H=d-R-s-1=0,
    K=M-R=0.

Choose F=M+s+1 and G=N-M. The exact ideal identity is

    q*F-G = -E-q*H+(q+1)*K.

All operands in N are nonnegative: raw123 and106 remain guarded, and
raw107 was proved in the previous stage. Raw59 and s remain guarded,
and raw87 was proved in stage1. Thus F>=2 and
`G+F=N+s+1>0`. The integer rule gives q>=0. This proof uses no meaning
of N as a product of powers or factorials.

The leading semantic rows are109,112 and117; the full twelve-row ideal
combination includes their actual gate definitions. In particular, it
does not silently equate d to a semantically intended modulus.

## 3. The CRT evaluation quotient

Let q=raw517 and F0=raw516. The actual row496 and its product gate give

    E=F0-R*q=0.

Together with the same K=M-R above,

    q*M-F0 = -E+q*K.

M=1+raw87*(raw59+1)>=1. The sequential original-row ledger proves
F0>=0 before this division. In particular, its final steps use the
**defining** rows

    raw515=raw505+raw510,
    raw516=raw515+raw514,

where raw505 is a sign-certified product and raw510/raw514 are exact
affine squares. The old greedy sign ledger had instead selected the
equality through the guarded quotient. Reusing that dependency would
be circular; the fresh certificate deliberately supplies the independent
defining-row proof. The checker verifies every required upstream product
and square identity. M>0 and F0>=0 imply q>=0, also certified by the
integer rule since F0+M>0.

## 4. The last endpoint quotient

Retain u=raw30(endpoint.u0), m=raw3(M0), r=raw31(endpoint.r0) and t0.
All are guarded nonnegative. Write n=raw5>=2, y=raw2, x=raw1 and
q=raw32(endpoint.ut). The three exact endpoint rows give

    E=x-m-2-u*(y+1)=0,
    H=y-m-r-2=0,
    L=x-1-q*(y*n+1)=0.

Put Y=m+r+2, F=Y*n+1 and G=m+1+u*(Y+1). Then

    q*F-G = E-L+(u-q*n)*H.

F>0 and G>=1 follow solely from the retained guards and n>=2. The
integer rule with L=1 gives q>=1. Thus its former nonnegativity guard
is redundant. This argument retains the first endpoint quotient u;
it does **not** license removing both endpoint quotient guards.

## Consequence and exact scope

These five arguments use102 guarded values, four preliminary bounds
and975 original-row sign inferences. All107 formerly guarded values
are then nonnegative, with no cyclic premise. Restoring the592 raw
affine wires and checking all1177 raw row identities is inherited from
the sealed mixed988 packet.

Consequently, a zero with only these102 guards can be extended to a
literal mixed988 zero by choosing15 fresh Legendre guard witnesses.
Conversely any mixed988 zero restricts by forgetting exactly those five
triples. The frozen mixed988/994 existence theorem then applies. This
is an ordinary proof of an equation-level existence equivalence; it
does not claim pointwise naturalness of every source coordinate.

Keeping the same667 body coordinates, the102-guard specification would
have973 integer unknowns and687 quadratic rows. The new whole coefficient
files and their optimized projections have **not** been materialized by
this research packet. In particular, no projected685-variable frontier
point is asserted here. No frozen candidate, page, common document or
Lean file is changed.

Other audited boundaries remain open. Dropping a range-division quotient
guard also loses the immediate sign of its free power-output numerator;
invoking the numerator's intended power meaning at that point would
require a new bootstrap proof. A sign reflection of a main Pell root
changes the actual power congruences. The U and bootstrap-Z sign orbits
look simpler, but need separate complete original-row symmetry and
guard-domain certificates before any extra reduction is claimed.

## Reproduction

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/research/guard-seed-consequences/generate.py --check
python3 -B Computability/DiophantineConsistency/research/guard-seed-consequences/check.py
python3 -B -O Computability/DiophantineConsistency/research/guard-seed-consequences/generate.py --check
python3 -B -O Computability/DiophantineConsistency/research/guard-seed-consequences/check.py
```

The normal and optimized receipts include rejection controls for every
new original-row identity, a preceding sign row, missing prerequisites,
coordinate identity, stage order and an assumed deleted sign. No H10
emitter, old array generator or Lean command is invoked.
