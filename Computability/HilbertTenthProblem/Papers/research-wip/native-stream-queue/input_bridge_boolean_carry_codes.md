# A computation and identity-return code for the hidden Boolean carry

The later [polynomial collapse theorem](native_controller_boolean_carry_polynomial_obstruction.md) rules out a universal compiler using only this hidden filter, a fixed polynomial input and affine external control with empty queues. The component and code identities below remain valid.

The [hidden-carry paired filter](native_controller_boolean_carry70.md)
admits an exact three-cell, two-phase code. Its computation phase allows
every logical read/write pair; its return phase enforces the identity.
This is a concrete local interface, not a universal compiler. A selected
code alphabet, phase control, ordinary-input loading and final emptying
are not consequences of the paid filter alone.

The existing bare64 and external-controller70 sources keep their stated
counts. No arithmetic cost for imposing the code below is claimed. In
particular the existing two-operation square alignment only forces even
exponents; it does not align these three-cell blocks. The established
complete universal bound remains76.

## 1. The exact three-cell interface

Write a physical word as its two Boolean ternary rail integers. Define

| Logical value | Ordinary code A | Temporary code B |
|---:|---|---|
|0|(1,13)|(1,10)|
|1|(4,10)|(4,4)|

All words have three cells, written low-first. The hidden recurrence is

    3e_next=e+2a0+a1+d0+d1-2, e in{0,1}.               (1)

For arbitrary Boolean read rails D0,D1 and append rails A0,A1 of length
ell, put Q=3^ell. Its exact block equation is

    Q*e_out=e_in+2A0+A1+D0+D1-(Q-1).                 (2)

Divisibility of the full numerator gives divisibility at every shorter
prefix. Starting at a hidden bit, each integral microscopic quotient
remains a hidden bit, by the interval argument in the source proof.
Thus(2), including the endpoint bit, is equivalent to the full local path.

Both ordinary codes have read sum14. Both temporary codes have weighted
append value `2A0+A1=12`. Since14+12=26, **every A_i->B_j** has a path
from hidden0 to hidden0. Its internal states are `0,1,j,0`.

Let p0=1 and p1=4 be their first-rail integers. A return B_i->A_j has
right side `e_in+p_j-p_i` in(2). Because the difference belongs to
{0,3,-3}, the only possible hidden endpoints are0->0 with i=j.
The identity return has internal states `0,1,i,0`. Entry hidden1 is
impossible for either kind of coded block. These endpoint conclusions
are proved consequences of the physical codewords, not extra assumptions.

Thus a queue consisting of ordinary codewords can make a sweep choosing
any temporary logical output word, followed by an identity recoding
sweep. The statement only concerns the hidden filter. An additional
external controller can restrict either sweep.

For this two-phase template with hidden boundary0, three cells are
minimal. Indeed all four computation pairs force common read sum R and
common weighted append value V, with R+V=Q-1. Write an ordinary code as
(p,R-p). Its matching identity-return code must be `(p,V-2p)`, obtained
by substituting the return equation. Exhausting the Boolean rails for
ell=1,2 gives no two distinct such pairs; at ell=3 the displayed pair
is the unique two-symbol family, up to exchanging its logical labels.
The checker records this finite minimality claim separately from the
general identities. It does not exclude other boundary states or other
phase protocols.

## 2. Arbitrarily large finite alphabets by concatenation

For n>=1 let

    Q=27^n, J=(Q-1)/26, R=14J, V=12J,
    p(b)=J+3*sum_(i=0)^(n-1) b_i*27^i, b_i in{0,1}.

Define `A_b=(p(b),R-p(b))` and `B_b=(p(b),V-2p(b))`.
These are concatenations of the three-cell words above, so all rails
are positive Boolean ternary words. All 2^n symbols are distinct.

For every b,c, A_b->B_c satisfies(2) with hidden endpoints0. For the
return, (2) reduces to `Q*e_out=e_in+p(c)-p(b)`. The difference is a
multiple of3 of magnitude at most3J<Q-1. If e_in=1, its residue modulo3
excludes divisibility by Q. If e_in=0, only the zero difference can be
a multiple of Q, forcing b=c and e_out=0. This proves the exact complete
computation relation and exact identity-return relation for every n.

This construction uses all binary strings of a chosen length as symbols.
It does not supply a mechanism that excludes uncoded physical words.

## 3. Exact external-carry constraints and the recoder restriction

Use the external controller

    3c_next=c+h+u0*d0+u1*d1+v0*a0+v1*a1.             (3)

For a three-cell block the additive constant is13h. A computation
A_i->B_j has increment

    b_compute(i,j)=13h+14u1+12v1
                    +(u0-u1)p_i+(v0-2v1)p_j.          (4)

An identity return B_i->A_i has increment

    b_return(i)=13h+12u1+14v1
                   +(u0-2u1+v0-v1)p_i.              (5)

The exact macro recurrence is `27c_next=c+b`. Integral macro endpoints
are equivalent to integral microscopic carries; no chosen finite subgraph
is imposed. The hidden endpoints and paths remain those in Section1.

Suppose the identity-return phase must handle **every finite binary
word** with a uniform bound on external carry magnitudes. This is a
substantive requirement, not automatic from the code. It forces

    u0-2u1+v0-v1=0.                                  (6)

To prove it, a block with fixed increment b satisfies
`27z_next=z`, where `z=26c-b`. With |c|<=C, choose L so that
`27^L>26C+max(|b_return(0)|,|b_return(1)|)`. An integral path through
L copies of a symbol forces its entry and exit carry to be exactly b/26.
Apply this to the return word `0^L1^L`: the shared middle carry makes
the two increments equal. Their difference is three times the left
side of(6). It also follows that the common fixed carry is integral.
Fixed controller data in a whole positive-source path provide the needed
uniform carry bound, independently of queue width.

If one additionally requires the identity-computation words
A_i->B_i to handle every finite binary word under such a bound, the
same argument gives

    u0-u1+v0-2v1=0.                                  (7)

Together these imply u1=v1 and u0+v0=3v1. Both phase constants then equal
`13h+26v1`. With `kappa=(13h+26v1)/26`, the centered computation rule is

    27(c_next-kappa)=(c-kappa)+(u0-v1)(p_i-p_j).       (8)

These are necessary conditions for the specified uniform recoding and
identity protocols. They do not prove nonuniversality of the entire
hidden-carry source, annotated alphabets, varying-phase controllers or
protocols that require a smaller word language. In particular condition(7)
is not required by a general computation that lacks arbitrary identity
passes.

## 4. Input and acceptance remain separate obligations

An ordinary-coded physical queue of width m=3N has scalar rail sum

    I0+I1=14*(27^N-1)/26=7*(3^m-1)/13,

independent of its logical payload. Directly equating it to the source's
ordinary input2x therefore admits only `x=7*(27^N-1)/26`; the existential
choice of rail split cannot supply the missing input encoding. A raw-input
loader or a different explicitly paid interface is required.

Every coded word is nonzero on both rails. A final zero queue is outside
both alphabets, so an accepting computation must also leave the coded
protocol. No sound emptying or halting construction is asserted here.

## 5. Evidence

The checker replays microscopic hidden paths for all codeword pairs at
concatenation lengths1 through5, including both possible initial hidden
bits. It checks the finite minimality statement, independently expands
the external macro equations, and tests exact bounded contraction.
The receipt records these domains. There is no claimed complete source
schedule for this interface or a universal simulation. Independent full
proof/source/default review passed, including the scoped minimality and
recoder hypotheses; fresh replay863751 matched the saved receipt.
