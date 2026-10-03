# A balanced five-operation controller and a zero-code obstruction

The balanced affine-carry family has a literal **five-operation** controller
identity when coupled to the scalar read and append sums already paid by
[the 63-operation FIFO](native_dualrail_fifo63.md). However, it cannot realize
the three-state Rule110 scan with a fixed all-zero codeword for logical zero
and unbounded ordinary input. This holds for **every fixed block length**:
merely containing the six desired coded edges forces both read coefficients
to have the same strict sign, which bounds every accepting FIFO width.

The conclusion concerns this precise compiler interface. It does not exclude
a different finite controller, a representation with additional logical-state
annotations, a nonzero zero-codeword, or nonzero offset/endpoints. The complete
universal bound remains76.

## 1. The paid balanced identity

Use append fields F0,F1 and read fields F2,F3, where Fi=H+Ti and Q=2H.
The existing computed scalar streams are

    A=F0+F1-Q, D=F2+F3-Q.

Take fixed integer weights

    append=(v+b,b), read=(c-v,c), h=cs=cf=0.             (1)

This is exactly the restriction that append0+read0=append1+read1. The
zero-initial, zero-terminal carry relation telescopes to

    v*(F0-F2)+b*A+c*D=0.                               (2)

Indeed the total four-weight sum is2(b+c), so the usual H correction is
(b+c)Q, which cancels when A,D are substituted. Compute

    delta=F0-F2; rail=v*delta;
    append=b*A; read=(-c)*D; left=rail+append;
    compare left=read.

There are3 multiplications and2 additions/subtractions. Fixed signed
numerals and the comparison are free; the difference register need not be
positive. No new existential coordinate is used. Together with63 this is
an exact **68-operation component**, subject to the FIFO's joint bound and
origin condition. Universality is not a consequence of this count.

## 2. All-length zero-code theorem

Fix a positive block length L and put B=3^L. Encode logical zero by the
all-zero block, and logical one by a fixed scalar ternary word g with
1<=g<B. A Boolean split of that word is (r,g-r), with integer0<=r<=g;
only actual digitwise Boolean splits may be selected. Each macro edge is
L consecutive applications of the carry recurrence with the fixed weights
in(1). Its weighted increment is the corresponding rail-word expression,
and its state multiplier is B.

Assume three distinct carry states implement these six selected edges:

| State | Read | Append | Next |
|---|---:|---:|---|
| A | 0 | 0 | A |
| A | 1 | 1 | Bstate |
| Bstate | 0 | 1 | A |
| Bstate | 1 | 1 | Cstate |
| Cstate | 0 | 1 | A |
| Cstate | 1 | 0 | Cstate |

The first edge forces the carry at A to be0. It is not assumed that these
are the only edges or that paths outside these states are rejected.

If v=0, the append increment for every coded one is the same number b*g.
The Bstate/read0 and Cstate/read0 edges then force the same carry, contrary
to distinctness. Thus v is nonzero. Divide all weights and carry states by
v for the algebraic argument. This is a rational normalization only; no
claim that it preserves the integer carry graph is needed. Write the
normalized weights as append=(b+1,b), read=(c-1,c), and set

    mu=b*g, nu=c*g.

Let rB,rC denote the first append-rail words on the two read0/write1 edges.
Let r2,a2 be the first read/append-rail words on Bstate/read1/write1, and
r3 the first read-rail word on Cstate/read1/write0. Write the normalized
carry values as sB,sC. The four selected edges give

    sB+mu+rB=0, sC+mu+rC=0,
    B*sC=sB+nu-r2+mu+a2,
    (B-1)*sC=nu-r3.                                    (3)

Subtract the last equation from the preceding one, then use the first:

    sC=r3-r2+a2-rB.                                    (4)

Consequently sC is an integer, even though we only normalized rationally.
It is nonzero because Cstate differs from A. From the last equation in(3),

    nu=(B-1)*sC+r3.                                    (5)

If g<B-1, then0<=r3<=g implies either nu>g (when sC>=1) or nu<0
(when sC<=-1). The remaining endpoint g=B-1 has every ternary digit2;
its Boolean split is unique, so rB=rC and the first two equations in(3)
force sB=sC. This endpoint is impossible under the distinctness assumption.

Thus c=nu/g lies strictly outside[0,1]. Both normalized read coefficients
c-1,c have the same strict sign. Multiplying by the original nonzero v
preserves their common strict sign. This proves the theorem for every L,
without any enumeration of coefficient values or bound on intermediate
carry states.

## 3. Why the sign conclusion bounds every accepting input

This consequence applies to the entire Boolean-labelled carry graph,
including arbitrary uncoded paths. Let the two original read weights be
rho0,rho1 with a common strict sign sigma in{1,-1}. Put

    mu0=min(sigma*rho0,sigma*rho1)>0,
    beta=min(sigma*append0,sigma*append1).

For nonnegative native rail streams, the zero-offset, zero-endpoint
controller equation and FIFO transport imply

    0 >= mu0*D+beta*A
      = mu0*I+(mu0*W+beta)*A,                           (6)

where D=I+WA, 0<I<W and A>=0. If A=0 this is impossible. Otherwise
mu0*W+beta must be strictly negative. Hence every accepted run satisfies

    0<I<W<(-beta)/mu0.                                 (7)

When beta>=0 the accepted set is empty. In every case the allowed widths
and ordinary inputs are effectively bounded by fixed controller numerals.
For the63 source I=6x, so the same statement bounds x. This argument needs
no block filter, no assumption about returnable intermediate states, and
no claim about when an uncoded output might be read again.

This strengthens the relevant same-sign special case of the general
[carry-structure analysis](pell_kernel_dualrail_carry_structure.md) for
zero initial and terminal carry. It also explains why allowing escapes
from a chosen three-state subgraph cannot rescue this particular compiler.

## 4. Symbolic and finite evidence

The [checker](native_controller_balanced_rule110.py) verifies the literal
5=3M+2A source and the exact symbolic linear consequence(4). Its additional
finite audit exhausts all rail assignments for every nonzero codeword at
lengths1,2,3 using an exact reduction, not a bounded coefficient search.
After v=1, all nondegenerate assignments determine mu,nu and all states
uniquely. The remaining A/read1 edge becomes one integer compatibility
equality, which the checker enumerates by grouped sums. It reconstructs
and checks all six macro equations for every admitted assignment.

| Block length | Nonzero codewords | Nondegenerate assignments | Primitive coefficient/state vectors |
|---:|---:|---:|---:|
| 1 | 2 | 0 | 0 |
| 2 | 8 | 50 | 24 |
| 3 | 26 | 1,640 | 420 |

Every reconstructed vector has strictly same-sign read weights. The
[saved receipt](native_controller_balanced_rule110.json) includes exact
counts and vector hashes. These finite checks support the implementation;
the proof in Sections2–3 supplies the all-length claim. No full accepted
transducer search or universal impossibility beyond the stated interface
is claimed. Independent full proof, source, and default-replay review passed.
