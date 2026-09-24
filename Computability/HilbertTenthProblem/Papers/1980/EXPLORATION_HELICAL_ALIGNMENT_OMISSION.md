# Deleting temporal alignment admits an independent successor row

The two operations enforcing `(B-1)*align=P-1` cannot be deleted from
the complete82 system. The resulting **80=43M+37A** source has32 positive
unknowns and20 equations, but accepts invalid raw inputs. The existing
dummy positions let a non-cell-aligned power P transport an independent
successor row into the genuine state positions. Every local mask,
positive bound, and retained Pell equation can still hold.

This is a counterexample to that precise deletion, with the native
compiler unchanged. It is not an impossibility theorem for different
encodings or different alignment arguments. The published82 proof,
source, and receipt are preserved.

The [checker](../verification/explore_helical_alignment_omission.py)
and [receipt](../verification/explore_helical_alignment_omission.json)
give the exact80 source, finite arithmetic examples, and genuine
initial tableau slabs for nonhalting inputs. The full positive Pell
extension is proved below; enormous complete Pell tuples are not
materialized numerically.

## 1. Exact deletion and native compiler notation

Start with the [complete82 source](FIXED_RAW_UNIVERSAL_82_PROOF.md).
Delete the two instructions `Pm1=P-1` and
`alignment=(B-1)*align`, their equality, and the positive coordinate
align. Nothing else changes. In particular retain

    (B-1)J=q-1, P*v=q,
    C+alpha+u=q, u=d*(x+2),
    (DC+B*DR+DY*P)C=F+z*(q-1),
    C=CS+Z+W,

the full inverse packing, all ten kernel equations, and all four
fixed-base exponent equations. The latter do not use P or Pm1.

Write k for the fixed state alphabet size, m for the population of
the homogeneous clause mask, and

    L=k+m+1, B=R^L=2^d,
    Ccell=sum_(j=0)^(m+1) z_j R^j.

Indices0,...,k-1 are genuine state bits. Indices k,...,m+1 are ignored
dummies. End has index0 and Start index1. The mask on Z permits only
indices2,...,m+1. The local field tests the genuine bits of three
independently typed cells; dummy bits cannot influence the tested
inner-radix block because of the coefficient-mass bound.

## 2. Two typed words with unrelated genuine states

Suppose

    m>=3k-3, k>=2.

Take any cyclic genuine state sequences g_i and h_i of length N,
and put `G_i=R^(g_i)`, `H_i=R^(h_i)`. Define

    s0=2k-1, a0=m-k+2,
    C_i=G_i+R^a0 H_(i+1),
    Y_i=H_i+R^s0 G_i,                               (1)

where all indices are modulo N. Then

    a0>=k, a0+k-1=m+1,
    s0>=k, s0+k-1=3k-2<=m+1.

Thus C_i and Y_i are both legitimate native cells: each has one
genuine state and one dummy bit. The two positions in each cell are
disjoint. The genuine state of Y_i is h_i, independently chosen from
the genuine state g_i of C_i.

Put `q=B^N`, `D=q-1`, pack the two words in radix B, and choose

    P=R^s0.

Since `a0+s0=L`, multiplication gives the exact identity

    P*C-Y=H_0*(q-1).                                 (2)

For clarity, the high dummy band in C_i stores **H_(i+1)**. After
one radix-B carry it arrives in cell i+1, producing H_i in Y_i.
Equation(2) follows by summing

    P*C_i=R^s0 G_i+B H_(i+1).

Both words are in `(0,q-1)`, so Y is exactly `P*C mod(q-1)`.
But `0<s0<L`, hence `1<P<B`, and P is not an integral power of B.
The retained equation P*v=q holds with the positive integer
`v=R^(LN-s0)`.

This failure is not limited to P<B. For any integer b>=0 with b+1<N,
choose `P=B^b R^s0` and instead set

    C_i=G_i+R^a0 H_(i+b+1),
    Y_i=H_i+R^s0 G_(i-b).                             (3)

Then Y is again `P*C mod(q-1)`, with all cells typed. The same mechanism
works above the cell radix; merely restoring the lower bound P>=B
would not supply alignment.

## 3. Local truth with an independent successor plane

Let the fixed ternary relation be T(center,right,next). Suppose

    T(g_i,g_(i-1),h_i)

holds at every i. The genuine right state of the spatially shifted
word `B*C mod(q-1)` is g_(i-1). Equations(1)--(2) make the genuine
state of the temporal word h_i. Thus the existing scalar compiler,
applied to these three typed cells, gives its exact field mask:

    F=DC*C+DR*Rword+DY*Y,
    F AND (MF*J)=0, 0<F<q-1.                         (4)

There is no need for the h_i states to be any cyclic permutation
of the g_i states. The occupancy clauses see one genuine bit at each
site and pass. The coefficient-mass bounds prevent off-diagonal and
dummy terms from carrying into the tested block.

A small decisive example uses k=3 and the fixed relation

    T(c,r,y) iff y=End.

Take g_0=Start, g_t=End, all other g_i equal the third state, and
every h_i=End. All local masks pass. No genuine cyclic temporal shift
can satisfy this marked relation: if every next state is End, the
permutation of cell indices forces every current state to be End,
contradicting Start. The checker evaluates these examples for several
lengths and both b=0 and b=1 in (3).

## 4. The actual window compiler has enough dummy positions

The inequality m>=3k-3 is automatic for the current helical tableau
compiler; it is not an extra padding hypothesis.

The alphabet consists of allowed3-by-3 windows. A permitted next
window must have its top two rows equal the current window's bottom
two rows. The fixed Start S3 and End E3 windows have different top
two rows. Therefore, for every pair(center,right), at least one of
the triples with next=S3 and next=E3 is forbidden. The k^2 pairs give
at least k^2 distinct forbidden triples.

Every forbidden triple contributes one distinct mask bit to the
homogeneous compiler. Consequently

    m>=k^2>=3k-3,

the last inequality following from `k^2-3k+3>0`. All compiler constants
are the existing ones. Reordering those forbidden clauses does not
remove this obstruction: the mechanism uses their correct local
truth table on fully typed cells, not any particular coefficient order.

## 5. A valid initial slab exists even for nonhalting inputs

Fix any normalized unary machine used by the82 construction and any
raw x>0, with `t=x+2`. Choose a sufficiently wide spatial strip and
write the following finite slab:

* the horizontal boundary row H;
* the genuine initialized row `L^a I^t Q R^2`;
* the configuration after the forced first transition;
* the configuration after the second transition.

The single vertical boundary column is V at every time. Choose enough
left margin that neither of the first two steps reaches V. The machine
has defined transitions at these steps; q0 and its forced successor q1
are nonhalting. This construction exists irrespective of eventual
halting.

At each spatial position, let g_i be the3-by-3 window centered on the
initial row, and let h_i be the window centered on its successor row.
Number the spatial positions in the reverse direction, so the head is
i=0 and spatial right has index i-1. Both kinds of window are allowed
alphabet symbols: their center rules inspect only the finite slab.
Horizontal and vertical overlaps give

    T(g_i,g_(i-1),h_i)

at every cyclic spatial index. The V seam is valid because V has one
constant symbol and does not compare payloads across the boundary.
There is one Start g_0 and one End g_t, and N>t. No acceptance row is
present in this slab, so eventual halting has not been imposed.

Apply (1) to these g_i,h_i. The resulting packed C word and independent
successor word satisfy every scalar local mask of the actual fixed
tableau compiler. Hence the obstruction applies to that compiler,
not just to an unrelated finite relation.

For a concrete false raw input, use the checker's normalized residue
machine with modulus2 and residue0. It halts exactly when the unary
length x+3 is even, so its raw accepted set is the positive odd integers.
Choose x=2, t=4. Its initial and next rows fit in a strip of width N=10,
with a=2 and right margin2. It never halts on this input, but the
construction above gives an80-source solution after the positive
extension in the next section. The compiler is fixed for that one
machine before the input is selected.

## 6. Every remaining arithmetic witness can be positive

Use the genuine state sequences just constructed and take b=0 in (1).
Set

    q=B^N, P=R^(2k-1), W=B^t,
    C=pack(C_i), Z=C-CS-W,
    J=(q-1)/(B-1), v=q/P, u=d*t.

The unique genuine Start and End bits occur exactly at0 and t. Removing
them leaves positive ordinary cells and dummy bits. Every remaining
bit is in an allowed Z position, so

    0<Z<C<q, Z AND (MC*J)=0, Z even.

Equation(4) supplies the positive field. The spatial wrap quotient
`kR=(B*C-Rword)/(q-1)` is positive. Equation(2) gives the temporal
quotient `kY=H_0>0`, so

    z=DR*kR+DY*kY>0.

All native cells remain bounded by B-2. Thus

    q-C>=J+1, J>=B^(N-1)>=B^t=2^u>u,

and `alpha=q-C-u` is positive. These choices satisfy all remaining
outer equations except the packed-index equation, which defines r:

    Lambda=q^2, D0=q^3,
    Scode=Z+qF, Mcode=(MC+q*MF)J,
    r=(Lambda-Scode)*(Lambda-1)+Mcode.

The two vanishing masks give

    popcount(r)=3dN, D0 divides binom(2r,r).

The strict bounds give `q^2<=r<q^4`, and r is odd because Z and qF
are even while MC and J are odd. These are the full hypotheses of
the fresh positive fixed-minus43 kernel extension. That extension
does not use P alignment and supplies all seventeen kernel coordinates
at this actual r,D0.

Finally the fixed-base15 bridge also does not use P. At the actual
kernel parameter choose

    kappa=psi_(a+2)(u), mu=chi_(a+2)(u),
    delta=(kappa-u)/(a+1), phi=c-kappa,
    rho=(mu-a*kappa-W)/(4a+3).

The established bridge inequalities, u>=12 and `W=2^u<q`, make all
five quantities positive integers. All20 equations of the deleted
source now hold, with all32 existential coordinates positive.

Therefore the precise80 deletion accepts every positive raw input
for the fixed normalized tableau machine. In particular it falsely
accepts x=2 for the positive-odd-integer machine above.

## 7. Executable evidence and scope

The checker symbolically verifies all80 instructions and20 residuals,
including the shifted index of the retained auxiliary-norm correction.
It evaluates26 finite arithmetic constructions, including independently
varying successor states and shifts P>B, and checks every remaining
outer equality, strict positive coordinate, mask, parity, and exact
population threshold. Separate initial-slab checks include genuinely
nonhalting inputs of fixed residue machines and confirm the actual
window overlaps and uniform Start/End markers.

The full window alphabet and its enormous compiler constants are not
numerically enumerated for the machine counterexample. The bound
m>=k^2 and the explicit formulas above prove the construction for that fixed
effective compiler. The numerical finite-relation examples exercise
the same compiler and arithmetic mechanism at manageable sizes.
The mathematical positive converse supplies the complete kernel and
input-bridge witnesses; no giant packed Pell tuple is claimed to have
been materialized.
