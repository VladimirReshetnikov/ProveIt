# Wider guards do not make temporal alignment intrinsic

Increasing the cell radix and moving Start to the highest genuine
position do not replace the two temporal-alignment operations. The
dummy-plane counterexample extends to **every inner-digit width
L>=k+m+1**, including L>=2(m+2), and to every ordering of the same
homogeneous clauses. A wider guard can move unwanted successor bits
outside the native state band while leaving them in unchecked parts
of the local field.

Deleting alignment from the published81 system gives the exact
**79=43M+36A** source with32 positive coordinates and20 equations.
With the modified constants proposed here, this source still admits
nonhalting raw inputs. This note concerns the unchanged linear
compiler with one target clause block and the same two packed masks;
it does not exclude other state encodings, additional mask predicates,
or a different arithmetic implementation of alignment.

The [checker](../verification/explore_wide_guard_alignment_omission.py)
and [receipt](../verification/explore_wide_guard_alignment_omission.json)
state the exact79 schedule and check finite arithmetic and tableau
instances. The published81 artifacts are unchanged.

## 1. Modified constants and the missing implication

Retain the homogeneous three-site compiler for a fixed alphabet with
k states. Let c_si be its positive coefficients, mu its fixed clause
mask, and m=popcount(mu). Choose any admissible inner radix R, a power
of two satisfying

    R>=max((m+2)sum c_si,mu)+2.

Choose **any** integer L>=k+m+1 and put

    B=R^L=2^d, p=k-1,
    Ds=sum_(j<k)c_sj R^(p-j), s=C,R,Y,
    MF=mu R^p,
    MC=B-1-sum_(0<=j<=m+1, j not in {0,p}) R^j.

End is state0 with code1. Start is state p, the highest genuine state,
with code CS=R^p. The other genuine positions lie between them. The
native cells still use the m+2 possible positions0,...,m+1; positions
k,...,m+1 are ignored dummies. The low mask allows exactly m positions
after removing End and Start. Thus the two mask populations still sum
to d, MC remains odd, and MF remains even.

A tempting argument assumes both C and `Y=PC mod(q-1)` are native
typed occupied words and then tries to deduce that P is a cell-aligned
power. The source types C but does not independently type Y. It tests
only the target clause block of

    Factual=DC*C+DR*Rword+DY*Y.

The following construction exploits precisely that missing implication.

## 2. An independent successor plane for every guard width

Assume m>=3k-3. For arbitrary cyclic genuine-state sequences g_i,h_i
of length N write `G_i=R^(g_i)`, `H_i=R^(h_i)`, and define

    a0=m-k+2, s0=L-a0,
    C_i=G_i+R^a0 H_(i+1),
    Y_i=H_i+R^s0 G_i.                                  (1)

The inequalities needed below are

    a0>=2k-1>p, a0+k-1=m+1,
    s0>=2k-1>p, s0+2p<=L-1.                            (2)

Indeed m>=3k-3 gives the first and last bounds, while L>=k+m+1 gives
the lower bound for s0. The genuine and dummy bits in C_i are disjoint
and lie in its permitted native positions. Put

    q=B^N, D=q-1, P=R^s0.

Because a0+s0=L, the packed words obey the exact identity

    P*C-Y=H_0*D.                                      (3)

The direction H_(i+1) in (1) is essential: multiplying its high dummy
band by P sends it across one cell boundary into the genuine positions
of the next cell. Thus `Y=PC mod D`, and its genuine target-block state
is h_i, chosen independently from g_i.

Here 0<s0<L, so P is a proper within-cell power and not a power of B.
The retained equation P*v=q has the positive integral solution
`v=R^(LN-s0)`. A positive integral cell shift can also be included:

    P=B^b R^s0,
    C_i=G_i+R^a0 H_(i+b+1),
    Y_i=H_i+R^s0 G_(i-b), b+1<N.                      (4)

This supplies misaligned examples with P>B as well.

For L>=2(m+2), the unwanted bit in Y_i lies outside every permitted
native position, since

    s0>=m+k+2>m+1.

Consequently Y is not native typed. The argument below shows why the
actual source masks nevertheless accept it.

## 3. No field carry exposes the unwanted bits

Let spatial right be the genuine cell shift, so
`Rword_i=C_(i-1)`. Consider a scalar field digit from (1):

    F_i=DC*C_i+DR*C_(i-1)+DY*H_i+R^s0 DY*G_i.          (5)

The first two native products have degree at most m+k<L as polynomials
in R. The ordinary DY*H_i product has degree at most2p<L. The final,
unwanted term has degrees only in the interval

    [s0,s0+2p] subset [p+1,L-1].

It therefore cannot reach the tested degree p or wrap across a radix-B
cell boundary. The high dummy terms in the first two products also
start above p, because a0>p.

Each of the three input cells has exactly two bits in this construction,
even though the temporal cell's second bit need not be native. The
total coefficient mass of (5) is

    2 sum c_si <= (m+2)sum c_si <=R-2.

There are no inner-radix carries, and every coefficient occurs below
degree L. Thus `0<F_i<=B-2`, with no outer cell carry. The coefficient
at degree p is exactly

    c_C,g_i+c_R,g_(i-1)+c_Y,h_i.

If T(g_i,g_(i-1),h_i) is permitted by the fixed local relation, the
homogeneous scalar test is true and `F_i AND MF=0`. Packing the fields
therefore gives both the exact transport congruence and the field mask,
while the unwanted successor bits remain in untested high positions.

This reasoning is independent of clause order. Permuting clauses
changes the fixed c_si and mu, but the target coefficient still tests
exactly the chosen valid triple. Enlarging R to accommodate the new
coefficient mass preserves every step. Adding zero-expression mask
clauses only increases m and the available dummy band. Increasing L
merely increases s0 in (1); the upper bound s0+2p<L still holds.

## 4. A finite relation with no intended marked cyclic solution

For a small numerical instance take k=3 or4 and the relation

    T(center,right,next) iff next=End.

Choose one genuine Start at index0, one End at x, and an ordinary
state at every other current cell. Set every h_i=End. The construction
above satisfies every field mask. No genuine cyclic temporal shift
can have these properties: if all next states are End, permutation
of the cyclic cell indices forces all current states to be End, in
contradiction to Start.

The checker tests the minimum guard, the proposed guard2(m+2), and
an even wider guard, each with original, reversed, and rotated clause
orders. It also checks a varying independent successor plane and
misaligned P>B examples. The wide cases explicitly verify that Y
is untyped despite all paid mask equations holding.

## 5. The same construction applies to the actual stay-step tableau

The current window compiler has m>=3k-3 automatically. Start and End
have different top two rows. For each of the k^2 `(center,right)`
pairs, at least one of those two symbols is forbidden as next, since
the next symbol's top two rows must match the center's bottom two
rows. Each distinct forbidden triple contributes a mask bit. Hence

    m>=k^2>=3k-3.

For any raw x>0, take the finite slab consisting of the H boundary
row, the initialized row `L^a I^(x+1) Q R^2`, and the two following
genuine configurations. The first machine step flags the origin and
stays; its successor state is nonhalting. Choose enough left margin
for both steps. This slab exists whether or not the machine eventually
halts.

Let g_i be the allowed3-by-3 windows centered on the initialization
row and h_i those centered on the next row. Number spatial positions
in reverse, with the last I as index0. Their overlaps satisfy
T(g_i,g_(i-1),h_i). There is one Start at0 and one End at x. The
uniform V seam is valid. No final acceptance row has been included.

Apply (1), assigning the fixed alphabet indices End=0 and Start=p.
The finite slab's h_i states become an independent successor plane
carried in the dummy bits. By Section3 all scalar masks of the actual
fixed compiler pass, for every permitted L and clause order.

A concrete false input uses the stationary residue machine with
modulus2 and residue0. It halts when the initial unary length x+2 is
even, so its raw accepted set is the positive even integers. At
**x=1**, its initial slab has I-run2 and fits in width N=8 with left
margin2 and right margin2. It does not halt, but the construction
gives a positive solution of the deleted79 source.

## 6. Full positive arithmetic extension

Set `W=B^x`, `CS=R^p`, and `Z=C-CS-W`. The unique genuine marker bits
are disjoint from the dummy band. Removing them leaves Z>0, with
the low mask zero and Z even. The positive field in (5) has the
field mask zero. Set `J=(q-1)/(B-1)` and v=q/P.

For b=0, equation(3) gives the positive temporal wrap quotient
`kY=H_0`; the spatial wrap quotient kR is positive because every C
cell is positive. Thus `z=DR*kR+DY*kY>0` satisfies the local equation.
Native C cells are at most B-2, and N>x, so

    q-C>=J+1, J>=B^(N-1)>=B^x=2^(d*x)>d*x.

Take `alpha=q-C-d*x>0`. These are precisely the unchanged strengthened
bound and input exponent of the81 source.

With the actual new fixed constants and words, define

    Lambda=q^2, D0=q^3,
    Scode=Z+qF, Mcode=(MC+q*MF)J,
    r=(Lambda-Scode)*(Lambda-1)+Mcode.

The two masks give popcount(r)=3dN. Thus D0 divides the central
binomial coefficient, `q^2<=r<q^4`, and r is odd. The retained fresh
positive fixed-minus43 kernel construction applies at this actual
r,D0. It has no premise about P alignment and supplies all seventeen
kernel coordinates.

Finally choose the fixed-base exponent witnesses at the actual kernel
parameter with index u=d*x. Since W=2^u<q and u>=4, the81 proof gives
positive integral kappa,mu,delta,phi,rho. All20 equations of the
79-operation deletion hold with all32 existential coordinates positive.
The concrete nonhalting x=1 above is therefore a full arithmetic false
positive, not only a scalar test failure.

## 7. Evidence boundary

The checker verifies every instruction and source residual of the
precise79 deletion, including the inherited norm-residual correction.
It checks73 numerical arithmetic constructions and16 actual stay-step
tableau slabs, including nonhalting examples. Polynomial coefficient
checks explicitly verify the target block, bounded high garbage,
absence of inner and outer carry, and positive quotient. Both original
and rearranged clause orders are covered numerically, while the proof
establishes arbitrary order.

The actual machine's full window alphabet and enormous constants are
not numerically enumerated. Its fixed effective compiler is covered
by the m>=k^2 argument and formulas above. Full positive Pell witnesses
are supplied by the mathematical converse, not materialized giant
tuples. These limits do not weaken the identified false-positive
mechanism, and no claim about arbitrary alternative encodings follows.
