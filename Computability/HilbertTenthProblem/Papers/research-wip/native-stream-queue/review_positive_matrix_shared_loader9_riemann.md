# Independent review of the nine-operation positive-matrix input loader

**PASS, with no correction requested.** Both complete nine-row schedules
produce the stated positive eight-coordinate input: one costs 5M+4A,
the other 4M+5A. The new fixed integer alphabet and its strictly positive
lift preserve the exact ordinary-input zero criterion. The signed
trajectory acquires the displayed duration scale, while the positive
lift represents that new signed action exactly. No unbounded-history
certificate or complete universal-polynomial saving is supplied.

## 1. Invertible fixed coordinates and exact integer inputs

The stated inverse of T is correct. To check its less immediate rows,
use z4=y4+2y7 in y3=z3+z4-2z7 and y6=z6+z4-2z7. This gives
z3=y3-y4 and z6=y6-y4. Substituting these in the first row yields

    2y1=z1+y3-y4+y6-2y7,
    z1=2y1-y3+y4-y6+2y7.

Together with the remaining displayed rows this proves invertibility
and an integral inverse. Also 2T is integral. In particular the repeated
values of some coordinates on the specific input curve do not imply
that T loses rank or identifies arbitrary state coordinates.

On the inherited Gram input, direct expansion gives

    a+c-2=(r^2+1)^2=V,
    u v(x)/2=V,
    T v(x)=(V,b-3,V,a-2,b-3,V,1).

This entire column is integral. No assertion that T sends every integer
column to an integer column is needed. The shared equality of the
first, third and sixth initial values is specific to the input curve;
the evolving coordinates remain distinct state coordinates.

The source uses r=alpha*x+beta with positive integers alpha,beta,x,
so r>=2, and the actual universal program recipe gives r>=36. After
the fixed buffer of one is added, the column is

    (V+1,b-2,V+1,a-1,b-2,V+1,2,1).

The formulas b-2=(r-1)(r^2+1) and a-1=(r-1)^2 prove positivity of
every entry at r>=2. The possible zero signed coordinate a-2 at r=2
causes no problem; the corresponding lifted coordinate is one.

## 2. Word order, scale and the single equality

For each inherited letter A_sigma,

    G_sigma=(2T) A_sigma T^-1

is an integer matrix. Both coordinate matrices are fixed and the old
alphabet is fixed independently of the program and input, so the new
finite alphabet has that same independence and effective specification.
Its numerical entries need not be materialized for this transfer theorem.

For a word of length t, adjoining factors T^-1 T cancel in their actual
order and give G_w=2^t T A_w T^-1. This includes the empty product.
The first row of T remains u/2, so

    2 e1 G_w T v(x)=2^t u A_w v(x).

Both sides are integers. As the two scalar multipliers are nonzero,
this equality preserves the first-coordinate zero test at each selected
word, including length zero. It does not assert that the signed state
trajectory equals the old trajectory. For example an identity letter
becomes 2I, as the author's first retained remark states.

The positive lift is then applied to G. Its row-absolute-sum choice of
kappa proves strictly positive integer entries, common row sum 8kappa,
and the exact identity D L_sigma=G_sigma D. Since Dz(x)=T v(x),

    2*((L_w z(x))_1-(L_w z(x))_8)=2^t u A_w v(x).

Consequently the sole terminal equality of coordinates 1 and 8 is
exactly the inherited Gram scalar-zero acceptance condition. No
intermediate guard, duration normalization, divisibility witness or
extra variable initial value is introduced. The empty word has first
minus eighth coordinate V>0 and rejects. The new signed scaling and
the exact positive decoder are separate, correctly stated identities.

## 3. Both complete nine-row arithmetic ledgers

In the primary schedule, the five products are alpha*x, r*r,
eta*eta, eta*u and u*u. The four additions/subtractions compute r,
eta, u and fhat. Thus the total is exactly 9=5M+4A, with

    eta=r-1, aa=eta^2, u=r^2+1,
    bb=eta*u, V=u^2, fhat=V+1.

In the alternative schedule, r*r and its +1 row are replaced by the
shared square aa=eta^2, the paid doubling twice_r=r+r and the sum
u=aa+twice_r. The identity

    (r-1)^2+2r=r^2+1

proves that u, bb, V and fhat agree with the primary schedule. Its four
products are alpha*x, eta*eta, eta*u and u*u; its five remaining rows
are additions/subtractions. Thus its exact cost is 9=4M+5A.

Both entire sources are present, not merely local tails. Every computed
operand precedes its use, every row reaches a column output, and all
three supplied ports alpha,beta,x are live. There are no auxiliary
witnesses. Copies of fhat and bb and the fixed entries 2 and 1 add no
arithmetic. T is compiled into the fixed matrices; neither schedule
applies an unpaid run-time matrix multiplication to obtain its input.

A fresh independent structural check parses all eighteen literal row
definitions, matches both Markdown tables with the saved metadata,
and confirms syntax, declared operation types, topology, liveness and
both ledgers. It does not evaluate or symbolically propagate either
source. The equations above are independent hand derivations.

## 4. Intermediates, contraction and retained boundaries

The 13-operation intermediate is valid: halving only the conjugated
first coordinate removes its former doubling while changing the final
shift to V+1. Its inverse is integral and twice its coordinate matrix
is integral. The 10-operation intermediate is also valid. Its inverse
restores z3,z4,z6 by adding 2y7, and its first coordinate is
2y1-y3-y4-y6-2y7. Its extra output cc=V-aa equals c-1 and costs one
additional subtraction. The final T arranges for those two outputs to
be copies of fhat instead. These are valid upper bounds, not claims
of necessity or failed constructions.

The common-row-sum positive lift inherits the same oscillation estimate
as the parent, with its newly computed row sum. Removing the uniform
1/C contribution leaves nonnegative rows of sum 1-1/kappa. This proves
contraction along every switching word; stochasticity and the positive
initial minimum give the common positive normalized limit. The empty
word and the zero-family kappa=1 case are handled separately.

The new scalar example also checks: G=[2] gives kappa=3, C=6 and
L=[[5,1],[3,3]]. Its row difference is (2,-2). Starting at (2,1), the
raw difference is therefore 2^t, never zero, while normalization by
6^t makes it (1/3)^t. Approximate agreement still cannot replace exact
finite-word equality.

The author's two numbered remarks retain two false extensions with
explicit witnesses: literal unscaled action fails for A=I, and strict
positivity at auxiliary r=1 fails because aa=bb=0. Neither extension is
used by the theorem. The latter excludes no positive ordinary input,
since such inputs already force r>=2. No new wrong or unproved claim
arose in this review, and no correction was requested.

The fixed-threshold replacement obstruction is inherited unchanged from
the accepted capped and Gram interfaces. The open task remains a paid
fixed-arity certificate for an unbounded selected word. Neither the
9-operation count nor the 8-dimensional transfer is asserted minimal,
and no reduction of the universal polynomial operation frontier is
claimed.

## 5. Authentication and executed scope

I read the complete new proof and metadata, and had already read and
independently reviewed the full frozen 14-operation parent and metadata
in this session. That earlier review binds its precise Gram, group,
capped and Markov read scopes; those external group foundations are
not re-audited here. The companion receipt pins the final author pair,
both immediate parent files and the earlier independent parent review.
It authenticates the parent's four inherited proof-note bytes and
read spans, without claiming a new substantive read of their entirety.

Only original byte/span and literal-source structural metadata ran.
No supplied, archived, committed, predecessor or frozen scientific
helper was executed or imported. No saved source was evaluated
numerically or symbolically, no degree was propagated and no universal
matrix alphabet was materialized. Review artifacts are confined to
/tmp, with no repository or Git mutation.
