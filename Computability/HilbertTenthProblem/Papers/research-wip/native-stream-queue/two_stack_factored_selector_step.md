# Factored read selectors reduce the two-stack scalar certificate

For the same total deterministic binary two-stack tables and affine
ordinary-input interface as the [eight-column construction](two_stack_affine_input_step.md),
the exact scalar graph has a schedule of **8B+18 operations**, where
**B=9K** is the number of branches for K states. It has **eight positive
witnesses and seven equations**. One polynomial costs **8B+38**.

The saving comes from the known source-state and read-symbol structure.
Three bounded selectors replace interpolation of the four source columns;
only the four arbitrary output columns are interpolated. All empty-stack
guards and target-state information remain exact. This is an operation
reduction with a larger local witness and equation count, and it does not
provide the still-missing arbitrary-duration history compiler.

## 1. The unchanged computational and input contract

Use positive stack codes

    enc(w)=2^len(w)+sum_j w_j*2^j,

with top-first bits and empty code1. Every positive integer is a valid
stack code. Fold the left stack X and state j into

    n=K(X-1)+j, 1<=j<=K,

and put r equal to the right stack code. The machine reads E,0,1 from each
stack, pops a nonempty read, pushes fixed binary words and changes state.
There is one transition for every state/read pair, hence B=9K. A state
that ignores one read repeats its action in the corresponding rows; those
rows are still counted. This theorem does not replace B by the number of
distinct output tuples or by a sparse instruction count.

The earlier note constructs a fixed universal machine in this normal
form, with a detectable finite-input endpoint and accepting target(h,1).
Its ordinary input is

    (n_0,r_0)=(s_start,kappa*x+lambda),

where the program prefix fixes kappa>0 and lambda>=0. That two-operation
loader, its execution of input conversion, and the normalization to an
absorbing target are unchanged. No new universality or input-coding
assumption is introduced here. The executable decoder and cleanup tables
remain nonuniversal fixtures for the arithmetic compiler.

## 2. Three bounded selectors recover the source columns

Supply eight strictly positive integers

    j,jbar,l,lbar,rsel,rbar,P,Q

and impose

    j+jbar=K+1, l+lbar=4, rsel+rbar=4.                  (1)

Thus j is a state and each read selector belongs to{1,2,3}, representing
E,0,1 respectively. Define

    c_l=(l-2)^2, d_l=l-c_l,
    c_r=(rsel-2)^2, d_r=rsel-c_r.                      (2)

Each side of(2) costs one subtraction, one square and one subtraction.
Its exact table is

| Selector | Read | c | d | Stack equation |
|---:|---|---:|---:|---|
|1|E|1|0|X=1|
|2|0|0|2|X=2P|
|3|1|1|2|X=2P+1|

Consequently the two source equations are

    n+K=K*(d_l*P+c_l)+j,
    r=d_r*Q+c_r.                                     (3)

The bounded j identifies the actual state in the unique folded
representation of n. Strict positivity of P,Q excludes code1 from
either nonempty-read branch: popping a1 from code1 would require quotient0.
On an empty read the corresponding quotient is arbitrary and positive.
There is no arithmetic division, digit extraction or extra variable for
the decoded stack value in the actual schedule.

## 3. Four output columns and the branch index

Enumerate the complete table lexicographically by state, left read and
right read, with read order E,0,1. The old branch index b in1,...,B obeys

    b=9j+3l+rsel-12.

Compute instead

    z=9j+3l+rsel.                                    (4)

This uses two numeral multiplications and two additions. It ranges
bijectively over13,...,B+12 for the bounded selector triples. There is no
runtime subtraction of12: interpolate at these shifted fixed nodes.

For a left read and pushed word v, write the original stack coefficients
(d,c,a,b0) as

    nonempty: (2,read_bit,2^len(v),val(v)),
    empty:    (0,1,0,2^len(v)+val(v)).

For the right side use(e,f,g,h0), and let O be the branch's target state.
The four output columns are exactly the earlier columns

    ts=K*a, tc=K*(b0-1)+O, us=g, uc=h0.                (5)

Interpolate them at the nodes in(4), clear denominators by one fixed
positive D, and call the integer polynomials TS,TC,US,UC. Their degrees
are at most B-1. The remaining two equations are

    D*n'=TS(z)*P+TC(z),
    D*r'=US(z)*Q+UC(z).                               (6)

Some fixed coefficients are signed. Every existential coordinate remains
strictly positive. In particular the empty case uses a=0 or g=0; an
arbitrary empty-stack quotient cannot affect the output.

Equations(1)–(3) force precisely the actual state and both actual read
symbols. The fixed-node table evaluations in(6) therefore give precisely
the prescribed output words and target state. This proves soundness for
every positive assignment. Conversely every genuine step supplies its
selectors, their positive complements, and the two positive tail codes;
choose any positive quotient on an empty stack. This proves completeness.

The fixed coefficient compiler can obtain the new polynomials from the
old ones by substituting z-12 into their coefficient lists. This is an
explicit computation on fixed program numerals. The paid evaluator
contains no z-12 operation and no runtime table lookup.

## 4. Exact arithmetic costs

The literal schedule has these blocks:

| Block | Multiplications | Additions/subtractions |
|---|---:|---:|
| Three selector bounds |0|3|
| Left read and folded source equation |3|5|
| Right read and source equation |2|3|
| Shifted branch index |2|2|
| Four Horner evaluations |4(B-1)|4(B-1)|
| Two output equations |4|2|
| **Total** |**4B+7**|**4B+11**|

The seven residual subtractions, seven squares and six sums cost another
7M+13A. Thus the scalar graph costs **8B+18** and one polynomial costs
**8B+38=(4B+14)M+(4B+24)A**, both with eight positive witnesses.
Register reuse and comparisons follow the same accounting convention as
the complete universal certificates; every numeral multiplication is paid.

For the explicit two-state decoder B=18, the graph drops from285 to162
operations, and the polynomial drops from299 to182. The local witnesses
increase from four to eight and the equations from five to seven. These
are exact generic padded schedules, not optimality claims. Their polynomial
degree is at most2B; no exact degree is asserted for arbitrary program
tables whose coefficient columns may specialize to lower degree.

For every externally fixed t>=1, unroll t steps with the two-operation
loader and fixed final configuration(h,1). The exact totals are

    witnesses=2(t-1)+8t=10t-2, equations=7t,
    graph operations=2+t(8B+18),
    graph M=(4B+7)t+1, A=(4B+11)t+1,
    polynomial operations=(8B+39)t+1,
    polynomial M=(4B+14)t+1, A=(4B+25)t.               (7)

The induction proving the unrolled graph is unchanged. Earlier acceptance
can be extended to t by actual absorbing-target transitions. The family
still grows with t; quantifying t does not produce a fixed Diophantine
polynomial.

## 5. Checks and the remaining history problem

The [checker](two_stack_factored_selector_step.py) and
[receipt](two_stack_factored_selector_step.json) verify the shifted nodes,
all fixed output coefficients, seven symbolic residual identities, the
sum-of-squares identity, and both operation ledgers. The source graph is
compared with independent word execution on the same total decoder table,
including wrong selectors, wrong outputs and arbitrary positive empty
quotients. Fixed-duration cleanup checks include computations which have
not reached the forced endpoint and actual zero-stack padding. Default
execution recomputes the deterministic receipt.

Independent proof/source/default review passed without findings. A separate
string executor checked3,000 cases on unrelated complete tables with1,3 and4
states and replacement words of length0 through5. These included780
empty-stack cases and arbitrary unused positive quotients. This supplements
the parametric proof and the explicit decoder/cleanup fixtures above.

This factoring exploits structure within a scalar branch table. For a
packed history, evaluating TS on a packed selector word is still not
coefficientwise interpolation; products of independently packed words
still create cross terms. A uniform history construction must pay for
that synchronization. The complete universal comparison and polynomial
bounds are not improved by this local result alone.
