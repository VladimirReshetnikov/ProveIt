# Index parity cannot always be chosen by padding a tag witness

Status: author and two independent complete proof/source reviews and fresh
verification runs passed without findings. The proof and arithmetic are
frozen. The published general105 certificate is unchanged.

For the fixed tag program with deletion number beta=2 and appendant u=00,
**every complete105 witness for the input 00 has odd index r, while every
witness for the input 0000 has even index r**. Both computations halt.
The result allows every width admitted by the certificate and every formal
post-halt continuation admitted by its equations. It is therefore stronger
than counting the parities of the canonical first-halt examples.

This obstructs the proposed method of obtaining104 by arranging one fixed
parity and invoking the established43-operation positive converse. It is
not a proof that the opposite-sign43 system has no other Pell witnesses:
`EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md` deliberately makes no such claim.
Nor does this nonuniversal example exclude a special universal appendant or
startup compiler whose inputs have an invariant parity. No104 certificate
or general lower bound is asserted here.

## 1. The current ten-field parity

Use the exact mask order of `EXPLORATION_GENERAL_SCALED_TAG_TRANSPORT.md`:

    Gstar,Q,S0,S1,M0,M1,Ebar,E,Nbar,N.

All are Boolean ternary words after the full105 decoding theorem. Their
integer sum is

    2Q+(A+c+2)H-S1+L+Nsum,

because Gstar=Q+AH+S0, S0+S1=H, M0+M1=L, Ebar+E=cH and
Nbar+N=Nsum. Since A and q are odd and L=2Nsum+H, the packing satisfies

    P = cH+Nsum-S1 modulo2.                              (1)

For a canonical source row of ordinary word length ell_j, its Nsum row is
(3^ell_j-1)/2, of parity ell_j. Thus the usual canonical formula is

    P = sum_j(c+ell_j-s_j) modulo2.                      (2)

The extra Gstar term matters: replacing it by the older G gives a different
parity formula. Also q^10=1 modulo4, so r=P+(q^10-1)/2 has exactly P's parity.

## 2. The zero-input content is zero in every witness

Fix beta=2,u=00, and input parameters Ninit=0,Linit=3^ell with ell>=2.
Here K=9, c=1, U=0. In any complete105 solution, use its already established
Boolean field recovery, geometry R=3^m,q=R^t and original transport source.
Set b=R/K>1 and d=3E+S1. The exact content equation becomes

    bN = N+bd+q Nfinal.                                  (3)

The prefix theorem makes d Boolean with support in the first two trits of
each row. Therefore bd is Boolean and has all its support strictly below q:
its last possible trit is at position tm-1. N is also Boolean below q.
The sum N+bd has ternary coefficients at most two and has no carries.
The term q Nfinal has support at or above q, so the entire right side of(3)
is a literal coefficient expression, with no carries between its parts.
The left side bN is Boolean.

If N were nonzero, its lowest occupied trit would occur on the right side,
strictly below the lowest occupied trit of bN on the left. All right-hand
terms are nonnegative, so this is impossible. Consequently

    N=0, d=0, Nfinal=0.

Since d=3E+S1 with nonnegative disjoint prefix fields, E=S1=0. The computed
equation M1=2Q+S1 and Boolean Q,M1 then give Q=M1=0. Finally Nsum=Nbar
and L=M0, where both Nbar and M0 are Boolean.

This step did not assume the encoded suffix is a real tag computation.

## 3. All source rows have exactly one length marker

The reviewed global length-flow theorem now has only the zero channel:

    M0+q Lfinal = Linit+(R/3)M0.                         (4)

It gives one increasing path from the initial marker to a single terminal
marker, including when the supplied positive integer Lfinal was not initially
assumed to be a power of three. Every edge increases its trit position by
m-1, strictly between zero and m. The initial marker lies in row zero,
and the terminal marker lies in row t. Hence each source row0,...,t-1
contains at least one path node: a jump of length less than m cannot skip
an entire row.

Containment has reduced to

    2Nbar+H=M0.                                          (5)

Consider a row with incoming carry zero. Its head contribution is one.
If the unit Nbar trit is zero, the head itself is the unique M0 marker;
any later Nbar trit1 with zero incoming carry would produce a forbidden
M0 trit2. If the unit Nbar trit is one, doubling plus the head starts
carry one. It continues through Nbar trits1, producing output zero,
and stops at the first Nbar trit0, producing a unique marker1. After that
no later Nbar trit1 is possible. The only way to carry out of the row
is for every Nbar trit to be one, in which case the whole M0 row is zero.

Every source row has a path node, so the last alternative is excluded.
Starting from the low end, induction through all rows proves zero outgoing
carry and exactly one M0 marker per row. This rules out both extra markers
in a row and a hidden borrow/carry repair in a formal suffix.

The edge shift m-1 therefore advances exactly one row and decreases the
within-row exponent by one. Thus

    ell_j=ell-j,  0<=j<t,
    Lfinal=3^(ell-t),  0<=ell-t<2.

There are precisely two possible heights:

    t=ell-1 with terminal exponent1,
    t=ell   with terminal exponent0.                    (6)

The second is a genuine allowed formal continuation of one row past the
first halt, not a presumption that the source equations forbid all suffixes.
No other suffix can satisfy their masks and containment.

## 4. The two allowed heights have the same parity

By(1), c=1 and S1=0,

    r = P = sum_{j=0}^{t-1}(1+ell-j) modulo2.

The extra source row in the second case of(6) has exponent1 and contributes
1+1=0. Therefore every solution for this fixed input has

    r = sum_{k=2}^{ell}(k+1) modulo2.                    (7)

For ell=2 or3 this is odd; for ell=4 or5 it is even. In particular the
same fixed program has halting inputs (Ninit,Linit)=(0,9) and(0,81) whose
entire complete105 witness sets have opposite parities. Increasing m,
choosing a different admissible A, or retaining an arbitrary formal suffix
cannot change(7).

Existence for both choices in(6) is also explicit. Choose any sufficiently
large power A, R=27A, q=R^t. Set Q=S1=N=E=0, S0=H,

    M0=L=sum_j 3^(ell-j)R^j,
    Nbar=Nsum=(L-H)/2, Ebar=H, Gstar=(A+1)H,
    Nfinal=0, Lfinal=3^(ell-t).

All masks and transports hold, including the extra exponent1 row leading
to terminal exponent0. The positive adapters are one where the raw value
is zero, the boundary slacks are positive, and the unit Gstar bit ensures
the unchanged native mask. The generic44 theorem supplies all positive
Pell witnesses for either index parity. No enormous auxiliary is required
to be materialized to prove this existence statement.

## 5. Exact evidence and scope

`explore_tag_index_parity_obstruction.py` freshly checks the existing full
105 schedule and all21 source comparisons for this fixed zero-leading
branch, and checks the unrestricted field-sum identity behind(1). It does
not propose a changed schedule or count an unaudited104 certificate.

Its finite content search enumerates every Boolean N at six small
geometries, solves d exactly, and tests every Nfinal in0,...,8. These small
geometries are explicitly tests of the coefficient lemma, not full105
input-width instances. A separate exhaustive row check tests the
no-empty-row decoder in(5). A length search solves(4) for every integer
Lfinal in1,...,8, including nonmarkers, without imposing rowwise markers.

Finally it builds complete positive outer tuples at three widths for
every ell=2,...,12 and both heights in(6). It checks every one of the ten
outer source residuals, all ten conceptual masks, the exact valuation,
and all generic44 preliminary inequalities. The receipt distinguishes
these full outer examples from the separately proved enormous Pell
extensions and from the small local searches.
