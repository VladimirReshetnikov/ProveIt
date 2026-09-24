# Omitting the source-word mask: a fixed-router counterexample

The count marker and the complement support test do not, by themselves,
recover Booleanity of an unmasked program source word. There is an exact
positive false solution for the acyclic graph0->1->2, claiming a four-step
return from0 to0. Its junk and both Test words are fully Boolean ternary
words, all five outer equations hold, and the complete positive Pell
extension exists.

This refutes the direct omission from the standalone nondeterministic
fixed router. It does **not** yet refute omitting the native NC field
from the complete cyclic118 counter/controller system: that system also
has typed sign and zero projections and the numerical counter equations.
The latter omission remains open. No smaller universal bound is claimed.

The exact regression, requiring only integer and symbolic arithmetic, is
`../verification/explore_unmasked_program_source_counterexample.py/.json`.
Its literal counterexample was found by a finite-domain carry solver;
the maintained verification does not depend on that solver or its timeout.

## 1. The precise weakened fixed-router system

Retain all five outer equations of
`EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md`:

    q=(R-1)H+1,
    TestC=C+[((R-1)/2)-S]H,
    TestV=V+ZH,
    (RK-g)C+gI=(gI)q+RV,
    TestC+TestV+alpha=q.

All six supplied coordinates H,C,V,TestC,TestV,alpha are positive;
q is the positive input parameter and R is a fixed numeral. Remove only
C from its four-field Boolean packing. Use instead

    P=V+q TestC+q^2 TestV,
    L=q^3, D0=9L, r=D0-3P-1.

Append every equation of the original fixed-sign43 base-three kernel.
The two powers q^2,q^3 cost the same as the old q^2,q^4, while three
Horner fields cost two fewer operations. The resulting formal arithmetic
certificate is66=37M+29A, with the same23 positive unknowns and16 equations.
Its exact source comparison is verified, but its claimed graph semantics
are false.

## 2. Fixed constants and literal positive tuple

Use the three phase-compatible state coordinates

    a=(8,10,14), d=14, l=2,
    edges={(0,1),(1,2)}, initial=final=0.

Their six unordered pair sums are distinct, and twice the smallest
coordinate exceeds the largest. The edge and marker exponents are
therefore distinct, on the l grid, exactly as required by the router.
Set

    S=3^8+3^10+3^14=4848579,
    g=3^14=4782969, I=3^8,
    K=3^16+3^18+3^6+3^4+1=430468021,
    Z=3^15=14348907,
    R=3^34=16677181699666569,
    q=R^4, H=1+R+R^2+R^3, J=(q-1)/2.

The fixed width satisfies even the stronger bound

    R>max((K+g)S,2S+1,Z).

The two nontrivial literal words are

    C=28871726544739970418459818800067147328666199790815308,
    V=12282797154274314089309142195079934980011510335861921202065040.

Define TestC=C+J-SH, TestV=V+ZH and alpha=q-TestC-TestV. Every one of
these numbers is positive. Direct exact calculation verifies the routing
equation and both support equations. The three words V,TestC,TestV are
Boolean ternary and below q. In contrast C has many digits two; the first
occurs at ternary position37. C is even.

The graph is acyclic and has no positive path from0 back to0, regardless
of length. In particular its set of endpoints after four steps is empty.
Thus this is an actual false positive for the specified graph predicate,
not merely a malformed witness for an otherwise true endpoint query.

## 3. Packing, parity, and the full positive Pell extension

Because the three retained words are Boolean and below q, their packed
word P is Boolean and lies in (0,q^3). Its parity is even. One may also
derive that parity from the support identities: q has even ternary
exponent136, H and J are even, and

    V+TestC+TestV=2V+C+J+(Z-S)H.

Therefore r=9q^3-3P-1 is even. Exact integer valuation gives

    v_3 binomial(2r,r)=410,
    D0=9q^3=3^410.

There is no pre-power square assumption here: this particular integer
scale has the explicit square root n0=3^205. Its index satisfies
n0<=r<2n0^3 and D0<r^2. Together with the exact central-binomial
divisibility and even index, these are the hypotheses of the original
base-three43 positive converse. It supplies all17 remaining positive
Pell coordinates. The literal tuple consequently extends to a full
positive solution of the weakened66 arithmetic system. The enormous
Pell coordinates themselves are not instantiated in the regression.

## 4. The support-test gap and the remaining composition question

With both C and TestC Boolean, the equation C+J=SH+TestC forces C to
be supported on SH because adding two Boolean words creates no ternary
carry. Without the C mask, write E=J-TestC, which is Boolean; the equation
only says C=SH-E. This subtraction can borrow across forbidden positions
and even across time rows. The count marker's proof also uses source
subsets to bound the raw coefficients and separate the rows of KC.
It cannot be applied to these borrow runs without a new argument.

In the full cyclic118 system, deleting NC leaves eleven native fields.
The corresponding direct scale q^11 requires a five-product power chain,
for example q^2,q^3,q^5,q^6,q^11, instead of the current four-product
chain ending in q^12. Thus the straightforward proposed omission would
be117, not116: it saves two Horner operations and pays one additional
scale product. Canonical parity is preserved because the deleted field
J+C is even for a true even-length one-head history.

The pre-kernel range is not the principal unresolved issue. The same
paid bounds give P6<2q^6 and bound the other five fields by3J-1, which
implies the eleven-field word lies below3(q^11-1)/2. Its first native
FKplus chunk would still restore the raw aggregate bound. What remains
unproved is source-state recovery in the presence of the typed ROM
outputs. The fixed-router counterexample above shows why the old marker
and complement lemmas alone cannot supply that missing implication.

Initial full typed-output searches used three fixed three-state tables
and one honest twelve-block numerical history; each hit its stated
solver timeout. A further 180-second finite-domain run on the acyclic
table with labels(+,-,-) also returned unknown. Those results are not
unsatisfiability evidence and are not included as a successful
mathematical or arithmetic check. The bounded search is paused; the
maintained exact counterexample is the separate fixed-router result.
