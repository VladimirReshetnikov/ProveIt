# A periodic seed does not preserve the derived-carry ripple theorem

The valid single-ripple compiler in `EXPLORATION_UNIT_TWO_TERNARY_RIPPLE.md`
recovers an omitted carry word D from Boolean C,E satisfying 3E=2C+1.
Replacing the single one by a periodic row-head word H does not preserve
that implication. The following counterexample satisfies complete native
field masks, positive slacks, geometry, both endpoint interfaces and the
positive Pell subsystem, yet encodes the two rows 5 -> 2 -> 3.

The maintained checker is
`../verification/explore_periodic_derived_carry_counterexample.py` with its
JSON receipt. It serializes and verifies all 72 primitive instructions and
20 source equations of this specific rejected extension. This negative
result does not apply to every possible four-field history compiler.
The valid 74-operation history retains its explicit carry mask and is
unchanged.

## 1. The rejected extension and its exact cost

Use native fields FA,FB,FC,FE and positive parameters FI,FF. The outer
equations are

    q=2Jrep+1,
    3FE=2FC+Jrep+H,
    FA+2FE=FB+FC+Jrep,
    FA+FE+alpha=q+Jrep,
    q=Wv,
    H(W-1)=q-1,
    FI+W FB=FA+q FF,
    FI+alphaI=W.

Pack P0=FC+q FA+q^2 FB+q^3 FE, set r=P0 and D0=q^4, and append
the eleven-equation parity-free Pell kernel of
`EXPLORATION_PARITY_FREE_PELL_KERNEL.md`. All its auxiliaries are positive.
This specifies the full rejected twenty-equation system, including the
mask rather than an external promise that its four fields are native.

The outer equations, Horner word and scale use 28 operations. The kernel
uses 44, giving the rejected total 72=36M+36A. There are 29 positive
unknowns and two positive parameters. The comparison for row geometry
uses the existing 2Jrep: its actual residual is the displayed geometry
residual plus q-2Jrep-1. The only other triangular adjustment is the
usual relaxed-norm residual times u^2-y_aux^2. The checker verifies all
twenty expanded source comparisons with precisely these adjustments.

## 2. An exact positive tuple

Take

    q=729, W=27, v=27, H=28, Jrep=364,
    FA=455, FB=475, FC=368, FE=376,
    alpha=262, FI=23, FF=17, alphaI=4.

All values are positive. The eight outer equalities hold exactly:

    q=2*364+1=27*27,
    28*(27-1)=728=q-1,
    3*376=1128=2*368+364+28,
    455+2*376=1207=475+368+364,
    455+376+262=1093=q+364,
    23+27*475=12848=455+729*17,
    23+4=27.

Subtracting the native offset gives

    A=91, B=111, C=4, E=12.

All four are Boolean ternary words of six digits. In particular each
native field has six digits in {1,2}; FC has unit digit two. Dividing
the words into rows of three ternary digits gives

| Row | A ternary code | A binary value | B ternary code | B binary value |
|---|---:|---:|---:|---:|
| 0 | 10 | 5 | 3 | 2 |
| 1 | 3 | 2 | 4 | 3 |

The endpoint offset for one row is (27-1)/2=13. Thus FI=13+10
correctly encodes binary five, and FF=13+4 correctly encodes binary
three. Both endpoint parameters are well-formed, and the intermediate
row agrees exactly. Two ordinary increments would instead give 5 -> 6 -> 7.

The precise omitted condition fails:

    D=C-E=4-12=-8.

The periodic seed equality 3E=2C+H holds, but it no longer forces E
to be a subset of C. An incoming carry at a row boundary can change
the seed behavior. The single-seed classification in the valid ripple
proof consequently cannot be invoked for this periodic word.

## 3. The complete mask and positive Pell extension

For the tuple above,

    P0=r=145922870402,
    D0=q^4=282429536481=3^24.

The packed word has exactly 24 native ternary digits, its unit digit is
two, and its index is even. Direct factorial valuation gives

    v_3(binomial(2r,r))=24.

The general parity-free kernel hypotheses are all satisfied:

    D0>=81, r>=27, r<D0<2D0, D0<r^2.

Its positive converse therefore constructs all seventeen remaining Pell
auxiliaries, including positive u and the positive squared-congruence
quotients. In detail the scale is a power of three, its central-binomial
divisibility is exact, and U=3^(2r+1) makes w=U/D0 integral and positive.
The canonical binomial integer part supplies positive integral s, and the
kernel theorem supplies all norms, interval witnesses and auxiliary
quotients. There is no missing parity assumption; evenness happens to
hold here as well.

The receipt evaluates all nine outer/index source residuals, the complete
packed digit predicate and exact central-binomial valuation. It does not
materialize the enormous positive Pell tuple. The theorem supplies that
extension independently, so this is a full counterexample to the rejected
positive-equation system, not merely a false local digit pattern.
