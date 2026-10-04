# Two positive substitutions reduce padded reversal to 129 producers

The complete [padded reversal130](native_binary_reversal130.md) can be
compiled into two smaller single-polynomial sources by eliminating defined
positive witnesses. Both new arrays have **129=66M+63A** producers and the
same external positive projection

    q=2^n, n>=2, 0<x<q, z=rev_n(x).

They differ in witness count, full polynomial cost and degree:

| Variant | Positive witnesses | Equations | Full polynomial M | Full polynomial A | Full cost | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| Inline selected output |47|33|99|128|227|40|
| Inline selected output and scale factor |46|32|98|126|224|52|

This is a local component improvement. The external padded width q remains
explicit, x remains positive, and no universal Diophantine frontier changes.
The [new helper](native_binary_reversal_inline129.py) reads the committed
130 JSON as inert data only and emits both complete arrays in its
[receipt](native_binary_reversal_inline129.json). It never executes or
imports the predecessor helper. The
[independent review](review_native_binary_reversal_inline129.md) challenges
the full substitutions and resulting polynomials.

## 1. Eliminate the selected output witness

In the parent, put

    D=q*((q-1)*(quotient_hat-1)+z).

The existing register `scaled_reverse_sum` computes D. The parent pays the
producer `congruence_right=D+1` and comparison
`Ahat=congruence_right`. Its AND output padding is computed in two rows:

    and__scaled_Z=16*Ahat;
    and__F3=and__scaled_Z-8.

Delete the `congruence_right` producer, its comparison and positive witness
Ahat. Keep D's existing paid rows and replace only the output padding by

    and__scaled_Z=16*scaled_reverse_sum;
    and__F3=and__scaled_Z+8.

This is exactly 16*(D+1)-8. No instruction computing D is removed and no
multiplication or comparison is free. The change saves one addition,
one existential coordinate and one comparison.

For every assignment of the remaining strictly positive coordinates,
q>=1, quotient_hat>=1 and z>=1 imply D>=q*z>=1. Thus the restored
Ahat=D+1 is always strictly positive, even before q is typed as a power
of two or the paid input bound is used. This makes the substitution valid
on the complete candidate domain, including inconsistent assignments q=1.

Projection of a parent positive zero forgets Ahat and satisfies all new
comparisons. Conversely, any new positive zero extends uniquely by
Ahat=D+1, restoring the deleted comparison and every original padded
register. All remaining residuals are equal after this substitution.
Hence there is a bijection between full positive zero tuples with that
coordinate omitted/restored. The parent theorem supplies the exact
unbounded padded-reversal projection; no new finite sample replaces it.

## 2. Eliminate the scale factor P

The first variant still has the paid comparison

    repunit_P=P, repunit_P=(2q-1)*J+1,

and the positive coordinate P. It computes `scale=q*P`. In the second
variant substitute `repunit_P` for every P input port, remove the comparison
and P coordinate, and topologically reorder the existing producers. The
repunit register remains a paid product plus addition. There is no deleted
producer and no new producer; its value is used directly by `scale`.

For all positive q,J, the restored value P=(2q-1)J+1 is at least two.
Consequently this second substitution also preserves and uniquely restores
full positive zero tuples, with no use of a semantic typing assumption.
The selected-output restoration then uses the already restored scale in
the unchanged native source. Both witness restorations satisfy all parent
comparisons, so the exact projection is inherited by a second explicit
bijection. The new polynomial need not equal the old polynomial away from
the positive zero set; the claimed equivalence is of the represented
relation and these tuple maps, not literal polynomials.

## 3. Literal source, cost and degree

For the first variant all 130 parent producer rows survive except the
single deleted output addition, and exactly two padding rows change as
shown. All 34 comparisons survive except the defined-output equality.
For the second variant the same producer rows remain, P is replaced by
its paid definition, and one further comparison is removed. The complete
receipts include parameters, ordered positive witnesses, producer arrays,
comparisons, residual subtractions, squares and final additions.

For k comparisons the ordinary SOS adds k squares, k subtractions and
k-1 additions. Thus 129+3*33-1=227 and 129+3*32-1=224, with the exact
multiplication/addition ledgers in the table. All producer rows and all
external/witness ports are live; an equality is never counted as a free
arithmetic evaluation in the full polynomial.

The first variant's expanded polynomial has 411 nonzero monomials and
exact degree40. Its unique highest-degree monomial remains

    2^48 * and__w^4 * and__s^8 * and__k^4 * q^12 * P^12.

Replacing P by (2q-1)J+1 gives the second variant 1,207 nonzero monomials
and exact degree52. Its unique highest-degree monomial is

    2^60 * and__w^4 * and__s^8 * and__k^4 * q^24 * J^12.

The source expands each whole new SOS over the independent supplied
variables, rather than inferring degree merely from semantic equivalence.
The second coefficient follows from the leading term 2qJ of restored P,
but the degree claim also requires that every other term stay below52;
that is checked on the full expanded polynomial.

## 4. Evidence and boundary

Fresh outer checks cover every positive word of widths2 through10:
2,035 words for each variant. They verify the exact selected output,
positive restored witnesses, native padding equality and, for the second
variant, the paid scale restoration. No full native Pell zero tuple is
materialized. The parent positive-projection theorem and the explicit
bijections prove the unbounded relation.

The new helper also audits topology, every supplied coordinate's liveness,
full source costs and exact whole-polynomial coefficients. Normal and
optimized exact-receipt checks are required before commitment. The
independent checker reads predecessor arrays as data and separately
reconstructs all residuals and witness-restoration substitutions. Committed
helpers and their temporary copies are thereafter frozen evidence.

These substitutions offer a degree/witness tradeoff for the reversal
component. They neither supply a canonical word length nor remove the
native AND used by the loader. A cheaper general loader and a complete
paid accepting-history compiler remain separate obligations.
