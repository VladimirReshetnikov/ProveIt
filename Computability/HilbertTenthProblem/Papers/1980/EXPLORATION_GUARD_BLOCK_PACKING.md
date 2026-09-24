# Factoring the counter guard block: a complete 108-operation family

The complete universal family in
`EXPLORATION_SHARED_PELL_INDEX_OFFSET.md` has a straight-line certificate of
109 operations. The exact coordinate elimination below reduces this to
**108 operations: 55 multiplications and 53 additions or subtractions**, with
36 positive unknowns and 24 source equations. All fixed integer numerals are
free; their multiplications are counted. The established universal frontier
remains 90. This is an improvement of the separate raw-counter/controller
architecture.

The source and full certificate are in
`../verification/explore_guard_block_packing.py`; its JSON receipt separates
fresh arithmetic, finite integer identities and fresh canonical transport.

## 1. The two supplied guards

Write the twelve raw fields of the 109 system, in increasing packing order, as

\[
 K_+,B_0,A_0,B_1,A_1,K_-,Z,D,C,V,T_C,T_V.
\]

They are supplied as strictly positive integer unknowns. Two source equations
are

\[
 B_0=A_0+T,\qquad B_1=A_1+T.                         \tag{1}
\]

The packed raw integer is the indicated base-\(q\) polynomial, denoted
\(P_{\rm raw}\). No claim that its coefficients are digits is needed at this
point. The 109 source imposes

\[
 2r+1=q^{12}+2P_{\rm raw},\qquad r+\beta=q^{12}.       \tag{2}
\]

The left side of the first equation reuses the Pell register
\(\mathtt{tr1}=2r+1\). The already charged power chain is
\(q^2,q^4,q^6,q^{12}\), costing four multiplications.

Delete the supplied unknowns \(B_0,B_1\) and their two equations (1).
Every occurrence of either symbol is replaced by its right side in (1).
Their only remaining occurrence was in the packing polynomial.

## 2. An exact packed identity

Set

\[
 Q=K_-+qZ+q^2D+q^3C+q^4V+q^5T_C+q^6T_V
\]

and define

\[
 G=(q+1)(A_0+q^2A_1)+(q^2+1)T.                       \tag{3}
\]

For arbitrary integers, expansion gives

\[
 G=(A_0+T)+qA_0+q^2(A_1+T)+q^3A_1,
 \qquad
 P_{\rm raw}=K_++q\bigl(G+q^4Q\bigr).                \tag{4}
\]

These are polynomial identities. They require neither a radix power,
coefficient bound, positivity, absence of carries, nor a decoded Boolean
word. Consequently they apply before all bounds and Pell arguments in the
109 proof.

The twelve semantic masks remain. The two guard words are computed
mathematically by (1) instead of being supplied independently; (4) puts them
in exactly their old positions, with exactly their old integer values.

## 3. Complete positive-witness equivalence

From any positive solution of 109, omit \(B_0,B_1\). Equation (1) and
identity (4) show that its new packing equation is true. All other retained
source equations are unchanged. In particular \(r,\beta,q\), all controller
coordinates and every Pell coordinate retain their values.

Conversely, from any positive solution of the new system, define
\(B_i=A_i+T\). Both are strictly positive because \(A_i,T\) are positive.
They satisfy (1), and (4) restores the old packing equation exactly. Every
other old equation is a retained equation. This reconstruction is unique.
The two maps are inverse positive-witness bijections for every fixed input
\(x\).

This argument precedes digit decoding. Thus the full 109 pre-kernel bounds,
power recovery, binomial divisibility, all twelve masks, controller and
counter semantics, input contract and parity apply to the reconstructed
solution. Conversely every canonical accepting computation of 109 gives a
new solution by deletion, without widening the radix or changing the
computation. In particular the positive Pell extension is precisely the old
one; it is not replaced by a finite test of selected auxiliary tuples.

The universal compiler and its prefix positivity annotations are unchanged.
They therefore establish the same represented recursively enumerable set
with 108 operations, for every fixed compiled program.

## 4. The full arithmetic saving

The old low part, starting from the already constructed \(Q\), uses five
Horner multiplications and five Horner additions. Constructing its two
supplied guard right sides costs another two additions. Its contribution is
therefore \(5M+7A\).

The new low part is constructed by these eleven instructions:

| Register | Operation |
|---|---|
| \(q_+\) | \(q+1\) |
| \(q_{2+}\) | \(q^2+1\) |
| \(a_s\) | \(q^2A_1\) |
| \(a_p\) | \(A_0+a_s\) |
| \(a_g\) | \(q_+a_p\) |
| \(t_g\) | \(q_{2+}T\) |
| \(G\) | \(a_g+t_g\) |
| \(Q_s\) | \(q^4Q\) |
| \(P_i\) | \(G+Q_s\) |
| \(P_s\) | \(qP_i\) |
| \(P_{\rm raw}\) | \(K_++P_s\) |

This is \(5M+6A\). The existing four-operation power chain is moved before
packing so its \(q^2,q^4\) registers are available; it is not duplicated.
The other operations are unchanged. The resulting count is

\[
 109-1=108=55M+53A.
\]

The new source has 24 equations and 36 positive unknowns. The checker
symbolically verifies every primitive and every source comparison. As in
109, the auxiliary norm comparison uses the retained preceding norm
residual times \(u^2-y^2\), where \(u=2r+1+jc\); that required correction is
checked after the source indices shift by two.

## 5. Evidence scope

The exact source check establishes all 24 new comparisons, both eliminated
equations after substitution, equality of the complete packed polynomial,
and the 108-operation count. The focused integer check covers 3,000 cases
including signed entries, non-power radices and overflowing coefficients;
these are polynomial checks, not additional solution claims.

The canonical routine freshly reruns the complete numerical 110 checker for
inputs 1 and 2, then applies the freshly checked 110-to-109 and 109-to-108
identities. The same integer packing and every retained coordinate are
preserved. Its receipt labels the 17 checked 110 outer equations, the 16
transported 109 outer equations and the 14 transported 108 outer equations
separately. The twelve positive conceptual raw fields remain twelve masks;
ten are supplied and two are reconstructed. No enormous Pell tuple is
numerically instantiated by this routine.
