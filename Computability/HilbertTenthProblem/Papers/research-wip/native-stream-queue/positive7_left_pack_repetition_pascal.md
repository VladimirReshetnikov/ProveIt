# Factoring the repeated high left-pack blocks

The unchanged high left pack in root's first repeated-pack compiler admits
an exact polynomial schedule costing

    (20+3r)M+(16+2r)A,

instead of its literal Horner cost(53+4r)M+(53+4r)A. All new powers,
block producers and joins are included. Relative to that high-left cut,
the saving is(33+r)M+(37+2r)A, or70+3r operations. The schedule uses
only the powers already paid in root's first compiler and explicitly paid
additional records below. No extra credit for another stage's powers
has been taken.

This is a local proof/count result, not an emitted complete compiler. It is an
identity for every integer assignment to the displayed cut. Root proposed
the repeated-block route and the shortened-history identity. The author
derived the reuse of the first Horner intermediate in that identity.

## 1. Exact inherited lane grammar

Use r>=1, m=8+2r and ell=62+6r. A pack has low-to-high convention

    pack(x_0,...,x_(n-1))=sum_i x_i*P^i.

The left selector prefix has length m and is already handled by root's
shared selector polynomial Q and the join P^m*L+Q. This note changes
only L, the high word beginning at original lane m.

The high word has52+4r selected lanes followed by aggregate lane S
and height lane D. Its selected lanes are, in low-to-high slot order:

* slots0,1: the identical block(H2,H3,H4,H5,H6,H7);
* slots2,3: the identical block(H1,H2,H3,H4,H5,H7);
* slots4,5,6,7: the identical block(H1,H2,H3,H4,H5,H6,H7);
* for j=1,...,r, the plus and minus slots of relator j both use the
  identical block(A_(j,1),A_(j,2)).

Here A_(j,1),A_(j,2) are the already computed common-center forms.
Their equality across the two signs is a fact of the source interface;
the associated selectors and selected-output words need not be equal.
The paired retained-port lists come from the paid sparse action note.
The two-form note specifies the relator lane order and the final two
lanes. These lane statements are read as text, not evaluated as arrays.

The literal old computation starts at D and descends through every
remaining high lane. There are54+4r high lanes, so it uses53+4r
multiplications by P and53+4r additions. Its selector-prefix work is
outside this count and remains outside every new count below.

## 2. Powers and all supporting records

The already paid cut from root's first repeated-pack compiler supplies P and

    P2=P^2, P3=P^3, P6=P^6, P7=P^7.

Its other geometric sums and P^m may remain in use elsewhere. This
construction does not need to charge them again. Prepare these new
records, with all displayed additions and products charged:

    P4=P2*P2; P5=P2*P3; P12=P6*P6;
    P14=P7*P7; P28=P14*P14;
    U4=1+P2; U6=1+P6; U7=1+P7; U14=1+P14;
    G7=U7*U14.                                          (1)

This is6M+4A. In particular

    G7=1+P^7+P^14+P^21=R_4(P^7).

No geometric-series division, nonzero hypothesis or positivity premise
is used. The formulas include P=0, P=1 and negative P.

## 3. Three history blocks from one Horner producer

Starting from H7, compute the six descending Horner steps through
H6,H5,H4,H3,H2,H1. This costs6M+6A and produces

    B7=H1+P*H2+P^2*H3+P^3*H4+P^4*H5+P^5*H6+P^6*H7.

Retain the first and penultimate intermediate words

    K=H6+P*H7,
    B6a=H2+P*H3+P^2*H4+P^3*H5+P^4*H6+P^5*H7.           (2)

They are already paid nodes of this same producer. Define the other
six-field block by

    diff=K-H7; correction=P5*diff; B6b=B7-correction.      (3)

These three records cost1M+2A. Expanding just the two top terms of B7
gives

    B6b=H1+P*H2+P^2*H3+P^3*H4+P^4*H5+P^5*H7.           (4)

Indeed the subtracted polynomial is
P^5*(H6+(P-1)*H7). Root's proposed formula is therefore exact; retaining
K avoids recomputing the product(P-1)*H7. P5 itself was fully paid in(1).
No division or truncation of packed words is performed.

## 4. Descending block joins

First initialize the top tail by

    acc=D*P+S,                                           (5)

at1M+1A. Descend through the relators in order j=r,...,1. The four
low-to-high entries under the current accumulator are(A1,A2,A1,A2),
where A1=A_(j,1),A2=A_(j,2). Use

    pair=P*A2+A1;
    repeated=U4*pair;
    acc=P4*acc+repeated.                                 (6)

This is3M+2A per relator, and equals appending those four entries
because(1+P^2)*(A1+P*A2)=A1+P*A2+P^2*A1+P^3*A2.

Next append the four identical seven-field blocks by

    repeated7=G7*B7; acc=P28*acc+repeated7,                (7)

at2M+1A. Finally append the two six-field pairs, in descending slot
order, by

    repeated6b=U6*B6b; acc=P12*acc+repeated6b;
    repeated6a=U6*B6a; acc=P12*acc+repeated6a.             (8)

Each line costs2M+1A. The final accumulator is L.

For any low block b of length n, appending two identical copies below
a higher word a gives P^(2n)*a+(1+P^n)*b. Four copies give
P^(4n)*a+(1+P^n+P^(2n)+P^(3n))*b. Applying these polynomial identities
in the specified descending order proves that(5)--(8) is the original
high word for every integer runtime assignment. The proof uses neither
selector exclusivity nor a native projection theorem.

## 5. Complete local ledger and limitations

The components are all charged once:

| Component | M | A |
| --- | ---: | ---: |
| Supporting records(1) | 6 | 4 |
| B7 with retained K,B6a | 6 | 6 |
| B6b correction(3) | 1 | 2 |
| High tail(5) | 1 | 1 |
| r relator pairs(6) | 3r | 2r |
| Four seven-field copies(7) | 2 | 1 |
| Two six-field pairs(8) | 4 | 2 |
| Total | 20+3r | 16+2r |

Subtracting from the old high-left Horner cost gives exactly
(33+r)M+(37+2r)A. The already shared selector prefix Q and the final
P^m*L+Q join are unchanged. Neither the right pack nor the output pack
is modified. Therefore a correct complete-source splice would preserve
all three packed polynomials, every native residual and the final
polynomial on the same supplied tuple. That source has not been emitted
or audited by this local note.

**Remark 1 (left repetitions do not identify selected outputs).** The
repetition used above is literal equality of the left input expressions.
It does not identify the selected outputs of different letters. For
example at P=2, two equal left inputs can accompany output values0 and1;
their two-lane output polynomial is2, whereas duplicating the first
output gives0. This arbitrary-integer cut example is not a complete native
zero. No output-pack reduction follows merely from the left repetition.

**Remark 2 (possible power reuse is not an unpaid credit).** Another
stage or the geometric extension for a particular m might already
produce some of P4,P12,P14,P28. The uniform local ledger deliberately
pays every new record in(1) beyond the explicitly stated shared cut.
An additional credit needs actual producer/consumer identification in
the complete source, with the producer moved or aliased as appropriate.
No such credit, and no r=0 source change, is included here.

**Open question 1 (complete composition, credited to root).** Emit and
audit the exact replacement of the unchanged high-left Horner rows in
the first repeated-pack successor, paying shared powers only once while
retaining every other consumer and native lane. Only then may a complete
compiler total incorporate this local saving. The universal relator list
remains unmaterialized numerically; no numerical universal bound or
generic optimality statement follows from this draft.

## 6. Provenance and execution boundary

Root supplied the actual repeated-block lane pattern, the relator and
four-copy geometric factors, and the B6b deletion identity. The author
checked them by handwritten expansion, derived the reuse of K in(3),
and counted every support and consumer operation. Root read the complete
197-line draft and independently checked all identities, descending order,
K reuse and the fully paid ledger, requesting no correction. Riemann
independently challenged the entire mathematical schedule and ledger by
hand, including the lane order and P=0,1 boundaries, with no correction.
These challenges certify the local proof, not an emitted replacement.

The author subsequently read all of the frozen parent proof,
positive7_repeated_pack_compiler_root.md, and bound its exact bytes in
the metadata. Its complete source and separate source audit are outside
this note's read scope. The earlier parent draft remains recorded only
as historical proof-reading provenance.

Dependencies are inert mathematical text. No supplied, archived,
committed, predecessor or frozen helper has been executed or imported;
no saved scientific source or coefficient array has been evaluated or
degree-propagated. No scientific sampling, emitter or build has been
used. Any companion receipt records fresh byte/read-span metadata only.
New files remain in/tmp; repository files, Git and previous frozen
artifacts are unchanged.
