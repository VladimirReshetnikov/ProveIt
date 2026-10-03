# Sharing an AND input gives63/64 and selected-source117/119

Reusing one already required input-port sum in the selector checksum saves
one addition in every [masked-selection parent circuit](native_binary_masked_selection65.md).
The complete unrestricted binary AND component now costs **63=32M+31A**;
its prescribed-scale version costs **64=33M+31A**. The corresponding
uniform eight-product components cost **117=55M+62A** and
**119=57M+62A**. No domain, comparison, typing obligation or positive
witness changes. Every comparison residual is the same polynomial as
in its parent, on arbitrary supplied integer assignments.

These are local arithmetic components. The interpretation as eight
selected-source products still requires the cell geometry and Boolean
selector semantics stated below. There is no complete universal
Diophantine certificate in this packet.

## 1. The literal shared checksum

The parent circuit computes its four-class checksum using four additions,
then separately computes both AND input ports:

    bs_sum01=F0+F1;
    bs_sum012=bs_sum01+F2;
    bs_Q=bs_sum012+F3;
    final_checksum=bs_Q+1;
    input_A=F1+F3;
    input_B=F2+F3.                                    (1)

The final register is q in the unrestricted versions, where the checksum
defines the kernel scale. It is bs_q in the prescribed-scale versions,
where the existing comparison bs_q=q is retained.

Replace (1) by five additions:

    input_A=F1+F3;
    shared_sum02=F0+F2;
    bs_Q=shared_sum02+input_A;
    final_checksum=bs_Q+1;
    input_B=F2+F3.                                    (2)

Compute input_A and the checksum immediately after F3, before any
q-dependent packing. The input_B gate may keep its original position.
The positive supplied F0,F1,F2 and the always positive computed F3 give
the same q as before; no circular dependency on the Pell core occurs.
The two obsolete partial sums bs_sum01 and bs_sum012 have no other users
in these AND sources. In particular no NAND output using the latter is
being claimed or silently deleted.

The identity

    (F0+F1)+F2+F3 = (F0+F2)+(F1+F3)

proves that bs_Q, the final checksum and both input ports are unchanged
on every assignment. Every other literal gate is retained, up to its
position in the acyclic schedule. Thus every comparison residual and
any fixed sum-of-squares compilation are identical polynomials to the
parent versions. The saving is one actual addition; no power, multiply
by a fixed numeral or equality test has become a free instruction.

## 2. Complete AND projections and positive domains

For the unrestricted63 component, the positive relation arguments are
Hhat,Mhat,Zhat. Its exact projection is

    Zhat-1 = (Hhat-1) AND (Mhat-1).                    (3)

Supply the same22 positive auxiliaries as its refined64 parent:

    F0,F1,F2,
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux,
    odd_half,bound_beta.

The source computes F3=16Zhat-8>=8. The shared checksum computes
q=F0+F1+F2+F3+1>=12 before any equation; the selector theorem recovers
q as a power of two, hence q>=16. Its kernel scale n2 is literally
aliased to q, and no positive q witness is supplied. The15 comparisons
are the retained parent comparisons, including both padded input ports.

For the prescribed-scale64 component, P is an additional positive
relation argument and q=16P remains a paid multiplication. Its16
comparisons include the retained checksum comparison. Its exact
projection is

    P=2^ell, ell>=0,
    H=Hhat-1, M=Mhat-1, Z=Zhat-1,
    0<=H,M<P, Z=H AND M.                              (4)

Both versions retain the four-bit truth prefix: input words16H+12 and
16M+10, output16Z+8, and low-first class labels0,2,1,3. This guarantees
all four positive truth classes, including when the unpadded words are
zero or empty. The tuple P=1,H=M=Z=0 remains admitted in (4).

The unchanged comparison polynomials give a bijection of the complete
positive solution sets with the respective parent on exactly the same
coordinates: the map is the identity. In particular the parent's full
parametric positive Pell extension is inherited, rather than inferred
from a finite truth-table sample. This preserves both directions of
(3)--(4) and all nineteen retained Pell/outer auxiliary positivity
requirements.

## 3. Eight selected-source products and canonical history digits

Retain positive parameters P,B, four positive histories H_j, eight
positive selector hats Shat_i, and eight positive output hats Zhat_i.
Decode S_i=Shat_i-1, Z_i=Zhat_i-1, and use the source-lane order

    j(i)=(1,1,0,0,3,3,2,2).

Both batch sources compute the same concatenations as their parents:

    Hb=sum_i H_(j(i))*P^i,
    Mb=(B-1)*sum_i S_i*P^i,
    Zb=sum_i Z_i*P^i,       i=0,...,7.                 (5)

The general source supplies eight positive beta_i and keeps

    Zhat_i+beta_i=P+1.                                (6)

The exclusive source instead supplies one positive beta and keeps

    sum_i Zhat_i+beta=P+1.                            (7)

Equation (6) enforces exactly0<=Z_i<P. Equation (7) enforces exactly
`sum_i Z_i<=P-8`; positivity then implies each Z_i<P. These are paid
scalar bounds, not new digitwise typing assumptions.

For117, the exact scalar projection is `Zb=Hb AND Mb` together with
(6) or (7), as appropriate. It does not prove a power condition on P.
For119, the source retains q=16P^8 and additionally proves that P is a
power of two and Hb,Mb<P^8. Its output and scalar bounds are the same.
These exact scalar projections follow from the complete parent AND
predicate and the unchanged comparisons.

To interpret either batch as cellwise selection, suppose

    B=2^b, P=B^t, b,t>=1,
    0<H_j<P,
    S_i=sum_(k=0)^(t-1) s_i(k)B^k, s_i(k) in{0,1}.    (8)

The canonical base-B digits h_j(k) of H_j automatically belong to
`0,...,B-1`. **Internal zero history digits are permitted.** The positive
whole-field bounds in (8) suffice; no positive lower bound on every
individual history digit is needed for this mask argument.

The word `(B-1)S_i` has either all zero or all one bits in each binary
cell. Since both it and H_(j(i)) are below P, the two input numbers in
(5) have eight nonoverlapping binary blocks of width log2(P). The global
AND and the paid output bounds give the unique base-P output chunks.
Therefore soundness recovers exactly

    Z_i=sum_k s_i(k)h_(j(i))(k)B^k, for i=0,...,7.     (9)

The general source is complete for every tuple satisfying (8)--(9): use
beta_i=P-Z_i>0 and the parent's positive AND extension.

For the exclusive source, soundness of (9) uses only (8), the global
AND and the paid bound (7). It does **not** need mutual exclusion of
selectors or a half-radix bound on the history digits. Its precise
completeness condition is that the correct selected outputs also satisfy
`sum_i Z_i<=P-8`, so beta=P-sum_i Z_i-7 is positive.

A useful sufficient completeness condition, already met by the matrix
history construction, is

    B>=16, 0<=h_j(k)<B/2,
    at most one of the eight s_i(k) is1 at each k.     (10)

Then `sum_i Z_i < P/2` and P>=16, so beta>0. A stronger quarter-radix
history margin also suffices. Conditions (10) provide a positive witness
for every genuine selected history; they are not inferred from the AND
source and are not prerequisites for its sound output decoding. The
regular controller, selector typing and shared physical duration remain
external obligations. The ordinary numerical input is not recoded or
otherwise altered by this local checksum change.

## 4. Exact ledgers and polynomial costs

The [source](native_binary_masked_selection63.py) constructs each successor
from the actual frozen parent schedule and deletes precisely one addition.
Its [receipt](native_binary_masked_selection63.json) includes every literal
DAG, comparison list and supplied witness list.

| Component | M | A | Total | Positive auxiliaries | Equations |
|---|---:|---:|---:|---:|---:|
| Unrestricted AND |32|31|63|22|15|
| Prescribed-scale AND |33|31|64|22|16|
| General batch, unrestricted AND |55|62|117|30|23|
| General batch, prescribed scale |57|62|119|30|24|
| Exclusive batch, unrestricted AND |55|62|117|23|16|
| Exclusive batch, prescribed scale |57|62|119|23|17|

Forming each residual, squaring it and summing gives these independently
counted single-polynomial ledgers:

| Component | M | A | Polynomial operations | Exact degree |
|---|---:|---:|---:|---:|
| Unrestricted AND |47|60|107|28|
| Prescribed-scale AND |49|62|111|28|
| General batch, unrestricted AND |78|107|185|112|
| General batch, prescribed scale |81|109|190|112|
| Exclusive batch, unrestricted AND |71|93|164|112|
| Exclusive batch, prescribed scale |74|95|169|112|

These polynomials are identical to the corresponding parent's literal
sum of squares; they are evaluated with one fewer addition. Exact degree
is preserved. Explicitly, the unique highest contribution is the square
of the first Pell-norm residual, whose highest form is
`w^2*s^4*k^2*q_top^6`. The highest scale forms are

    F0+F1+F2+16Zhat          unrestricted AND,
    16P                     prescribed-scale AND,
    16Zhat_7*P^7             unrestricted batches,
    16P^8                   prescribed-scale batches.

They are nonzero, giving exact SOS degrees28 and112. Fixed numerals
have degree zero, while all supplied relation arguments and witnesses
have degree one. The polynomial compilation preserves the declared
positive witness domains and, for the selected-source interpretation,
the explicitly conditional semantics in Section3.

## 5. Exact checks and remaining scope

Default execution replays the deterministic receipt. For each of the six
variants the checker proves symbolic equality of all common registers and
all comparison residuals with the parent, and independently verifies the
imported selector residuals with its auxiliary correction. On512 further
assignments per variant,384 positive and128 signed, it verifies all
residuals and the complete sum-of-squares value. Signed cases audit only
polynomial identities. A weighted offset specialization per variant
checks the exact total degree and highest coefficient.

Another1,536 canonical-history fixtures verify the selected outputs,
including internal zero history digits, for both prescribed and
unrestricted scales. Half use arbitrary independent selectors; half use
mutually exclusive selectors and check the positive global-bound witness.
The outer data admit full positive Pell extensions by the parent theorem;
these tests do not materialize the enormous Pell coordinates.

No new typing is assumed in the circuit saving: (1) and (2) are equal
integer polynomials. The open uniform-computation problem still includes
cell geometry, Boolean selector typing, regular control and linking the
history duration to other native powers. This packet pays the selected
products conditionally and improves their arithmetic evaluation; it does
not settle those remaining obligations.

Two independent full proof and source reviews passed without findings.
They checked the five-addition checksum, its acyclic placement, unchanged
positive domains and residuals, all six ledgers and leading forms, and
the canonical zero-digit interpretation with its distinct exclusive
completeness condition. One review additionally replayed the default
receipt and compared every surviving residual and both ports against
the parent on 1,536 independent signed assignments. These off-zero
identity checks supplement the exact polynomial identities and positive
projection proofs; they are not used as a bounded universality argument.
