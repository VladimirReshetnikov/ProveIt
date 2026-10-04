# The unprotected auxiliary nine-gate frontier

For the joint outputs

\[
 V=cTf-c-Rf^2,\quad Q=\Delta^2i^2c^4,\quad
 S=\Delta f^2-Q,
\]

a circuit of at most nine gates, if one exists, must have **exactly five nonconstant multiplications and four additions**. Exactly one addition must cancel nonmonomial terms to produce a monomial U. Up to a nonzero scalar, U must be one of these **17** monomials:

\[
 \boxed{\Delta^a c^b i^2\ (0\le a\le2,\ 0\le b\le4),
 \qquad \Delta c^2i,\qquad \Delta^2c^4i.}
\]

These are necessary conditions, not realizable nine-gate candidates. There is no new operation reduction. The current ten-gate schedule remains the upper bound, and its complete84-row splice is retained in the receipt. Unlike the previous protected-cut theorem, the new conclusions permit arbitrary interleaving of all producers and do **not** fix either Q's construction or the final subtraction for S.

The [fresh helper](complete84_auxiliary_nine_gate_frontier.py) and [receipt](complete84_auxiliary_nine_gate_frontier.json) check the exact finite premises, enumerate the remaining monomial shapes, and authenticate the complete attaining source. The unbounded circuit arguments are proved below, not inferred from sampling or a bounded program search.

## 1. Model and inherited lemmas

The independent variables are Delta,c,i,f,T,R. The only extra paid ports are the dependent monomials c² and Delta*c². Work over the rational polynomial ring; constants and scalar multiples may be free in the lower-bound relaxation. A scalar-weighted binary sum costs one addition, and a product of two nonconstant expressions costs one multiplication. Free arbitrary linear combinations are permitted only when proving a multiplication-only lower bound. Any actual binary `+,-,*` circuit of at most nine paid gates satisfies the resulting necessary conditions.

Write W=Delta*f² and P=f²−Delta*i²*c⁴, so S=Delta*P. The pinned [mixed-cut proof](complete84_auxiliary_mixed_cut.md) supplies these lemmas:

1. V needs at least three nonconstant multiplications, even after setting Delta=i=0 and giving additions free, with c² still paid.
2. V and W jointly need at least four nonconstant multiplications with the original paid ports.
3. V and S jointly need at least three additions, even if all monomials are supplied free.
4. With exactly two additions, V has only three monomial-grouping forms: a sum of its three monomials, c(Tf−1)−Rf², or f(cT−Rf)−c. This follows from irreducibility and its noncollinear three-term support, not a restriction on multiplicative depth.

The present theorem does not enlarge those paid-port sets when invoking the first two lemmas. In particular, an internally computed cancellation pivot is never silently made a free port in a multiplication-count argument.

## 2. Five products without protecting any row

Give additions free. Every circuit output lies in the scalar linear span of the original paid ports and multiplication outputs g1,...,gm. The classes of Q and S modulo the paid-port span are linearly independent: on the independent classes W,Q they have coefficient rows (0,1) and (1,−1), with determinant −1. Neither the degree-three monomial W nor the degree-eight monomial Q belongs to the original paid span.

Set Delta=i=0. Both outputs Q,S become zero, giving two independent scalar relations among the specialized multiplication outputs and paid ports. Row-reduce these relations with the largest multiplication indices as pivots. Each pivot output is thereby expressed using paid ports and earlier product outputs. Substitute these expressions at all later uses and delete the two pivot multiplications. This preserves the specialized computation of V, using at most m−2 products and free additions. Lemma1 gives

\[
 \boxed{m\ge5.}
\]

The argument does not assume that either original pivot gate computes a monomial or individually specializes to zero.

## 3. Exactly three additions force seven products

If a three-addition circuit had a monomial-valued addition, including a zero value, supply that value free and remove that addition. The remaining two-addition circuit would contradict Lemma3. Thus all three addition outputs are nonmonomial.

Q is a monomial. A product containing a nonmonomial factor cannot become a monomial in this polynomial ring. Therefore its entire ancestor cone consists of monomial products and paid monomials; no addition contributes to Q.

Let the addition outputs in chronological order be g,h,k. Between additions each wire is a monomial times nonnegative powers of the previous addition outputs. V is irreducible with no monomial factor, so its output must be, up to scalar, one of these addition outputs itself. It cannot be g, which is only a binomial. S has the single nonmonomial irreducible factor P with multiplicity one; hence the addition output from which S is obtained by products must be, up to scalar, either P or Delta*P. That addition is different from the one producing V.

### V is the second addition

Lemma4 shows that g groups two V monomials, so both g and h=V are independent of Delta and i. The remaining addition k, which supplies S's core, has two operands of the form monomial times powers of g and h. Each operand therefore has one (Delta,i) multidegree. Both P and Delta*P have two different such multidegrees. The two operands must occupy different multidegrees, so no cancellation between them can remove unwanted terms within either operand. Each must itself be one of the required monomials. S's core is consequently formed by a single addition of monomials, and its construction uses neither g nor h.

### S's core is the first addition

Now g is a scalar times P or Delta*P. Reduce modulo P and localize c and i, substituting Delta=f²/(i²c⁴). V remains its three noncollinear Laurent monomials, while g becomes zero.

Write h=m*g^r+n*g^s. If either exponent is positive, h reduces to zero or a single Laurent monomial. The final addition for V would then reduce to at most two Laurent monomials, a contradiction. Hence r=s=0: h is a binomial of monomials independent of g as a circuit expression.

If an operand in the last addition contains a positive power of g, its reduction is zero. The sole remaining operand is a Laurent monomial times a power of a Laurent binomial, whose support is collinear; it cannot equal V. Both last operands therefore use no g. V is built from h by its two-addition grouping of Lemma4, separately from S's single binomial addition.

### S's core is the second addition

Here h is a scalar times P or Delta*P, and k=V. Write h=m*g^r+n*g^s.

If r,s are both positive, g divides h. As g is nonmonomial and h has only the nonmonomial factor P, g also vanishes modulo P. Both g and h then vanish there, and the final addition gives at most two Laurent monomials, again impossible.

If r=s=0, h is an addition of monomials independent of g. The same quotient argument as in the previous case, with the first two additions interchanged, forces V to use g but not h. This is again the separate two-addition V and one-addition S structure.

It remains to consider exactly one positive exponent, so h=m*g^r+n with r positive. Because h has two terms, both with T/R multidegree (0,0), g must also be independent of T and R. To see this explicitly, expand the binomial power. If its two monomials have the same nonzero T/R multidegree, every term has that nonzero multidegree and a single extra monomial cannot cancel all the distinct terms. If their T/R multidegrees differ, the r+1 expanded terms have distinct such multidegrees; at most one is (0,0), and the extra monomial can cancel at most one other term. The exponent-one exception leaves only a monomial, whereas h has two surviving terms. Thus this exception is impossible too. Both g and h lack T and R. Each operand of the last addition then has just one T/R multidegree, so their sum has at most two, while V has three. This finishes the classification.

These cases exhaust all addition placements. They require no protected coefficient or final-subtraction row.

### Counting the products in the classified forms

S's sole binomial addition is either directly W−Q, or f²−Q0 followed by multiplication by Delta, with Q0=Delta*i²*c⁴.

* In the direct case, the V grouping and the required W together need at least five products by the exact divisor counts in the mixed-cut proof. The monomial Q needs at least two products. No new monomial product can be shared between Q and those V/W cones: the relevant greatest common divisors are only1,c or Delta, already paid. Mixed products containing V's binomial cannot occur in Q's monomial cone. Total: at least seven.
* In the unscaled-core case, V together with f² needs at least four products. The three V groupings give respectively 2+2+1−1, 1+2+1−1+1 and1+1+1+1. Q still needs two separate products, and multiplication of the nonmonomial P by Delta needs one more. The additional Q0 obligation can only raise the cost. Total: at least seven.

Thus

\[
 \boxed{A=3\quad\Longrightarrow\quad M\ge7.}
\]

Together with M≥5 and A≥3, any circuit of at most nine gates must have exactly **M=5,A=4**. In particular, six multiplications and three additions cannot work, even with arbitrary producer interleaving.

## 4. Monomial coefficient cones cannot give nine gates

Suppose Q has a pure monomial-product cone, without restricting its association or intermediate monomials. It must contain at least two product outputs with positive i exponent. Otherwise Q itself is the sole such output. Its operands can then only obtain i from the supplied variable i: degree two in i forces both operands to be scalar multiples of i, giving only a scalar i² and missing Delta²*c⁴.

Set i=0 and replace those two monomial product outputs by literal zero, deleting their two multiplications. Keep every other computation. The remaining circuit produces V and S|i=0=W from the original paid ports, so Lemma2 requires at least four remaining products. Therefore

\[
 \boxed{Q\text{ has a monomial-product cone}\quad\Longrightarrow\quad M\ge6.}
\]

This permits arbitrarily many additions elsewhere. Combining it with Section3 excludes every nine-gate circuit of this type, even if its final S subtraction and all other producers differ from the parent.

More generally, in any five-product circuit computing V,Q,S there can be **at most one multiplication output anywhere** that is a nonzero monomial with positive i exponent. Two such outputs could be deleted by the same specialization, leaving only three products for V,W. This observation will control the last steps after a cancellation pivot.

## 5. A unique genuine cancellation and its 17 possible values

In the remaining five-product/four-addition budget, at most one addition can have a monomial value: supplying two such values free would leave at most two additions for V,S, contradicting Lemma3. There must be at least one such addition on a path to Q; otherwise Q has a pure monomial-product cone and Section4 applies. Thus there is exactly one; call its nonzero output U.

This addition genuinely cancels nonmonomial terms. An addition of monomial operands whose output is monomial is merely a scalar alias or zero and can be removed in the lower-bound model, leaving the excluded three-addition case. The same excludes an output already available up to scalar. After U, every path contributing to Q is monomial multiplication. Hence U is a monomial divisor of Q, with no f,T,R factors.

U cannot be i-free. If it were, Q's monomial part, treating U as an i-free input, would still contain at least two i-containing product outputs. At i=0 delete just those product gates, and **retain and count the entire original computation of U**. The remaining at-most-three multiplications still compute V,W from the original paid ports, contrary to Lemma2. This does not supply U, c³ or c⁴ as new paid ports; even if U specializes to such a power, every gate that produces it remains charged.

Write U=Delta^a*c^b*i^e up to nonzero scalar. Necessarily 0≤a≤2,0≤b≤4, and e is1 or2. Section4 allows at most one pure i-containing product in the entire five-product circuit. Above U, Q must therefore be one of:

* U itself;
* U times an i-free monomial H;
* U²;
* U*i.

There is no other i-containing computed monomial available for an operand: producing it and then multiplying to obtain Q would already use two i-containing products. Arbitrary i-free intermediates are harmless for this necessary-shape argument.

For e=2, all15 exponent choices (a,b) survive this necessary test, with H=Delta^(2−a)*c^(4−b), including the alias case H=1. For e=1, the square case forces (a,b)=(1,2), and the product by i forces (a,b)=(2,4). These are exactly the17 boxed values. The helper enumerates all30 positive-i monomial divisors of Q and verifies this precise one-product shape census, while relaxing every i-free divisor to an available operand only for this enumeration.

None of these17 values is asserted to have a sufficiently cheap cancellation construction compatible with V and S. The result identifies the remaining task: either construct such a full five-product/four-addition circuit, or exclude its cancellation pivot. Mere multiplication reassociation, a different S subtraction, or mixed V/W factorization cannot reach nine.

## 6. Complete source and evidence

The receipt retains the complete original84 source and a fully paid attaining source with the mixed quotient form

    f2=f*f;
    cT=c*T; Rf=R*f; inner=cT-Rf; V=f*inner-c;
    Uroot=i*Ac2; Q=Uroot*Uroot;
    W=Delta*f2; S=W-Q.

Here Uroot is the existing multiplication-built coefficient root, not the hypothetical cancellation pivot of Section5. The cut has7M+3A. The helper reconstructs the five-row splice independently, compares it with the pinned mixed receipt, expands all four local polynomials exactly, checks every external cut consumer, and verifies all other rows are literally retained. All84 rows and25 supplied ports remain live, with47M+37A and the same18 positive witnesses. The full polynomial identity and degree187 follow from the exact V replacement and unchanged consumers. No new lower-count source is claimed.

Finite certificates in this receipt are the independent Q/S relation matrix, exact quotient/support checks, all three divisor-count cases and the17-shape census. They support the mathematical normal-form and specialization proofs; they are not presented as machine formalization of arbitrary circuits. No bounded numerical sample is used to justify an exclusion, and no positive compiler zero is newly materialized.

| Inert dependency | SHA-256 |
|---|---|
| `complete84_scaled_strong_output.py` | `8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737` |
| `complete84_scaled_strong_output.json` | `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf` |
| `complete84_scaled_strong_output.md` | `01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade` |
| `complete84_auxiliary_mixed_cut.py` | `a77f326d98550ed21643d5f1ea2aa25d9dca7d9a7fdca26c40e8bf1cdf80c13a` |
| `complete84_auxiliary_mixed_cut.json` | `1aa60da5b6b7278efdfd8535d10ec8f9af604b729b1f95c124eca714721dfc47` |
| `complete84_auxiliary_mixed_cut.md` | `b16bcf8b4013345d25a5d2bbb0598ae2caaaeaa31a529e00af7ea4647d78d7f2` |

```sh
frontier_wip=/absolute/path/to/native-stream-queue
python3 "$frontier_wip/complete84_auxiliary_nine_gate_frontier.py" \
  --root "$frontier_wip" --expect "$frontier_wip/complete84_auxiliary_nine_gate_frontier.json"
python3 -O "$frontier_wip/complete84_auxiliary_nine_gate_frontier.py" \
  --root "$frontier_wip" --expect "$frontier_wip/complete84_auxiliary_nine_gate_frontier.json"
```

The helper rejects duplicate/nonfinite JSON and compares receipts with recursively type-exact equality. All guards remain active under optimized Python. Fresh normal and optimized exact replays from `/` pass. Predecessor files are read only as inert data; none is imported or executed. No repository file is modified.
