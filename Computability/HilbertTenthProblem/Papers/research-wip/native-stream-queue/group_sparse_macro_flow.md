# Shared hub-path flow lowers the complete matrix compiler

The [complete matrix compiler](group_complete_matrix_compiler.md) can
evaluate the same polynomial more cheaply by sharing state-flow
arithmetic along its fixed macro paths. No native kernel, supplied
coordinate, physical edge or comparison is removed. **Every comparison
residual is identical on arbitrary integer assignments**, so the full
positive theorem and both directions of its witness construction are
preserved on exactly the same coordinates.

Let m=2^h be the unchanged padded edge count and p its unchanged physical
port cost. Let L be the total length of the nonempty macro codes, n the
number of internal states, and b the number of codes of length at least
two. An explicit table-dependent flow cost f_flow, defined below, obeys

    f_flow<=2n+2b<=2L.

The complete certificate now costs

    3m+3h+p+272+f_flow,

with the same **60 equations** and **m+87 strictly positive witnesses**.
Its literal SOS polynomial costs

    3m+3h+p+451+f_flow

and remains exactly the parent's polynomial, of exact degree
**max(112,12m+16)**. This is a fixed-table compiler improvement, not a
numerical instantiation of the universal subgroup alphabet or a new
bound below88 operations.

## 1. The unchanged table and its four edge classes

Use the canonical table construction in
[regular macro control](group_regular_macro_controller.md). Each code
has its own hub-to-hub path; all positive state codes are distinct and
numbered consecutively along each path. The set of positive states is
`{1,...,n}`, with one incoming and one outgoing edge at each such state.
The identity hub loop and all duplicated padding loops remain. Codes
of length one are also direct hub-to-hub edges.

For an edge e, let a_e,b_e be its fixed source and target state codes,
and let Ehat_e be its strictly positive supplied edge hat. Define the
four disjoint classes:

| Class | Source and target | Number |
|---|---|---:|
| I, internal | a_e>0, b_e=a_e+1 | k=n-b |
| F, first | a_e=0, b_e>0 | b |
| L, last | a_e>0, b_e=0 | b |
| H, hub | a_e=b_e=0 | remaining edges |

Here n=sum_codes(length-1), and k=sum_codes max(length-2,0). The source
validates the consecutive-state and unique-incidence properties before
applying the rewrite. It does not silently apply this specialization to
an arbitrary branching graph with the same number of edges.

Only the addition tree of the existing edge checksum is reordered.
The actual table, edge indices and their packed radix-P lane order are
unchanged. No physical word is changed by this arithmetic reassociation.

## 2. Group sums already paid by the edge checksum

The parent computes `sum_e Ehat_e` using m-1 additions and compares it
with J+m. Sum each nonempty class separately, then sum the class totals.
If there are g nonempty classes, this uses

    sum_classes(size-1)+(g-1)=m-1

additions, exactly the same number. The resulting raw class sums

    R_I=sum_(e in I) Ehat_e,
    R_F=sum_(e in F) Ehat_e,
    R_L=sum_(e in L) Ehat_e

are now available to the flow circuit without an additional sum. Empty
class sums are the fixed zero; singleton sums are aliases of their hat.
The checksum's residual is unchanged as an integer polynomial. The
subset kernel and positive proof order in the parent still apply.

The word “available” here means actual computed registers in the source,
not mathematical abbreviations treated as free additions. The checker
records the exact group-sum instructions and verifies that their count
is m-1 for every table.

## 3. A shared weighted word and one common correction

Put C=n(n+1)/2, a fixed compiler numeral, and compute

    V=sum_(e in I) a_e Ehat_e,
    F=sum_(e in F) b_e Ehat_e,
    Lw=sum_(e in L) a_e Ehat_e.                        (1)

Every positive state appears exactly once as a source and once as a
target. Therefore both total hat corrections are C. Since an internal
edge has target coefficient a_e+1, the two parent state words are
identically

    A=V+Lw-C,
    T=V+R_I+F-C.                                      (2)

When k>0, compute W=V-C once, then A=W+Lw and T=W+R_I+F, and compare
A with B*T. This shares every internal weighted term between the
source and target words. It also shares the correction C and the raw
internal sum already produced in Section2. Formula(2) holds for
arbitrary signed Ehat values; no Boolean digits, checksum equation,
state path or positivity hypothesis is used in this identity.

This is more than deleting zero and one coefficient products. A
separately evaluated sparse pair of state sums, after that deletion,
costs `(2n-1)M+2nA` when n>0. Sections2--4 give further savings even
against that baseline.

## 4. Sharing a raw sum with its fixed weighted sum

Each group in(1) has distinct positive coefficient weights. Suppose
its two least weights are u and u+1, and its already paid raw sum is R.
Then

    sum_j w_j Ehat_j
      =u*R+sum_(j:w_j>u) (w_j-u)Ehat_j.               (3)

The smallest term has disappeared from the second sum and the next
coefficient has become1. Every multiplication by a coefficient1 is
an alias, and no zero product is emitted. If u=1, the first product
is also an alias; if u>1, that first product is charged. In either
case(3) saves exactly one multiplication compared with direct weighted
evaluation, and uses the same number of additions.

For a group with fewer than two terms, or without consecutive least
weights, the source uses direct weighted evaluation, still removing
zero and one coefficient products. Define epsilon_I,epsilon_F,epsilon_L
to be1 precisely when the respective group has consecutive least
weights, and0 otherwise. Put epsilon equal to their sum. These flags
are computed from the fixed table, not from supplied witness values.

For k>0, the two occurrences of fixed coefficient1 across the three
groups account for the first two uncharged aliases. Summing the literal
costs in(1)--(3), the common correction, the two state words and B*T gives

    flow_M=n+b-1-epsilon,
    flow_A=n+b+1,
    f_flow=2(n+b)-epsilon.                            (4)

The formula includes all products by fixed state codes. It does not
assume repeated multiplication by a particular numeral is free.

The degenerate cases have smaller exact schedules:

* If n=0, both state words are identically zero. Retain their comparison
  as `0=0`, with no flow gate. Thus flow_M=flow_A=f_flow=0.
* If n=1, the only nontrivial path has one first and one last edge.
  Reuse the parent's already computed B-1 and compare
  `Ehat_last+(B-1)` with `B*Ehat_first`. The residual is exactly
  `(Ehat_last-1)-B*(Ehat_first-1)`. This costs1M+1A=2.
* If n>=2 and k=0, all b=n nontrivial paths have length two. The first
  and last weight sets are both `{1,...,n}`, so both flags in(3) are1.
  Compute A=Lw-C and T=F-C separately, then B*T. This costs
  `(2n-3)M+2nA=4n-3`.

Every case satisfies f_flow<=2n+2b. If s_1 is the number of length-one
codes, then n+b=L-s_1, giving the slightly sharper uniform bound

    f_flow<=2(L-s_1)<=2L.                             (5)

For k>0, the saving beyond the zero/one-folded baseline is
`2k-1+epsilon`, at least one operation. For k=0,n>=2 it is two
operations, and for n=1 it is one. For a single code of length L>=4,
the exact flow cost is `(L-2)M+(L+1)A=2L-1`, compared with4L-5
operations for that simpler sparse baseline.

## 5. Exact controller and complete-compiler ledgers

The parent's dense flow has `(2m+1)M+2mA=4m+1` gates. Remove only
that block and replace it by the flow above. The regrouped checksum
has the same number of additions as before. Let f_M,f_A be the casewise
counts just proved, and f_flow=f_M+f_A. The resulting exact ledgers are

| Certificate | M | A | Total |
|---|---:|---:|---:|
| Regular macro controller |m+2h+29+f_M|2m+h+p+30+f_A|3m+3h+p+59+f_flow |
| Complete matrix compiler |m+2h+127+f_M|2m+h+p+145+f_A|3m+3h+p+272+f_flow |

The controller retains all25 comparisons and the same m+22 positive
auxiliaries beyond B,P and the eight physical hats. Its dyadic B,P
interface theorem is unchanged. Its literal SOS adds25M+49A and costs
`3m+3h+p+133+f_flow`.

The complete compiler retains all60 comparisons, its three disjoint
Pell cores, m+87 positive existential coordinates and sole ordinary
input x. Its literal SOS adds60M+119A and costs

    (m+2h+187+f_M)M+(2m+h+p+264+f_A)A
      =3m+3h+p+451+f_flow.                            (6)

Even an identically zero flow comparison in the n=0 case is kept in
these literal25/60-comparison and SOS schedules. No equation-count
reduction is hidden in(6).

For reference, the recorded audit tables have these values. Their
physical labels determine p; the displayed lengths alone need not
determine that parameter.

| Code lengths | m | p | n | b | f_flow | Old complete cost | New complete cost |
|---|---:|---:|---:|---:|---:|---:|---:|
| none |2|0|0|0|0|290|281|
| 2 |4|0|1|1|2|307|292|
| 2,2 |8|0|2|2|5|338|310|
| 10 |16|4|9|1|19|401|355|
| 2,3,4 |16|2|6|3|17|399|351|

For example the ten-letter fixture saves46 operations overall, of
which16 are beyond removing zero and one coefficient products. Its
complete SOS cost falls from580 to534. These fixture alphabets carry
no universality claim.

## 6. Exact residuals, degrees and the complete positive theorem

The only changed comparisons are the edge checksum and the state-flow
comparison. Sections2--4 prove their residual identities on every
integer assignment; every other comparison retains its original
polynomial. This includes the signed n=1 residual rewrite and the
identically zero n=0 case. The native core gates and packed edge lane
order are not modified.

Consequently the two controller systems have identical positive
solution sets, with the identity map on all supplied coordinates.
After inserting the rewritten controller into the complete source,
all shared B,P,J,H,Shat,Zhat aliases are unchanged. The complete
systems again have identical positive solution sets, and their SOS
outputs are **identical integer polynomials**, evaluated by different
circuits. This proves full soundness and completeness from the
[established fixed-table theorem](group_complete_matrix_compiler.md),
without a new conditional typing argument or an altered Pell witness.

In particular the ordinary affine input r=alpha*x+beta, the recovered
duration geometry, hub padding, every positive slack and the final
matrix endpoint remain exactly as in that theorem. The same subgroup
membership statement applies when the fixed macro list includes its
generators and inverses. This rewrite uses no hypothesis concerning
how a word happens to visit the graph beyond those already paid by
the unchanged comparisons.

Since the polynomial itself is unchanged, its exact degree is unchanged.
The standalone controller SOS has degree12m+16: its unique highest
residual is the first native norm, with highest form
`w^2*s^4*k^2*(8J*P^(m-1))^6`. In the complete source the selected-source
norm also contributes degree56 before squaring, giving exact SOS degree
max(112,12m+16). At m=8 both squared highest forms remain. All native
index coordinates are independent supplied variables for this degree
calculation; no zero-set identity is substituted into the polynomial.

The optimization is confined to controller flow. It neither merges
native typing kernels nor assumes those kernels have a common scale.

## 7. Source and independent formula checks

The [source](group_sparse_macro_flow.py) exports
`build_controller(codes)`, `rewrite_controller(parent_packet)` and
`build_complete(codes,alpha,beta)`. The first constructs the canonical
fixed table, the second verifies its structural hypotheses, and the
third replaces only that controller block in the full parent source.
The [receipt](group_sparse_macro_flow.json) records actual composed
DAGs, group partitions, checksum additions, flow instructions, fixed
coefficient savings, comparisons and exact ledgers.

Thirty-one tables check both changed residuals symbolically. Another
1,984 positive and signed assignments compare every controller residual
and its SOS against independent parent formulas. Five complete tables
check all60 residuals and the complete polynomial on640 further
assignments. Weighted and offset polynomial evaluations recover the
exact complete degrees and leading coefficients at m=2,4,8,16, including
the m=8 tie. These are exact arithmetic identity checks, not a search
for accepting Pell witnesses or an unbounded membership algorithm.

Default execution compares the deterministic receipt; `--write`
regenerates it. Parent sources and their receipts remain unchanged.

Two independent full proof/source/default reviews passed without findings.
They checked the grouped checksum count, exactly two coefficient-one
occurrences, all weighted-sum savings and degenerate cases, unchanged
residuals and witness domains, and every displayed cost and degree.
One review additionally compared all 60 complete residuals with the frozen
parent on 512 signed arbitrary-table assignments: 75 had n=0, 13 had n=1,
one had only length-two nontrivial paths, and 423 had internal edges.
The exact multiplication/addition totals and saving4m+1-f_flow matched
in every case. No bounded fixture is used to infer the complete theorem.
