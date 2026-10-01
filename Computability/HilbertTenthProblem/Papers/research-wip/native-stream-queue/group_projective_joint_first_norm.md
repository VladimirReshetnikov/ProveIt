# The joint bound and positive first-root coordinate commute

The [joint history/output bound](group_projective_joint_bound.md) and
the [positive first-norm unit](group_projective_first_norm_unit.md)
combine into one complete ordinary-input compiler. Applying either
rewrite first gives the same named arithmetic DAG, ordered comparisons
and supplied coordinates. Only the topological instruction order may
differ. No additional gate or hypothesis is needed for the composition.

Let

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

Here m=2^h is the fixed padded edge count, p the physical-port cost,
f_flow the sparse-flow cost, epsilon=1 the controller-mask option
(requiring m>=8), and chi=1 the computed-P option. All compiler numerals
are fixed positive integers with alpha+beta+1>=m, as supplied uniformly
by the explicitly padded enumeration in the parent construction.

| First norm | Native field variant | Certificate | Equations | Positive witnesses | SOS polynomial |
|---|---|---:|---:|---:|---:|
|separate|four|C|17-chi|m+33-chi|C+50-3chi|
|merged|four|C+1|16-chi|m+33-chi|C+48-3chi|
|separate|six|C|15-chi|m+31-chi|C+44-3chi|
|merged|six|C+1|14-chi|m+31-chi|C+42-3chi|

The four-field variant computes a,d,k,s; the six-field variant also
computes c,r. The exact degree tradeoffs are

| First norm | Four fields | Six fields |
|---|---:|---:|
|separate|10nu L+32|nu*(32L+4m+60)+38|
|merged|16nu L+42|nu*(38L+4m+60)+48|

For the illustrative ten-letter table, m=16,h=4,p=4,f_flow=19. With
both optional projections C=258. The merged six-field certificate has
**259 operations, 13 equations and 46 positive witnesses**; its polynomial
has **297 operations and exact degree3488**. The separate six-field
option instead has258 certificate operations,14 equations,299 polynomial
operations and degree2974. This table is an audit example, not a
numerically instantiated universal alphabet. The separate75/88
frontiers remain unchanged.

## 1. Disjoint literal rewrites

Start with the actual padded-margin source. The joint-bound rewrite
changes the radix multiplication from B=8D to B=16D, and replaces

    Hsum+hbound=P, Zsum+zbound=P+1

by the single positive comparison

    Hsum+Zsum+b=P+1.                              (1)

It retains both final bound additions, removes the hbound coordinate
and its comparison, and keeps the name selection__bound_global for b.
All histories, eight selected-output hats and scalar geometry remain.

The first-norm rewrite replaces the positive supplied triangular root
tau by positive g and replaces its six private gates by the six-gate
definition

    V=XY^2, N0=g^2+4Vk(g-k).                     (2)

The root-base product Vk=E*(kY) is one of the six paid gates; kY is
already shared. Thus (2) costs the same 4M+2A as the old first equation. In the separate option it compares
N0 to one. In the merged option it appends one multiplication and
compares N0*N1*N3*Q to one, omitting the separate first comparison.

The two rewrites modify disjoint named gates and supplied coordinates.
Their removed comparisons are different. The first-norm rewrite
continues to read the same X,Y,k and existing three-unit product;
the joint-bound rewrite continues to read only the history and output
sums and their bound. Substituting the new B into all its downstream
registers is identical in either order.

Consequently, the named operation and operand attached to every output
register is the same, as is the ordered comparison list. Removing
hbound and renaming tau to g also commute. Sorting the dependency graph
adds no arithmetic. The [source](group_projective_joint_first_norm.py)
checks these identities for both routes:

    first_norm.rewrite(joint_bound.build(...), merge_first)
    joint_bound.rewrite(first_norm.build(..., merge_first)).

It performs no additional constant folding or uncharged common-expression
rewrite. The claimed costs are the counts of the resulting literal DAGs.

## 2. Positive restoration before native typing

The ordinary input remains x>0, with u=alpha*x+beta+1. The common shift
is C0=D-1, D=u+height_slack, and B=16D. The fixed-numeral margin gives
B>m. The exact paired-action predicate remains the action on (1,u)
ending at e2 in each block, with the fixed alphabet reflection and
padded-program interpretation already established in the parent.

Before invoking any native typing conclusion, (1) restores positive
old bounds by

    hbound=Zsum+b-1>0, zbound=Hsum+b>0.            (3)

It also gives P>=12. Since the computed J is nonnegative and the
repunit equation is retained or a definition, P=(B-1)J+1 forces J>0.
If P is computed it is already at least one on every positive supplied
assignment. Thus q=16P^L is positive and X,Y,V,k are positive before
any Pell or checksum conclusion.

The integer factors are

    N1=d^2-((a+2)^2-1)c^2,
    N3=(ic^2)^2*(U^2-y^2)+y^2,
    Q=q-(F0+F1+F2+F3).

The two older norm factors cannot equal -1 modulo four, independently
of every equation. The same is true of N0 because N0 is congruent to
g^2 modulo four. In the merged option their product with Q equals
one, so N0=N1=N3=Q=1. In the separate option N0=1 is explicit and
the older three-unit argument recovers the other three equations.

Now

    root=2Vk+g,
    root^2=1+4V(V+1)k^2,
    tau=(root-1)/2                               (4)

restores a strictly positive integer triangular root. Oddness follows
from the norm equality, and positivity follows from V,k,g>0. Conversely,
an old positive root gives g=2tau+1-2Vk>0 by that same norm. Both ratio
slacks eta,zeta and the full strong auxiliary equality remain unchanged.

Equations (3) and (4) change independent supplied coordinates: the root
map does not read bound witnesses, and the bound map does not read tau
or g. They restore the complete widened parent before invoking its
typing and trace theorem. Thus the composition has the same complete
positive paired-action relation, without a circular use of typing to
recover either bound or unit sign.

## 3. Positive completeness and the same universal input

For a genuine accepted macro word choose a sufficiently large dyadic D
with D>u and D>1+max|signed state|. At radix16D, every shifted history
digit and every active selected-source digit is at most2D-1. Therefore

    Hsum+sum_i Zi<=5(2D-1)J,
    b=P-Hsum-sum_i Zi-7>=(6D+4)J-6>0.             (5)

The complete native AND converse at the actual joined scale supplies
the old positive native tuple. Apply (4) in the forward direction to
obtain positive g. Its first unit is one, so either the separate or
merged comparison holds. This supplies every positive coordinate of
the composed system.

More precisely, each rewrite is a positive solution bijection with its
appropriate widened parent: (3) in one direction and (5) in the other
restore the joint bound; (4) restores the first root. These bijections
commute. Changing the radix multiplier preserves accepted inputs by
the full trace theorem and its large-D converse; it need not preserve
a particular tuple from the old radix8D convention.

For the fixed reflected alphabet built from the explicit padded
enumeration, the established projective theorem identifies this same
paired-action predicate with the required universal ordinary-input
query. No new input code, runtime program exponentiation, alphabet
dependence on x or unpaid history/selection hypothesis is introduced.

## 4. Full arithmetic ledger

Let mu be zero for a separate first norm and one for a merged first
norm. Write f_flow=f_M+f_A and retain the inherited common-register
savings d_M,d_A. The certificate split is

    M=m+2h+82+f_M-d_M-epsilon+mu,
    A=2m+h+p+103+f_A-d_A.

The comparison counts are e=17-chi-mu for four native fields and
e=15-chi-mu for six. Compiling all residuals into one SOS adds e
squares, e subtractions and e-1 summation additions. The resulting
polynomial splits are

    four: M=m+2h+99+f_M-d_M-epsilon-chi,
          A=2m+h+p+136+f_A-d_A-2chi-2mu;
    six:  M=m+2h+97+f_M-d_M-epsilon-chi,
          A=2m+h+p+132+f_A-d_A-2chi-2mu.

These prove the opening table. In particular the merged first norm
adds one certificate multiplication, but that is canceled in the
polynomial count by one fewer residual square; the net saving is two
additions. The joint bound independently saves one square and two
additions, for a combined five-operation polynomial saving relative to
the padded-margin source when mu=1. The retained joint inequality
continues to exclude the known output-lane counterexamples.

## 5. Exact degree with the widened radix

All supplied coordinates, including x, have degree one; fixed compiler
numerals have degree zero. If P is supplied, P*=P. Otherwise

    P*=16*(alpha*x+height_slack)*sum_e Ehat_e,

which has degree two. The coefficient is16, as required by the widened
radix, rather than the old coefficient8. Define

    q*=16(P*)^L, s*=2*odd_half, k*=eta+zeta,
    a*=w*(s*)*(q*)^2.

The new first unit has nonzero highest part

    N0*=4w*(s*)^2*(q*)^3*(k*)*(g-k*),
    degree(N0)=3nu L+5.                          (6)

For four computed native fields, c and r remain supplied. The highest
parts of the three older units give

    T*=[8ga*(a*)^2*(c+2ga)]*[i^2*j^2*c^6]*q*,
    degree(T)=5nu L+16.                          (7)

For six computed fields put

    c*=(k*)*(s*)*q*,
    r*=16^4 H2 (P*)^(3L+m+15).

Then the older three-unit product has highest part

    T*=[8ga*(a*)^2*c*]*[i^2*(c*)^4*(2r*)^2]*q*,
    degree(T)=nu*(16L+2m+30)+19.                  (8)

The cancellation in d^2-Delta*c^2 is already included in (7)–(8);
in the four-field case both equal-degree surviving contributions
produce c+2ga. The changed radix coefficient does not change either
cancellation identity.

In the separate option T is the unique highest residual and its square
has the exact SOS highest part (T*)^2. In the merged option the last
source multiplication has highest part N0*T*, dominates all other
residuals, and gives SOS highest part (N0*T*)^2. These forms are nonzero,
proving every degree in the opening table. The joint-bound residual
has degree at most nu and cannot affect this conclusion. No equation
such as P=B^t is substituted to lower the degree.

## 6. Literal and semantic checks

The [receipt](group_projective_joint_first_norm.json) stores forty
compact variant ledgers and one complete ten-letter source example.
All forty configurations check exact named-DAG, ordered-comparison
and supplied-coordinate commutation. On1,280 assignments, including320
signed cases, both rewrite orders agree at every register and on the
full residual list and SOS output.

The same assignments also compare with the actual joint-bound parent
under the rational off-zero substitution

    tau=Vk+(g-1)/2.

The first parent residual is multiplied by -4; in the merged option
the replacement residual is
`(old_unit_residual+1)*(1-4*old_first_residual)-1`.
Half-integral off-zero parent roots are counted explicitly. Integrality
and positivity at zeros follow from Section2, not from these off-zero
identities alone.

Twenty exact weighted univariate evaluations compute the separate
certificate residual polynomials once each. Their exact degrees and
leading coefficients also certify the merged source's final product:
both factors are nonconstant, so degrees add and leading coefficients
multiply, and subtraction of one cannot alter that term. All forty
residual degree lists and highest square sums are checked against
(6)–(8). The checker never needs to expand the redundant full SOS
polynomial symbolically; full numeric SOS evaluations are still tested.

The executable also replays the joint-bound parent's eight genuine
positive outer fixtures and the first-root packet's384 exact positive
Pell coordinate maps and64 modulo-four cases. Their combination is
justified by the commuting positive maps above. The outer fixtures'
native coordinates remain explicit placeholders; full positive Pell
extensions are proved parametrically rather than falsely claimed as
materialized numerical zeros.

Run the source normally to compare the deterministic receipt, or use
`--write` to regenerate it. Both parent packets remain unchanged.

The root reviewer independently checked the full proof and literal source,
including both positive maps, the commuting rewrites, all ledgers and
exact leading forms, with no mathematical findings. The author
regenerated the receipt and ran a fresh default replay; both passed.
