# Project out scalar guards after enlarging the freely chosen shift

The complete [unit-product projective compiler](group_projective_unit_product.md)
can remove two scalar comparisons and two positive witnesses at unchanged
certificate cost. One optional further substitution removes a third
comparison and witness, again at unchanged cost, but raises the exact
polynomial degree. Every ordinary accepted input is preserved.

The changes have distinct justifications. The repunit J is computed from
nonnegative edge counts; its strict positivity follows from retained
scalar equations before any native typing theorem. The radix-margin
witness is made unnecessary by choosing the freely adjustable history
shift above the fixed edge count. Finally, the length power P can be
computed from its already paid positive repunit definition.

Let epsilon=1 mean the parent's optional controller-mask reuse, requiring
m>=8, and epsilon=0 mean its default eight-lane range mask. Write

    C=3m+3h+p+186+f−3min(h,3)−epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1.       (1)

Here C is the unit-product comparison certificate cost. Let chi=1 if P
is computed and chi=0 if it remains a supplied positive coordinate.
The exact complete ledgers are

| Computed native fields | Certificate | Equations | Positive witnesses | SOS polynomial |
|---|---:|---:|---:|---:|
|a,d,k,s|C|18−chi|m+34−chi|C+53−3chi|
|a,c,d,k,r,s|C|16−chi|m+32−chi|C+47−3chi|

Thus the four polynomial base constants, before subtracting epsilon, are
239/236 for the four-field variant and233/230 for the six-field variant,
where each pair means supplied/computed P. The witness convention remains
strict positivity, and x is still the only ordinary relation argument.

For the illustrative ten-letter table m=16,h=4,p=4,f=19, the six-field
source with both optional choices costs259 comparison operations and
**303 polynomial operations**, has **15 equations and47 positive witnesses**,
and exact degree2974. With supplied P, the same mask choice instead gives
306 polynomial operations,16 equations,48 witnesses and degree1506.
These are complete fixed-table constructions; this example is not a
numerically instantiated universal alphabet. The separate75/88 bounds
are unchanged.

## 1. The three scalar equations in the parent

Write E_e=Ehat_e−1 for each positive edge hat. The parent pays a checksum
addition tree whose final register is

    R_edge=sum_e Ehat_e.

Its tree is arranged to expose the sparse-flow sums, so this is a real
existing register even when its source name is table-dependent. The
three relevant parent comparisons are

    R_edge=J+m,
    m+radix_beta=B,
    (B−1)J+1=P.                                  (2)

The retained history bound is

    H0+H1+H2+H3+history_bound=P.                  (3)

In the parent u=alpha*x+beta+1 and D=u+height_slack, with B=8D.
All quantities in (3) on the left are positive supplied coordinates.
No digit semantics, Pell equation or Boolean constraint is needed to
interpret (2)–(3) as ordinary integer comparisons.

## 2. Enlarge the origin and remove the radix slack

Change the definition of D to

    height_sum=u+height_slack,
    D=height_sum+m.                              (4)

This adds one addition. Delete the existing gate m+radix_beta, its
comparison to B, and the positive witness radix_beta. This deletes
one addition, so the certificate cost is unchanged. Because u and
height_slack are positive,

    D>u+m>m, B=8D>m,

and the omitted parent coordinate is restored positively as

    radix_beta_old=B−m>0.                        (5)

There is no hidden congruence restriction: (4) is an additive shift by
a fixed numeral, not a multiple of m. A genuine finite history can
always choose a sufficiently large power of two D with D>u+m and
D>1+max|state|. Then height_slack=D−u−m is positive. This is the same
free choice used in the parent's completeness proof, with a larger
lower bound.

The associated parent height coordinate is

    height_slack_old=height_slack+m.

It makes the computed D, radix, range masks, initial and final values
identical in both sources. The stronger convention need not retain a
particular old tuple whose height slack is at most m. Accepted inputs
are preserved by the large-D completeness argument; an unrestricted
bijection with all parent witness tuples is not claimed.

## 3. Compute J and prove its strict positivity before typing

Replace the existing one-addition register J+m by the one-subtraction
register

    J_computed=R_edge−m=sum_e(Ehat_e−1).           (6)

Alias every use of J to this register, delete the first comparison in
(2), and remove J from the positive witness list. All original checksum
tree gates and sparse-flow sums remain, and the replacement gate has
the same cost.

For all positive supplied edge hats, J_computed>=0. Equality can occur
away from the zero set, for example when every edge hat equals one.
We therefore do not describe this as an unconditionally positive graph
substitution. At any zero of the new source, (3) gives P>=5. The retained
repunit equation and B>1 then imply

    (B−1)J_computed=P−1>=4,

so J_computed>0. This restores precisely the parent positive domain
before invoking its AND theorem, power typing, controller semantics or
history interpretation. The proof uses only scalar equations that are
still present. It neither discards the J=0 case by convention nor uses
a typing conclusion to prove its own hypotheses.

The first omitted comparison in (2) becomes an identity under (6).
Every other parent residual is unchanged after this substitution and
the height-coordinate translation from Section2.

## 4. Optionally compute the length power P

The parent already evaluates

    P_computed=(B−1)J_computed+1                  (7)

to compare it with its supplied P. Alias P to this existing register,
delete that comparison and remove P from the witness list. No source
gate is added or deleted. Before equations hold, B>=32 and J_computed>=0
imply P_computed>=1, so P is restored positively on every positive
supplied tuple.

The same proof of strict J positivity still works: the retained history
bound (3), now using P_computed, gives P_computed>=5; the repunit relation
is the identity (7). Therefore J=0, which would force P=1, cannot occur
at a zero. All scalar bounds used by the parent remain valid after the
three omitted comparisons have been restored.

The source dependencies are acyclic. The raw edge sum uses only supplied
edge hats; the larger D uses only x and height_slack; these compute J and
P before any lane powers or masks that consume them. A stable topological
sort verifies operand availability for the literal source.

## 5. Full positive soundness and completeness

Extend a new positive zero to the parent by

    height_slack_old=height_slack+m,
    J_old=J_computed,
    radix_beta_old=B−m,
    P_old=P_computed if chi=1.                   (8)

All restored coordinates are positive by Sections2–4. Every removed
parent comparison vanishes identically on this graph extension, and
every retained residual equals its parent residual. Thus the full
parent positive theorem applies with the same ordinary x. Its unit
product still restores the native checksum and two norm comparisons
by unconditional sign exclusions; no step in the scalar restoration
assumes the result of that typing argument.

For completeness, start from a genuine accepted macro word. Choose D
as in Section2. The parent construction supplies all positive data at
that exact D and its corresponding P,J. Equations (2) force the values
(5)–(7), and its height slack exceeds m. Erasing those coordinates and
subtracting m from the old height slack gives the required new positive
tuple. This proves the same generic paired-action relation and, for the
fixed reflected universal alphabet, the same universal input sets.

The residual identities hold on arbitrary signed assignments too, with
the explicit extension (8), even though restored coordinates need not
be positive there. Consequently the new SOS equals the parent's SOS
under (8): the removed residual squares are identically zero. With e
remaining equations the literal polynomial cost is C+3e−1, proving the
opening table. The positive theorem follows from the scalar restoration
and completeness arguments, not from off-zero identities alone.

## 6. Exact degree cost of computing P

Every supplied coordinate has total degree one; fixed program and table
numerals have degree zero. Put nu=1+chi. If P remains supplied, its
highest part is simply P. If it is computed, (4), (6) and (7) give

    D*=alpha*x+height_slack,
    J*=sum_e Ehat_e,
    P*=8 D* J*,                                 (9)

so P has degree two. The constant m and the subtracted integer m affect
no highest homogeneous part. Both highest factors in (9) are nonzero.
The affine substitution for J alone does not raise degree.

Write

    q*=16(P*)^L, s*=2*odd_half, k*=eta+zeta,
    a*=w*s*(q*)², c*=k*s*q*,
    r*=16⁴ H2 (P*)^(3L+m+15).                   (10)

Here the last two expressions are used in the six-field variant only.
In the four-field variant the first native norm remains uniquely highest:
its degree is6nu L+8, whereas the merged unit product has degree at most
5nu L+16. Since L>=20, the former is strictly greater. Its nonzero
highest form is w²(s*)⁴(k*)²(q*)⁶. Hence the four-field SOS has exact degree

    12nu L+16.                                  (11)

In the six-field variant the computed main norm has highest part
8*ga*(a*)²*c*, as in the parent after its necessary cancellation. The
auxiliary norm has highest part i²(c*)⁴(2r*)²; the third unit has highest
part q*. Their product has degree nu*(16L+2m+30)+19 and uniquely dominates
all unmerged residuals. Squaring gives exact degree

    nu*(32L+4m+60)+38.                           (12)

Equivalently:

| Fields | P | Eight-lane mask | Controller mask, m>=8 |
|---|---|---:|---:|
|four|supplied|12m+232|24m+136|
|four|computed|24m+448|48m+256|
|six|supplied|36m+674|68m+418|
|six|computed|72m+1310|136m+798|

These degrees are measured in the actual remaining supplied coordinates.
In particular (7) is a polynomial substitution, not an equation used
for a free zero-set degree reduction. The unchanged leading terms are
checked after substitution, including the high-degree computed index r.

## 7. Source checks and finite evidence

The [source](group_projective_scalar_projections.py) exposes
`build(codes, alpha, beta, variant, controller_mask, compute_length)`.
The final option defaults to false; the field and mask options retain
their parent meanings. It retains the exact certificate gate count,
constructs every omitted coordinate and performs the stable source sort.

The checker covers twenty configurations over m=2,8,16, both field
variants, both admissible mask choices, and both length-coordinate choices.
For each it verifies64 full graph extensions, all common computed
registers, every residual and the entire SOS. This gives1,280 identities,
with960 positive supplied assignments and320 signed assignments. Positive
fixtures explicitly include J=0 away from zeros; with computed P this
forces P=1 and a nonzero history residual, as the proof requires.

Twenty weighted offset univariate evaluations verify the exact degree
and independently derived leading form. The receipt records the bit
length and SHA-256 of each large leading coefficient; the checker compares
its exact integer value before forming that compact record. Eight genuine
reflected macro fixtures construct all positive outer coordinates at
the stronger shift bound, check J/P reconstruction and the actual joined
AND, and verify the retained transports. The native Pell placeholders are
not claimed to be full numerical zeros.

Run the checker normally to compare its deterministic
[receipt](group_projective_scalar_projections.json); `--write` regenerates
it. The receipt includes summary ledgers for all variants and one complete
literal source example. These finite audits supplement the parametric
proof above; they do not instantiate or test universality by a finite list
of inputs.
