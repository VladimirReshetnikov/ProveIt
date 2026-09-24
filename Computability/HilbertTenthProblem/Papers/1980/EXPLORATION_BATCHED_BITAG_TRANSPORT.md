# Batched bi-tag transport: an exact component, not a universal bound

This note removes the passive rotations from a bi-tag computation and counts
the resulting arithmetic transport. The three accepting-history transport
equations cost **13 operations, 6M+7A**. This subtotal excludes the common
history geometry, row bounds, joint rule selection, weighted selection,
positive-variable conversion and raw numerical input interface. It does not
improve the complete 90-operation normalized tag certificate or the universal
90-operation raw-input certificate.

## 1. Canonical batching and first halting

Use the bi-tag systems of Neary and Woods,
[*Four Small Universal Turing Machines*](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf),
Definitions 2.2--2.3 and Theorem 2.1. The disjoint finite alphabets are A and E,
with halt marker e_h in E. Every valid word contains exactly one E-symbol and
at least one A-symbol. The rules are

    a -> a,                 a in A;
    ea -> u e',             e != e_h, a in A, u in A union A^2, e' in E.

A step removes the displayed left side from the front and appends its right
side. There is exactly one rule for each nonhalting pair (e,a). Halting means
that e_h is at the front, not merely that it occurs somewhere.

**Canonicalization.** A word x e y, with x,y in A* and xy nonempty, reaches
e y x after exactly |x| passive steps. No earlier word halts: before that point
its front symbol belongs to A, even if e=e_h.

**Batched step.** From canonical e a w with e != e_h, an active rule gives

    e a w -> w u e' ->* e' w u.                         (1)

The second arrow consists of exactly |w u| passive rotations. Every preceding
front is an A-symbol, so if e'=e_h this is exactly the first halt within the
batch. If e'!=e_h, it is the next canonical nonhalting word. Since |u| is 1
or 2, the data word w u is nonempty. Its length differs from |a w| by 0 or 1.

Consequently the original computation, after its finite canonicalization,
halts if and only if the deterministic batched system reaches e_h. An infinite
batched computation expands into an infinite original computation, because
each batch has finite positive length; an infinite original computation cannot
remain forever in a single finite passive rotation segment. This establishes
equivalence of halting, not just of bounded examples.

The normalized state is the pair (e,v), where e is stored separately and
v in A+ is the data queue. Exactly one marker is structural in this model;
there is no additional marked-position history to certify. An initially
halting marker is accepted with **zero batches**. No positive-time promise is
introduced. The numerical input conversion below is separate from the
universality theorem: fixing a universal TM in Theorem 2.1 fixes a universal
bi-tag program on encoded finite words, not a free loader for a raw integer.

## 2. Exact scalar arithmetic

Choose an injective digit map A -> {1,...,a} and a fixed base b>a. All such
numerals are free. Encode the front at the least significant end:

    code(d0...d_(ell-1)) = sum d_i b^i,    L=b^ell.

Thus 0<n<L and ell>=1. For a batch, write a for the front digit, u for the
code of its appended data word, and g=|u_word|-1 in {0,1}. Then

    b*n_next = n-a+u*L,
    L_next = (1+(b-1)*g)*L = b^g*L.                     (2)

For a two-symbol output d d', u=d+b*d'; for a one-symbol output d, u=d.
The fixed program can store those values as numerals without arithmetic.

Conversely, given a valid source word and the same selected active rule,
(2) produces precisely its batched successor: n-a is b times the code of the
remaining suffix, and u*L/b appends the selected word at its end. The new
length marker has the required value. Induction preserves valid nonempty
data words. This converse assumes that each scalar equation and the joint
rule choice have actually been recovered; the packed equalities alone do not
establish either assumption.

## 3. Three packed transports and their exact cost

For h>=0 batches choose a common time radix R>1 and Q=R^h. Let e_halt have
state code 0 and give all nonhalting states distinct positive codes. Let
n_0,L_0,s_0 and n_h,L_h,s_h be the endpoint data, length and state codes.
Define the seven source words

    N = sum n_i R^i,       A = sum a_i R^i,
    U = sum u_i L_i R^i,   Z = sum L_i R^i,
    W = sum b^g_i L_i R^i,
    S = sum s_i R^i,       F = sum s_(i+1) R^i,         0<=i<h.

Multiplying (2) and the state shifts by R^(i+1) and summing gives

    R*(N-A+U) = b*(N-n_0+n_h*Q),
    R*W       = Z-L_0+L_h*Q,
    R*F       = S-s_0+s_h*Q.                          (3)

At acceptance s_h=0, so the last term disappears. The accepting equations
cost respectively 7=3M+4A, 4=2M+2A, and 2=1M+1A: **13=6M+7A** in total.
Both nonzero terminal data terms are paid. Equality comparisons are free;
intermediate differences may be signed. The checker lists every primitive
and compares the resulting residuals to independently written equations.

For h=0 every source word is zero and Q=1. The content and length equations
hold with unchanged endpoints, and the accepting state equation forces
s_0=0. Thus the identities also cover the zero-batch case. Their zero-valued
fields need an explicit conversion before use in a strictly positive-variable
certificate. Even when h>0, F can be zero for a one-batch accepting run.

If one supplies B and pays R=b*B, the content equation becomes

    B*(N-A+U) = N-n_0+n_h*Q.                          (4)

It costs one multiplication less, exactly offset by the paid radix relation.
Together with the unchanged length and state equations the subtotal remains
13=6M+7A. If G is the residual of (4) and C the first residual of (3), then

    C-b*G = (R-b*B)*(N-A+U).

Thus this substitution is exact on R=b*B. No radix factor is silently free.

The weighted successor-length word W avoids evaluating (b-1) times a growth
field in the transport schedule. It does not eliminate the requirement that
W select the same g_i and L_i as the content and rule histories. Equivalently,
with V=sum g_i L_i R^i one has W=Z+(b-1)V; explicitly constructing W that way
costs 1M+1A in addition to the displayed transport subtotal.

## 4. Exact remaining rule obligations

There are m=|A|*(|E|-1) active rules. For each rule r=(e_r,a_r,u_r,g_r,e'_r),
let delta_(r,i) indicate its use at row i. Each row needs exactly one active
rule. In a direct selector implementation introduce

    J = sum R^i,
    D_r = sum delta_(r,i) R^i,
    T_r = sum delta_(r,i)*L_i R^i.

The required identities are

    sum D_r = J,
    A = sum a_r D_r,   S = sum e_r D_r,   F = sum e'_r D_r,
    Z = sum T_r,       U = sum u_r T_r,   W = sum b^g_r T_r.  (5)

In addition to these linear forms, every D_r must be a Boolean row selector,
the selectors must partition the common rows, and T_r must select **the same
rows of Z**. Ordinary multiplication D_r*Z produces cross-row convolution
and does not implement T_r. The joint table simultaneously chooses the read
digit, source and target states, output word, and growth flag. Allowing those
choices independently gives a different, unsound machine.

These are a concrete sufficient specification, not a claim that m independent
masks are optimal or necessary. Shared rule families and packed table tests
may reduce the number. Likewise, a large fixed table can be one free numeral,
but verifying a variable lookup into it still needs arithmetic. The three
transport equations do not evaluate the six linear forms in (5).

The remaining geometry must establish Q=R^h, all common row supports, row
bounds sufficient to prevent carries, and the initial pair (n_0,L_0).
For example, once scalar residuals rho_i are known to satisfy |rho_i|<R,
sum rho_i R^i=0 implies every rho_i=0 by reduction modulo R and induction.
That elementary decoding lemma is available; its hypotheses are not supplied
by (3). A complete verifier must derive appropriate bounds from its own
equations before using the lemma.

For comparison, retaining a 43-operation kernel leaves 47 operations in a
90-operation target. The conditional 13-operation transports would leave
34 for all geometry, initialization, bounds, rule/weighted selection,
packing and positivity. This is a budgeting comparison, not a 56-operation
candidate: a valid common-mask interface has not been constructed. The
normalized queue avoids passive histories but trades the binary tag rule for
a finite joint lookup table. Its best achievable complete cost remains open.

## 5. Reproducible evidence

`../verification/explore_batched_bitag_transport.py` checks both schedules
symbolically, exhaustively checks canonicalization and every local output
over a two-letter alphabet and three marker states with data lengths through
four, and explores all deterministic one-nonhalting-state/two-letter tables
on data lengths through three. It compares each batched step to actual
microsteps and packs the same rows for the arithmetic checks. It also checks
all seven rule-partition/linear-form identities in (5), including unused rules.
Halting runs, exact repeated-state cycles, and merely bounded prefixes are counted
separately; a cutoff is not reported as nonhalting. Zero-batch halts and
weighted-product counterexamples are included. The JSON receipt records
these finite checks, not a universal-certificate result. Author and two
independent complete scoped proof/source reviews pass, and fresh verification
reproduces the saved receipt.
