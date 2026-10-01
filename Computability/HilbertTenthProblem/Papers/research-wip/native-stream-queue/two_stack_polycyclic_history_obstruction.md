# Typed stack histories: exact partial products and a sharp linear obstruction

The [ordinary-input two-stack model](two_stack_affine_input_step.md) has
an exact description by two synchronized colored-parenthesis histories.
Its empty tests require a bottom marker. Replacing those partial actions
directly by invertible matrix actions loses information: the four-step
word **push0, pop1, push1, pop0** is an identity in every group, although
it contains mismatched pops. Its height never becomes negative.

There is also a sharp bound on a different proposed shortcut. An exact
linear model that retains every binary stack of depth at most H, kills
illegal pops, and implements each raw action by a fixed matrix needs at
least **N=2^(H+1)-1 coordinates**. The same bound applies to a linear
weighted recognizer that returns exactly the characteristic function of
the bounded-depth Dyck language. A sparse N-coordinate construction
attains both bounds.

These are scoped obstructions, not arithmetic lower bounds for universal
Diophantine equations. Free-group automata with auxiliary transitions and
nonlinear matrix acceptance conditions are outside the hypotheses. The
note gives an exact positive ordinary-input loader for the sparse model,
costing **2N operations and two equations with N witnesses**, to make its
input and dimension costs explicit. No uniform existential-history
compiler, or new complete universal bound, is claimed.

## 1. Exact two-stack contract, including empty reads

All binary words are written top first. The positive code of a word is

    enc(w)=2^len(w)+sum_j w_j*2^j.

Its empty value is1, and enc(bw)=2enc(w)+b. The earlier note proves a
fixed universal interpreter with initial stacks

    left=empty, right=p_S dec(x),

and fixed initial state. Here x is the ordinary positive input,
enc(dec(x))=x, and p_S is a fixed program prefix for the chosen recursively
enumerable set S. Its cleanup accepts in a fixed state with both stacks
empty. This uses an ordinary finite-word endpoint convention. It does not
assume a prefix-free input domain, and its universal transition table has
not been numerically transcribed.

Introduce a third color #, used as a bottom marker. The physical stack
for binary w is w#. Write +b for push b and -b for a matching pop. A
transition which reads a bit b and replaces it with a fixed top-first
word v becomes

    -b, followed by pushes of v in reverse order.       (1)

A transition which reads empty and writes v becomes

    -#, +#, followed by pushes of v in reverse order.  (2)

The adjacent -#, +# pair can execute exactly when the binary stack is
empty. A bit pop on an empty binary stack encounters # and fails.
Successful actions restore the bottom marker before the next branch.
All later pushes are binary except the explicit restoration in(2).

For a complete proposed branch sequence, let T_L,T_R be its compiled
action words. Prepend +# to T_L. Prepend pushes of (p_S dec(x))# in reverse
order to T_R. Append -# to each. Then the following conditions are
equivalent:

1. The branch sequence is an accepting computation on ordinary input x.
2. Its source/target states form a path from the designated start to the
   designated accept state, and both resulting action words are colored
   Dyck words: every pop matches the current top, no pop underflows, and
   both final stacks are empty.

The implication in each direction follows one branch at a time from(1)
and(2). The final -# enforces an empty binary endpoint. This also proves
that a state-path guard is still necessary: two consecutive empty-stack
preserving branches with state changes1->2 and3->4 can pass both stack
checks while failing state compatibility. The two Dyck words must use
the same branch sequence; independently chosen projections do not suffice.

This is an exact word-level contract. Extracting the variable-length
word dec(x), reversing it into the initial push sequence, synchronizing
the two projections, and selecting a finite accepting state path have
not thereby become arithmetic operations of constant cost.

## 2. Partial products retain precisely the missing guards

For top-first words, +b maps w to bw; -b is defined only on words bw
and maps bw to w. Every nonzero product of these partial maps has the
form

    u z -> v z, for all suffixes z,                    (3)

for a pair of fixed words(u,v). A product with a mismatched forced pop
is the nowhere-defined map, denoted0. One can compute(3) by maintaining
the required input prefix u and produced output prefix v. A push extends
v at its front. A pop removes a matching first symbol of v; if v is
empty it extends u at its end; a different first symbol makes the
product0. Induction proves this normal form and its exact domain.

Thus -0,+0 is the identity only on words starting with0. It is not a
total identity, and in particular is undefined on the empty stack.
A complete action word is colored Dyck exactly when its normal form
is(empty,empty). These definitions agree, after reversing the top-first
convention, with the partial-function model of polycyclic monoids in
[Kambites, Section4, pages8–9](https://arxiv.org/pdf/math/0601061).

An empty-stack test is not one of the nonzero binary maps(3): their
domains are whole prefix cones u{0,1}*, whereas the empty test has the
singleton domain{empty}. The bottom-marker compilation in Section1
therefore supplies a real missing guard; it is not merely notation.

In this partial-product model all three requirements are exact: the
domain retains underflow, zero retains symbol mismatch, and the image
retains the endpoint. An arithmetic representation must pay for the
normal-form calculation or for an equivalent certificate. Writing a
formal product in this monoid does not supply that calculation.

## 3. Why direct affine or group endpoint products fail

The tempting two-by-two rational matrices act on stack codes by

    P_b: S -> 2S+b,
    Q_b: S -> (S-b)/2,                                (4)

with Q_b=P_b^(-1). They implement legal pushes and pops, but as total
rational transformations they forget the domain of each pop.

At empty code1, the word -0,+0 follows1->1/2->1. Its product is the
identity although its first operation is an illegal pop. Checking only
positive rational intermediate values does not remove it.

A stronger example survives every prefix-height test. Compare

    good = +0,-0,+1,-1,
    bad  = +0,-1,+1,-0.                               (5)

Both have height trace0,1,0,1,0 and the same multiplicity of every action.
The good word is legal on every stack and returns it unchanged. The bad
word fails at its second action, on every stack. Nevertheless its affine
trajectory from any positive integer S is

    S, 2S, S-1/2, 2S, S,                             (6)

and all these rational values are positive. Its composed matrix is the
identity. More generally, assigning pushes arbitrary group elements
g0,g1 and pops their inverses sends the bad word to

    g0 g1^(-1) g1 g0^(-1)=1.                          (7)

Product order can be reversed to match column-vector matrix composition;
the cancellation and conclusion are unchanged. Consequently any test
depending only on these direct group products, prefix heights, action
multiplicities and input/final codes cannot distinguish(5). Multiple
group or invertible-matrix products do not help if they all assign each
raw pop the inverse of its push. The action words themselves do differ,
so guards using their order in other ways are outside this statement.

There is no conflict with [Kambites, Theorems7–8 and the following
construction](https://arxiv.org/pdf/math/0601061): those results use
finite control and auxiliary transitions to recognize context-free
languages with free-group automata, and recursively enumerable languages
with direct products. Such constructions can repair the failure in(7).
They do not justify mapping each raw pop to the inverse of its push
without their additional control and word-encoding work. This note makes
no impossibility claim about those richer models.

## 4. Sharp finite-depth linear bound

Fix H>=0 and let W_H be the binary words of length at most H. Its size is

    N=1+2+...+2^H=2^(H+1)-1.

Consider a vector space over any field. Assign each w in W_H a vector
v_w, with v_empty nonzero, and require fixed linear maps P_b,Q_b such that

    P_b v_w=v_(bw)                      if len(w)<H,
    Q_b v_(bw)=v_w,
    Q_b v_(cw)=0                        if c!=b,
    Q_b v_empty=0.                                    (8)

No assumptions about positivity, bases, matrix entries, or overflow
actions are needed for the following lower bound.

**Theorem.** The N vectors v_w are linearly independent.

Suppose there is a nontrivial finite linear relation. Choose a word u
of maximal length among its terms with nonzero coefficient. Apply the
pops of u in top-first order to the relation. Every shorter term either
mismatches or is popped past empty, and hence becomes0. Every other
term of the same length has a differing symbol and also becomes0. There
are no longer terms. The result is the coefficient of u times
v_empty=0, a contradiction. The empty-word case is included. Therefore
the dimension is at least N. Letting H grow rules out any fixed finite
dimension for an exact unbounded raw stack action satisfying(8).

A related bound needs even less state interpretation. Suppose a fixed
initial vector a, final linear functional f, and a fixed matrix per raw
action return exactly1 for each depth-H legal empty-to-empty history,
and exactly0 for all other action words. For each u,v in W_H, form a
word which pushes u from empty and then pops the symbols of v. Its value
is1 exactly when u=v. Hence the N-by-N matrix of these values is the
identity. It factors as the rows f Q_v multiplied by the columns P_u a,
so its rank is at most the representation dimension. Again that
dimension is at least N. This is a statement about exact characteristic
values, not about arbitrary matrix equalities or inequalities at the end.

Both bounds are sharp. Use the N basis vectors e_w. A push maps e_w to
e_(bw) when the latter is within the depth bound, and to0 otherwise.
A matching pop maps e_(bw) to e_w; every mismatch and empty pop maps to0.
The empty test maps e_empty to itself and all other basis vectors to0.
These are partial-permutation matrices, with at most one1 in every row
and column. Starting from e_w, their product is exactly the remaining
stack basis vector if the history is legal within H, and0 otherwise.
Zero is permanent. The empty coordinate of the final vector is1 exactly
for a legal empty endpoint.

For two stacks one may maintain two such blocks and require both empty
endpoints. A bad action kills its own block permanently, so it cannot
be hidden by the other block. This gives dimension2N for that construction;
no optimality claim for all joint encodings is intended. The independent
state-path and synchronized-action constraints from Section1 still apply.

## 5. A paid positive loader and the fixed-word certificate

Index the binary basis by its sentinel code i. These codes are exactly
1,...,N. For the fixed program prefix, put kappa=2^len(p)>0 and
lambda=sum_j p_j*2^j>=0. The desired code is kappa*x+lambda.

Supply **N strictly positive integers u_1,...,u_N** and impose

    sum_i u_i=N+1,
    sum_i i*u_i=kappa*x+lambda+N(N+1)/2.               (9)

The first equation and positivity force exactly one u_i to be2 and all
others to be1. The second puts that2 precisely at i=kappa*x+lambda.
This proves both directions without Boolean equations or an unpaid
input lookup. A solution exists exactly when the affine code is at most
N. The vector u-1 is the desired basis vector, but no separate witnesses
for its zero coordinates are introduced.

The literal schedule shares suffix sums. Start a running sum and a
weighted sum at u_N. For i=N-1,...,1, add u_i to the running sum, then
add that running sum to the weighted sum. At the end they equal
sum_i u_i and sum_i i*u_i respectively. This uses2(N-1) additions.
Compute the right side with one multiplication and one addition; the
fixed offset lambda+N(N+1)/2 is a program numeral. Thus(9) costs

    1M+(2N-1)A=2N,
    N positive witnesses, 2 equations.                (10)

There are no numeral multiplications by the indices i in this schedule.
This is an explicit schedule, not a minimum. Its sum-of-squares
polynomial adds2M+3A, for2N+5 operations.

For completeness, there is also a fully paid positive certificate for
any **fixed nonempty action word** a_1...a_t and fixed H. Supply one
shifted vector u^(j)=1+v^(j) before each of the t actions, so there are
Nt positive witnesses. Initialize by(9); fix the final vector to1+e_empty.
For each fixed partial-permutation matrix, its row either has one
preimage column k or has none. Impose respectively

    u'_(row)=u_k, or u'_(row)=1.                      (11)

These are N equations per action with no arithmetic gates. Starting
from(9), induction proves that each supplied vector is exactly the
appropriate shifted basis vector or the all-ones dead vector. In
particular, no extra coordinate typing is needed. The dead vector cannot
reach the final1+e_empty. Conversely every valid bounded-depth history
supplies all these positive vectors.

The exact literal totals, checked in the executable source, are

    graph: 2N operations, Nt witnesses, Nt+2 equations;
    polynomial: [Nt+3]M+[2N(t+1)+2]A
                =N(3t+2)+5 operations.              (12)

The graph count stays small only because it has Nt coordinate equations
and because every action label is already a source constant. The final
polynomial pays for every equation. This is a separate circuit for each
entire action word, not a certificate choosing the word existentially.
It therefore does not solve the finite-history problem left by the
scalar two-stack compiler.

For fixed H, (9) can load only finitely many ordinary inputs. Allowing H
to grow changes N, all the matrices, the number of equations and the
number of witnesses. Treating H as another integer witness cannot make
that family into one fixed polynomial. Input loading, action selection,
finite control, trace synchronization and variable-size linear algebra
must all be replaced by a uniform paid construction before claiming a
universal arithmetic bound.

## 6. Reproducible checks and scope

The [checker](two_stack_polycyclic_history_obstruction.py) recomputes the
[receipt](two_stack_polycyclic_history_obstruction.json) by default.
Independent string execution is compared with prefix-replacement normal
forms over binary and three-color alphabets. It checks the group and
affine counterexamples with exact rational arithmetic, the full
characteristic identity matrices through depth5, sparse actions and
random histories, bottom-marker empty reads with replacement words, and
the positive input and fixed-word operation ledgers. Negative cases
include wrong colors, empty pops, depth overflow, false input vectors,
nonempty endpoints and disconnected finite control.

An independent proof, source and default-replay review passed, including
the cited primary definitions and Theorems7–8. A separate manual
residual construction matched512 arbitrary positive vector assignments
across H=0,...,4 and t=1,...,9, including every operation count and the
full sum-of-squares polynomial.

The linear-independence and unbounded-dimension statements are proved
above; finite replay is evidence for the implementation, not their
proof. The result rules out a direct guard-erasing matrix compression
and quantifies the cost of one exact bounded-depth repair. It leaves
nonlinear encodings, auxiliary-word group constructions, and a uniform
Diophantine compiler for synchronized typed histories open. It does not
improve the complete universal comparison or polynomial bounds.
