# Native controller synthesis by arithmetic carries: an exact boundary

This note supplies a precise compiler criterion and an obstruction for the
current delayed-loader controller. It does **not** improve the complete
76-operation certificate. The six/eight-operation queue interface remains
conditional. Its purpose is to separate a potentially cheap arithmetic
machine architecture from two unsound shortcuts: assigning arbitrary state
codes to arithmetic carries, and eliminating all controller witnesses.

## 1. A global affine equality is already an exact carry automaton

Fix a radix b>=2, integer coefficients a_1,...,a_r,h, and fixed integer
endpoint states c_start,c_final. For t>=1 put q=b^t and H=(q-1)/(b-1).
Supply ordinary radix-b words Z_i in [0,q). Then

    sum_i a_i Z_i + h H + c_start = q c_final                 (1)

is equivalent to an integer carry path of length t with the prescribed
endpoints and local transitions

    b c_(j+1) = c_j + h + sum_i a_i digit_j(Z_i).             (2)

The forward implication needs no supplied carry words or divisibility
predicate. Reduce (1) modulo b: its units numerator is divisible by b, so
c_1 from (2) is an integer. Subtract the units identity and divide by b.
The same argument applies to the remaining words and the remaining
repunit. Induction ends with c_t=c_final. Conversely, multiply (2) by b^j
and sum; the carry terms telescope to (1).

This is genuinely a *finite* controller. Set

    U=abs(h)+(b-1) sum_i abs(a_i),
    B=max(abs(c_start), ceil(U/(b-1))).

Whenever abs(c_j)<=B, (2) gives abs(c_(j+1))<=(B+U)/b<=B.
Thus every path reconstructed from (1) stays in the fixed integer interval
[-B,B]. The coefficients, endpoints and B are fixed independently of t
and of the varying ordinary input.

For vector carries, use one copy of (1) for each coordinate. The same
coordinatewise proof gives a fixed finite box. No state-word positional
injectivity premise is needed: the local arithmetic, rather than a native
linear encoding of arbitrary state histories, supplies the states.

This yields an exact synthesis test. A desired transducer can use (1)
without extra typing only if its accepting labelled language equals the
accepting language of the entire arithmetic carry graph. Merely finding
state codes satisfying (2) on the desired edges proves completeness, not
soundness: other integral transitions in [-B,B] remain available. Both
the omitted-edge question and endpoint accessibility must be checked.

For example, with ternary words, c_start=c_final=0 and local weights
(1,1,-1), the one-addition equation Z_1+Z_2=Z_3 is exactly the ordinary
two-state ternary adder with carry states 0 and 1. It is an inexpensive
controller relation, but no universal queue simulation is claimed for it.

## 2. Paid affine schedule

Assume first that all displayed coefficients in a dense schedule are
nonzero, with the r stream coefficients and h evaluated by scalar
multiplications. Partition positive and negative terms between the two
sides if signed fixed numerals are not used. Computing the r products,
the hH product, the q*c_final product and combining the terms with the
fixed c_start takes at most

    (r+2) multiplications + (r+1) additions/subtractions.

This is a schedule upper bound, not a minimality claim; coefficients 0,
1 or -1 can reduce it. One literal signed schedule is:

1. Compute a_i*Z_i for each i: r multiplications.
2. Sum these r registers: r-1 additions.
3. Compute h*H and add it: one multiplication and one addition.
4. Add the fixed c_start: one addition.
5. Compute q*c_final and compare: one multiplication, free equality.

If H is not already available, (b-1)*H+1=q costs another multiplication
and addition (only one addition when b=2). Thus the dense r=4 ternary
schedule is at most 13=7M+6A operations including H, **with power geometry and
stream bounds still external**. H is positive for t>=1. The carries are
deduced integers rather than existential coordinates, so their signs do
not violate a positive-witness convention. The ledger does not establish
strict positivity of the Z_i: a complete application must prove positive
stream witnesses, as the existing queue interface does, or pay offsets.
These numbers are conditional
controller costs and must not be added to an unrelated mask kernel without
proving compatible geometry and a universal machine contract.

## 3. The current erase/copy controller has no nontrivial affine embedding

Consider the existing delayed-loader machine from
`../../verification/explore_delayed_blank_raw_queue.py`. Whenever an erase
state E can reach its accepting state F, its transition table includes:

| State | Read | Append | Next |
|---|---|---|---|
| E | (0,0) | (0,0) | E |
| E | (1,0) | (0,0) | E |
| E | (0,2) | (0,0) | E |
| F | (0,0) | (0,0) | F |
| F | (1,0) | (1,0) | F |
| F | (0,2) | (0,2) | F |

Try to assign fixed integer or rational carry codes c(s) and fixed weights
a_0,a_1,b_0,b_1,h satisfying every transition's necessary condition

    3 c(next) = c(state)+h+a_0*d_0+a_1*d_1+b_0*e_0+b_1*e_1.  (3)

The difference of the first two erase-loop equations forces a_0=0.
The first and third force 2a_1=0. The accepting loops then force b_0=0
and 2b_1=0. The zero loops give c(E)=c(F)=h/2. Every state that can reach
F has the same carry code, by backwards propagation along (3).

Consequently the only resulting identity is

    h H + h/2 = q h/2,

the repunit identity. This proof applies coordinatewise to any fixed
number of affine carry equations. Arbitrarily large codes or additional
affine carry coordinates do not help this particular controller.

This is a local table obstruction, stronger in scope than a finite code
search, but not a lower bound on controller verification. It assumes the
arithmetic relation must admit **all** syntactically accepting controller
paths. A compiler may restrict to queue-compatible paths, add nonlinear or
typed witnesses, or change the machine. In particular, retaining only the
zero self-loop after acceptance preserves genuine zero-queue extensions
and removes the stated accepting-loop premise. That simple repair alone
does not provide an arithmetic controller.

## 4. A single-coordinate affine-carry queue cannot supply a universal replacement

There is also a machine-independent obstruction for the most direct new
architecture suggested by Section 1. Use one radix-three FIFO coordinate
N in [0,W), W=3^m, initialized by the ordinary input N=x. Suppose its
entire controller is the affine carry relation

    3 c' = c+h+u*d+v*e,

with fixed integer coefficients and fixed initial and final carries c_s,c_f.
The target is the zero queue with carry c_f. Require that this target has
the zero-read, zero-append self-loop used for accepted zero extensions.
That requirement is exactly h=2c_f.

For any accepting history, the global carry and FIFO identities give

    uD+vA+hH+c_s=q*c_f,    D=x+WA,    2H=q-1,

and hence the time power cancels:

    u*x+(uW+v)*A = K,             K=c_f-c_s.                  (5)

Here x,A are nonnegative; the carries are fixed integers. If u is
nonzero, put

    B = floor(max(abs(v),abs(K))/abs(u)).

Every accepted input satisfies x<=B. Indeed, if W<=abs(v)/abs(u), then
x<W gives the result. Otherwise uW+v has the sign of u. Multiplying
(5) by that sign gives

    abs(u)*x + abs(uW+v)*A = sign(u)*K,

which again bounds x by abs(K)/abs(u). The possible zero coefficient
uW+v=0 lies in the first, bounded-width case. Thus this architecture
recognizes only a finite ordinary-input set when u is nonzero. No
coefficient-size search, coprimality hypothesis or state-code bound is
used in this proof.

If u=0, the local relation is independent of the removed digit d. For
the *entire* arithmetic carry graph, either c_f is unreachable from c_s,
or a fixed control/output path reaches it independently of x. In the
second case append zero for another m steps at c_f to clear any queue.
Choosing any adequate width W>x then accepts every input. Consequently
this case recognizes either all ordinary inputs or none. This second
conclusion assumes there are no additional read-dependent edge filters.

An equivalent local conservation law is useful when designing variants.
Set Y=vN+W(c_f-c). A queue step satisfies

    3Y' = Y-(uW+v)d.

The global version is Y_start=(uW+v)D at a zero endpoint. It agrees with
(5) after substituting D=x+WA. The checker derives both residuals
independently and checks local integer transitions with signed weights.

This rules out a universal replacement using **one queue coordinate,
one unfiltered affine carry equation and an absorbing zero endpoint**.
It does not rule out the current two-coordinate queue, multiple carry
equations, nonlinear relations, a coded-input bridge, or a terminal
state without that zero self-loop. Those are substantive design changes,
not consequences of the thirteen-operation conditional ledger.

## 5. Several coordinates: an exact reduction to one width parameter

The cancellation in Section 4 survives with d queue coordinates and k
carry coordinates. Let U,V be fixed k-by-d integer matrices, and let the
entire local carry relation be

    3 c' = c+h+U*d+V*e.

Here c,h are vectors, and d,e are the read and append trit vectors. The
absorbing zero endpoint requires h=2c_f coordinatewise. If I is the
initial queue vector, the complete zero-reaching condition is equivalent
to the existence of a nonnegative integer append vector A satisfying

    U*I+(WU+V)*A = c_f-c_s.                                 (6)

Necessity follows by telescoping and D=I+WA. For sufficiency, given A
satisfying (6), set D=I+WA and choose a power q=3^t larger than every
stream and their required joint sums. The global carry equalities now
hold. Section 1 reconstructs the unique integer carry path in its fixed
box; the FIFO lemma reconstructs the queue and its zero endpoint. This
uses the entire arithmetic carry graph, with no extra state or edge
filters. Strict positivity of selected streams can be added as ordinary
linear inequalities in A; it does not affect the reduction. Arbitrary
zero extensions account for the freedom to choose q this large.

In the actual proposed geometry W=3L, I=(x,L), fix an ordinary numerical
input x. Equation (6), nonnegativity and x<L define a **one-parameter
Presburger family** in the width parameter L: all quantified variables
occur linearly, with coefficients polynomial in L. The same is true for
any fixed affine initialization in x,L. Theorem 1.15, Property 1, of
Bogart, Goodrick and Woods proves that the set of admissible integer
widths L is eventually periodic. This is an application of their theorem
to (6), not a claim that their paper studies queue machines.
See [the primary paper, pp. 5-6](https://arxiv.org/pdf/1608.08520).

Once a valid cutoff, period and admissible residues are available, the
restriction L=3^ell is decidable: inspect the finitely many smaller powers
and the eventual finite cycle of 3^ell modulo the period. The paper's
proof uses constructive reductions and Presburger quantifier elimination
in Sections 2-4. The subsequent
[effectivity audit](input_bridge_presburger_effectivity.md) checks those
constructions for this parameter-only sentence and gives a uniform
algorithm computing a cutoff, period, exceptions and admissible residues.
It closes the original effectivity gap: adding finitely many unfiltered
affine carry coordinates with this absorbing zero endpoint still gives
a decidable ordinary-input language. The full quantifier eliminator is
not implemented; the separate checker implements the terminal periodicity
and powers-of-three procedure and a hand-eliminated matrix example.

## 6. Even arbitrary witness-free polynomial equalities cannot capture this language

The unchanged controller admits a stronger, fully scoped obstruction,
provided an erase state is syntactically reachable from its initial state.
This productive-prefix hypothesis is essential: an empty accepted language
satisfies every polynomial identity. Fix such a prefix to an erase state E,
and let its
length be r and its four stream values be pD_i,pA_i. For each k>=1:

* At E, read k pairs from {1,2} x {0,1} and append zero. These pairs are
  all non-delimiters, so E remains unchanged.
* Read the delimiter (0,1), append zero and enter the accepting state F.
* At F, copy k pairs from {0,1} x {0,1}.

Let V_k be the 2^k integers whose k ternary digits are in {0,1}, and let
H_k=(3^k-1)/2. The erasing words range independently over

    E_0 in H_k+V_k, E_1 in V_k,

and the final copying words range independently over C_0,C_1 in V_k.
The resulting accepted stream tuple has

    q_k = 3^(r+2k+1),
    D_i = pD_i + 3^r E_i + 3^(r+k) [i=1] + 3^(r+k+1) C_i,
    A_i = pA_i + 3^(r+k+1) C_i.                              (4)

For each fixed k this is an invertible affine change of four variables
over the rationals. Every set in this Cartesian grid has 2^k values.
Excluding C_i=0 makes all four streams positive and leaves 2^k-1 values
per C_i. The common bound D_0+D_1<q_k also holds: the prefix contribution
is at most 2(3^r-1), the erase contribution at most
3^r*3(3^k-1)/2, and the delimiter contributes 3^(r+k). Their sum is
strictly less than 3^(r+k+1); the two final copying words sum to at most
3^k-1. Thus even these positive, jointly bounded accepted tuples suffice.

Suppose a polynomial P(D_0,D_1,A_0,A_1,q) over the rationals vanishes on
every such accepted controller tuple. Let d be its total degree. For any
k with 2^k-1>d, substitute (4) and q=q_k. A polynomial of degree at most
d in each of four variables which vanishes on this Cartesian grid is the
zero polynomial: apply the univariate root bound successively in each
variable. Invertibility of (4) then gives

    P(D_0,D_1,A_0,A_1,q_k) = 0

identically in its first four arguments. Infinitely many distinct q_k
have this property, so applying the univariate root bound to each
coefficient as a polynomial in q shows P=0 identically.

Hence the full current controller language, even restricted to positive
streams with the paid joint bound, satisfies **no nonzero polynomial
identity in just its four streams and q**. No finite collection of such
identities can characterize it. The controller is a proper language:
for example, its initial state rejects a delimiter as the first read.

This does not prohibit existential polynomial descriptions, extra witness
words, bounds expressed through witnesses, inequalities, joint equations
using the queue transport, or a controller that recognizes a smaller
sufficient language. It is not a universal operation lower bound. It
does rule out replacing the current independent controller predicate by
a clever witness-free high-degree equation in the same five supplied
integers.

## 7. Evidence and next direction

`audit_native_controller_carry.py` checks the six actual table entries
on every productive supplied fixture, the exact rational rank of their
linear constraints, the global carry reconstruction on bounded arbitrary
tuples, explicit Cartesian-grid paths, positivity and the joint bound.
It separately checks the scalar-queue conservation law and the finite
ordinary-input bound from Section 4 against arbitrary small tuples.
It also checks that the grid's polynomial evaluation matrix has full
column rank through total degree three. This finite rank check supports
the construction; the root-bound proof above covers all degrees.

Default execution compares its adjacent saved receipt. `--write` creates
or refreshes that receipt. The original queue proof, source and receipts
are unchanged. No complete-certificate bound, positive universal witness
map or Lean formalization is claimed. Section 4's scalar-queue theorem
received an independent mathematical review with no findings. The carry
criterion, exact ledger, affine obstruction and polynomial obstruction also
received an independent proof/source/receipt review; its productive-prefix
scope clarification has been incorporated. Section 5's exact reduction and
eventual-periodicity consequence were checked against the primary theorem.
The separate effectivity audit subsequently received two independent
scoped proof/source/default reviews, including the primary reductions.

The useful remaining target is a proved small family of typed witness
streams that restricts a carry graph to the desired language, or a
computation model outside the unfiltered affine/absorbing-zero scope.
The restrictions must be designed together with erasure, ordinary-input
loading and acceptance. Encoding a large existing controller by larger
free state numerals cannot solve the obstruction.
