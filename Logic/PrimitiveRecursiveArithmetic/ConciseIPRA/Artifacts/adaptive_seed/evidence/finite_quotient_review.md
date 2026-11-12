# Independent audit: unary coordinate bounds exclude infinite unital quotients

## Verdict

The proposed theorem is valid over the standard natural numbers, under the
stated domain-closure and total unary-bound assumptions. Arbitrary subsets
and arbitrary equivalence relations do not invalidate it. No compatibility
of the binary operation with the equivalence relation is needed for the
finiteness argument; that makes the result stronger than the application
to a well-defined quotient magma.

The important technical repair is to replace each bounding function by its
nondecreasing envelope before composing inequalities.

## Precise statement

Let d be a fixed nonnegative integer. Let D be a subset of N^d, let E be an
equivalence relation on D, and let e belong to D. Let f:D x D -> D.
For every output coordinate i, suppose one of the following holds uniformly
for all x,y in D:

- f_i(x,y) <= C_i, for a fixed natural number C_i;
- f_i(x,y) <= F_i(x_j), for a fixed coordinate j and total unary F_i:N->N;
- f_i(x,y) <= F_i(y_j), with the analogous data.

Assume only the pointwise unit laws

    f(e,z) E z,       f(z,e) E z       (z in D).

Then D/E is finite. More precisely, there is a composition Phi of at most d
maps chosen from L(z)=f(e,z) and R(z)=f(z,e), and natural constants B_i,
such that Phi(D) is contained in the finite box product_i [0,B_i], and
Phi(z) E z for every z in D. Consequently

    |D/E| <= product_i (B_i+1).

For d=0, N^0 is a singleton, so the claim is immediate with the empty word.
For a nonempty d-dimensional domain the argument below applies directly.

## Bounding-function normalization

Replace F_i by

    Fbar_i(n) = max { F_i(m) : 0 <= m <= n }.

Then Fbar_i is total and nondecreasing and still bounds the corresponding
coordinate. This makes all compositions of inequalities valid. If the
original functions are primitive recursive, these finite maxima are also
primitive recursive. The theorem itself only needs ordinary total unary
functions, not effective descriptions.

## Partial dependency maps

For each output coordinate i fix one of its permitted bounding descriptions.
It is harmless if more than one exists; choose one once and for all.

If the bound controls a left-input coordinate x_j, then L_i is bounded by
the constant Fbar_i(e_j), while R_i is bounded by Fbar_i(z_j).
If the bound controls a right-input coordinate y_j, the roles reverse.
A constant-bounded coordinate is constant-bounded under both letters.

Thus each letter A in {L,R} defines a partial map delta_A from {1,...,d}
to itself: delta_A(i)=j when A_i is bounded by a unary function of z_j;
it is undefined when A_i has a constant bound. Each state i has at least
one letter under which its transition is undefined.

For a set S of currently live dependency indices, put

    delta_A(S) = { delta_A(i) : i in S and delta_A(i) is defined }.

If S is nonempty, choose i in S and a letter A with delta_A(i) undefined.
Then

    |delta_A(S)| <= |S|-1.

This remains true even when another surviving state maps back to the
index i just killed: at most |S|-1 states contribute images, and collisions
can only reduce the count further. This addresses the most plausible
apparent objection to the argument.

Starting with all d indices, repeat this choice. After at most d letters
A_1,...,A_k the live set is empty.

## Composition order and uniform boundedness

Use the letters in outer-to-inner order:

    Phi = A_1 o A_2 o ... o A_k.

A bound on output coordinate i of A_1 either is already constant, or refers
to one coordinate of the next inner map A_2. Follow this unique dependency
path. The construction ensures that every such path encounters an undefined
transition within k steps. At that transition it acquires a constant bound.
Apply the previously traversed nondecreasing unary envelopes to that constant.
The resulting B_i is independent of the original input z.

Equivalently, prove by induction on the word prefix that every composed
output is either constant-bounded or controlled by one index in the current
live set. Empty live set means all coordinates have uniform constant bounds.

Reversing the implementation order of the word without adjusting this
reasoning would be an error. The displayed outer-to-inner convention is the
one the dependency construction proves correct.

## Quotient finiteness uses no extra congruence

Closure f:D^2->D ensures every intermediate application of L and R remains
in D. The pointwise unit laws therefore apply to every intermediate value.
For any composition Phi of these maps, transitivity gives

    Phi(z) E z.

This conclusion does not substitute E-equivalent arguments into f; it simply
uses A(w) E w at each intermediate w. Therefore no E-congruence assumption
is needed here. Since Phi(D) is contained in D intersected with a finite box,
every E-class meets that finite set. The quotient has finitely many classes.

## Scope and necessary qualifications

1. The conclusion is external finiteness over standard N. In a nonstandard
   model, a bounded box with nonstandard bounds can be externally infinite.
   An internal boundedness statement may still obstruct internally infinite
   arithmetic, but that would require a separate formalized argument. For
   refuting an interpretation that must work in the standard source model,
   the standard-N theorem already suffices.
2. The output tuple must be given by functions satisfying the coordinate-bound
   property and must map D^2 into D. A relation defining a unique output modulo
   E, with witnesses or minimization not realized by such terms, is not covered.
3. No definability or computability of D or E was used. The unit representative
   e may be any chosen member of D; it need not be term-definable.
4. No associativity, commutativity, cancellation or compatibility with E was
   used. A two-sided identity modulo E is enough.
5. Infinite is essential. Finite quotient magmas may satisfy all the hypotheses.
6. The result is new relative to the present investigation only; this audit
   makes no literature-wide novelty claim.

## Sanity-check escape example

The natural-number operation

    f(x,y) = y if x=0, and x otherwise

has two-sided identity zero and an infinite underlying magma. It escapes the
hypotheses: at x=0 its output is unbounded in y, excluding every bound F(x),
and at y=0 its output is unbounded in x, excluding every bound G(y).
It also has no uniform constant bound. Thus it does not contradict the
obstruction and illustrates why relationally defined case distinction can
leave the restricted term clone.
