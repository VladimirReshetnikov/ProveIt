# A compact finite-theory route (proved source theorem; uncompiled endpoint)

This note records a separate source construction. It is not a new fully compiled
Diophantine endpoint or a claim that the existing numerical frontiers have been
beaten. The source theorem below is ordinary mathematics formalizable in ZFC.

## 1. The fixed-signature construction

Let P be an explicitly supplied integer polynomial in n variables, presented by
a finite acyclic arithmetic circuit with m stored gate values. Gates are integer
constants, inputs, addition, negation, and multiplication. All coefficient
recipes must be resolved into finite data or supplied as explicit finite
constant circuits; an unknown coefficient is not permitted.

Use first-order logic with equality and the fixed function signature

    0, 1;  -, L, R;  +, *, pair.

The first pair are constants, the next three functions are unary, and the last
three are binary. Let E be the finite equations for a commutative unital ring,
together with

    L(pair(x,y)) = x,
    R(pair(x,y)) = y.

The ring equations can be the eight usual universal equations: additive
associativity, additive commutativity, additive zero, additive inverse,
multiplicative associativity, multiplicative commutativity, multiplicative
identity, and distributivity. No separate nontriviality axiom is required.

For r=ceil(log2(max(1,n))), pad n inputs to 2^r leaves. Let pi_i(z) be the
composition of L and R determined by leaf i of a balanced binary tree.
For s=ceil(log2(max(1,m))), define similarly rho_j(u) for the gate-value tuple.
Pairing identities prove that every specified n-tuple and every specified
m-tuple is the projection tuple of a suitable nested pair term.

For each gate j, let G_j(z,u) be its equation, for example

    rho_j(u) = pi_i(z)                         (input),
    rho_j(u) = numeral(c)                      (constant),
    rho_j(u) = rho_k(u) + rho_l(u)              (addition),
    rho_j(u) = -rho_k(u)                       (negation),
    rho_j(u) = rho_k(u) * rho_l(u)              (multiplication).

Let o be the output gate. Define the single sentence

    theta_P := forall z exists u [ (AND_j G_j(z,u)) AND rho_o(u) != 0 ],

and the finite theory T_P=E+theta_P. Arrange the finite conjunction as a
balanced binary tree. Every term and every sentence is an actual finite
syntactic object.

## 2. Exact equiconsistency theorem

ZFC proves

    Con(T_P) <-> (forall x in Z^n, P(x) != 0).

In particular, if an inherited P is already proved in ZFC to have no integer
zero exactly when Con(ZFC), then the fixed finite theory T_P is equiconsistent
with ZFC, by a proof in ZFC. This does not select coefficients by deciding
consistency and does not assert that either consistency statement is true.

### Forward implication, proved contrapositively

Suppose P(a)=0 for a tuple of actual integers. Represent each a_i by a closed
ring numeral, using unary minus for negative integers. Form a closed nested
pair term z_a having these numerals as its first n projections.

Instantiate theta_P at z_a. The resulting existential assertion supplies gate
coordinates satisfying every G_j. By finite induction along the acyclic circuit,
the ring equations and projection equations prove that each gate coordinate
is the closed numeral for that gate's value at a. The output is therefore
zero, contrary to rho_o(u)!=0. This is a finite first-order derivation of a
contradiction from T_P. The transformation from a zero witness to the derivation
is effective and formalizable in ZFC; it is not an appeal to numerical testing.

### Reverse implication

Suppose P has no zero in Z^n. Interpret the ring symbols in the ordinary integer
ring. Choose a specific pairing bijection Z x Z -> Z, for example by transporting
the Cantor bijection on N through the elementary bijection between Z and N.
Interpret L,R as its inverse coordinates. These are set functions in ZFC and
satisfy the pairing equations.

For any integer z, its input projections form a genuine integer tuple. Evaluate
the finite circuit and encode its m values in a paired integer u. All G_j hold,
and the output is nonzero by the hypothesis. Hence theta_P holds in this set
structure. First-order soundness gives Con(T_P). This proof works inside ZFC,
where the structure and its satisfaction relation are available as sets.

## 3. Why this is more compact than a naive ground consistency axiom

The circuit values occupy one existential tuple variable, and the polynomial
inputs occupy one universal tuple variable. There are only two outer quantifiers
in theta_P, irrespective of n,m. Projection term depths are logarithmic in the
respective tuple sizes, and balanced conjunction has logarithmic depth in m.

Ignoring the separately charged representations of integer constants, the
functional syntax has depth O(log(m+n)) and length O(m log(m+n)). The complete
signature is fixed, rather than having one function symbol for every gate.
An unbalanced list of n+m quantified variables would lose this property.

The same theorem has a natural-number version: replace the ring by a
commutative semiring and compare two nonnegative circuits P+ and P-. The final
clause is that the two output coordinates differ. The ordinary natural semiring
with a pairing bijection is the canonical model.

## 4. What is still missing for an improved literal polynomial

The current C222 source has only a binary relation and numerical formula codes.
T_P has function symbols. A complete new endpoint requires an explicit
satisfiability-preserving translation to the exact target signature, a proved
logical calibration for that translation, a materialized formula-code constant,
and a replay of the entire arithmetic compiler. None of those steps is supplied
here.

An effective graph interpretation into a single irreflexive relation is a
possible route, but its exact overhead matters. Naively flattening all function
terms at once can introduce a long quantifier prefix, destroying the small-depth
advantage. Introducing term witnesses locally or using balanced definitions is
necessary before any coefficient-size advantage can be claimed.

In the present Cantor code, implication and universal quantification perform
quadratic pairing. Formula-code bit length can therefore grow exponentially in
syntactic depth. A finite, completely specified code recipe may still have an
unusable expanded coefficient payload. The source theorem alone supplies no
numerical variable count, no coefficient payload, no equation, and no new
frontier point. The measured existing equations remain the completed results.

## 5. Relation to prior sources inspected

ProveIt package105-bootstrap-certificates uses a factorial fixed point to supply
its own precision radius. Its README does not describe this finite ring/pairing
theory construction. No claim of world-first priority is made for encoding a
Diophantine sentence into consistency of a finite theory, for pair coding, or for
definitional circuit extensions.

A separate classical alternative is finite NBG. Taras Banakh's 2026 revision of
Classical Set Theory: Theory of Sets and Classes, arXiv:2006.01613, lists14 axioms
in Section5 and develops elementary class comprehension in Section8. This is an
appropriate primary source for a grounded class-theory experiment:
https://arxiv.org/abs/2006.01613
https://arxiv.org/pdf/2006.01613

Its displayed axioms use substantial abbreviations (set-restricted quantifiers,
ordered pairs/triples, functions, images). Those are not primitive syntax in the
current kernel. Expanding them and proving the exact NBG-to-ZFC calibration are
necessary before claiming that fourteen short displayed axioms yield fourteen
small numerical constants. That experiment was not completed here.
