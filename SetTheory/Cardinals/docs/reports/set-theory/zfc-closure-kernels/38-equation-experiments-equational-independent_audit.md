# Independent audit of the seven-equation cyclic-algebra proposal

## Outcome

The algebraic reduction is mathematically sound under the stated finite-payload
assumptions. The seven equations imply a Df3 reduct, the cyclic product reflects
all single identities, and the fresh-constant disequation method correctly
avoids the failure of preservation under arbitrary equational premises.

The executable reference is a ground-equation certificate engine. It does not
yet contain the particular term obtained from a fixed finite ZFC-equiconsistent
class theory, nor a compiled binary Turing machine. The seven equations alone
have finite models. All set-theoretic consistency content is carried by the
additional target disequation. These limitations must accompany any equation
count or claim of a potential state reduction.

This audit read the current cyclic_algebra.py and test_cyclic_algebra.py,
independently checked the algebraic argument, and opened the primary sources
listed below. It does not add a Lean formalization of the algebraic argument.

## 1. The Boolean axiom is the advertised one

The source's Sh1 is exactly

    (x | ((y | x) | x)) | (y | (z | x)) = y.

This is the single Sheffer-stroke basis proved in McCune et al.,
Short Single Axioms for Boolean Algebra, formula Sh1. Hence it is legitimate
to reason in a Boolean algebra using the derived operations

    not x = n(x,x),
    x join y = n(not x, not y),
    top = n(x,n(x,x)).

The finite semantic test alone would not establish this characterization;
the cited theorem is the necessary justification. The source's AST matches
the cited axiom exactly.

## 2. The three q equations supply the needed closure laws

Write q for the unary operator and not for Boolean complementation.
The equations are extensivity, join preservation, and

    q(not q(x)) = not q(x).

Idempotence need not be an additional axiom. Apply the last equation to
not q(x), then use the equation at x on both sides:

    q(not q(not q(x))) = not q(not q(x))
    q(q(x)) = q(x).

Normality follows from join preservation and the same complement equation.
Let a=q(0). Then

    not a = q(not a) = q(0 join not a)
          = q(0) join q(not a) = a join not a = top,

so a=0. Monotonicity follows from join preservation. Extensivity,
idempotence, additivity and complementedness therefore give precisely the
Df3 unary-operator requirements. Nothing here assumes q commutes with r.

## 3. One commutation equation gives all three

Rhom says that r preserves n, so it preserves every derived Boolean
operation. The identity r^3(x)=x makes r a Boolean automorphism with inverse
r^2. Set

    f0 = q,
    f1 = r q r^2,
    f2 = r^2 q r.

Each fi is a conjugate of q and satisfies the same closure equations.

The source Qrot is exactly f0 f1 = f1 f0. Conjugate it by r to obtain
f1 f2 = f2 f1, and conjugate again to obtain f2 f0 = f0 f2.
Thus the reduct with f0,f1,f2 is a Df3 algebra. The source translation uses
the same conjugation orientation.

## 4. The cyclic product genuinely reflects identities

For any Df3 algebra A with operators f0,f1,f2, take B=A^3 with pointwise
Boolean operations and define

    r(a0,a1,a2) = (a1,a2,a0),
    q(a0,a1,a2) = (f0(a0),f1(a1),f2(a2)).

All seven equations hold. In particular, the derived fi acts in coordinate j
as the original f_(i+j mod 3). This immediately verifies Qrot because the
original closures commute.

The first projection B -> A is a surjective homomorphism from the derived
Df3 reduct of B to A. Therefore a translated identity valid in all
seven-equation algebras must have been valid in all Df3 algebras. The
converse follows from Section 3.

This proves preservation and reflection for every single equation,
including equations with several algebraic variables. In the intended
application there is just one generator, later replaced by c.

## 5. Arbitrary equational premises are a real obstruction

It would be false to claim the analogous theorem for arbitrary sets of
equational premises.

For example, the premise f0(x)=x is consistent in Df3 with nontrivial f1.
After translation, q(x)=x forces all its conjugates fi to be identity.
Consequently the translated theory proves a conclusion that the original
theory with that premise does not prove.

The finite counterexample in the test file implements this correctly:
on the four-element Boolean algebra let f0=f2=id and let f1 be indiscrete
saturation. The corresponding cyclic product satisfies the seven base
equations, but does not satisfy q=id.

The proposal's one-validity-query construction avoids this problem. It
must not be replaced by “translate all set-theory axioms as equational
premises.”

## 6. The primary translation theorem suffices for the validity route

Andréka and Németi's published Reducing first-order logic to Df3, free
algebras, Theorem 1.6(i), gives a computable translation into the restricted
language with one ternary atom. Taking the premise set empty gives exact
reflection of validity. Their Remark 1.3(ii) identifies theoremhood in that
restricted logic with validity of a one-generator Df3 equation t=1.

For a fixed finite relational first-order sentence sigma, apply that
translation to not sigma. Do not replace this by Boolean complementation
of the translation of sigma: the source explicitly warns that the
translation need not preserve negation.

The resulting equation satisfies

    sigma has no model
      iff t(p)=1 is valid in Df3
      iff tau(t)(p)=1 is valid in every seven-equation algebra.

The source theorem is used with no equational premises; the counterexample
in Section 5 therefore has no bearing on this equivalence.

The published source is preferable to an unqualified citation of the
2011 preprint because the published theorem explicitly covers arbitrary
first-order theories and a single ternary atom.

## 7. Fresh constant and one disequation are sufficient

Let E be the seven universal equations and introduce a fresh constant c.
Let T_sigma consist of E and

    tau(t)(c) != top(c).

Because c occurs in none of E's equations, T_sigma has a model exactly
when the one-variable equation tau(t)(p)=1 fails in some E algebra.
A counterexample element interprets c. Conversely every model of
T_sigma supplies such a counterexample.

Therefore T_sigma is equiconsistent with sigma.

For the intended target, sigma must be an actual fixed finite theory whose
consistency is effectively equivalent to Con(ZFC). A finite conservative
class-theory extension is a legitimate route. The final proposal chooses
the finite CGB presentation conservative over ZF and composes its
consistency equivalence with the standard relative consistency of Choice
via the constructible universe: Con(CGB) iff Con(ZF) iff Con(ZFC).
That choice is valid; adding the correctly set-relativized Choice axiom
to CGB is an alternative, with conservativity extended by the deduction
theorem. Any function symbols must first be relationalized to fit the
exact source theorem.

A mere finite fragment of ZFC would not suffice. Nor does the existence of
some finite payload establish its numerical length or initialization cost.

## 8. Ground rewriting is the correct proof engine

The source enumerates complete finite ground rewrite chains under E.
Each move gives an axiom index, orientation, a substitution for x,y,z,
and a one-hole context. The entire substituted axiom must match the
current ground term before it is replaced by the other side.

This is sound by equational substitution and congruence. It is complete
for the intended query by the ground term-algebra argument: quotient all
ground terms over c by the equivalence generated by these rewrites.
The quotient satisfies every universal equation of E. If the two target
terms are not joined by a finite chain, that quotient is a model of E
where they differ. Thus the checker has no need for a unifier, object
variables, quantifier binders or variable-freshness checks.

The term decoder, move decoder and list decoder cover their claimed
objects. Every list-tail code is at most the previous code minus one.
Every recursive child of a positive term or context code is strictly
smaller. Hence each candidate code denotes a finite witness, and exhaustive
enumeration is mathematically a semidecision procedure for derivability.

The single constant is sufficient: a proof involving other algebraic
variables can be grounded by replacing them all by c. Conversely, replacing
fresh c by a variable in a ground proof yields the universal identity.
This is another place where freshness of c is essential.

The code's integer witness interface always constructs valid Move values.
Some auxiliary Python metadata/evaluation functions are ordinary research
utilities; their finite tests do not certify the general theorem or a
binary implementation.

## 9. Claims suitable for the report

Supported:

- an explicit seven-equation signature-reduction kernel;
- a proved ordinary-mathematical validity-preservation and reflection result;
- a concrete complete ground rewrite-certificate algorithm;
- a conditional assembly procedure yielding an equiconsistent finite theory
  once the exact ZFC-equiconsistent sigma is fixed and translated;
- finite semantic and adversarial checks of the implementation.

Not supported by the present artifacts:

- a complete expanded target term for Con(ZFC);
- a state count for a blank-tape Turing machine implementing the pipeline;
- an improved published state-count record;
- a proof-assistant verification of the cyclic-algebra or payload translation;
- a general preservation theorem for arbitrary equational premises.

The base-equation symbol count is a syntax metric. It omits the target
disequation, encodings, enumerator, table dispatch and blank initializer.
Conjugate operators also increase the length of translated terms. Direct
tree expansion of Boolean abbreviations can duplicate subterms, so the
target payload and any sharing machinery require separate accounting.

## Primary sources opened during this audit

- McCune et al., Short Single Axioms for Boolean Algebra:
  https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf
- Andréka and Németi, Reducing first-order logic to Df3, free algebras,
  Theorem 1.6(i), Remark 1.3(ii):
  https://old.renyi.hu/pub/algebraic-logic/CAIII-ANpaper.pdf
- The earlier arXiv text states the equational Df3 axioms in Section 2:
  https://arxiv.org/html/1111.0995v1

The finite CGB theorem is documented in the accompanying cyclic_proposal.md.
This independent audit checks the relative-consistency and syntax conditions
required of that input; it does not instantiate the finite payload or the
published first-order-to-Df3 translation.

