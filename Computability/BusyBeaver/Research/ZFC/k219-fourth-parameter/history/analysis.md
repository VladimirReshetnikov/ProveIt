# Membership-headed rho8: what the broader matrix argument proves

Source-only mathematical analysis by opening_encoder, 20 October 2026.
No candidate or proof assistant was executed for this note. The target remains
an exact machine with at most 218 states; none is established here.

## Exact semantic hypotheses

Use a nonempty domain D, a value set V, distinct values 0,t, and **the single
designated value t**. Write J for implication. Assume:

1. J(x,0)=t when x!=t, and J(t,0)=0.
2. J(0,x)=t.
3. J(t,x)=t iff x=t.
4. Quantification returns t if every assignment instance is t and returns
   exactly 0 otherwise. Equality, if used in the interpreted matrix, is
   actual identity with values t/0.
5. Atomic membership is an arbitrary r:D×D→V, with r(x,x)=0.
6. Native evaluation is compositional, uniform under variable renaming, and
   validates every emitted restricted rho8 and the unchanged gated V/K
   bundles under every assignment. Code0 is truth t, including I(0,0)=0.

The designation assumption matters. With several designated values, the
stated t-only implication law is insufficient; it must be strengthened or
one must first justify a quotient to a single designated value.

## Two concrete consequences of the restricted row

First use A=1=F, B=0=truth, C=73=R(2,3), U=5=R(1,0).
All four variable labels can be assigned independently. For c=r(w,q)!=t
and u=r(z,p), if J(c,u)!=t then

- J(J(c,u),0)=t;
- J(0,c)=t;
- J(t,c)!=t and J(t,J(t,c))!=t;
- consequently L(0,t,c,u)!=t.

Validity therefore forces J(c,u)=t whenever c is a nondesignated atomic
membership value, for **every** atomic membership value u. When c=t,
hypothesis 3 supplies the other case. Thus the designatedness of implication
between any two membership atoms is exactly material implication. It follows
that the native Sub(a,b) denotes ordinary inclusion for the designated
relation R*(x,y) iff r(x,y)=t. This part uses only the designation condition
on Q; its nondesignated output need not be exactly 0.

Second, the unchanged K schema forces R* to have at least one edge under
the Boolean-Q hypotheses. Suppose it were empty. Choose its enabled true
matrix instance c=0 and public labels a=1,b=2. In W the existence of a
matrix witness is true but existence of a matrix witness belonging to C
is false, hence W=0. Its H is Boolean because its outer constructor is Q.
Therefore H→N W has value t, its outer Q has value t, and the bare K part
has value0. The other bundle conjunct V has value J(r,0)=t since r!=t.
The literal bundle N(I(V,Qcore)) consequently has value0, contradiction.
This does not need a prior general derivation of set-theoretic singleton or
separation; it checks the actual true-matrix K instance.

Now take A=C=0=truth, B=73=R(2,3), U=R(0,73). Labels0,73 are disjoint from
2,3. Assign U to the known designated edge and B to any membership value b.
The row becomes

    L(t,b,t,t) = J(t, J(t, J(b,t))).

Its validity and hypothesis3 imply J(b,t)=t. Combining this with hypothesis1
shows that implication from a raw membership value to a Boolean consequent
has exactly its classical meaning. This extra fact is needed in H; atomic
Sub alone did not establish it.

## A correct ordinary-K interpretation within this class

Translate an ordinary matrix recursively: replace each membership atom by
NN of that atom; leave actual equality Boolean; commute the translation
with implication and quantification. Hypotheses1–4 imply that every translated
subformula has value0 or t and exactly its ordinary truth value. Merely
putting NN around an arbitrary *raw* compound matrix does not prove agreement
with its ordinary classical interpretation.

Use the translated matrix's actual native numerical code as the K private
label. The existing strict support bound makes that label fresh from its
own formula; double negation gives a nonzero matrix code, avoiding the sole
zero alias. Public labels can be renamed/padded as in the original finite
calibration, but the private label must be chosen **after** translation.
There is no claim that one may preserve the original matrix's old code.

Native Sub is ordinary inclusion by the first consequence. W and the
quantified intermediate expressions are Boolean. Raw membership antecedents
in H have classical implication into Boolean consequents by the second
consequence. Hence the exact unchanged K bundle for each translated matrix
has the ordinary K meaning, with support retained. Irreflexivity follows
from r(x,x)=0. Thus any model in this explicitly described class supplies
an ordinary K+IR model, and the inherited ordinary K calibration applies.

This strengthens the four-value observation: no atomic surjectivity is
needed. It is still a semantic reduction for a restricted model class.

## The remaining lower-bound gap

There is currently no justification that every consistent modified native
calculus has one of these models. Ordinary classical first-order completeness
cannot be used here: the missing unrestricted propositional basis is one
of the hypotheses needed to invoke it. A Lindenbaum construction for the
actual nonstructural code-coupled axioms produces a general algebra; it
does not automatically make quantifiers Boolean or its atomic relation
surjective. Variable renaming is a metatheorem in the stated assignment
semantics, not an unproved admissible syntactic substitution rule for the
code-coupled rho8 family.

Removing exact Boolean Q from the argument has a concrete obstruction in
the proof, rather than just a notational issue. In the actual K core,

    Sub = Q_z (R(z,p) → R(z,u))
    W   = Q_y (matrix → N Q_y(matrix → N R(y,C)))

occur together as Sub→W. If Q returns two different nondesignated values,
our atomic implication lemma does not control this implication: neither
operand must be an atomic value or 0. Double-negating the *matrix* does
not normalize these built-in quantifiers. Also, without Boolean H the
true-matrix argument above can no longer infer H→t is designated. Thus
replacing 'Q returns0' with merely 'Q is nondesignated' is not valid without
another lemma.

A specific route worth testing is a syntactic negative-fragment bridge,
not a general semantic completeness assertion. The desired intermediate
contracts are:

- derivability of implication composition/monotonicity for Booleanized
  formulas using only the restricted rho8 plus retained quantifier rows;
- normalization, in the provable implication sense, of the particular
  Sub and W quantifications to their double negations;
- then the literal translated K instance above, with its actual matrix-code
  binder chosen after translation.

The K support clause suggests a concrete reification target. With a matrix
P independent of the two public variables, its container would satisfy

    P ↔ exists x R(x,C),

because support gives membership→P and W supplies a member when P holds.
This is a candidate **syntactic obligation**, not yet a derivation: extracting
those implications and eliminating existential witnesses must not silently
use the very classical basis being recovered. It represents P by a quantified
membership formula, not immediately by an arbitrary atomic value. A stronger
atomic biconditional/replacement lemma would close the gap, but has not been
proved. This target isolates a small proof obligation that exploits K rather
than asking for atomically rich models by assumption.

The immediate computational result remains only the measured 205-DAG
membership layouts. Selective allocation now reaches222 raw states according
to root's ongoing work; neither calibration nor a <=218 verified machine
follows from the semantic argument in this note.
