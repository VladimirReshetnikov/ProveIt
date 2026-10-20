# A uniform obstruction to eliminating rho8's fourth independent formula

## Status and provenance

This extends the four-valued HC countermodel in the published 219-state
construction of 20 October 2026, at ProveIt commit
`26d5de6d21fa354d50e0b84fe851c289925b8d72`. It is an ordinary mathematical
proof formalizable in ZFC, accompanied by a finite algebra checker. It is
not a Rocq certificate and does not assert a lower bound on the number of
states of a Turing machine.

The inherited source is
`research/theory/restricted_rho8_strong_countermodel.md`. That proof
constructs a single model of all retained native rows, the complete gated
seed-K bundle, MP and GEN, while falsum is not designated. It previously
recorded the five replacements `U=F,truth,A,B,C`. The same model rules out
an infinite family of compound replacements, without any search bound.

## The theorem

Write the original propositional row as

\[
L(A,B,C,U)=((C\to U)\to A)\to((A\to C)\to(B\to C)).
\]

Replace the unrestricted row by any or all of the following instances:

1. `U=A`, `U=B`, or `U=C`;
2. `U` is any formula whose outer constructor is implication, universal
   quantification, or equality, including native truth code zero;
3. more generally, `U=t(A,B,C,F,truth)` is any finite expression built
   using implication and universal quantification, with arbitrary binder
   labels and optionally additional equality atoms.

Retain every other native row and the entire seed-K schema, and even add
the schemes `A→A`, `F→A`, and `A→(B→A)`. **ZFC proves consistency of this
modified calculus.** Therefore none of these replacements provides the
requested calibration to `Con(ZFC)`, assuming ZFC is consistent.

Clause 2 permits arbitrarily many independent formulas *inside* the
displayed outer constructor. Thus, for example, restricting `U` to
`X→Y` remains inadequate even when `X,Y` are independent formula inputs.
The statement does not cover all alternative three-variable bases, nor
does it cover a fourth input ranging over arbitrary membership atoms.

## Finite algebra lemma

Use the inherited implication matrix, with designated value 3 and
falsum value 0:

| → | 0 | 1 | 2 | 3 |
|---|---:|---:|---:|---:|
| 0 | 3 | 3 | 3 | 3 |
| 1 | 3 | 3 | 1 | 3 |
| 2 | 3 | 3 | 3 | 3 |
| 3 | 0 | 0 | 0 | 3 |

Direct inspection of all 256 valuations gives exactly two
nondesignated values of `L`:

\[
(A,B,C,U)=(0,3,1,2),\qquad(1,3,1,2).
\]

Every implication has value in `{0,1,3}`; value 2 is never the output of
the implication operation. In the inherited model, every quantified
formula and every equality atom has value in `{0,3}`. Native truth is 3.
Consequently any formula in clause 2 has value different from 2, so its
substitution makes `L` designated.

For clause 1, neither bad valuation has any of `A,B,C` equal to 2. For
clause 3, inspect the outer constructor of the finite expression. If it
is a variable or constant, its value at either bad tuple is in
`{0,1,3}`. If it is an implication, equality atom or quantifier, its value
is in that set independently of the values of its children. Hence no
expression in the stated family can take value 2 at either bad tuple.
This is a structural argument over arbitrary finite expressions; it
does not depend on a maximum term size or modal depth. A quantifier may
change the values of its inner formula parameters under reassignment,
but its own output remains Boolean, so this causes no exception.

## Why the full seed-K argument still applies

For clarity, the inherited model is not merely a propositional matrix.
Its domain is `HC`, the set of hereditarily countable sets. Equality is
actual equality, taking values 3 or 0. Universal quantification is 3
exactly when every instance is designated, and otherwise 0. Its native
existential is 3 exactly when at least one instance is designated.

Membership has value 3 exactly on actual membership and 0 on the
diagonal. Nondiagonal nonmembership values are 1 or 2. They are assigned
using an antichain of binary sequences indexed by `HC` and a map from
`HC` onto the natural numbers with uncountable fibers. For distinct
objects `p,u`, a coordinate witnessing the antichain property has an
object `z` outside their countable sets of members such that
`R(z,p)=1` and `R(z,u)=2`. Since `1→2=1` is not designated, the native
subset formula is designated **exactly when `p=u`**.

The complete seed-K bundle then needs only countable closure under
selected witnesses: choose a witness for each supported parameter,
start with a witness for the seed when available, and close the
resulting countable set under that selected-witness function. The union
of the finite closure stages is a countable subset of `HC`, hence an
element of `HC`. Every chosen member satisfies the required support
clause; equality of subset parameters gives the remaining closure
condition. The inherited proof treats coincident bound-variable labels
separately. Failed arithmetic gates emit native truth and are valid.

The interpretations of the retained rows, the seed-K bundle, and the
inference rules are unchanged. The finite algebra lemma adds designated
instances to the *same* model. Falsum remains nondesignated because
diagonal membership is 0. Induction on a finite derivation therefore
proves in ZFC that falsum is not derivable in the enlarged restricted
calculus.

## Consequence for earlier candidate screens

This closes the earlier unsolved suggestions `U=A→A`, `B→B`, `C→C`,
`A→B`, `A→C`, `B→A`, `B→C`, `C→A`, and `C→B`, as well as all more
complicated finite implication/quantifier expressions in the same three
parameters. Their failure is no longer merely a failure of bounded
condensed-detachment search. A successful reduction must preserve a
genuinely independent fourth formula in this row, permit fourth-input
membership atoms in a sufficient family, or change the propositional
basis itself (for example, the previously calibrated two-row G/H basis).

Run `python uniform_rho8_obstruction.py` to regenerate the finite
premise certificate. The certificate does not substitute for the
inherited infinite-domain proof or the structural argument above.
