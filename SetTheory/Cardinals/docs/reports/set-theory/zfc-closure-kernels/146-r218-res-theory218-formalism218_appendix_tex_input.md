---
title: "Formalism research below the published 219-state machine"
date: "20 October 2026"
---

# Results and proof boundaries

This appendix records new logical investigations made after the release of
K219 at ProveIt commit `26d5de6d21fa354d50e0b84fe851c289925b8d72`.
The published source has 206 DAG nodes and 4,744 primitive occurrences.
The target of this research is a machine with at most 218 working states.
A machine-level reduction that retains the published calculus does not
depend on any unproved theory change investigated here.

The new formalism results have four distinct statuses:

| Result | Status |
|---|---|
| A uniform obstruction to a large family of fourth-parameter restrictions | Proved in ZFC, using the inherited full-HC model and a new finite algebra certificate |
| The fused row D is exactly equivalent to T plus explicit explosion | Proved by an explicit 211-node implication certificate |
| A nontrivial terminal cluster in a specified Kripke semantics yields an ordinary calibrated model | Proved for that semantic class; no representation theorem is asserted |
| Replacing the original rho6 by T plus explosion preserves Con(ZFC) | Open |

No changed-calculus source in the finite hardware screens reaches 218.
Their costs are bounds inside the stated preserved-row compiler model,
not state lower bounds for arbitrary Turing machines. Bounded proof-search
failures below are reported as search outcomes, not as independence proofs.

The existing G/H calibration and older encoding-family work remain in the
previous frozen research reports. They are not repeated or relabeled as
new results here.


# Logical calibration required by an unchanged-source reduction

The new 219 release at ProveIt commit
`26d5de6d21fa354d50e0b84fe851c289925b8d72` changes the implementation of
four equality tests while retaining the calibrated native calculus. Its
`report/sections/calibration.tex` states the internal equivalence

\[
\operatorname{Halt}(M_{219},\mathrm{blank})
\quad\longleftrightarrow\quad
\exists d\;\operatorname{Proof}_{\mathrm{ZFC}}(d,\bot).
\]

The inherited comparison uses effective transformations of finite
refutations, not an assumption of soundness or a set model of all of ZFC.
The source interfaces retain the formula codes, exceptional code-zero
convention, equality rows, arithmetic freshness gates, complete seed-K
bundle, retained theorem stack, and contradiction code 1. The equality
macro is total on every natural input and clears the same two scratch
registers, so exceptional and coincident numerical codes stay within the
original calibration.

For a further change that retains `sites219.json` exactly, the logical
part needs no new theorem about T, explosion, G/H, or a weakened set theory.
It is enough to prove the exact binary table implements that source and
to establish its blank startup. Specifically:

1. Every guarded primitive interface must be total on arbitrary natural
   logical registers, arbitrary permitted gap, and every finite nonempty
   spare list. It must return a complete valid frame with the same source
   outcome, take positive finite time, and have no intermediate machine
   halt unless the source primitive halts.
2. A separate literal blank-tape simulation must reach the required source
   entry and logical register vector. Equality of the physical gap, spare
   count, and tape support with the predecessor is unnecessary, but every
   field in the new frame must be checked.
3. The transition table, state count, start state, terminal outcome, and
   canonical relabeling must describe the exact bytes under review.

Concatenation of the finite primitive simulations then gives the two
directions of blank-halting equivalence. Positive duration prevents an
infinite source trace from corresponding to only finitely many machine
steps. Composing with the pinned finite-refutation translations gives,
inside ZFC,

\[
\neg\operatorname{Halt}(M,\mathrm{blank})
\quad\longleftrightarrow\quad \operatorname{Con}(\mathrm{ZFC}).
\]

These requirements do not assume `Con(ZFC)`. They also do not assert
unconditional nonhalting or minimality of the state count. The inherited
and new endpoint proof boundary is an ordinary mathematical argument,
formalizable in ZFC and supported by executable symbolic certificates;
it should not be described as a newly compiled Rocq or Lean theorem for
the exact final machine bytes unless such a theorem is actually supplied.


# A single row for universal instantiation and explosion

## An exact logical equivalence

Write \(P=Q_i A\), and retain the released classical implicational row
\(L\). Define

\[
 D(i,A)=((Q_i A\to F)\to F)\to A.
\]

The following three formulas are derivable using **only** the retained
implicational row and modus ponens:

\[
\begin{aligned}
D(i,A)&\to(Q_i A\to A),\\
D(i,A)&\to(F\to A),\\
(Q_i A\to A)&\to((F\to A)\to D(i,A)).
\end{aligned}
\]

Therefore replacing the original rho6 by the single scheme D gives
exactly the same theorem set as replacing it by T and explicit explosion.
All other axioms and inference rules may be retained unchanged. This is
an equivalence of the two *modified* calculi. It does not establish their
consistency equivalence with the original native calculus or ZFC.

Here is a short proof of all three implications. The deduction theorem is
used only in the pure implicational subsystem, so there is no hidden
generalization rule applied to an open assumption.

1. Assume D and P. Under a further assumption \(P\to F\), modus ponens
   gives F. Discharge that assumption to obtain \((P\to F)\to F\), and
   apply D to get A. Discharging P and D gives the first implication.
2. Assume D and F. The K combinator gives \((P\to F)\to F\), so D gives
   A. Discharging the assumptions gives the second implication.
3. Assume \(P\to A\), \(F\to A\), and \((P\to F)\to F\). Under an
   additional assumption \(A\to F\), composition gives \(P\to F\),
   hence F and then A. Discharge \(A\to F\), obtaining
   \((A\to F)\to A\), and use Peirce's law to obtain A. Discharging the
   first three assumptions gives the third implication.

For an independently checkable finite certificate, all three proofs have
been expanded using only these schemes:

\[
\begin{aligned}
K(X,Y)&=X\to(Y\to X),\\
S(X,Y,Z)&=(X\to(Y\to Z))\to((X\to Y)\to(X\to Z)),\\
P(X,Y)&=((X\to Y)\to X)\to X.
\end{aligned}
\]

The inherited `CD230.v` proves `thm_K`, `thm_S`, and `thm_P` from rho8
alone. Substituting their derivations for each corresponding certificate
leaf transports the proof into the native calculus. No use of the deleted
rho6, falsum explosion, quantifier normality, or a semantic completeness
assertion is hidden in this transport. F is an arbitrary formula parameter
throughout this purely propositional proof.

The retained certificate has **211 nodes**, consisting of **106 explicit
K/S/Peirce instances and 105 modus ponens steps**. Its three roots are
nodes 44, 72, and 210. The verifier checks exact formula structure and
earlier-node references; it performs no unification, proof search, or
truth-table inference. Run

```sh
python3 certify_fused_d.py --verify-only
```

The code-level exceptional identity \(I(0,0)=0\) causes no difficulty:
the certificate is a schematic proof under arbitrary substitutions into
the native implication constructor. Specializing P to \(Q_i A\) is valid
even though P then contains A.

## Literal source construction

The old rho6 emitter has 283 primitive occurrences. In the published
219 source, its exact primitive interval is \([895,1178)\), with zero-based
half-open indices. The relevant closed macro word is

```text
binder, binder, matrix, Q, N, Q, N, matrix, I.
```

The binder and matrix pushes each have 26 leaves, Q has 29, N has 47,
and I has 27. The first binder push is the closed interval
\([895,921)\); the outer Q is \([1049,1078)\). Deleting those two
closed fragments produces

```text
binder, matrix, Q, N, N, matrix, I,
```

which emits D and has 228 leaves. The full primitive word decreases from
4,744 to 4,689 leaves. The axiom operation still emits ten outputs.
Other than the altered axiom formula, its source interface is unchanged.

The exact two-deletion layout has 207 source DAG nodes, but its preserved
hardware row cost is 222: the bare cost is 220, and two inherited helper
roles cannot be covered by its live source nodes. It also has a nonzero
context penalty. This is why a shorter primitive word is not itself a
smaller binary machine.

The finite layout census varied the ordered binder/matrix parameter
assignment over six choices, tested both whole-row splice locations,
and distributed the seven macro atoms over the three original closed
source chunks. Together with the exact deletion, this gives **103
layouts**. The minimum protected hardware bound is **221**, with 208 DAG
nodes and zero helper or context penalties. The minimum DAG count alone
is 207. The best bound is still three states above the requested 218.

Two further three-implication fusions with a single occurrence of P are

\[
 ((P\to A)\to F)\to A,
 \qquad
 ((F\to A)\to P)\to A.
\]

Both are propositionally equivalent to D, and each has a 234-leaf emitter.
A further **318 layouts** have minimum protected hardware bound **222**.
These are exhaustive counts only for the stated finite layout families;
they are not lower bounds over all emitters, source trees, or machines.

For comparison, emitting T and explosion as two separate rows uses only
207 leaves in place of 283, but increases the axiom output count from ten
to eleven. The 72 whole-row layouts have minimum hardware bound 226; the
756 layouts preserving the three original closed chunks reach 222.

All these counts use the repaired `hardware_objective219.py`, which
accounts for the duplicated logical `(CD6,CC2)` at native states 13 and
108 and preserves the classified engine/helper rows. The model was
calibrated against the literal 219 table before each screen. It is an
exploratory preserved-row bound, **not** a compiled table or runtime proof.
No altered-calculus machine from these screens is presented as satisfying
the 218-state task.


# Universal instantiation plus explicit explosion: a terminal-cluster theorem

## Status

Let `K_TEXP` be the released native seed-K calculus with the single row

\[
\rho_6(i,A):\quad \operatorname{Ex}_i Q_i A\to A
\]

replaced by the two schemes

\[
T(i,A):\quad Q_i A\to A,
\qquad
\mathrm{EXP}(A):\quad F\to A.
\]

Here the other native rows and the complete gated V/K bundle remain
unchanged, `F=R(0,0)`, `N A=A->F`, and `Ex_i A=N Q_i N A`.

**The equivalence `Con(K_TEXP) <-> Con(ZFC)` has not been proved.** No result
below is a calibration of a consistency machine for this replacement.
There are, however, two rigorous results that narrow the problem:

1. If `K_TEXP` has a standard constant-domain relational Kripke model
   with a nontrivial terminal cluster, then the original native calculus
   is consistent. In particular, a finite-world model with falsum
   invalid entails `Con(ZFC)` through the inherited calibration.
2. Relative to an ordinary model of calibrated K+IR, there is a
   two-world model of all of `K_TEXP` that falsifies an instance of the
   deleted row. Thus an argument for equiconsistency must allow unequal
   theorem sets.

The terminal-cluster result allows arbitrary reflexive accessibility:
**transitivity and directedness are not assumed.** Equality need not
initially be identity, and a separate irreflexivity axiom is unnecessary.

## Semantic class and its limits

Fix a nonempty set of worlds `W`, a reflexive relation `<=` on `W`, and a
nonempty constant domain `D`. At each world `w`, interpret membership and
equality by arbitrary binary relations `R_w,E_w` on `D`. For an assignment
`v:N->D`, use classical material implication and

\[
w,v\models Q_i A
\quad\Longleftrightarrow\quad
\forall u\,(w\preceq u\Rightarrow
    \forall d\in D\;u,v[i\mapsto d]\models A).
\]

Atoms depend only on the displayed two arguments. This is a specified
semantic class, not a representation theorem for all abstract models of
the native calculus. In particular, the argument below must not be
applied to arbitrary cylindric or nonclassical matrix interpretations.
The source theory's equality symbol is initially an interpreted relation,
not an assumed built-in identity.

Assume every axiom of `K_TEXP` is true at every world and assignment and
that `F` is false at at least one world and assignment. The native
exceptional formula code zero denotes truth, which agrees with the
arithmetic identity `I(0,0)=0`.

## Explosion removes the non-irreflexive worlds

Call a world *trivial* if some `d in D` satisfies `R_w(d,d)`.

**Lemma 1.** At a trivial world, every native formula is true under every
assignment. At every other world, membership is irreflexive and falsum is
false under every assignment.

**Proof.** Suppose `R_w(d,d)`. For arbitrary `x,y in D`, choose an assignment
with \(v(0)=d\), \(v(1)=x\), and \(v(2)=y\). Applying the explosion instance with conclusion
`R(1,2)` gives `R_w(x,y)`. The equality conclusion `E(1,2)` similarly
makes `E_w` universal. Hence `R_w(e,e)` holds for every `e in D`, and falsum
is true under every assignment. Applying each explosion instance now
gives every native formula under every assignment. Conversely, a
nontrivial world has no diagonal membership by definition. (End of proof.)

Delete the trivial worlds and restrict accessibility to the remaining
set `W*`. It is nonempty because falsum was not globally valid, and its
accessibility relation remains reflexive.

**Lemma 2.** Every native formula has exactly the same truth value at
every surviving world and assignment after this deletion.

**Proof.** Induct on the decoded native formula. Atoms and implication
are immediate. In a universal-quantifier clause, all instances at each
deleted successor were true by Lemma 1, so deleting them does not alter
the universal condition. (End of proof.)

Thus all `K_TEXP` axioms are still valid on `W*`. Falsum is now uniformly
false, so its native negation and existential are ordinary Boolean
negation and the dual of the displayed modal quantifier. This pruning
step is essential: one cannot simply assume that an arbitrary model of
the original numerical calculus interprets `R(0,0)` as false everywhere.

## A terminal cluster is classical

A terminal cluster is a nonempty set `C subseteq W*` that is strongly connected
under finite accessibility paths and has no outgoing edge to `W*\C`.
Every nonempty finite directed graph has such a cluster. More generally,
the following proof applies whenever any such cluster exists, even when
the entire frame is infinite.

### Membership is constant throughout the cluster

The retained gated bundle gives every positive fresh-variable vacuity
instance

\[
R(a,b)\to Q_cR(a,b),\qquad c\ne a,b.
\]

Indeed, after Lemma 2 falsum is false, so the bundle's Boolean conjunction
can be projected. Fixing three distinct labels and varying their assigned
values shows that `R_w(x,y)` implies `R_u(x,y)` whenever `w<=u`.
Along finite paths this implication persists. Strong connectivity
therefore makes `R_w` the same binary relation for every `w in C`.

### Equality first becomes reflexive, then constant

The retained existence and G rows are

\[
\operatorname{Ex}_aE(a,b),
\qquad
E(c,a)\to(E(c,b)\to Q_{\kappa(a,b)}E(a,b)).
\]

Fix `w in C` and `d in D`. Equality existence supplies a successor `u in C` and an
object `e` with `E_u(e,d)`. The G row with its two endpoint labels equal
gives a quantified diagonal equality, and reflexivity of accessibility
gives `E_u(d,d)`.

Once `E(d,d)` holds at any world, the diagonal instance of G with pivot
equal to that endpoint yields `Q_k E(d,d)`. At each successor one may
choose the quantified coordinate's original value. Therefore diagonal
equality persists along every accessibility edge. A finite path from
`u` back to `w` gives `E_w(d,d)`. Since `w,d` were arbitrary, equality is
reflexive throughout the cluster.

Now use G with pivot equal to its first endpoint. Its first antecedent
is the already established reflexive equality, so any `E_w(x,y)` gives
`Q_k E(x,y)`, and therefore `E_u(x,y)` at each successor with the original
coordinate values. Strong connectivity makes `E_w` constant throughout
`C` as well. No unproved symmetry or transitivity of accessibility was
used. Selecting original values also handles a constructed binder that
happens to equal one of the displayed labels.

For an ordinary relational interpretation, G additionally makes this
constant equality relation Euclidean; reflexivity then gives symmetry
and transitivity. The retained two membership-congruence rows make
membership descend to its quotient. This quotient is available if an
actual-identity model is desired, but it is not needed for the next
native-calculus argument.

### All formulas lose their world dependence

Both atomic relations are now constant on `C`. Induction on formulas
shows that every native formula's truth is independent of its world in
`C`. The implication step uses material implication. For a universal
quantifier, all successors remain in `C`, and the inner formula is
world-independent by induction; nonempty reflexive successor sets
therefore make `Q_i` exactly ordinary quantification over coordinate `i`.

Consequently the deleted row is valid throughout `C`:

\[
\exists x_i\,\forall x_i\,A\to A.
\]

The outer existential does not change the truth of the inner universal,
and its truth gives the instance at the original assigned value. All
other original native axioms were retained and remain valid because `C`
is closed under successors. MP and GEN preserve this global validity.
Falsum is false everywhere on `C`, so induction on any original native
derivation proves that falsum is not derivable.

**Terminal-cluster theorem.** In ZFC, the existence of a model in the
specified semantic class whose nontrivial part has a terminal cluster
implies consistency of the original native seed-K calculus, hence
`Con(ZFC)` by the released calibration.

In particular, a finite-world `K_TEXP` countermodel to falsum would not
give a ZFC-provable weak-consistency obstruction unless ZFC itself proved
its consistency. Conversely, an ordinary model of calibrated K+IR gives
a one-world model of `K_TEXP`; the inherited interpretation and ordinary
first-order completeness make existence of such finite-frame models
equiconsistent with ZFC. This is a result about model existence in this
semantic class, **not** a completeness theorem for `K_TEXP`.

## A relative full-K countermodel to deriving the deleted row

Let `M=(D, in ^M)` be any ordinary model of the calibrated K+IR theory with
actual equality. Use two worlds `0<=1`, including both reflexive loops,
and put

\[
R_0=\varnothing,\qquad R_1=\in^M,
\qquad E_0=E_1=\text{identity on }D.
\]

Falsum is false at both worlds. Material implication validates the
propositional row and explicit explosion. T is valid by reflexivity;
normality and commutation hold for the modal quantifiers. Equality
existence, G and both membership-congruence rows are valid with actual
identity. Membership grows, so positive fresh-variable vacuity is valid.

At world 1 the full gated K bundle is exactly its ordinary interpretation
in `M`. At world 0, choose its outer existential's world to be 1 and use
the container supplied in `M`. All inner requirements are then evaluated
at world 1. Its other conjunct is positive membership vacuity, already
valid. Failed numerical gates give truth. Thus this is a model of the
**complete** modified calculus, not just its modal-logical fragment.

The K schema for the true matrix ensures that `M` has some membership
pair `p in ^M q`. Choose an atom `A=R(a,b)` assigned this pair and a distinct
binder `i`. At world 0, `A` is false, whereas `Ex_i Q_i A` is true by
choosing world 1. The corresponding original rho6 instance therefore
fails.

This model depends on the existence of `M`; it does not prove consistency
of `K_TEXP` in ZFC alone. Its conclusion is that an eventual successful
consistency translation cannot simply claim that the old rho6 row is
derivable from T, explosion, and the full core.

## What remains open

The unresolved possibility is a set-sized model whose nontrivial frame
has no terminal cluster, or a sound model outside the specified relational
Kripke class. No representation or filtration theorem ruling those out
has been supplied. In particular, propositional modal finite-model
properties do not automatically preserve an infinite first-order schema
with quantification over an infinite domain.

A familiar potentialist translation theorem does not close this gap.
The first-order mirroring theorem in Øystein Linnebo's *Potentialism
Demodalized* assumes S4.2 and both positive and negative stability of
atomic predicates. The literal native replacement supplies T and positive
membership vacuity, without the required transitivity, directedness, or
negative stability. Moreover, its `Q_i` is a single indexed operator;
decomposing it as a separate modal operator and ordinary quantifier would
itself require justification. See the theorem and its hypotheses in
[the primary article](https://www.cambridge.org/core/journals/review-of-symbolic-logic/article/potentialism-demodalized/8D71CD16100FDA9AF95F68A30960604F).

The finite terminal-cluster theorem is useful evidence about where a
proof or countermodel must act. It is not a replacement for the missing
equiconsistency proof.


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
the schemes `A->A`, `F->A`, and `A->(B->A)`. **ZFC proves consistency of this
modified calculus.** Therefore none of these replacements provides the
requested calibration to `Con(ZFC)`, assuming ZFC is consistent.

Clause 2 permits arbitrarily many independent formulas *inside* the
displayed outer constructor. Thus, for example, restricting `U` to
`X->Y` remains inadequate even when `X,Y` are independent formula inputs.
The statement does not cover all alternative three-variable bases, nor
does it cover a fourth input ranging over arbitrary membership atoms.

## Finite algebra lemma

Use the inherited implication matrix, with designated value 3 and
falsum value 0:

| -> | 0 | 1 | 2 | 3 |
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
`R(z,p)=1` and `R(z,u)=2`. Since `1->2=1` is not designated, the native
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

This closes the earlier unsolved suggestions `U=A->A`, `B->B`, `C->C`,
`A->B`, `A->C`, `B->A`, `B->C`, `C->A`, and `C->B`, as well as all more
complicated finite implication/quantifier expressions in the same three
parameters. Their failure is no longer merely a failure of bounded
condensed-detachment search. A successful reduction must preserve a
genuinely independent fourth formula in this row, permit fourth-input
membership atoms in a sufficient family, or change the propositional
basis itself (for example, the previously calibrated two-row G/H basis).

Run `python uniform_rho8_obstruction.py` to regenerate the finite
premise certificate. The certificate does not substitute for the
inherited infinite-domain proof or the structural argument above.



# Eliminating a different propositional parameter

The uniform negative theorem concerns the fourth slot U of the native row

\[
L(A,B,C,U)=((C\to U)\to A)\to((A\to C)\to(B\to C)).
\]

It does not rule out eliminating B instead. A concrete three-parameter
proposal sets B to native truth, while preserving A,C,U independently.
Once the required truth and detachment are available, its reduced form is

\[
 ((C\to U)\to A)\to((A\to C)\to C).
\]

The alternative B=A->A was also tested. No positive calibration was found.
The final bounded screen includes the arithmetic identity I(0,0)=0;
ordinary free-term unification would miss such native specializations.
The search permits a cyclic implication equation only when the complete
cyclic component can collapse to zero. A positive quantifier code cannot
collapse this way. This follows from positivity of the nonzero native
constructor codes and their strict growth above their children.

The modal runs include one fixed binder, native GEN, retained quantifier
normality, and the original rho6. Their bounds are formula size 101,
quantifier depth 8, at most 2,000 processed nodes, and 90 seconds. The
recorded results are:

| Basis and added schemes | Generated / processed | New target theorems | Search boundary |
|---|---:|---|---|
| B=truth, propositional only | 36 / 36 | none | saturated within bounds |
| B=truth, modal | 1561 / 1521 | none | time bound |
| B=truth, modal, identity supplied | 1666 / 1607 | none beyond the supplied identity | time bound |
| B=truth, modal, explosion supplied | 1910 / 1873 | none | time bound |
| B=A->A, modal | 316 / 316 | none | saturated within bounds |
| B=A->A, modal, identity supplied | 412 / 412 | none beyond the supplied identity | saturated within bounds |
| Reduced row, modal | 390 / 390 | none | saturated within bounds |
| Reduced row, modal, identity supplied | 453 / 453 | Peirce | saturated within bounds |


Identity was not independently recovered in the rows where it was supplied
as an extra assumption; those entries are not positive derivations of a
basis. The reduced row with supplied identity does derive Peirce within
the discovery system, but the remaining basis targets were not found.
This does not calibrate the complete native calculus. Positive results
from this search would still require explicit substitution/MP/GEN replay.
The finite search boundary cannot establish nonderivability.

An untested logical direction survives the uniform obstruction: allow U
to range over a sufficient family of membership atoms. Those atoms can
take value 2 in the inherited four-valued model, so the range argument
does not apply. Whether such a restriction admits a structural
completeness proof, and whether it can be emitted more cheaply than the
33-leaf fourth-argument reader, remain open. There is no claimed candidate
or calibration along that direction.

# Reproducibility and source dependencies

The finite proof and algebra checks require only Python and have no network
dependency:

```sh
python3 certify_fused_d.py --verify-only
python3 uniform_rho8_obstruction.py
```

The source screens require the vendored 219/220/221 macro dependencies and
the repaired 219 hardware objective. Their JSON receipts retain every
layout choice and every evaluated cost. Bare-cost pruning discards only
layouts whose nonnegative-overhead bound cannot improve the current best
inside this same model. Recreating these exploratory screens is separate
from replaying the accepted machine's exact literal table.

| Source-screen script | Layouts | Best protected hardware bound |
|---|---:|---:|
| `t_explosion_source_screen.py` | 72 | 226 |
| `t_explosion_chunk_screen.py` | 756 | 222 |
| `fused_d_source_screen.py` | 103 | 221 |
| `fused_d_equivalent_screen.py` | 318 | 222 |

The mathematical proofs of the uniform extension and terminal-cluster
theorem are ordinary proofs formalizable in ZFC. The finite certificates
check their explicitly identified finite premises; they do not pretend
to kernel-check the infinite-domain arguments.

Primary dependencies in the published K219 packet are:

- `report/sections/calibration.tex`: finite-refutation calibration.
- `research/theory/restricted_rho8_strong_countermodel.md`: the full HC model.
- The vendored `CD230.v`: K, S, and Peirce from rho8 alone.
- The vendored `Comp_Prop230.v`: the pure-implicational deduction theorem.

The local proofs are pinned through the supplied predecessor archives.
Public source:

- [ProveIt ZFC research, pinned new release](https://github.com/VladimirReshetnikov/ProveIt/tree/26d5de6d21fa354d50e0b84fe851c289925b8d72/Computability/BusyBeaver/Research/ZFC)
- [Inherited implicational derivations](https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/CD230.v)
- [Inherited deduction theorem](https://github.com/elliotglazer/k230-rocq/blob/main/coq/logic/Comp_Prop230.v)
