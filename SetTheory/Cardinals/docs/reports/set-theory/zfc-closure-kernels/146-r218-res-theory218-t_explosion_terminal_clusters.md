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
unchanged, `F=R(0,0)`, `N A=A→F`, and `Ex_i A=N Q_i N A`.

**The equivalence `Con(K_TEXP) ↔ Con(ZFC)` has not been proved.** No result
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

## 1. Semantic class and its limits

Fix a nonempty set of worlds `W`, a reflexive relation `≼` on `W`, and a
nonempty constant domain `D`. At each world `w`, interpret membership and
equality by arbitrary binary relations `R_w,E_w` on `D`. For an assignment
`v:N→D`, use classical material implication and

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

## 2. Explosion removes the non-irreflexive worlds

Call a world *trivial* if some `d∈D` satisfies `R_w(d,d)`.

**Lemma 1.** At a trivial world, every native formula is true under every
assignment. At every other world, membership is irreflexive and falsum is
false under every assignment.

**Proof.** Suppose `R_w(d,d)`. For arbitrary `x,y∈D`, choose an assignment
with \(v(0)=d\), \(v(1)=x\), and \(v(2)=y\). Applying the explosion instance with conclusion
`R(1,2)` gives `R_w(x,y)`. The equality conclusion `E(1,2)` similarly
makes `E_w` universal. Hence `R_w(e,e)` holds for every `e∈D`, and falsum
is true under every assignment. Applying each explosion instance now
gives every native formula under every assignment. Conversely, a
nontrivial world has no diagonal membership by definition. ∎

Delete the trivial worlds and restrict accessibility to the remaining
set `W*`. It is nonempty because falsum was not globally valid, and its
accessibility relation remains reflexive.

**Lemma 2.** Every native formula has exactly the same truth value at
every surviving world and assignment after this deletion.

**Proof.** Induct on the decoded native formula. Atoms and implication
are immediate. In a universal-quantifier clause, all instances at each
deleted successor were true by Lemma 1, so deleting them does not alter
the universal condition. ∎

Thus all `K_TEXP` axioms are still valid on `W*`. Falsum is now uniformly
false, so its native negation and existential are ordinary Boolean
negation and the dual of the displayed modal quantifier. This pruning
step is essential: one cannot simply assume that an arbitrary model of
the original numerical calculus interprets `R(0,0)` as false everywhere.

## 3. A terminal cluster is classical

A terminal cluster is a nonempty set `C⊆W*` that is strongly connected
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
values shows that `R_w(x,y)` implies `R_u(x,y)` whenever `w≼u`.
Along finite paths this implication persists. Strong connectivity
therefore makes `R_w` the same binary relation for every `w∈C`.

### Equality first becomes reflexive, then constant

The retained existence and G rows are

\[
\operatorname{Ex}_aE(a,b),
\qquad
E(c,a)\to(E(c,b)\to Q_{\kappa(a,b)}E(a,b)).
\]

Fix `w∈C` and `d∈D`. Equality existence supplies a successor `u∈C` and an
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

## 4. A relative full-K countermodel to deriving the deleted row

Let `M=(D,∈^M)` be any ordinary model of the calibrated K+IR theory with
actual equality. Use two worlds `0≼1`, including both reflexive loops,
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
pair `p∈^M q`. Choose an atom `A=R(a,b)` assigned this pair and a distinct
binder `i`. At world 0, `A` is false, whereas `Ex_i Q_i A` is true by
choosing world 1. The corresponding original rho6 instance therefore
fails.

This model depends on the existence of `M`; it does not prove consistency
of `K_TEXP` in ZFC alone. Its conclusion is that an eventual successful
consistency translation cannot simply claim that the old rho6 row is
derivable from T, explosion, and the full core.

## 5. What remains open

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
