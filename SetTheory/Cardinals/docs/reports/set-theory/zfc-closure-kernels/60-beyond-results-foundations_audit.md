# Consistency-preserving startup data and the exact ZFC proof boundary

Research notes, 17 October 2026. ProveIt source pin:
`a2bf288dead95b653919b86608e3f2cca47552f7`. Independently inspected prior-art
branch `jeff87654/busy-beaver:zf-254` at
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`.

## 1. Result of this investigation

There is a useful broader correctness criterion for an initializer: the
formulas it leaves behind need only preserve the consistency of the search
theory. They need not already be theorems of that theory. This gives a
mathematical enlargement of the repository's sufficient seed family without
adding any runtime instruction or state. A standalone recognizer implements
two new sound certificate families: raw Extensionality and denials of finite
membership cycles, with the original Code254 encoding.

This result does **not** supply a machine with fewer than 252 states. It also
does not replace a complete binary root-frame proof, prove a new compiler
correct, or extend the existing Lean endpoint automatically. The general
argument below is ordinary mathematics formalizable in ZFC; the recognizer is
an executable diagnostic with finite conformance checks. No historical
priority is claimed for the underlying model-theoretic method.

The distinction from the pinned repository is concrete:

* `safe_initializer_families.md` requires `C254 st.tw`, `C254 st.p2`, and
  `Enum254.Good st.ws`; its conclusion is based on native derivability.
* `seed_invariant254.md` and `safe_seed254.py` recognize six constructors
  that produce actual native `C254` theorems.
* `dirty_initializer_credit.md` protects a dirty stack bottom by a proved
  safe prefix and by the enumeration's stack balance, or erases initial
  information through resets. The surviving active information is still
  governed by native-theorem invariants.

Those documents correctly reject merely satisfiable open atomic seeds,
because generalization requires validity under every assignment. They do not
state the relative-consistency criterion below. The new criterion always uses
universal closures; it does not discard that generalization requirement.

## 2. Exact code and source theory

Write

\[
 P(a,b)=\frac{(a+b)(a+b+1)}2+b,
 \qquad I(a,b)=4P(a,b),\quad R(i,j)=4P(i,j)+1,
\]
\[
 Q(i,a)=4P(i,a)+2,\qquad E(i,j)=4P(i,j)+3.
\]

These are the original dual-Cantor, base-four constructors, not the rejected
base-three equality-free experiment. Code 0 is the truth alias and code 1 is
the falsity alias. The theorem stack uses the **unshifted** pairing `P`:
there is no extra `+1` in a stack cell. Repeated unpairing of any positive
stack code strictly decreases its tail; zero denotes an infinite zero tail.

Let `D(n)` be the normalized named-formula decoding: 0 is True, 1 is Bottom,
and every other code is decoded by its constructor tag. The literal code-1
reading is `v0 in v0`; in the intended irreflexive models it is equivalent to
Bottom under every assignment, including below a binder with label 0. The
exception `I(0,0)=0` is semantically harmless because True implies True.
No generic assumption that a code has no free variables is made.

Let `S` be the native theory SIR in the verified construction: ordinary
first-order logic with equality, the powerset-container sentence CP, every
closed instance of global-image collection GIC, and irreflexivity IR. In a
readable one-sorted notation:

\[
\mathrm{CP}:\quad
 \forall p\exists V\,[p\in V\land
 \forall x\in V\,(x\subseteq V\land
    \exists W\in V\,\forall z(z\subseteq x\to z\in W))],
\]
\[
\mathrm{GIC}_\varphi:\quad
 \forall B\exists C\,[
 \forall x\in B(\exists y\,\varphi(x,y)\to
                       \exists y\in C\,\varphi(x,y))
 \land\forall y\in C\exists x\,\varphi(x,y)],
\]
\[
\mathrm{IR}:\quad\forall x\,x\notin x.
\]

All finite parameter lists and all first-order matrices occur in the GIC
schema. The unrestricted input in its support clause is intentional. The
numerical implementation's freshness gate and its collision cases remain
exactly as in the original complete calculus.

The pinned construction already supplies the important two ingredients:

1. Every emitted logical/theory root is valid in every model of `S`; modus
   ponens and theorem generalization preserve validity. Code aliases and the
   `a=b` gate-collision cases are included in this statement.
2. If `S` is inconsistent, the enumerator eventually halts from arbitrary
   retained initial formula data and arbitrary candidate counter. Candidate
   completeness is not restricted to theorem-valued initial data.

The binary-to-enumerator adapter has its own hypotheses. The argument here
begins at a genuine enumerator root and transports to a Turing machine only
after those hypotheses have been proved for that exact machine and frame.

## 3. The relative-consistency seed theorem

Fix an initial enumerator root `s`. Let `Sigma(s)` consist of its current
formula code, its cached formula code, and every formula code in the finite
nonzero prefix obtained by unpairing its theorem-stack code. The infinite zero
tail contributes only True. Let

\[
 \Gamma_s=\{\operatorname{UC}(D(n)):n\in\Sigma(s)\},
 \qquad S_s=S\cup\Gamma_s,
\]

where UC is universal closure over the free variables. The closure is a
metatheoretic certificate; the initializer does not have to write its usually
much larger numerical code.

### Theorem 1: the seed consistency sandwich

For the original complete enumerator,

\[
 \operatorname{Con}(S_s)\Longrightarrow
 \operatorname{Nonhalt}(s)\Longrightarrow\operatorname{Con}(S).
 \tag{1}
\]

Consequently, if ZFC proves

\[
 \operatorname{Con}(\mathrm{ZFC})\Longrightarrow
 \operatorname{Con}(S_s),
 \tag{2}
\]

then the existing consistency calibration of `S` yields

\[
 \mathrm{ZFC}\vdash
 \operatorname{Nonhalt}(s)\leftrightarrow
 \operatorname{Con}(\mathrm{ZFC}).
 \tag{3}
\]

**Proof.** Work in ZFC with finite syntax, proof codes, and finite computation
traces. Assume `Con(S_s)`. First-order completeness supplies a nonempty,
set-coded model `M` of `S_s`. Every initial current/cache/stack formula is true
in `M` under every assignment, by its universal-closure axiom. At each
enumerator step, all newly emitted roots are valid in `M` because `M` models
`S`. A successful modus ponens preserves validity; a failed comparison inserts
True. Stack pushes and pops preserve the validity invariant, as does
generalization because the invariant quantifies over **every** assignment.
The halt test would recognize code 1 as valid, contradicting its Bottom
interpretation in a nonempty model. Thus the run does not halt.

For the second implication, contrapose the already available completeness
theorem: a native `S` refutation compiles into a candidate program which the
enumeration eventually executes from any retained initial formula data.
Therefore inconsistency of `S` implies halting from `s`. Combining (1), (2),
and the native theory's ZFC consistency equivalence proves (3). No model is
assumed to be transitive, well-founded externally, or an omega-model. QED.

It is unnecessary, and generally unwarranted, to claim that the run from `s`
halts iff `S_s` is inconsistent. Some initial formulas may be overwritten or
remain inaccessible. The two implications in (1) are all that the application
requires.

### Corollary 1: universally ZFC-valid seeds

If each `UC(D(n))` for `n` in `Sigma(s)` is a theorem of ZFC, then (2) holds.
Indeed, from `Con(ZFC)`, completeness gives a model of ZFC. Its **same
membership relation and equality** satisfy the native theory: every native
CP, GIC, and IR axiom holds in that ZFC model. The finitely many seed theorems
hold by first-order proof soundness. The same model therefore satisfies `S_s`.
No quotient or reinterpretation of the raw seed formulas is used. Abstract
equiconsistency with another theory, by itself, would not suffice for this
corollary.

This is not an appeal to a truth predicate for the set-theoretic universe or
to ZFC proving its own global soundness. It is an argument about set-coded
models and satisfaction, conditional on `Con(ZFC)`, with explicit finite seed
proofs. The allowed certificate family must itself have a uniform proof of
soundness if its parameters are to vary in the proposed search.

### Corollary 2: constructible-model seeds

The conclusion also holds when a fixed class interpretation constructs from
every ZF model a model of `S+Gamma_s`. For example, seeds uniformly valid in
the constructible submodel `L^M` are allowed, since the existing construction
proves that this inhabited submodel satisfies ZFC, hence the native theory.
This permits compatible strengthening such as suitably encoded instances of
`V=L`; such seeds need not be theorems of ZFC itself. The implementation below
does not attempt to recognize `V=L`.

## 4. Strictness: Extensionality as a safe seed

For pairwise distinct labels `a,b,c`, consider

\[
 X(a,b,c)=
  [\forall v_c(v_c\in v_a\leftrightarrow v_c\in v_b)]
   \longrightarrow v_a=v_b.
 \tag{4}
\]

It is universally valid in ZFC and therefore is an admissible startup
formula by Corollary 1. Its universal closure need not be a theorem of the
native nonextensional theory. A precise relative model argument shows the
difference.

From any model of ZFC, form its ordinary internally coded hierarchy of sets
over two distinct urelements. One concrete interpretation uses two atom tags
and set tags `(set,X)` whose members are the tagged objects in `X`; take all
objects built through the model's own ordinal hierarchy. The external carrier
is a subset of the original model's set carrier, so this construction does
not require the original model to be externally well-founded. Forget the
predicate that distinguishes atoms from sets, and retain actual equality and
membership. This is a model of native `S`:

* IR holds by the hierarchy's Foundation principle.
* GIC follows from Collection and Separation in the atom hierarchy for each
  translated first-order matrix.
* CP holds in a sufficiently high limit stage. For an object `x`, all raw
  subsets consist of the ordinary set-subsets of its members **together with
  both atoms**, since atoms have no members and are raw subsets of every
  object. A power bound must include those atoms. Choose that bound inside
  the same higher limit stage. This detail is necessary for native CP and
  prevents silently importing the wrong powerset convention from ZFA.

The two atoms have exactly the same empty predecessor set and are unequal,
so (4) fails under an assignment of them to `a,b`. Thus, relative to
`Con(ZFC)`, Extensionality is not a native theorem. The enlarged admissible
seed class is genuinely broader than native derivability, not only broader
than an incomplete native-theorem recognizer.

The construction is a standard finite-atom interpretation; the new use here
is as a witness that consistency-preserving startup criteria exceed the
repository's positive native-theorem certificate family.

## 5. Executable certificate family

`semantic_seeds.py` preserves the six earlier certificate constructors and
adds:

1. `("extensionality",a,b,c)` reconstructs exactly (4), with `c` distinct
   from `a,b`. The biconditional and conjunction use the original relative
   falsity constructors. Generalization certificates can close its free
   variables if desired.
2. `("foundationCycle",[a0,...,ak-1])`, for a nonempty finite list, reconstructs

   \[
   R(a_0,a_1)\to(R(a_1,a_2)\to\cdots
      (R(a_{k-1},a_0)\to F)\cdots).
   \]

   ZFC proves this under every assignment: if all edges held, the finite
   nonempty set of assigned vertices would have no membership-minimal
   element, contradicting Foundation. Repeated labels and coinciding values
   are permitted. An edge `R(0,0)` is the exceptional Bottom code, which is
   also false in ZFC by Foundation, so this alias introduces no exception.

The existing truth, identity, weakening, ex-falso, equality-reflexivity, and
generalization certificates remain uniformly valid in ZFC. Induction on the
certificate therefore proves universal ZFC validity for every accepted
formula. The code reconstructs the exact natural number before accepting;
the stream recognizer checks every finite entry, including buried ones.
Fuel exhaustion rejects and never grants a certificate.

A practical scalar example is

\[
 19364=I(R(0,1),I(R(1,0),1)),
\]

the denial of a two-cycle. The pinned legacy recognizer rejects it and the
new recognizer returns `("foundationCycle",[0,1])`. Its singleton theorem
stack has the different value `P(19364,0)=187491930`. The Extensionality core
with labels `(0,1,2)` has a 410-bit numerical code and is recognized by a
four-item schema certificate. This is an initializer-admission result; no
literal blank bootstrap ending with either value has been found here.

### Reproduction and evidence

```
python semantic_seeds.py --audit --output semantic_seed_audit.json
python semantic_seeds.py --formula 19364
python semantic_seeds.py --state 0 19364 0 0 0 0 0 0 0
```

The 65,536-code scalar and stack census preserves every old accepted value.
Scalar acceptance increases from 13,516 to 13,521; the five additions are
688, 5104, 19364, 19408, and 52816. The bounded stack census remains 4,051,
because the new singleton stack values exceed that census. The audit checks
376 cycle/Extensionality templates, 27,300 cycle-validity cases and 341
Extensionality-validity cases over all 29 acyclic directed relations on
nonempty carriers of sizes at most three; 15 of those relations are
extensional. Eight malformed certificate/freshness cases are rejected.

`legacy_conformance.json` records an independent comparison against the
actual pinned `safe_seed254.py`, not merely a comparison against the copied
legacy routine: all 65,536 formula certificates and all 65,536 stream
certificates match exactly. The legacy source SHA-256 is
`bd28149821879fd6f960f5da1b0bc12ba0d4352e4a5e50c4aab9ba3cc165cb56`.
These tests check implementation behavior and small semantics. They are not
the reason for the universal mathematical theorem, which is proved above.

## 6. Why the existing external Lean endpoint is relevant to an in-ZFC goal

The current canonical 252-state table already has a closed external Lean
metatheorem:

\[
  \neg\exists t\,\operatorname{Halted}(M_{252},t)
   \quad\longleftrightarrow\quad
  \neg\operatorname{BProv}(\mathrm{ZFCax_s},\bot).
\]

The inspected `BinaryPerm252.lean` composes the literal 82,552-step bootstrap,
the complete instruction coverage certificate, the actual program adapter,
native refutation calibration, and full ZF comparison. The two ZFC adapters
`ChoiceCalibration254.lean` and `BinaryZFC252.lean` then use the constructible
model construction. No startup, coverage, supplied model, `V=L`, or Choice
premise remains in their endpoint statements.

The PA internalization work remains incomplete in the pinned repository.
That does **not** automatically leave the user's weaker in-ZFC requirement
open. The mathematical proof may be formalized in ordinary ZFC:

* Finite transition tables, finite tapes, arithmetic formula/proof codes,
  register configurations and trace witnesses are sets over the natural
  numbers. All finite certificate checks and induction arguments can be
  expressed there.
* First-order syntax and satisfaction for a set-coded structure are
  definable by recursion. Completeness can be used inside ZFC to pass
  between a consistency statement and a model. Countable structures suffice.
* Inside a possibly nonstandard model, the constructible submodel is defined
  by the model's own formulas and recursions. External transitivity is not
  required. Its carrier is a subset of the original set carrier, and the
  proof explicitly establishes inhabitedness.
* `ZFAxioms` in `SetTheory/ZF/Lean/ZF/Zf.lean:334` quantifies Separation and
  Replacement over coded first-order `Form` and parameter environments. It
  does not assume arbitrary second-order predicates.

This is an independent set-coded internalization argument, **not** a claim
that every Lean theorem automatically becomes a ZFC theorem. General soundness
of unrestricted Lean universes is not needed for this specific argument.
Nor has the present audit emitted a serialized derivation in the repository's
object-level ZFC proof system. The existing `choice_calibration254.md` is
explicit about that proof-artifact boundary.

For a proposed smaller table, preserving the exact verified runtime relation
would allow the same ZFC argument to be reused. A finite trajectory alone
does not establish that relation. If the source calculus changes, its
calibration must be checked again; the repository's equality-free 248/250/251
benchmarks already demonstrate how an apparently smaller logical source can
lose the required strength.

## 7. A precise obstruction to freezing finitely many schema instances

### Theorem 2: fixed finite true-axiom barrier

Let `T` be a fixed finite set of sentences in the ordinary membership/equality
language, and suppose every sentence of `T` is a theorem of ZFC. Then ZFC
proves `Con(T)`. If ZFC is consistent, it therefore cannot also prove
`Con(T) <-> Con(ZFC)`.

**Proof.** Apply the ZFC reflection theorem to the finitely many sentences
and their required subformulas. A suitable nonempty rank segment `V_alpha`
satisfies all of `T`. Soundness of first-order deduction for this set model
gives `Con(T)`. A consistency equivalence would imply that ZFC proves its own
consistency, contrary to the second incompleteness theorem under its usual
hypotheses. QED.

In particular, freezing CP, IR and finitely many selected GIC matrices cannot
replace the full theory. This is a fixed-standard-fragment statement, not a
uniform ZFC theorem that *all* finite fragments are consistent. There is no
contradiction with finitely axiomatized class theories or with a refutation
search that enumerates a matrix together with a proof: a uniform unbounded
payload or a class interpretation has not been removed in those proposals.
The barrier is a classical consequence of reflection, stated here to delimit
a concrete compiler simplification; it is not a lower bound on TM states.

## 8. Consistency and logical independence are different conclusions

For a machine with the desired internal equivalence, `Con(ZFC)` implies its
actual nonhalting and, by the second incompleteness theorem, the inability of
ZFC to prove that nonhalting statement. To conclude that ZFC cannot prove the
opposite halting statement, a suitable soundness hypothesis is needed, such
as Sigma-1 soundness. A false halting statement is Sigma-1; consistency alone
does not generally prevent a recursively axiomatized theory from proving a
false Sigma-1 statement or its own inconsistency. The requested equivalence
with consistency does not require strengthening the target to soundness.

The supplied Busy Beaver wiki has a stale opening bound of 432 while its
history table records the 254-state formalized construction dated 13 October
2026. The exact repository artifacts and theorem statements are better
evidence for the present baseline than that opening bound. The 252-state
ProveIt table is a separate later result with its own explicit hashes and
proof objects; it must not be conflated with the older reduced-calculus
252-state experiment.

## References and inspected source locations

1. [ProveIt candidate-permutation252 README, pinned](https://github.com/VladimirReshetnikov/ProveIt/blob/a2bf288dead95b653919b86608e3f2cca47552f7/Computability/BusyBeaver/Research/ZFC/candidate-permutation252/README.md).
2. [ProveIt choice calibration note, pinned](https://github.com/VladimirReshetnikov/ProveIt/blob/a2bf288dead95b653919b86608e3f2cca47552f7/Computability/BusyBeaver/Research/ZFC/choice_calibration254.md).
3. [ProveIt binary ZFC endpoint source, pinned](https://github.com/VladimirReshetnikov/ProveIt/blob/a2bf288dead95b653919b86608e3f2cca47552f7/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/BinaryZFC252.lean).
4. [Jeff Ketchersid, m254 README, pinned](https://github.com/jeff87654/busy-beaver/blob/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254/README.md), and the adjacent `coq/e2e/E2E254.v`, `coq/settheory/S_def.v`, `S_main.v`, `S_sound.v`, `coq/logic/Bridge254.v`, `Codes254.v`.
5. [ProveIt safe-initializer families, pinned](https://github.com/VladimirReshetnikov/ProveIt/blob/a2bf288dead95b653919b86608e3f2cca47552f7/Computability/BusyBeaver/Research/ZFC/safe_initializer_families.md), and adjacent `seed_invariant254.md`, `dirty_initializer_credit.md`, `safe_seed254.py`.
6. [The Stacks Project, Section 3.8, Reflection principle, tag 000F](https://stacks.math.columbia.edu/tag/000F), Theorem 3.8.1 and the explicit explanation of its fixed finite-list scope.
7. [Busy Beaver Wiki, Logical independence](https://wiki.bbchallenge.org/wiki/Logical_independence), historical page inspected 17 October 2026.

No files in either upstream checkout were modified in this audit. The
artifacts in this directory are independent research notes and diagnostics.
