# Logical alternatives audit and a collection-based equality theorem

Prepared 19 October 2026 against ProveIt commit
`ce192939372ac7944fe2a0208c68a96d49fb5e3b`. This is scratch research for the
parent report. It introduces no repository change and no claimed smaller
machine. The parent construction independently reaches the requested state
threshold while retaining the calibrated native proof calculus.

## 1. Main auxiliary result

There is a useful distinction between minimizing a *first-order theory* and
deleting rows from the native numerical proof engine. In an ordinary complete
first-order calculus, global-image collection lets one recover the second
membership-congruence axiom from the first. The theorem below gives the exact
finite argument. It is an original derivation for this report; no historical
novelty claim or Lean verification is made.

### Definitions

Work in ordinary first-order logic **without built-in equality**, with two
binary relation symbols `E` and `R`. Write `x in y` for `R(x,y)`; `E` is initially
an arbitrary relation, not logical equality. Quantifiers have one common
nonempty domain and the proof calculus includes unrestricted capture-avoiding
first-order instantiation.

Assume the following universally closed sentences:

\[
\begin{aligned}
  H_1 &: \quad \forall b\,\exists a\,E(a,b),\\
  H_7 &: \quad \forall a\,b\,c\,
    [E(c,a)\to(E(c,b)\to E(a,b))],\\
  H_5 &: \quad \forall a\,b\,c\,
    [E(c,a)\to(R(c,b)\to R(a,b))].
\end{aligned}
\]

For a formula `theta(x,y;p)` whose displayed seed and collection-set variables
are fresh, use exactly this version of global-image collection:

\[
\operatorname{GIC}(\theta):\quad
\forall A\,\exists B\left[
 \forall y\left(R(y,B)\to\exists x\,\theta(x,y;\bar p)\right)
 \;\land\;
 \forall x\left(R(x,A)\to
    \left((\exists y\,\theta(x,y;\bar p))\to
      \exists y\,(R(y,B)\land\theta(x,y;\bar p))\right)\right)
\right].
\]

All parameter tuples are universally closed. The first conjunct is global
range purity, not just a condition referring to inputs in `A`. The second is
ordinary collection coverage of each nonempty fiber over `A`.

### Theorem 1: one explicit GIC instance supplies right congruence

The sentences `H_1,H_7,H_5` together with the universally closed instance

\[
 \theta(x,y;a,c)\;:=\; E(y,a)\land R(c,y)
\]

prove

\[
 H_3:\quad \forall a\,b\,c\,
       [E(a,b)\to(R(c,a)\to R(c,b))].
\]

The matrix does not depend on its input variable `x`. No Extensionality,
container axiom, irreflexivity, Infinity, or separately assumed nonempty
member set is needed. A presumed member `c in a` supplies the seed needed in
the proof itself.

**Proof.** First derive that `E` is an equivalence relation using only `H_1`
and `H_7`.

1. For arbitrary `b`, choose `d` with `E(d,b)` by `H_1`. Apply `H_7` with
   `c=d,a=b,b=b` to get `E(b,b)`.
2. From `E(a,b)` and the just-proved `E(a,a)`, the instance of `H_7` with
   common left endpoint `a` gives `E(b,a)`.
3. From `E(a,b)` and `E(b,c)`, symmetry gives `E(b,a)`. The instance of
   `H_7` with common left endpoint `b` gives `E(a,c)`.

Now assume `E(a,b)` and `R(c,a)`. Apply the displayed GIC instance to the
seed `A=a`, obtaining `B`. Reflexivity gives `E(a,a)`, so `y=a` witnesses
`theta(c,y;a,c)`. Since `R(c,a)`, coverage gives an object `w` satisfying

\[
 R(w,B),\qquad E(w,a),\qquad R(c,w).
\]

Transitivity gives `E(w,b)`. From `H_5` and `R(w,B)` obtain `R(b,B)`.
Range purity for the member `b` supplies `exists x theta(x,b;a,c)`, whose
second conjunct is exactly `R(c,b)`. Discharging the two assumptions and
universally generalizing proves `H_3`. Every quantified instantiation in this
argument is an ordinary first-order inference. QED.

**Why the premise is not circular.** We never replace equal objects inside
the second argument of `R`. The only membership transport used is
`R(w,B) -> R(b,B)`, in its first argument, which is precisely `H_5`.
The transfer into the second argument is obtained from collection purity.

**The missing law is not a consequence of the three `H` laws alone.** On
`D={0,1,2}`, let the `E` classes be `{0,1}` and `{2}`, and let the sole `R`
edge be `R(2,0)`. Then `H_1,H_7,H_5` and even irreflexivity hold. But
`E(0,1)` and `R(2,0)` hold while `R(2,1)` does not. For the theorem's matrix
with `a=0,c=2`, the only output is `0`; the GIC seed `A=0` contains `2`, but
there is no object containing the required output `0`. Thus this precise
GIC instance fails, as it must. This is a complete hand-checkable
three-element counterstructure; no infinite-computation claim rests on it.

The local derivation of Theorem 1 uses only positive first-order reasoning
(`and`, `implies`, `forall`, `exists`); it is valid intuitionistically as
well. The model-to-consistency corollary below uses classical completeness.

### Theorem 2: definable predicate saturation

Let `E` be an equivalence relation satisfying `H_5`, and suppose there is a
member set, `exists u A R(u,A)`. For an arbitrary formula `phi(y;p)`, assume
the GIC instance with matrix

\[
 \theta_\phi(x,y;a,\bar p):= E(y,a)\land\phi(y;\bar p).
\]

Then

\[
  E(a,b)\to(\phi(a;\bar p)\leftrightarrow\phi(b;\bar p)).
\]

**Proof.** Fix `u in A`, `E(a,b)`, and `phi(a;p)`. Apply GIC to `A`.
The output `a` witnesses the fiber over `u`, so collection produces
`w in B` satisfying `E(w,a)` and `phi(w;p)`. Transitivity and `H_5` put
`b` in `B`; purity gives `phi(b;p)`. Reverse `a,b` and use symmetry for
the other direction. QED.

This direct result applies even in an expanded relational language, provided
the schema contains the corresponding matrices. It does not assume beforehand
that additional predicates respect `E`. For the language consisting only of
`E,R`, Theorem 1 already makes both atomic relations congruent; ordinary formula
induction then gives all formula congruence without a separate nonempty-member
assumption.

### Corollary 3: an alternative theory equiconsistent with native SIR

Let `T_minus` be the following theory in the relational language `{E,R}`:

- `H_1,H_7,H_5`;
- the published power-container axiom `C_P`, expressed using `R`;
- `forall x not R(x,x)`;
- GIC for every finite `{E,R}` formula, with arbitrary finite parameter tuples.

Its background logic is full equality-free first-order logic. In particular,
`H_3` is not an axiom and `E` is not a built-in equality symbol.

Then, with conventional effective first-order proof predicates,

\[
 \mathrm{ZFC}\vdash
  \operatorname{Con}(T_{\mathrm{minus}})
    \leftrightarrow \operatorname{Con}(\mathrm{SIR})
    \leftrightarrow \operatorname{Con}(\mathrm{ZFC}).
\]

The last equivalence invokes the *existing* native-SIR/ZFC calibration, not a
new proof of that calibration. The first equivalence has the following direct
model/complete-logic proof, formalizable in ZFC.

**From SIR to `T_minus`.** Interpret `E` as actual identity and keep membership
unchanged. The three displayed `H` axioms hold; each translated GIC instance
is a native SIR instance. Therefore any SIR model expands to a `T_minus` model.

**From `T_minus` to SIR.** Theorem 1 gives `H_3`; `H_1,H_7` give an equivalence
relation. `H_5,H_3` and symmetry show that `R` is congruent in both coordinates.
Form the quotient domain `D/E`, defining

\[
  [a]\in^*[b]\quad\Longleftrightarrow\quad R(a,b).
\]

It is well-defined. Equality of quotient classes is exactly `E` of
representatives. Induction on formulas proves the usual truth lemma: a native
formula in the quotient is true precisely when its equality-to-`E` translation
is true in the original structure. The quantifier induction uses the
surjectivity of the quotient projection. Hence `C_P`, irreflexivity, and
every native GIC instance transfer to the quotient, which is a SIR model.
This argument chooses no global system of representatives.

By the completeness theorem for ordinary first-order logic, the two model
transports prove the two consistency implications. All languages, schema
translations, the fixed `H_3` derivation, and finite formulas used here are
effective. This note does not supply a serialized PA proof-code transformation
or a Lean theorem for the complete equivalence.

### Relation to the actual emitter

`H_1,H_7,H_5,H_3` are the ordinary universally closed relational versions of
the upstream `rho1,rho7,rho5,rho3` respectively. Their formulas are confirmed
directly in `ZF/m254/coq/logic/Codes254.v`, lines 103 onward. The native
numerical calculus in `Thm254.v` has only truth, MP, GEN, its eight rows, and
the gated bundle as primitive rules. It does **not** offer ordinary
capture-avoiding UI as a primitive operation. The inherited proof of that
operation uses the equality rows, including `rho3`.

Therefore Theorem 1 **does not justify deleting `rho3` from the native
240/239/238-state machines**. Doing that would require an explicit native
numeric proof of every `rho3` instance from the remaining rows and gated
bundles, or a new complete quantifier engine with a verified compiler.
In particular, the proof above applies GIC with seed `A=a`, uses the witness
`y=a`, and specializes purity to `y=b`. Those are exactly the instantiations
that must be justified in a replacement engine. The theorem is a concrete
alternative presentation to measure, and a sharper logical target than simply
deleting all equality rows.

The ordinary syntax count saved from an axiom list is one three-atom/two-
implication schema; with atoms treated as leaves this is five formula nodes.
No numerical TM-state saving follows. The equality constructor and its formula
tag remain needed for `H_1,H_7,H_5` and GIC matrices, and a substitution engine
has a cost of its own.

## 2. What the source audit establishes about other formalisms

All counts below are **reported matched compiler controls in the inspected
repository**, not new executions by this sub-agent. They cannot be compared
as if each were a fully verified machine. In particular, the original public
Wade source reconstruction is 281 states while the separately optimized and
verified native baseline is 240 states.

| Direction | Exact benefit or obstruction | Reported cost/status |
|---|---|---|
| Retain native SIR and optimize source/tape control | Preserves the calibrated complete logical layer; new transformations require source or tape simulation | Existing exact 240-state external Lean endpoint; parent report develops the smaller table |
| Delete equality rows; ternary formula tags; C/G or fixed-slot PSC | Missing cross-variable instantiation admits the repository's finite-sort counterinterpretation; primitive Bottom does not repair it | 248–252-state experimental controls are not legitimate substitutes for the calibrated engine |
| Full logic with raw subset-seeded PSC | A mathematically eligible theory change retaining the whole logical engine | Best fixed shared control 279 vs original Wade 281; new table calibration/runtime remain separate |
| Extensional subset PSC | Extensionality plus subset-seeded PSC has a checked first-order comparison to ZF without Foundation/Choice | Particular fixed emitter 320 states, not a competitive table |
| Functional/equality-bound subset closure | A legitimate same-model comparison to foundation-free, choice-free ZF when Union is included | 347-state fixed control; 27 more than its corresponding 320-state subset-bound control |
| GEN elimination by prefix closure | Correct ordinary admissibility/proof transformation using QI | Best measured full control 285 vs original Wade 281 |
| Eight registers via `2^a(2b+1)-1` pairing | Saves a scratch register but changes all arithmetic and formula coding | Best measured full control 306; hybrids 293–308 |
| Ground equational theorem generation | Removes matching/context parsing in favor of generation of valid equalities | Best complete generic control 299 **before a literal ZFC query and its writer**; no state bound for ZFC |
| Ground clauses / finite quotient certificates | Complete common-domain logic; colliding substitutions are present, and equality can be stored as classes | Reference algorithms or finite-stage costs; no competitive compiled binary implementation |

The practical research conclusion is specific: logical simplicity must be
priced together with parameter management, binding/substitution, enumeration,
arithmetic, data, and blank initialization. None of the measured alternative
backends above supplied the parent report's two-state improvement. That
improvement keeps the existing SIR engine and changes how its computation is
encoded.

## 3. Further questions that this audit makes concrete

1. Can `rho3` be derived **inside the exact native numerical calculus** from
   the other seven logical rows and the gated GIC bundle? Theorem 1 supplies
   a fixed target argument, but its first-order instantiations cannot be taken
   for granted. A positive answer should give an explicit finite proof scheme,
   freshness constraints, and an effective transformation on arbitrary numeric
   parameters, including label collisions.
2. Can a complete binding or ground-clause engine for `T_minus` be compiled
   with less control than the original eight-row engine, once its substitution
   and matrix costs are counted? The relevant cost comparison is complete
   blank-tape binaries, not the five-node deleted row.
3. Can a verified optimizer search *pairs* of individually established tape
   reductions and prove their invariant compatibility automatically? The
   parent report's successful construction demonstrates the value of this
   route without changing consistency strength.
4. Which source or runtime invariants let one shrink the accepted configuration
   domain while maintaining all genuine proof computations? Existing finite
   searches often certify arbitrary register files; stronger phase invariants
   may permit further savings, but unexplored cases must not be treated as
   unreachable.
5. Can exact internal consistency calibration be packaged once as a reusable
   proof transport from an original machine to each positively clocked block
   simulation, avoiding repetition of the logical theory proofs?

## 4. Sources checked and citation guidance

Repository revision: `ce192939372ac7944fe2a0208c68a96d49fb5e3b`.

- Mira-Cult machine, Jeff Ketchersid verification, and SIR proof-layer
  description: https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/README.md
  (read through the selected GitHub plugin; blob
  `d2f3eb1d7150a35f99cc866720aeb9bb75981f5f`).
- Exact upstream row definitions:
  https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/coq/logic/Codes254.v
  (GitHub plugin, blob `fd6f94345cfb65be33f427c03ba09fe003b2fbbb`).
- Exact native rules:
  https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/coq/logic/Thm254.v
  (GitHub plugin, blob `207262643ee248032ee3db4e69b3cc41bfdddbf8`).
- Full equality engine, dependency on `rho3`, and substitution caveat:
  https://github.com/VladimirReshetnikov/ProveIt/blob/ce192939372ac7944fe2a0208c68a96d49fb5e3b/Computability/BusyBeaver/Research/ZFC/tarski_logic_layer.md
- Finite-sort obstruction, including PA strengthening and primitive Bottom:
  https://github.com/VladimirReshetnikov/ProveIt/blob/ce192939372ac7944fe2a0208c68a96d49fb5e3b/Computability/BusyBeaver/Research/ZFC/typed_countermodel.md
- Detailed full-engine PSC and complete-logic controls:
  https://github.com/VladimirReshetnikov/ProveIt/blob/ce192939372ac7944fe2a0208c68a96d49fb5e3b/Computability/BusyBeaver/Research/ZFC/logical_engine_completeness.md
- Same base URL and directory, checked locally: `psc_calibration.md`,
  `functional_subset_closure.md`, `gen_free.md`, `register_lifetime.md`,
  `equational_generator_cost.md`, `clausal_reference.md`,
  `finite_quotient_frontend.md`, `mira_containers.md`, `native_theory254.md`.
- Primary pedagogical exposition of equality as an equivalence congruence
  followed by a quotient, and of complete first-order refutation engines:
  Jeremy Avigad et al., *Logic and Mechanized Reasoning*, chapter 16,
  https://avigad.github.io/lamr/proof_systems_for_first_order_logic.html,
  especially section 16.4. Opened as web result `turn3view3`; parent must open
  it before citing. This supports only the ordinary general logical background,
  not the new collection derivation or any state count.

The GitHub pages were unavailable through the generic web fetch, but their
actual contents were successfully obtained through the explicitly selected
GitHub connector. Cite those URLs normally or as repository sources; do not
cite failed generic web-fetch reference IDs as evidence.
