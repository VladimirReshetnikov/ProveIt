# Atomic orientation as a safe source-encoding degree of freedom

## Result and scope

A bounded compiler experiment, performed at ProveIt commit
`e58338db7545909907e07a7603e8eb88625c527a`, improves the retained-complete-logic
Wade control from 268 to **267 working states**. The successful change reverses
the argument order in the membership and equality atom codecs together. The
formula alphabet still has all four constructors, and every original logical
row remains. CP, GIC, both atomic vacuity families, generalization, parameter
reads, freshness tests, cleanup and the complete arithmetic framework remain
present.

This is a measured compiler-control result, not a 267-state consistency endpoint
and not a smaller machine than the 243-state user baseline. In particular, it
does not provide a binary simulation theorem for the generated table. It is
useful supplementary evidence that changing the encoding can improve source
sharing while keeping a complete logical specification. No historical-priority
claim is made for exchanging the arguments of a binary constructor.

## 1. Exact codec and transport theorem

Put

\[
P(a,b)=\frac{(a+b)(a+b+1)}2+b.
\]

The original numeric syntax uses

\[
I(a,b)=4P(a,b),\quad R(i,j)=4P(i,j)+1,\quad
Q(i,a)=4P(i,a)+2,\quad E(i,j)=4P(i,j)+3.
\]

Code zero is treated as a canonical truth constant when decoding. This is
semantically the same truth alias as the original code equation
`0 = I(0,0)`. It does not assert injectivity of an unrestricted syntax that
contains both a truth constant and its implication expansion.

Choose two orientation bits \(\epsilon_R,\epsilon_E\). Replace the atomic
constructors by

\[
R_\epsilon(i,j)=
\begin{cases}4P(i,j)+1&\epsilon_R=0,\\4P(j,i)+1&\epsilon_R=1,\end{cases}
\]

and the analogous definition with tag 3 for \(E_\epsilon\). The implication
and universal constructors are unchanged. Let \(D_\epsilon\) be the decoder
that interprets each atomic field pair in the chosen orientation.

Define \(\kappa_\epsilon:\mathbb N\to\mathbb N\) by \(\kappa(0)=0\).
For a positive code, write \(n=4P(a,b)+t\), and set

\[
\kappa(n)=
\begin{cases}
4P(\kappa(a),\kappa(b))&t=0,\\
4P(b,a)+1&t=1,\ \epsilon_R=1,\\
n&t=1,\ \epsilon_R=0,\\
4P(a,\kappa(b))+2&t=2,\\
4P(b,a)+3&t=3,\ \epsilon_E=1,\\
n&t=3,\ \epsilon_E=0.
\end{cases}
\]

Only formula children are recursively transformed; an atomic argument and the
first argument of a universal constructor are variable labels.

**Theorem.** For each choice of orientation bits:

1. \(\kappa\) is a total primitive-recursive involution.
2. \(D_\epsilon(\kappa(n))=D_0(n)\) for every natural \(n\), with the
   canonical truth convention at zero.
3. Both distinguished codes are fixed: \(\kappa(0)=0\),
   \(\kappa(1)=1\).
4. The set of variable labels in \(D_\epsilon(n)\) equals that in
   \(D_0(n)\). For \(n>0\), every such label is strictly less than \(n\).
   Code zero has empty semantic support. Consequently the old matrix-code
   freshness argument survives the atomic orientation change.
5. The corresponding operation on named formula trees commutes with variable
   renaming and capture-avoiding substitution.

**Proof.** The Cantor projections of \(P(a,b)\) satisfy
\(a,b\leq P(a,b)\). Thus every recursive formula child of a positive code is
smaller than that code. Course-of-values primitive recursion defines
\(\kappa\). At tag 0 it transforms exactly the two formula children; at tag
2 exactly the body; at tags 1 and 3 it exchanges the two finite labels when
requested. Applying the same operation twice restores every atomic pair and,
by induction, every formula child. The exceptional zero alias is fixed.
Equivalently, one may first establish the four constructor identities for
\(\kappa\), treating the sole zero-valued implication separately, and then
perform strong induction on the original code. This proves involutivity and
therefore bijectivity.

For the decoder identity, the implication and universal cases follow from the
induction hypotheses. At a swapped atom the encoder exchange and decoder
exchange cancel. The zero case is literal truth on both sides. Code 1 is the
diagonal atom with field pair \((0,0)\), so it is fixed even when membership
is reversed. In particular the relative-falsity target has not changed.

An exchange of two endpoints does not change their set of labels. Induction
through implication and universal nodes gives label-set preservation. The
strict label bound follows from the displayed Cantor bound and the factor 4;
at a universal node the binder label is also smaller than the parent code.
The zero truth alias must be described semantically: in the historical
expansion `Rel(0,0) -> Rel(0,0)`, label 0 does occur syntactically, although
the formula is independent of every assignment. Finally, applying a label
map and exchanging two endpoints commute. The connective and binder cases
then give the renaming and capture-avoiding-substitution claims by formula
induction. This is an ordinary mathematical proof, not a new Lean module.

**Semantic corollary.** In every nonempty first-order structure and valuation,
interpreting code \(\kappa(n)\) by the oriented decoder gives exactly the
truth value of \(n\) under the original decoder. This is true for an arbitrary
binary membership relation; it does not assume membership is symmetric. The
codec reverses which numeric field names the source and target of membership.

**Proof-system corollary.** If a numeric proof system is conjugated in full by
\(\kappa\), including all axiom instances, rules and numeric side conditions,
then finite derivations are in bijection, and its refutation code 1 is fixed.
Proof induction establishes this statement. The theorem applies to complete
and incomplete calculi alike; it does not repair a pre-existing incomplete
calculus.

There is an important distinction between this general corollary and the
literal emitter control below. In the inherited generator, the same scalar
`c` denotes both a matrix code and a fresh binder label. A pointwise
conjugation sends the former to `kappa(c)`, whereas a variable label is not
transformed by `kappa`. Thus the two literal bundles are not simply identical
after replacing every scalar by `kappa`. Their schema comparison uses the
label bound and alpha conversion of the fresh binder. The finite experiment
does not serialize that proof translation, a new enumerator theorem, or its
arithmetic internalization. This distinction prevents a source-level codec
identity from being advertised as a complete binary consistency proof.

## 2. Why this particular encoding change has a low implementation cost

For an atom \(R(i,j)\), the original postfix emitter pushes \(i\), pushes
\(j\), and calls the ordinary tag-1 constructor. The reversed codec pushes
\(j\), pushes \(i\), and calls exactly the same constructor. Equality works
the same way. The number of macro calls therefore stays **186** for every
tested complete AX word.

The membership change is propagated through every logical and set-theoretic
template, including both arguments of the atomic-vacuity antecedent and its
quantified consequent. Arbitrary matrix codes remain arbitrary payloads and
are interpreted by the oriented decoder. Since implication and universal
coding are unchanged, this change does not require a new MP parser or a
different GEN constructor. It changes source sharing because a repeated word
`push-a; push-b; membership` becomes `push-b; push-a; membership`, and those
new adjacencies can be shared with different neighboring templates.

The useful negative lesson is also concrete: reversing membership alone
made this measured family larger; the improvement appeared only when both
atomic constructors were reversed. State cost does not follow simply from
the number of constructors or free parameters.

## 3. Exact bounded comparison

All four lanes use source 19's already accepted C2/G1/outer-order16/tree1
conjunction layout. They retain every original logical row, including old
rho6 and the four equality rows. Each orientation is measured with four
tokenizations (`coarse`, `primitive`, `existing_short`, `existing_minimum`),
three Re-Pair weight exponents (2, 4, 8), and seeds 0 through 255. This gives
3,072 recipes per orientation, or **12,288 recipes** in total.

| Atomic orientation | Decision nodes | Framework | Working states | Best recipe |
|---|---:|---:|---:|---|
| Original R and E | 206 | 62 | 268 | coarse, exponent 4, seed 130 |
| Reverse R only | 207 | 63 | 270 | coarse, exponent 4, seed 186 |
| Reverse E only | 207 | 62 | 269 | coarse, exponent 4, seed 223 |
| Reverse R and E | 205 | 62 | **267** | coarse, exponent 4, seed 115 |

The full framework is charged, including initialization. Each evaluated DAG
is checked to preserve the original read-sensitive register/control leaf
set. The charged cost is `decision nodes + 55 + dispatcher depth`; an actual
compiler check and independent edge re-extraction is made for every encountered
dispatcher depth. Every selected winner is actually compiled, normalized to a
complete binary table, and all its decision edges are independently extracted.
In particular, the membership-only lane really needs 63 framework states.

The winning complete table has 534 rows, states 0 through 266, start 0,
and a separate halt state 267. Its SHA-256 is

`97eb28d3de8dd772a6050dbb9522738866c8b385cc9a826fd3cb35a4caa9ec82`.

The unchanged public Wade backend has one undefined `1.inc/read1` edge.
The inherited normalizer replaces it by writing the symbol read, moving right,
and entering the separate halt state. This charges no working state. No
claim is made here that this edge is unreachable in the changed blank run.

The search is finite and layout-specific. The number 267 is not an optimality
bound for this codec, the Wade backend, or binary Turing machines generally.
The minimum improving the matched 268 control does not improve the 243-state
baseline, whose much smaller specialized binary runtime is a separate artifact.

## 4. Why the other theory directions were not used for the new state bound

The following source findings are prior project work, checked against the
pinned repository, and are retained here to avoid repeating invalid shortcuts.

* Deleting the equality rows from the old C/G engine is not justified by the
  ordinary equiconsistency of an equality-free theory. The finite-sort
  counterinterpretation validates the emitted reduced calculus while keeping
  the refutation target false. Same-variable specialization does not repair
  its cross-variable substitution defect.
* Raw equality-free PSC has an ordinary hereditary-saturation calibration,
  but the inexpensive reduced logic used in earlier PSC tables has the same
  obstruction. The complete PSC and outgoing-equality controls have measured
  costs above the retained source control. The theory calibration alone does
  not provide a smaller interpreter.
* Finite GIC-selector fusion is already established in source 37. The fused
  matrix depends on the finite proof being searched; it is not one fixed
  first-order membership sentence equivalent to the whole ZFC-strength
  schema. Matrix generation and its selector payload must be counted.
* Three-parameter propositional bases, three-congruence fusion, prefix-closed
  GEN elimination, and finite equational kernels have already been measured
  or given exact proof-search interfaces. Their existing complete controls
  do not beat the current specialized machine. This is not an impossibility
  theorem for other implementations of those formalisms.

The experiment above therefore keeps the known complete engine and varies a
representation choice whose syntax and semantics can be stated precisely.

## 5. Reproduction and provenance

Run `orientation_control.py --repo /path/to/ProveIt --seeds 256 --out /tmp/orientation-results`
with the pinned ProveIt checkout available. The driver
copies the exact vendored Wade inputs out of Git into its output directory,
verifies the supplied hashes, and reads the unchanged source 08/source 19
helpers. It writes no changes into the checkout. It saves the table, DAG,
recipe, label map and evidence for each winning orientation.

The required working helper files must match that pin, and the driver checks
their bytes against Git. A partial clone may need Git to fetch missing blobs
on its first run; for an offline replay, materialize the required pinned
objects beforehand. The driver uses `git show` for inputs and never requests
an alternate revision or silently replaces changed helper files. Run without
Python's `-O` option, since the finite checks use assertions.

The original code calculus, program and verification are due to Mira-Cult
and Jeff Ketchersid; the compiled framework is Andrew James Wade's unchanged
MIT-0 backend. Source 08's exact-word Re-Pair helpers and source 19's complete
conjunction layout are reused with their existing attribution. The new work
here is the orientation comparison driver, the selected oriented word, the
bounded measurements and the accompanying ordinary codec argument.

Primary repository references (all at the pinned commit above):

* `Computability/BusyBeaver/Research/ZFC/tarski_logic_layer.md`
* `Computability/BusyBeaver/Research/ZFC/logical_engine_completeness.md`
* `Computability/BusyBeaver/Research/ZFC/theory_backend_experiment.md`
* `Computability/BusyBeaver/Research/ZFC/layout_grammar_experiment.py`
* `Computability/BusyBeaver/Research/ZFC/outgoing_profile.md`
* `Computability/BusyBeaver/Research/ZFC/gen_free.md`
* `Computability/BusyBeaver/Research/ZFC/equational_generator_cost.md`
* `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/37-fusion-references-source_audit_notes.md`
* `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/46-borrowed-code-fusion-README.md`

Canonical URL prefix:

`https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/`

