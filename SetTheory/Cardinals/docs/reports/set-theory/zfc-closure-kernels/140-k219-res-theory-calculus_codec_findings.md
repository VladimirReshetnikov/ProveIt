# Calculus and codec exploration: findings and limits

## Scope and status

This branch explored changes to the native calculus and its arithmetic
encoding, starting from `K220_Construction_2026-10-20`. The baseline source
has 4,744 primitive occurrences and 208 distinct syntactic subtrees. Its
literal machine has 220 working states. A source DAG count is not a Turing
machine state count: decoder sharing, arithmetic-helper entries, and prefix
contracts must also be preserved.

**No independently valid machine with at most 219 states was produced by
this branch.** The separate clean-equality-macro branch preserves the
calculus and is the promising construction route. This report records
rigorous results from the broader search, including a new obstruction that
uses the full native seed-K schema, and distinguishes them from bounded
computational exploration.

## 1. A rigorous obstruction to simplifying the propositional row

The original row is

\[
L(A,B,C,U)=((C\to U)\to A)\to((A\to C)\to(B\to C)).
\]

One tempting saving is to eliminate its unique fourth input field by
restricting `U` to falsum, truth, or one of `A,B,C`. All five restrictions
are inadequate for the requested consistency calibration, even if they are
all emitted simultaneously and the following schemes are added:

\[
A\to A,\qquad F\to A,\qquad A\to(B\to A).
\]

The proof supplies a four-valued model of every remaining native logical
row, the full gated seed-K bundle including support, MP, and GEN. Its
domain is `HC`, the set of hereditarily countable sets. Designated
membership is actual membership, but false membership is colored in two
different ways. The nonclassical implication makes the **native subset
formula express equality of objects**, so the set-existence schema needs
only countable closure under selected witnesses. ZFC constructs this model
and proves consistency of the altered calculus.

The single implication matrix is

| → | 0 | 1 | 2 | 3 |
|---|---:|---:|---:|---:|
| 0 | 3 | 3 | 3 | 3 |
| 1 | 3 | 3 | 1 | 3 |
| 2 | 3 | 3 | 3 | 3 |
| 3 | 0 | 0 | 0 | 3 |

Here only `3` is designated and falsum is `0`. The matrix validates all
five restricted rows, identity, ex-falso, and the K combinator. Quantifiers
return Boolean values according to designatedness of all instances.
The HC coloring uses an antichain of binary sequences, so distinct columns
always have a witness to the nondesignated implication `1→2=1`.

The full proof is in `restricted_rho8_strong_countermodel.md`. The independent
stdlib checker `restricted_rho8_strong_countermodel.py` verifies the finite
matrix claims; its receipt is
`generated/restricted_rho8_strong_countermodel.json`. The proof is ordinary
mathematics formalizable in ZFC, not a Rocq/Lean certificate. The finite
receipt does not replace the HC closure argument.

This obstruction is stronger than a failure of propositional completeness:
it incorporates the complete native seed-K bundle. Conversely, it says
nothing about arbitrary alternative three-parameter bases or about the
separate proposal replacing rho6 by universal instantiation. A countermodel
to deriving a deleted row alone does not establish failure of
equiconsistency.

## 2. Safe transformations that did not improve the measured machine

### 2.1 Fusing equality existence with the G helper

Replace the separate existence row and G row by

\[
H=\exists x\,[E(x,y)\land Q_xG].
\]

Over the retained classical propositional and normal-quantifier rules,
this is exactly equivalent to the two original rows. Projection and
existential monotonicity give `exists x E(x,y)`. The other projection gives
`exists x Q_x G`, and retained rho6 yields `G` directly. Conversely, from
the theorem `G`, generalization gives `Q_xG`; combine this with equality
existence. No universal-instantiation assumption or circular recovery of
rho6 is needed.

The source experiment deleted the actual two old rows and emitted one
fused row, changing the batch output count from ten to nine. Across 72
parameter/placement variants, the smallest measured source had 229 DAG
nodes and 4,826 primitive occurrences. This particular implementation is
uncompetitive; the theorem remains a valid simplification option.

Artifacts: `h_fusion.py`, `generated/h_fusion/summary.json`.

### 2.2 Nesting the fourth parameter into an existing field

Let an AX field contain the Cantor pair `P(U,S)`. Its first emitted row can
be written

\[
((P_0\to U)\to R_0)\to((R_0\to P_0)\to(S\to P_0)).
\]

The ordinary fourth-parameter reader instead destructively unpairs that
existing parameter register, returning `U` as its output and leaving `S`
in the register. Every later row uses the unpaired parameter. No axiom
strength is lost: Cantor pairing is bijective, so the four values remain
independently arbitrary. With the matrix-code register chosen, all later
rows retain their post-decoding parameters, while rho8 uses a permutation
of those parameters. The axiom families are unchanged; individual AX
batches need not be literally identical. The cache/delta-register variants also have
unrestricted coverage after the ordinary reset to zero.

All six register/role choices preserve 4,744 primitive occurrences. Their
source DAG sizes were 211–215, versus 208 for the baseline. Every raw
incremental compilation hit a decoder binding mismatch. These are source
experiments, not valid small-machine candidates.

Artifacts: `nested_fourth_parameter.py`,
`generated/nested_fourth_parameter/summary.json`.

### 2.3 Ordinary complete three-row propositional bases

The fourth-field reader was completely removed and rho8 replaced by each
of the standard bases `K,S,Peirce`, `K,B,Peirce`, and `K,S,DNE`, where

\[
\begin{aligned}
K&=A\to(B\to A),\\
S&=(A\to(B\to C))\to((A\to B)\to(A\to C)),\\
B&=(A\to B)\to((B\to C)\to(A\to C)),\\
\operatorname{Peirce}&=((A\to B)\to A)\to A,\\
\operatorname{DNE}&=((A\to F)\to F)\to A.
\end{aligned}
\]

For each basis, 3,888 parameter-permutation, row-order, and tree-shape
variants were measured. The best source DAG sizes were respectively
216, 214, and 216, including variants with the baseline maximum zero run
six. The AX batch has twelve outputs in these replacements. Retained
best candidates did not compile correctly with the raw incremental
compiler. The finite family does not rule out a better representation of
these bases.

Artifacts: `three_row_proposition.py`,
`generated/three_row_proposition/summary.json`.

### 2.4 Equality-helper binder arithmetic

The established helper theorem permits any total binder function
`kappa(a,b)` that differs from both labels whenever `a≠b`; the diagonal
case has no freshness requirement. The simple choice `a+b+1` saves 46
primitive occurrences but produced 210 DAG nodes and a raw 223-state
table. Sixteen ordinary constructor choices and 120 scaled-Cantor/tag/
orientation/association choices reached the original 220-state count,
without a verified reduction. These are bounded grammar measurements,
not a minimality result for binder arithmetic.

Artifacts: `additive_binder.py`, `constructor_binders.py`, `pair_binders.py`,
and their corresponding `generated` summaries.

## 3. Arithmetic-code transformations

### 3.1 Six fixed-modulus tag permutations

Membership retained tag 1 and falsum code 1. The tags `0,2,3` were assigned
in all six ways to implication, universal quantification, and equality.
All 81 constructor occurrences were changed, including the specialized
GEN and MP builders. The full primitive control-flow graph was checked
after each source edit, accounting for the inserted/deleted tag increments.

The zero-code exception remains sound in each assignment: whichever
constructor receives tag 0, its `(0,0)` instance is a tautology
(`truth→truth`, universal truth, or reflexive equality). Every positive
formula retains the strict subcode/label bound needed by the private
matrix-code binder. Thus the transformations are logically safe when the
emitter and proof commands use the same codec.

Thirty-six direct implementations were measured: six assignments, three
edit policies, and two increment-parenthesizations. The original assignment
remained best at 208 DAG nodes/220 states. The closest nonidentity
assignment had 209 DAG nodes but zero-run ten, beyond the existing decoder
contract. Further nonlocal reparenthesization found a different
209-node, zero-run-six source, but its raw table failed an interface test.
A protected 232-state compilation passed all 6,183 finite primitive
interfaces; that receipt is a finite screen, not a uniform compiler proof.

Artifacts: `tag_permutations.py`, `generated/tag_permutations`,
`generated/codec_reassociate_032`, `generated/protected_codec032`.

### 3.2 Independent Cantor-field orientations

All sixteen choices of reversing the arguments of implication,
quantification, equality, and membership were implemented by postfix
operand re-emission. GEN operands and the MP pair builder were updated
where necessary. Symbolic decoding verifies each emitted AX formula;
the complete source graph is compared with the closed-atom reference.

With the old closed-atom tree shape retained, the best nonidentity source
had 212 DAG nodes. A further adjacent-pair grammar heuristic tried twenty
parses for each orientation and obtained a minimum of 216 nodes in that
separate family. No verified machine improvement resulted. These searches
do not cover all possible grammars, field encodings, or machine compilers.

Artifacts: `orientation_postfix.py`, `orientation_repair.py`, and their
`generated` summaries.

## 4. Compiler caveat discovered during the search

Several inherited decoder states are also arithmetic helpers. Merely
obtaining a consistent decoder map after reparenthesizing source does not
make it safe to repurpose all old decoder rows. Raw incremental tables
repeatedly failed actual primitive-interface runs despite attractive source
counts or decoder-map checks.

`protected_compile.py` preserves whole states observed on arithmetic
execution paths after complete decoder passes. Its protection set was
obtained from 6,167 finite primitive frames and therefore does not itself
prove unbounded completeness of the protected-state inventory. It is a
conservative debugging tool, not a replacement for the machine-level
proof. The final construction must prove every modified entry and its
prefix/frame preconditions.

## 5. Independent review of the clean equality macro

Under the structured source semantics, the original q77 equality macro's
left subtree is

\[
D=\langle CD_6,\langle\langle CD_5,CC_2\rangle,
\langle CI_5,\langle CD_6,CC_2\rangle\rangle\rangle\rangle.
\]

On input registers `(a,b)` in positions 5 and 6, it terminates normally
with `(|a-b|,0)`. While both inputs are positive it cancels one from each.
If register 6 reaches zero first it exits. If register 5 reaches zero first,
the nested increment/decrement loop transfers the remaining difference
into register 5. The outer right subtree

\[
\langle CD_5,\langle\langle CD_5,CC_1\rangle,CB_1\rangle\rangle
\]

returns normally exactly on zero difference; otherwise it clears the
difference and returns `Break_1`. This proves the old open-tree contract
for all natural inputs and all surrounding registers.

The replacement proof in `research_encoding/clean_eq_proof.tex` was reviewed
independently. Its cancellation, equality-branch, and cleanup lemmas are
valid for all natural inputs. It has exactly the same open-tree contract,
including clearing both compared registers on either branch and preserving
every other register. Matching macro boundaries therefore proves the
source-level stuttering simulation. Correct literal decrement/break entries
remain separate machine-level obligations.

## Research limits

The source searches above are finite, representation-dependent searches;
their failures establish no global lower bound. The four-valued HC model
is an unbounded negative theorem about the specifically listed restricted
calculus. The equality-macro replacement is an unbounded positive theorem
about the source program. Neither theorem alone certifies a literal
219-state Turing machine; the final table, startup, interfaces, and
state-count certificate must be supplied by the construction branch.
