# PA196 and the incoming U208 construction

This note compares the literal binary machines and the proof obligations as of
13 November 2026. **No machine below 196 states, and no PA proof of the full
PA196 consistency biconditional, is established here.** The state counts below
count working states and exclude a distinguished halt control. Every machine
starts in state 0 on a two-way infinite, all-zero tape.

## Sources and their proof status

* James Chang's imported [PA196](../jamesyc-upstream/pa196/) is the upstream
  revision `407cdc356f6b586635e71ac92be394255f4bfea4`. Its
  [`data/pa196.tm`](../jamesyc-upstream/pa196/data/pa196.tm) has 196 working
  states, 392 transitions and the separate halt label 196. Its SHA-256 is
  `e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
  The upstream [paper](../jamesyc-upstream/pa196/paper/pa196.tex) and
  [theorem inventory](../jamesyc-upstream/pa196/docs/result.md) distinguish a
  Lean theorem of literal nonhalting in the metatheory from the *internal*
  PA theorem `nonhaltingSentence → Con(PA)`. The theorem in
  [`Independence.lean`](../jamesyc-upstream/pa196/PA196/Independence.lean)
  proves that latter implication, not the biconditional. In particular,
  [`Logic/Soundness.lean`](../jamesyc-upstream/pa196/PA196/Logic/Soundness.lean)
  explicitly describes its HF-model proof as external; it is not an internal
  PA consistency proof. This is an observation about the shipped theorem
  statements, not a claim that the other direction is false or unprovable.
* The imported [PA209](../jamesyc-upstream/pa209/) is the requested earlier
  revision `69d98241a721ead20b4f0b17df9062950b40fbfe`. It has 209 working
  states and halt label 215, and exposes the analogous one-way internal
  nonhalting-to-consistency result. PA196's paper identifies it as the direct
  predecessor and records a reduction of 13 working states. Its program has
  3,948 sites, versus PA196's 3,812.
* The incoming [U208 archive](../docs/U208_ConPA_2026-10-29/)
  contains `U208_ConPA_2026-10-29/report.tex`, `machine/u208.tm`, and the
  parent `baseline/u209.native.tm`. The dense U208 table has 208 working
  states and 416 rows, with halt 208. Its report states the intended
  `PA ⊢ ¬Halt(U208) ↔ Con(PA)`, combining a PA-formalizable local fold with
  inherited source/calculus and unary-theory calibrations. The archive says it
  contains **no new end-to-end exported PA, Lean, Rocq, or MM0 certificate**
  for that endpoint. It remains an external submission in
  [`docs/incoming`](../../../../../docs/incoming/README.md), not an imported
  proof of the PA196 endpoint. The [separate review dossier](../docs/pa_consistency_research_2026-10-29/)
  reports 3,909 source primitives for its U208 classes. Its U209 parent is
  **not** thereby identified with James Chang's distinct PA209 machine.

## Source-program changes versus physical folds

PA196's paper, sections 3 and 5, identifies the following changes from its
PA209 predecessor:

1. The universal-quantifier constructor reverses the Cantor-pair arguments:
   `wal a B = 4 * pair B a + 2`; the implication, membership and equality
   constructor tags remain 0, 1 and 3. The matching decoder is changed too.
2. The axiom emitter drops head ρ7, introduces guarded equality vacuity into
   its gate, changes the ordering of the remaining heads and exchanges some
   antecedents. The paper explains how the missing uses of ρ7 are recovered.
3. It shares six pairs of complementary left/right source-tree nodes and
   removes two now-unnecessary states outside the changed axiom body. The
   resulting machine uses 36 engine states, 13 leaf-routing states and 147
   source-tree reader states. The paper's stated six folds are not six more
   states to subtract from 196: they are already included in the table.

U208's final one-state reduction is a different, explicitly local tape
simulation. In the selected Joint *native* U209 parent, its state 211 is
entered by the two rows of state 163:

```text
163 0 0 L 211
163 1 1 R 211
172 1 1 R 184
211 1 1 R 184
```

Its report merges 211 into 172, changes the zero row of the keeper, and uses
incoming-history invariants and an existing helper to distinguish the needed
paths. This fold preserves halting of its particular parent; it does not, by
itself, certify the source/calculus calibration or change PA196's table.

A direct finite scan of PA196's 392 rows finds **no** working state `p` whose
zero and one rows respectively write 0/move L and write 1/move R to the same
working target. Thus no state relabeling can transplant the exact mixed-entry
pattern above into PA196. This rules out that specific literal motif, not
other history-sensitive folds, different helpers, offset simulations, or a
source-level reallocation. The check is reproducible from the table as follows
(run from the repository root):

```sh
python3 - <<'PY'
from pathlib import Path
p = Path('Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/data/pa196.tm')
r = {}
for line in p.read_text().splitlines():
    q, bit, write, move, target = line.split()
    r[int(q), int(bit)] = (int(write), move, int(target))
assert set(r) == {(q, b) for q in range(196) for b in (0, 1)}
matches = [(q, r[q, 0][2]) for q in range(196)
           if r[q, 0][:2] == (0, 'L') and r[q, 1][:2] == (1, 'R')
           and r[q, 0][2] == r[q, 1][2] < 196]
print(matches)  # []
PY
```

The accompanying [local-fold search](search/README.md) checks a wider but
still bounded family, including the U208 fold as a positive control. The
[source search](source-search/README.md) tests directional reassociations.
Neither produced a smaller physical machine. A separate
[zero-transfer specialization](source-search/ZERO-TRANSFER.md) removes three
source sites while preserving halting from the clean seed. A
[second cleanup](source-search/SECOND-CLEANUP.md) removes two more, but the
combined changes increase the number of distinct source nodes from 159 to 162;
no state saving follows.

## Combining two incoming source rewrites

The later incoming comparison proposes an MP-success branch that returns the
consequent in `H`; another incoming archive supplies a shorter negation macro.
The [combined experiment](source-search/negation-mp197/README.md) gives a
3,573-site source and a 197-state machine. Both independently replayed symbolic
primitive checkers and the exact startup check pass. Its negation rewrite needs
a scratch-zero entry invariant, which the experiment checks for all eight
entries; the [local audit](source-search/negation-mp197/local-audit/README.md)
explains the block identity and shows a counterexample without that condition.
This is an experimental candidate, not a smaller machine or a proved PA
consistency equivalence. In particular, the new MP compiler and full
literal-to-source and proof-code transport remain unverified in PA.

## The missing internal consistency direction

To obtain the requested *PA-provable* biconditional for PA196, and for any
smaller descendant, it remains to establish the reverse implication
`Con(PA) → ¬Halt` internally. One possible route is to construct a uniform
coded proof transformation, rather than appeal to a truth predicate for all
formulas:

1. Formalize, for arbitrary PA-internal finite binary runs, a halted literal
   PA196 trace as a finite derivation of code 1 in the exact PA196 calculus.
   The external positive-block simulation and the existing all-model
   source-to-tape direction do not automatically supply this reverse trace
   extraction. The arbitrary-internal-time statement and termination of the
   required macro blocks must be proved, including startup and any partial
   final block.
2. Translate that coded derivation into a refutation in the unrestricted
   weak-covering theory W plus irreflexivity used in the incoming U208
   calibration. Recursively translate the **transposed** quantifier coding;
   preserve code 0's truth convention and code 1's false target. Supply
   uniform proof templates for the six heads, restricted ρ8, modus ponens,
   generalization and the guarded bundle, including variable collisions and
   freshness. This must work for nonstandard proof and formula codes inside
   arbitrary models of PA, not only for each externally fixed formula.
3. Supply the uniform refutation translation from W + irreflexivity into PA,
   using PA's binary-bit interpretation of membership. Composing the
   translations proves `Halt → ¬Con(PA)` in PA. The existing PA196 theorem
   `¬Halt → Con(PA)` provides the other direction after classical
   contraposition as appropriate.

A candidate numeric recoding from PA196 formulas to the old U208 convention
would recursively swap the two Cantor-pair components at tag 2. For a PA196
quantifier `4 * pair(body, label) + 2`, it would produce
`4 * pair(label, recode(body)) + 2`; implication recursively recodes both
formula children, while membership and equality keep their numeric variable
labels. Code 0 is a special truth alias and needs an explicit base case.
Proving totality and a PA-representable graph for this recursion, decoding
agreement, bounds, and transport of bounded coded derivations are **open
obligations** here; a slogan about swapping arguments does not establish
any of them.

There is a further interface issue. PA196 uses the same natural number `c`
as the original property formula code and as a bound-variable label. After
recoding, that property has code `recode(c)` while the variable label remains
`c`. Thus a native U208 gate theorem restricted to binder = property code does
not directly give the translated gate unless these numbers coincide. A viable
route needs a generic W + irreflexivity proof template with an arbitrary
property code and the original fresh binder, plus an internal proof of
freshness after recoding; alternatively, it must implement and verify a
suitable alpha-renaming. Neither is supplied by the comparison below.

There is a concrete possible bridge for the changed gate. Let `V` be the old
membership-vacuity formula, `Q` the old quantified separation part and `Δ`
the new equality-vacuity formula. PA196's
[`Logic/Basic.lean`](../jamesyc-upstream/pa196/PA196/Logic/Basic.lean)
sets `G = ¬(V → Q)` and `F = ¬(Δ → (V → Q))`. Classical propositional logic
proves `F ↔ (Δ ∧ G)`: both sides are true exactly when `Δ` and `V` are
true and `Q` is false. A direct check of all eight propositional valuations
is:

```python
from itertools import product
for delta, v, q in product((False, True), repeat=3):
    implication_vq = (not v) or q
    old_gate = not implication_vq
    new_gate = not ((not delta) or implication_vq)
    assert new_gate == (delta and old_gate)
```

This finite check says nothing about whether `Δ` or `G` has a W +
irreflexivity proof for the decoded numeric parameters. A *uniform syntactic proof* of the old gate
and one of `Δ` under the PA196 freshness guard are a plausible starting
point for translating the new gate, once that binder/code mismatch is handled.
This observation is not itself a proof
of the complete translation: PA196's different numeric constructor and the
internal coding/trace obligations above still need verified implementations.

No inference from a finite blank-tape prefix to nonhalting is used here, and
no failed finite search is a lower bound on all 195-state machines.
