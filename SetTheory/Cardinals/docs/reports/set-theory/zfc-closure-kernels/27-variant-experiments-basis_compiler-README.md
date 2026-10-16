# Complete three-parameter propositional bases: compiler comparison

**Result:** the best measured K/S/Peirce variant has **268 working states**,
matching the supplied source19 Lukasiewicz-basis compiler baseline.  The best
K/B/Peirce variant has **269 working states**.  Both are complete propositional
bases and remove the fourth formula-parameter read from an AX command.  This
bounded search found no improvement over the 268-state compiler baseline and
does not improve the public 253-state consistency-machine submission.

These are actual binary transition-table counts, including the blank-tape
initializer and the full dispatcher generated for each decision DAG.  The
archive includes the literal tables and independently checkable finite RM
bisimulation certificates.  The new tables have not received an end-to-end
formal proof of their ZFC consistency equivalence.

## Mathematical scope

Write `I(a,b)` for implication and instantiate the following schemas at
arbitrary formula codes:

\[
\begin{aligned}
K(a,b)&=a\to(b\to a),\\
S(a,b,c)&=(a\to(b\to c))\to((a\to b)\to(a\to c)),\\
B(a,b,c)&=(a\to b)\to((b\to c)\to(a\to c)),\\
P(a,b)&=((a\to b)\to a)\to a.
\end{aligned}
\]

The tested bases are `KSP = {K,S,P}` and `KBP = {K,B,P}`.  The latter is the
Tarski–Bernays basis, explicitly stated in Frank Pfenning,
[Single Axioms in the Implicational Propositional Calculus](https://www.cs.cmu.edu/~fp/papers/cade88.pdf),
CADE 1988, section 2.1.  That paper calls K “Simplification” and B
“Hypothetical Syllogism.”  The report's separate propositional certificates
give finite, substitution-uniform basis translations; the compiler directory
does not substitute a semantic-completeness assertion for those certificates.

In the original program the propositional row is the four-parameter axiom

\[
 ((c\to u)\to a)\to((a\to c)\to(b\to c)).
\]

Each tested program replaces this one row by three rows.  It retains every
other original logical schema, including equality axioms, `rho6`, quantified
implication distribution, quantifier commutation, existence of equals, GEN,
both vacuity clauses, the base-4 formula codec, CP, GIC, and the original
freshness gate.  It permits independent permutations of the three arbitrary
parameters in a schema, permutations of the emitted rows, and commutations
and reassociations of conjunctions in the set-theory bundle.  No extra free
fourth parameter is silently supplied to any new row.

The command format changes from `AX c x y u` to `AX c x y`: the original
`read_u` and `move_u` macros are absent from the emitted AX word.  The current
formula and cached formula behavior, including GEN's read of the old cache
before `read_b`, remains represented exactly in the symbolic emitter.  All
three scalar parameters can still range independently when preparing an
axiom leaf from reset auxiliary registers.

### What is established at each layer

The finite propositional certificates establish that the old and new
**logical bases** derive each other.  They remain applicable to the numeric
formula representation because they use exact MP and uniform substitution,
without assuming constructor injectivity.  Retaining the other logical and
set-theory rows therefore preserves the intended complete calculus, subject
to the displayed valid conjunction rearrangements.

For each frozen recipe, `reference.dag.json` directly emits that recipe's
modified AX macro word without Re-Pair grammar rules.  `candidate.dag.json`
emits the identical word with grammar sharing.  The finite certificate checks
that these **two RM programs** have matching increment/decrement/halt
operations and both decrement branches at all related reachable instruction
sites.  It does not relate the changed proof stream to the original `p254`.

The source-level enumeration proof must be adapted to the new command fields
and the two extra stack rows: in particular the leaf selectors, cleanup
counts, `DISCARD`, and GEN block depths.  The original proof architecture
provides the method, but the modified enumerator-to-calculus theorem is not
claimed as a checked artifact here.  Likewise, reextracting the generated
decision edges is a compiler sanity check, not a formal correctness proof of
all arithmetic tape routines.  The `binary_compiler_proved` and
`ZFC_endpoint_proved` flags in the evidence consequently remain false.

See [internalization.md](internalization.md) for the source-specific ordinary
ZFC argument for the established 254-state construction and the precise
additional links needed for changed compiler outputs.

## Measured comparison

| Frozen recipe | AX macros | Decision states | Framework and boot | Total working states | Explicit transition rows | RM certificate pairs |
|---|---:|---:|---:|---:|---:|---:|
| L: supplied source19 baseline | 186 | 206 | 62 | **268** | 536 | 4,533 |
| KSP: best complete three-parameter variant | 196 | 206 | 62 | **268** | 536 | 4,750 |
| KBP: best complete three-parameter variant | 194 | 207 | 62 | **269** | 538 | 4,713 |

The baseline uses C variant 2, G variant 1, outer conjunction order 16,
binary conjunction tree 1, Re-Pair seed 341 and weight exponent 4.  Its
logical rows retain their original order and parameter names.

The final KSP recipe uses C=2, G=3, outer order=16, tree=3, seed=3122,
exponent=8.  Its three propositional emissions, in order, are

\[
 a\to(c\to a),\quad ((c\to b)\to c)\to c,\quad
 (c\to(b\to a))\to((c\to b)\to(c\to a)).
\]

The final KBP recipe uses C=2, G=1, outer order=18, tree=4, seed=2251,
exponent=8.  Its propositional emissions are

\[
 ((a\to c)\to a)\to a,\quad
 (b\to a)\to((a\to c)\to(b\to c)),\quad c\to(b\to c).
\]

The complete parameter permutations and other-row orders are in
`recipes.json`; each result's `evidence.json` contains the full formula ASTs
and expanded macro word.  Removing one input field increased the raw emitted
word by ten macros for KSP and eight for KBP.  Sharing recovered the KSP cost,
but a smaller parameter count did not by itself produce a smaller machine.

The cost function actually invoked `TMBuilder.generate()` and `tm.gc()`.
Some trial grammars required 63 framework states.  An unconditional estimate
`number_of_DAG_nodes + 62` would therefore undercount those machines.  No
such estimate was used to select the displayed winners.

### Search budget and reproducibility

| Stage | Budget per basis | Best KSP | Best KBP |
|---|---:|---:|---:|
| Fixed source19 layout, seeds 0 through 999, exponent 4 | 1,000 | 272 | 271 |
| Additional randomized row/permutation trials | 3,000 | 271 | 271 |
| Directed search with source19 bundle fixed | 20,000 proposals | 269 | 270 |
| Directed search also varying conjunction layouts | 40,000 proposals | 268 | 269 |

Across both bases this is 128,000 proposals.  There were 111,141 actual
candidate compilations: 55,542 for KSP and 55,599 for KBP.  The directed
stages cache repeated word/seed/exponent triples; the counts exclude the
additional baseline and final reproduction runs.  This is a bounded
heuristic search, not a global optimality claim.

The random seeds are 10616 for the additional initial trials, 10617 for the
fixed-bundle directed stage, and 10618 for the final joint stage.  The saved
stage records include every strict improvement, cost histograms for the
initial stage, final recipes, budgets and actual compilation counts.

## Files and commands

Python 3.10 or later and its standard library suffice.  The frozen outputs
are in `frozen/L`, `frozen/KSP`, and `frozen/KBP`.  Each contains a complete
numeric table, readable named table, state map, candidate and direct-reference
DAGs, RM certificate and evidence.  State 0 is the start, symbol 0 is blank,
and the distinct uncounted halt identifier equals the number of working
states.  Missing rows of the named backend representation are explicitly
totalized as “write the symbol read, move right, halt,” adding no working
state.  The displayed numeric tables have two rows for every working state.

From this directory, check the packaged certificates without importing the
grammar generator or the binary compiler:

```sh
python -B check_certificates.py --directory frozen
```

Recompile the three selected recipes and generate fresh certificates into
a new directory outside this input package:

```sh
python -B reproduce.py --output /tmp/proveit-basis-reproduction
```

The reproducer verifies the input SHA-256 manifest, reextracts every generated
decision edge, checks the independently implemented RM certificate, and
compares the generated table hashes with the frozen recipes.  It was also
tested after copying its inputs to a shallow directory under `/tmp` and
running from a different working directory.  The vendored sources remain
byte-exact; the driver adjusts the old repository-root assignment only in
memory before using the local snapshot.  No command requires a network
connection, Git checkout, Coq installation or external Python package.

To repeat the bounded searches, use new output paths:

```sh
python -B basis_search.py --seeds 1000 --permutation-trials 3000 \
  --rng-seed 10616 --output /tmp/proveit-basis-stage1
python -B basis_anneal.py --iterations 20000 --rng-seed 10617 \
  --input /tmp/proveit-basis-stage1/comparison.json \
  --output /tmp/proveit-basis-stage2
python -B basis_anneal.py --iterations 40000 --rng-seed 10618 --vary-bundle \
  --input /tmp/proveit-basis-stage2/comparison.json \
  --output /tmp/proveit-basis-stage3
```

Wall-clock fields vary between machines.  The frozen recipes and table bytes
are the reproducible results; no exhaustive search must be repeated to
verify them.

### Table SHA-256 digests

```text
L268   77f88b15383b13846090a31f3780673daf57c8b66fed2b9e7de252686901a61d
KSP268 f69e4cfbc78c8189843b3bf60283e75d43bc8cb4c0d1f36b707ed145f36998d6
KBP269 fa9dce155edb25edeba7f6c6ad6338331922d9b10c4fa8a46e54006443614d5a
```

## Sources, attribution, and licenses

The public Wade compiler is Andrew James Wade's MIT No Attribution backend.
`backend/LICENSE.wade` accompanies its three unmodified modules.  The exact
SHA-256 values are in `input_manifest.json`; in particular `TMBuilder.py`
has digest `03d3a636404e1bcdeceafd98b9478b7a367ab334f3ab9f8a00df1d5c03fdf517`.
The finite DAG and pure symbolic spec are pinned copies of the m254 inputs;
the corresponding digests are
`538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3` and
`7d96deff6994315b714579c74d10efeb65374694d476c802c727356e258578e9`.

* Upstream compiler and snapshot:
  [jeff87654/busy-beaver, commit 297ab8df](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF).
  The established m254 proof used in the accompanying audit is pinned to
  [c132d7ea](https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254).
* `recover_wade_dag.py`, `theory_backend_experiment.py`, and
  `pairing_backend_experiment.py` are byte-exact copies from
  [ProveIt 47f3a360, Research/ZFC](https://github.com/VladimirReshetnikov/ProveIt/tree/47f3a3602946dfe48803a91a910c646e74637ac8/Computability/BusyBeaver/Research/ZFC).
  They are used only through the selected functions; the old scripts' other
  experimental theories are not the basis of any completeness claim here.
* `rebracket_axioms.py` and `verify_rm_certificate.py` are byte-exact copies of
  [08-schema-machine-rebracket_axioms.py](https://github.com/VladimirReshetnikov/ProveIt/blob/4747142d5d15213eb711bdadfa3cc7e769fcb7a7/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/08-schema-machine-rebracket_axioms.py)
  and
  [08-schema-machine-verify_rm_certificate.py](https://github.com/VladimirReshetnikov/ProveIt/blob/4747142d5d15213eb711bdadfa3cc7e769fcb7a7/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/08-schema-machine-verify_rm_certificate.py).
  The weighted Re-Pair grammar heuristic and the existing finite RM path
  checker are attributed to that prior ProveIt research package.
* The conjunction-layout recipe and enumeration order follow the supplied
  source19 full-logic compiler experiment.  This experiment changes the
  propositional basis and performs additional searches; it does not claim
  authorship of the prior 268-state L recipe or of weighted Re-Pair.

ProveIt's MIT No Attribution license is included as `LICENSE.ProveIt`.
New drivers and analysis in this directory are supplied under the same
license for integration into ProveIt.  Source transport had added trailing
newlines to some parent-workspace copies; the packaged copies were restored
to the independently verified exact public blob bytes before final
reproduction.  The manifest records both public Git blob identifiers and
SHA-256 integrity hashes.
