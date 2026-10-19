# Encoding search and an exact finite grammar obstruction

No grammar with fewer than 128 rules was found. This folder contains an exact
lower-bound certificate for a precisely specified finite grammar family,
reproducible search programs, their completed run logs, and selected abstract
grammar witnesses. It does not contain a new binary machine below 245 states.

## Quick independent verification

From any working directory, run:

```sh
python /path/to/this/folder/quick_verify.py
```

This uses only the Python standard library. It reconstructs and verifies the
finite-universe certificate, then audits nine selected abstract grammar
witnesses. The source-variant audits check exact expansion into the declared
fine control atoms; the row-permutation audits check the declared whole-row
order. These are abstract grammar checks, not binary machine validation.
Run without `-O`, since the verifiers use assertions.

The certificate alone is checked by:

```sh
python verify_restricted_bound.py lp128_restricted.lp.json.gz \
  restricted_bound128_certificate.json.gz \
  --inputs restricted_universe_inputs.json
```

## Exact result

The universe consists of the existing grammar words and repeated AX substrings
of length 2 through 40, with the existing incoming-bit restrictions on terminal
children. After pruning unsupported words, it contains **797 nonterminal
words and 4,511 productions**. The 43 original productions traversed by the
fixed route and bootstrap constraints remain frozen. There are 47 required
presence variables. This model has **no scanner zero-run restriction**.

A binary branch tree with nine nodes and five leaves establishes the exact
lower bound 128. Its leaf lower bounds are 1398/11, 1409/11, 4205/33, 1398/11
and 1779/14. Every value exceeds 127. The original 128-rule grammar is checked
as a witness, proving sharpness in this family. Verification uses exact
rational arithmetic, including all residual coefficients. It imports no
optimizer. `restricted_bound_note.tex` gives the derivation and precise scope.

The checker reconstructs the vocabulary, frozen productions, forced words,
permitted productions and every model equation from the pinned input texts
embedded in `restricted_universe_inputs.json`. It checks both compressed and
uncompressed model/certificate hashes. This excludes accidental substitution
of a different finite optimization problem.

This theorem makes no statement about unrestricted grammar minimality or
Turing-machine minimality. Longer new words, changed routes, different
semantic atom spellings, alternative source templates and framework changes
can escape it. In particular, the broader heuristic searches below are not
bounded by this certificate.

## Completed searches

| Search | Budget | Best grammar size / result |
|---|---:|---:|
| Inherited routing annealer, original source | 1,200 s; 22,868,679 iterations | 128 |
| Coupled parent-reparse/node-eviction annealer | 1,200 s; 21,372,420 iterations | 128 |
| Whole-row permutation dictionary search | 1,200 trials; 266 distinct orders | 128; best changed order 129 |
| Three changed-order seeds, coupled annealing | 360 s per seed | 129, 129, 129 |
| Equality converse / membership converse / both | 400 trials per variant | 137 / 134 / 142 |
| Anchored orientation family | 64 variants, five trials each | 128; best nonidentity 130 |
| Three anchored seeds, coupled annealing | 360 s per seed | 129, 131, 131 |
| Best anchored flip plus row permutations | 1,200 trials; 173 distinct variant-order pairs | 130 |
| Larger finite MIP with prefix/suffix complements | 6,596 words; 85,865 productions | Time limit, no incumbent |

Four of the unchanged annealing seeds fail the tighter zero-run requirement
of the 117-state framework: permutation seeds 1 and 2 have 129 rules and
maximum zero run 7; anchored seeds 1 and 2 have 131 rules and maximum zero
run 7. The interval-DP construction bounded ranks locally, but changes to
shared words also affect the bodies of opaque atoms, so a complete global
property audit is necessary. The inherited annealer saves its initial seed
before applying the property guard to subsequent moves. These four results
are retained as diagnostics and marked `scanner245_eligible:false` by the
independent replay. Their raw rule counts are not eligible machine counts.
Permutation seed 0 and the best anchored rho7 seed both have maximum zero
run 6. This issue does not affect the exact lower bound, whose model has no
zero-run guard, or the original-source 128-rule controls.

The larger MIP's elapsed wall time was 486.6 s including preparation and
presolve, despite a requested solver limit of 240 s. Its status is not an
infeasibility certificate. The separate small-universe solver reports are
retained, with the exact certificate replacing numerical status as the basis
for the stated theorem.

The 129-rule anchored witness changes the conclusion orientation of equality
schema rho7. Its source properties are lead 3, maximum zero run 6, maximum
leaf depth 49. It retains all 22 routed projections and 54 bootstrap
projections. Its source expansion matches the declared oriented variant.
It remains an abstract grammar and is larger than the baseline.

The source-call minimum and grammar-state objective differ substantially.
The supplied orientation family can reduce the shortest spelling over the
existing 44 semantic atoms from 533 to 493 calls, yet these searches did not
improve the shared grammar. Dictionary sharing, terminal orientation, routed
entries and tree ranks must be optimized jointly.

## Replaying and extending searches

`reference/` contains the minimal pinned original inputs needed by these
programs. Search requires a C++17 compiler or Python with NumPy and SciPy,
depending on the script. Verification does not require them.

```sh
c++ -O3 -std=c++17 anneal_coupled.cpp -o anneal_coupled
./anneal_coupled reference/inputs/state_reduction/route-grammar.txt \
  reference/inputs/state_reduction/route-constraints.txt new-run.json \
  1200 120261018 127 \
  reference/inputs/state_reduction/bootstrap-lock54.txt resume128.txt

python permutation_search.py --package reference \
  --parts axiom_parts_original.json --output new-orders --trials 1200

python converse_dictionary_search.py --package reference \
  --source anchored_source_snapshot.json --parts axiom_parts_original.json \
  --output new-orientations --anchored --trials 320

python mip_grammar.py --package reference --output rediscovered-lp.json \
  --zero 0 --length 40 --target 800 --lp
```

The explicit LP uses the redundant budget 800, exceeding its 797 presence
variables. The archived certificate is tied to the exact archived model
serialization; regenerate hashes and rediscover a proof if rebuilding the
model with a different serialization. Heuristic execution is not bitwise
portable across C++ standard-library implementations, and wall-time budgets
do not imply fixed iteration counts.

`anneal_coupled.cpp` adds two operations to the inherited routing annealer:
a newly introduced substring is offered to all compatible parents in one
move, and a nonroot node may be removed by reparsing all its parents using
existing alternatives. Exact projection and AST-property checks gate
accepted moves. `converse_dictionary_search.py` matches existing grammar
phrases against fine-atom expansions, then runs oriented, rank-bounded
interval dynamic programming on the selected semantic spelling. This is a
heuristic decomposition; it does not solve the joint problem exhaustively.

## Artifact conventions

`permutation_seeds/` and `anchored_seeds/` each contain three independent
inputs, starting grammars, resulting grammars and complete search logs.
The other search folders contain summaries and selected best witnesses.
`search_summary.json` records numerical results in machine-readable form.
`MANIFEST.sha256` pins all files in this supplement except itself.

Inherited abstract JSON files contain the legacy field `framework_states:118`.
This field predates the separately verified one-state scanner reduction and
must not be used to assert a realized state count. The routed245 baseline
uses 117 fixed framework states plus its 128 grammar states. Every search
candidate in this folder is explicitly abstract; no binary table was built
from these tied or worse candidates.
