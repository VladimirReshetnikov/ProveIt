# Three-congruence fusion: a reproducible 271-state control

This experiment replaces three native equality/membership axiom families by
one interderivable three-parameter family. It saves six calls in the selected
axiom-emission word (186 to 180). The best tested complete compilation has
**271 working states**, comprising 209 decision nodes and 62 framework states.
This is larger than the previously recorded 268-state complete-logic control
and the public 253-state machine. It is a useful source transformation and
negative compiler result, **not a new state record**.

## Quick offline verification

From the root of this artifact package, run:

```sh
python3 -B code/fusion/verify.py
```

Python 3.10 or newer and its standard library suffice. No ProveIt checkout,
network connection, Coq, Lean, or external Python packages are needed. The
command writes its JSON result to standard output. `-B` avoids cache files;
do not use `-O`, because the unchanged upstream path interpreter uses
assertions. The verifier explicitly rejects optimized Python mode.

The script also works when invoked by its absolute path from another working
directory. `--root /path/to/package` can select the data location explicitly.
The package-root file `data/fusion/quick_verification.json` records a checked
run. The same command was also verified from a temporary standalone copy with
Python's isolated mode (`python3 -I -B`); the copy contained only the three
fusion directories, with no checkout beside it.

The quick verification checks:

1. SHA-256 integrity of the supplied data, machine table, and vendored helpers.
2. A 4,549-pair register-machine relation between the **new uncompressed fused
   reference** (284 DAG nodes) and its compressed candidate (209 nodes).
   Every pair has the same operation and register; both decrement exits match;
   all successor indices and reachability of all records are checked.
3. All 418 candidate decision edges, read independently from the delivered
   numeric TM table, including read-sensitive break/continue, written symbol,
   direction, and target state.
4. Byte-for-byte regeneration of the complete 542-row binary table, including
   its 62 framework states, using the included Wade generator.
5. Rejection of five corrupted certificates and three corrupted decision rows.

The RM certificate compares two implementations of the new fused program. It
does **not** compare the fused program with the original axiom emitter: that
change alters the theorem stack and requires the logical argument below.
Regeneration establishes reproducibility of a finite table. It does not prove
that the binary framework simulates its register specification on all relevant
configurations, nor the internal ZFC theorem relating this particular machine
to consistency. Those endpoints remain open for this control.

## Machine convention

`machines/fusion/fused271.tm` uses one tape, symbols `0` and `1`, blank symbol
`0`, and initial state `0`. Working states are numbered `0` through `270`;
state `271` halts and has no outgoing rows. Every working state has one row
for each read symbol. A row is `state read write direction next_state`.

The upstream framework has one missing row, the read-1 transition of its
named state `1.inc`. The source-19 normalizer replaces this immediate undefined
halt by `write 1; move right; enter halt`. This preserves the halting outcome
and charges no extra working state. The verifier checks that this is the only
totalized row. The convention is explicit because different machine formats
count an undefined transition differently.

The table SHA-256 is:

```text
ca2d23fe6880e4a1ca6522e5b7ed4fc6d4c07249c564059a8f1a066407efdc7b
```

## Logical replacement

Write `E` for native equality and `R` for membership. The old families are

```text
rho7(a,b,c) = E(c,a) -> (E(c,b) -> E(a,b))
rho5(a,b,c) = E(c,a) -> (R(c,b) -> R(a,b))
rho3(a,b,c) = E(a,b) -> (R(c,a) -> R(c,b)).
```

Replace them by all instances of

```text
J(a,b,c) = E(a,b) ->
          (((E(a,c) -> E(b,c)) AND (R(a,c) -> R(b,c)))
           AND (R(c,a) -> R(c,b))).
```

Projection of `J(c,a,b)` gives `rho7(a,b,c)` and `rho5(a,b,c)`;
projection of `J(a,b,c)` gives `rho3(a,b,c)`. Conversely,
`rho7(b,c,a)`, `rho5(b,c,a)`, and `rho3(a,b,c)` have the same antecedent
`E(a,b)` and conjoin to `J(a,b,c)`. Replacing each axiom occurrence by these
finite derivations, while preserving MP and GEN, gives both theorem inclusions.
The parameter relabelings select available axiom-family instances; no missing
equality-congruence or variable-substitution theorem is assumed.

All other original logical rows, both gated atomic vacuity families, and GEN
are retained. The implementation uses the existing relative conjunction
`AND(A,B) = ((A -> (B -> F)) -> F)`, where `F = Rel(0,0)`. The retained
propositional row and explosion theorem `F -> A` justify these classical
conjunction inferences. A truth-table argument with arbitrary true `F` would
not justify this replacement.

This is elementary propositional factoring, without a claim of historical
novelty in logic. Its experimental role is to alter the complete logical
emission family, while using exactly the old three scalar parameter roles.
The retained nonlogical bundle is source 19's already existing complete C/G
conjunction layout (`C=2, G=1, outer_order=16, tree=1`).

## Reproduce the full search

The full driver deliberately reuses the pinned ProveIt research infrastructure;
it is separate from the self-contained quick verifier. Supply a checkout at
commit `61e77836565f63582561f54745f633d50efd9c7d` that includes
`Computability/BusyBeaver/Research/ZFC`, the closure-kernel report code, and
`lib/jeff-busy-beaver-zfc254`.

From the artifact package root:

```sh
python3 -B code/fusion/search.py \
  --repo /path/to/ProveIt \
  --output /tmp/fusion-search \
  --seeds 32 --positions 3 \
  --lanes coarse existing_short existing_minimum \
  --exponents 2 4 8
```

This performs 20,736 recipe evaluations: six scalar permutations, six factor
permutations, two conjunction associations, one insertion position, three
tokenizations, three weighting exponents, and 32 random seeds. It is a finite
grid, not a global search or optimality claim. The expected best result is
271 states. Python's random implementation or changes in the helper sources
could change a search trajectory, so the frozen recipe and finite certificates
are also supplied.

The best recipe uses script variables `['b','c','a']`, factor order `[0,1,2]`,
grouping `0`, insertion position `3`, the `coarse` lane, exponent `4`, and seed
`29`. The script's builder uses a `c,a,b` orientation; this recipe emits the
displayed `J(a,b,c)`. The exact grammar, residual word, macro word, and recipe
are in `data/fusion/recipe.json`. Aggregate results and the state histogram
are in `data/fusion/search_results.json`.

The search driver also checks the full charged framework for every encountered
dispatcher depth, reconstructs the emitted formulas symbolically, retains the
original framework leaf contracts, constructs the RM certificate, and verifies
the actual compiled decision edges. To compare a repeated search with the
frozen candidate:

```sh
cmp /tmp/fusion-search/candidate.tm machines/fusion/fused271.tm
cmp /tmp/fusion-search/candidate_dag.json data/fusion/candidate_dag.json
cmp /tmp/fusion-search/reference_dag.json data/fusion/reference_dag.json
cmp /tmp/fusion-search/rm_certificate.json data/fusion/rm_certificate.json
```

Elapsed time in `results.json` is run-specific. It is not expected to compare
byte-for-byte; the machine, DAGs, certificate, labels, and recipe are.

## Files

| Package-root path | Purpose |
|---|---|
| `code/fusion/verify.py` | Offline finite verifier and full table regeneration |
| `code/fusion/search.py` | Full research search, with explicit `--repo` |
| `code/fusion/vendor/` | Four unchanged upstream Python helpers and license notices |
| `code/fusion/PROVENANCE.md` | Exact source pins, paths, attribution, licensing scope |
| `data/fusion/reference_dag.json` | Uncompressed new fused register program |
| `data/fusion/candidate_dag.json` | Selected compressed fused register program |
| `data/fusion/rm_certificate.json` | Operation-preserving finite relation |
| `data/fusion/recipe.json` | Frozen winning grammar and search parameters |
| `data/fusion/labels.json` | Named-to-numeric state mapping, including halt |
| `data/fusion/search_results.json` | Aggregate search results and limits |
| `data/fusion/quick_verification.json` | Saved successful offline verification |
| `data/fusion/reproduction_check.json` | Standalone-copy and full-search reproduction record |
| `data/fusion/sha256.json` | Data/helper/table integrity manifest |
| `machines/fusion/fused271.tm` | Complete normalized binary transition table |

The certificate is the only roughly 1.4 MB file. The larger search workspace,
duplicated named transition table, and earlier 272-state candidate are omitted.
