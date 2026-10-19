# Source compression modulo independent register operations

This is a reproducible source-level investigation of the retained 245-state
candidate. It provides two exact dictionary-parsing results and an exact
128-rule optimum for one explicitly serialized finite grammar universe. It
does not contain a new machine with fewer than 245 states.

## Results and their scope

The AX constructor expands to 1,270 closed fine atoms, using 20 of the 30 fine
atom types present in the full source. There are 44 inherited coarse atoms.
Each atom's footprint is the set of registers mentioned by any of its
increments or decrements. The order of occurrences sharing a register is
preserved; occurrences with disjoint footprints may commute.

The resulting occurrence partial order has 1,669 order ideals and 2,068
single-occurrence edges. The largest level contains four ideals, and at most
three atom occurrences are enabled at once. The number of distinct legal words
is exactly

```
9388163967439862234522569223429454154625811663326254181648582645340406446607564800
```

This is approximately `9.388e81`, or `2^272.307`. The number is counted by an
integer dynamic program; the experiment does not enumerate the words one by
one.

| Optimization problem | Exact result | Evidence |
|---|---:|---|
| Minimum number of 44 coarse-atom dictionary calls, across every allowed ordering | 533 | Complete ideal graph, integer distance potentials, matching word |
| Minimum calls when 51 fixed non-AX grammar words are also free dictionary entries | 108 | Same, with 95 dictionary entries |
| Minimum selected grammar rules in the serialized length-20 factor universe, retaining those 51 fixed rules | 128 = 51 + 77 | Exact integer LP dual plus an independently checked 128-rule positive control |
| Feasibility of 127 rules in the enlarged length-40 factor universe | Solver reported infeasible | Retained HiGHS report; no independently replayed dual certificate for this larger model |

The first two minima equal the minima for the original fixed order. Thus
allowing every disjoint-register reordering cannot reduce these particular
dictionary-call metrics. This is stronger than trying a sample of reordered
source words. The third result is a minimum for the frozen finite model only;
it is not a lower bound for unrestricted grammars or Turing machines.

The 128-rule positive control expands to exactly the original sequence of
1,270 fine atoms, expressed with 682 coarse-atom calls. It has full source-tree
properties `(leading zeros, maximum zero run, maximum depth) = (3,6,51)`.
Dictionary call count and number of shared grammar rules are different
objectives; the 533-call dictionary optimum need not yield the smallest shared
grammar.

## Replaying the certificates

From this folder, run:

```sh
python verify_trace_results.py --package pinned_inputs --reordering baseline_trace.json --model trace_lp20.lp_model.json.gz --certificate trace_lp20.lp_certificate.json --positive-control trace128.json --output verification_replay.json
```

Only Python's standard library is needed. The verifier checks the source
projections, independently reconstructs the entire ideal graph using register
queues, recounts all legal words, checks both distance certificates, rebuilds
the LP constraints from the grammar model, evaluates the lower bound with
integer arithmetic, and verifies that the positive control belongs to that
same model. It checks all 128 source grammar productions and their inherited
terminal orientation and zero-run constraints. It does not execute a TM or a
proof assistant.

For the slower additional audit of production completeness within the listed
semantic words, run:

```sh
python verify_trace_results.py --package pinned_inputs --model trace_lp20.lp_model.json.gz --certificate trace_lp20.lp_certificate.json --positive-control trace128.json --complete-productions --output verification_complete_replay.json
```

This enumerates every order-ideal split of every listed word, establishing that
the serialized model contains exactly the allowed productions over its
post-pruning vocabulary. It does not establish a minimum beyond that explicitly
listed vocabulary. The lower bound is already exact without this extra check;
the additional check establishes the asserted production completeness of the
model, rather than changing its optimum.

`verification.json` and `verification_complete.json` record the original
successful replays. These records are evidence of past execution; the commands
above perform the checks again.

## Why the source reorderings are sound

The inherited source is a structured register program. Its control-bound
calculation is recomputed for every atom: a closed atom has no break or continue
that escapes the atom. The AX atoms used here are also halt-free. Their only
state observations or changes are increments and decrements on their listed
registers; a zero test counts as access to its register.

Two such atoms with disjoint footprints commute as deterministic partial
register transformations. If both terminate, each sees the same input registers
and they produce the same combined final state in either order. If one
diverges, the other cannot change the registers governing that divergence, so
both sequential orders diverge. Closed control prevents either atom from
altering the other's surrounding continuation.

For each register, form the chain of occurrences mentioning it. The union of
these chains generates the occurrence partial order. Any two linear extensions
are connected by adjacent swaps of incomparable occurrences. Two incomparable
occurrences cannot share a register, so each swap has the commuting property
just proved. This establishes equality of the whole AX partial transformation
and preservation of termination for every admitted word.

The scripts check the syntactic hypotheses and all finite certificates. This
mathematical commutation argument is not advertised as a new kernel-checked
formalization. It does not license arbitrary instruction motion, escaping
control operations, or source changes justified only by short simulations.

## Dictionary lower-bound certificates

The ideal automaton reads one enabled atom per edge. A dictionary token forms
an edge from ideal `u` to ideal `v` whenever its fine word labels a path between
them. All tokens have unit cost.

Each certificate supplies an integer potential `d` at every ideal, with
`d(final)=0`, and checks

\[
d(u)\le 1+d(v)
\]

for every dictionary edge. Telescoping along any complete parse gives
`number of calls >= d(initial)`. A supplied complete parse attains equality.
The independent verifier checks 2,198 such inequalities for the coarse
dictionary and 3,524 for the fixed-core dictionary. It also checks each chosen
token's dictionary membership and fine expansion.

## The finite semantic grammar model

A semantic word is the canonical representative of an equivalence class under
the commuting swaps. Canonicalization preserves the ordered projection onto
each register's occurrence chain. A production `w -> a b` is allowed when the
concatenation has the same register projections as `w`. Thus a production may
choose a different legal source ordering, rather than merely a different
bracketing of one fixed string.

The producer builds its vocabulary from:

1. the 44 inherited coarse atoms and 51 fixed non-AX grammar words, with their
   permitted entry orientations and source-tree properties;
2. semantic words of the inherited AX-private grammar and the complete AX
   target word;
3. all semantic factors of length at most 20 between ideal pairs that occur for
   at least two distinct `(start ideal, end ideal)` pairs.

The third count refers to ideal pairs. It need not mean two disjoint textual
occurrences. The producer then lists every ideal split whose two children are
available, and repeatedly removes words with no remaining production. The
final model is serialized in `trace_lp20.lp_model.json.gz`; its word list is the
authoritative finite universe for the certified result. The compressed file's
uncompressed SHA-256 is recorded in the dual certificate.

The model has 2,816 charged semantic words, 22,227 possible productions,
27,859 variables, and 60,636 rows before a target cutoff. There is one selection
variable per charged word, one per production, and one leading-zero rank per
charged word. Selecting a word selects exactly one production and requires its
nonfree children. A selected production has parent rank at least one greater
than its left child's rank. Ranks are bounded by six; AX's leading rank is
bounded by its inherited value of five. Free dictionary words have their exact
inherited source properties. Terminal orientation restrictions are retained.

The restriction to one production per semantic word matters. The model does
not permit two separately charged implementations of the same semantic trace
with different internal structures. It also fixes the 51 non-AX rules, their
dictionary implementations, and the finite vocabulary. Changing any of these
restrictions requires a new model and certificate. State accounting of
`117 framework + grammar rules` belongs to the retained routing architecture;
this folder establishes source-grammar facts and does not re-prove a binary
machine endpoint or a blank-tape bootstrap.

## Exact integer LP certificate

The solver was used to discover dual multipliers. Its floating-point output is
not trusted by the verifier. For model rows with multipliers `lambda`, their
signs are checked against the corresponding lower or upper inequalities. Let
`r = c - A^T lambda`, where `c` is the objective and `l,u` are variable bounds.
Every feasible point satisfies

\[
c^\top x\ge\lambda^\top b+
\sum_j\min(r_jl_j,r_ju_j).
\]

The certificate scales all multipliers by the positive integer `10^9`. The
verifier reconstructs every integer constraint and evaluates this inequality
with exact integers, including every residual and finite variable bound. The
result is `77,000,000,000 / 1,000,000,000 = 77` private rules. There are 152
nonzero dual-row multipliers. Adding the fixed 51 rules gives 128, and the
positive control supplies the matching upper bound in the very same model.

## Reproducing the searches

The discovery scripts used Python 3.12.14, NumPy 2.3.5, SciPy 1.17.0, and SciPy's
bundled HiGHS. Optimizer versions can change the selected witness or dual
multipliers. Exact certificate replay does not need these packages.

First create an output directory:

```sh
mkdir reproduced
```

Regenerate the dictionary certificates:

```sh
python trace_dictionary.py --package pinned_inputs --output reproduced/dictionary.json
```

Regenerate a length-20 lower-bound certificate and the 127-rule infeasibility
query:

```sh
python trace_grammar_search.py --package pinned_inputs --length 20 --target 127 --seconds 120 --lp-certificate --output reproduced/trace20.json
```

For an infeasible query, the producer writes the report and LP certificate
files, but no feasible candidate JSON. For a positive control, change the
target:

```sh
python trace_grammar_search.py --package pinned_inputs --length 20 --target 128 --seconds 120 --output reproduced/positive128.json
```

The enlarged query is reproduced with `--length 40 --target 127`. Its retained
report has 4,786 words, 56,639 productions, 66,211 variables and 158,790 rows
including the target cutoff; HiGHS reported infeasible. This result has weaker
independent evidence than the certified length-20 result and is kept separate.

An additional experiment inserting prefix and suffix complements of the
inherited private words was interrupted during model generation. No solver
result or lower-bound conclusion exists for it. The `--seconds` option limits
the MIP solve, not universe generation; it is not a total wall-time bound.

## Files and provenance

`trace_dictionary.py` produces the dependency graph and exact dictionary
parses. `trace_grammar_search.py` produces semantic grammar models and solver
queries. `verify_trace_results.py` independently checks the retained witnesses
and exact bounds. The JSON files contain the complete certificates, not just
printed summaries.

`pinned_inputs/` contains only five small inherited inputs needed by these
scripts. Their individual hashes, the incoming archive hash, the producer
environment, and ProveIt commit
`6d69a46dce1de15397a9d2448dcc946d08c90327` are in `PROVENANCE.json`. The source
archive is `docs/incoming/zfc245-proof-20261018.zip`, SHA-256
`5a38b0e7475905584eabcb75912caa8d5f4149148e8c2a2439b2702a9de49ba1`.

The inherited construction is due to Jeff Ketchersid and collaborators and the
ProveIt research contributors. Its notices and the ProveIt and Andrew James
Wade licenses are retained here. The trace-model experiments, exact certificate
code, and this explanation are new work prepared on 18 October 2026. No new
licensing restrictions are asserted over that newly prepared material.
