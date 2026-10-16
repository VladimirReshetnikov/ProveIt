# Batch 148: full-grammar engineering review

Verdict: **accept as a reproducible, source-preserving compiler comparison**.
All advertised engineering replay and certificate checks pass, including the
full 4,000-choice search. No engineering flaw or inflated state claim found.
The output is **270 named working states with 539 partial rows**, not a new
total numbered machine or a new state record. Prior source 08 already reaches
269 in the same backend. The original equality/theory frontend is preserved;
binary simulation and the changed instruction-pointer/initializer interface
remain the missing proof layer.

Arrival `5e5603303d`, untouched extraction
`/tmp/zfc-intake-148-51452zxy/original/zfc_machine_research`.
All execution used `/tmp/zfc-review148-engineering-l4tesx_o/package` and output
beside it. Read the complete engineering driver, inherited grammar and
independent certificate checker, engineering README/notices, generated
artifacts and experiment-results section. Other theory, ground-clause checker,
PA and PDF reviews belong to root's separate assignments. No repository edit,
checksum audit, Coq or Lean build was performed.

## Source and functionality

The report audits ProveIt through
`47f3a3602946dfe48803a91a910c646e74637ac8`. The packaged minimal helper inputs
originate at `17d0f2eaa650901cda59764dfcc4661c199e49c8`; the upstream program,
symbolic spec and Wade backend are attributed to
`297ab8df7e5de329605c3875b4934643b371a5e3`. Weighted Re-Pair and its independent
RM checker are inherited source-08 code, introduced with the one-schema
archive in `39409c8c921cccdbd6162c8767c84cfb7df65df1`. Their attribution and
license boundaries are retained; the driver claims no ownership of the backend
or original verified machine.

The new driver expands the **full original AX** into 186 macro calls and checks
it against a second expansion of the imported source DAG. Its symbolic contract
matches GEN and **all eight original logical rows**, the complete old CP/GIC
bundle, both equality/membership vacuity arms, parameter reads and cleanup
gates. Original four-tag coding and relative-F interface remain unchanged.
All 17 macro roots actually used in this word have zero escaping control levels.
This is not one of the equality-free engines defeated by the finite-sort model.

Only binary bracketing and sharing of that identical word change. The driver
retains all non-AX DAG definitions verbatim, interns productions, checks a
register-operation correspondence, compiles the transformed DAG and re-extracts
every emitted decision edge. It proves no changed theory/calculus equivalence
because none is proposed here. It also does not prove that the public Wade
binary interpreter and its blank boot implement the register specification.

The winning recipe is exponent4/seed287: 26 productions, residual length78,
**219→208 decision nodes**. The unchanged public framework contributes62
physical states, including initialization, yielding270 working names. The
actual named table has539 rows and sole missing pair `1.inc/read1`; its only
external target is `halt`, and its start is `0.boot.A`.
Named-table SHA-256:
`49013eb2d701779f12537b37aa2e553f14a063b8ec0a3eee690534aa13f6700e`.
There is no delivered total numbered table. Under the standard inherited
missing-transition-halting convention it could be totalized with one terminal
move, preserving270 working states; that is not a newly supplied endpoint.

## Independent certificate audit

The certificate compares the **actual original219-node DAG** with candidate208,
not a newly invented plain-comb frontend. Each unfolds to6,460 sites. The
independent string/integer path checker imports neither generator nor backend.
It validates the entry, same operation and register index at every related
site, **both** zero and positive decrement successors, unique records,
reachability of all records and termination of contracted control-only paths.

The positive result has4,533 pairs:2,601 increment,1,931 decrement and1 halt.
Maximum contracted control length is4 in both programs. This supports the
ordinary theorem that equal register vectors undergo equal operations and
agree on finite halting. It neither establishes the binary TM simulation nor
instantiates the current generic Lean register theorem.

The independent checker passes on the supplied artifact. Six mutations were
rejected: wrong operation, missing pair, duplicate pair, wrong zero successor,
wrong positive successor and wrong initial pair. These checks run with only
source-digest assertions bypassed in memory; all semantic assertions remain
enabled. Records: `independent-rm-check.json`, `certificate-mutations.json`.

## Full replay

From the scratch package root:

```sh
uv run --no-project python ../run_without_hash_enforcement.py \
  code/search_full_grammar.py --archive . --output ../full-search --seeds 1000

uv run --no-project python ../run_without_hash_enforcement.py \
  vendor/one_schema_machine/verify_rm_certificate.py \
  --source vendor/ProveIt/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v \
  --candidate data/full_grammar/candidate_dag.json \
  --certificate data/full_grammar/rm_bisimulation.json
```

The scratch runner transforms only digest-enforcement comparisons in memory;
it does not edit delivered code or disable assertions globally. Actual source
structure, word equality, macro scope, instruction paths, operation relations,
decoder actions and state counts remain checked. No checksum manifest was run.

The complete search covers seeds0–999 at each exponent1,2,4,8. All four exact
histograms reproduce (each sums to1,000); their decision minima are212,209,208,208.
The seven minimum208 samples at exponent4 and five at exponent8 are a bounded
sample result, not a lower bound. The selected tie-break recipe and all six
generated artifacts are **byte-identical** to delivery:

- `results.json`, including its entire symbolic contract and all histograms;
- `baseline_dag.json`, `candidate_dag.json` and `grammar.json`;
- `rm_bisimulation.json` and the actual named table.

Records: `full-search.log`, `comparison.json`, `full-search/` and the joined
`engineering-review.json`. The full replay already regenerates the fixed
winner and certificate; it does not depend on a live repository or network.

## Comparison with prior269 and next useful work

The prior source-08 **269=207+62** comparison is reproduced independently by
applying its seed341/exponent4 recipe to its original185-token coarser word.
Expanding that coarser word gives exactly the new driver's186-token word.
The two grammar searches therefore optimize different tokenizations of the
same full semantic macro sequence. This explains why the present search is
a useful independent comparison without improving the earlier result.
Record: `prior269-comparison.json`.

The new driver uses the inherited weighted Re-Pair, including its conservative
early stop when a chosen equal-token pair has fewer than two nonoverlapping
replacements. Batch147's overlap-safe pair counting is a concrete optimizer
component to try on this **complete** frontend; the current bounded histograms
remain correct for the algorithm actually executed. This observation is not
a claim that the change will lower270 or269.

The most reusable proof task is to port the finite operation-certificate
checker and control-path contraction interface, then instantiate
`RegisterBisimulation.halts_from_any_registers`. The expensive remaining
machine task is the actual public backend/blank initialization proof, or
an equally certified smaller backend. Replacing62 arithmetically by another
interpreter's state count cannot yield a new machine. No endpoint can be
inferred merely from retaining a complete source theory, finite certificates,
or the hash of a named partial table.
