# Historical and ancillary verification coverage supplement

This supplements the frozen main checker preflight; it does not replace its source-only scope. All commands below run from a separate copied package with assertions enabled and explicit fresh output paths. The four historical entry points were read in full by this reviewer; the four architecture/propositional investigations have the separate complete source review in `machine-review/ancillary-review.json`. No supplied program was executed by this reviewer.

The four historical checks omitted from the main final-machine driver are:

```sh
python3 -B code/state_reduction/safe_lifetime_witness.py \
  --program reference/source/Prog254.v --dag reference/source/Dag254.v \
  --output /absolute/fresh/safe-lifetime.json

python3 -B code/state_reduction/map_reassociated_leaf.py \
  results/state_reduction/gradient-repaired.json \
  1110100100101011101010101110000000 --inputs reference/grammar \
  --metadata reference/interval/instruction-metadata.json \
  --output /absolute/fresh/gradient-leaf.json

python3 -B code/state_reduction/check_route_grammar.py \
  results/state_reduction/gradient-repaired.json --inputs reference/grammar \
  --bootstrap-lock inputs/state_reduction/bootstrap-lock54.txt \
  --output /absolute/fresh/zero7-grammar.json

python3 -B code/state_reduction/check_route_grammar.py \
  results/state_reduction/gradient-zero6-k129.json --inputs reference/grammar \
  --bootstrap-lock inputs/state_reduction/bootstrap-lock54.txt \
  --output /absolute/fresh/zero6-k129-grammar.json
```

`safe_lifetime_witness.py` uses both a path interpreter and a structured control-stack interpreter on two explicit theorem-safe register roots. The delivered results reach nine pairwise-distinct live values in 13,517 source instructions per interpreter and root; the source bounds each trace at two million instructions. This obstructs only direct pointwise register aliasing on every admitted safe root. It gives neither blank-run reachability nor a Turing-machine state lower bound, and does not rule out packing, recomputation or different algorithms. The source writes only its named JSON report.

`map_reassociated_leaf.py` fully expands the old and historical revised ASTs, checks all 6,460 ordered operation/argument pairs equal, and maps selected leaf 2,337 to the old path and its two interval fixtures. It establishes static leaf correspondence. Dynamic register-program equivalence needs the separate bisimulation; a failed or unfinished historical runtime replay is not strengthened by this leaf map.

The two grammar audits are positive abstract controls. The first has 128 rules, maximum zero run 7 and depth 49; the second has 129 rules, maximum zero run 6 and depth 49. Neither is the final 128-rule, zero-run-6, depth-51 candidate. Both audits use the retained 118-framework-role accounting and therefore report abstract totals 246 and 247 respectively; these totals do not include the final candidate's scanner shortening. They test all 22 inherited routing projections and 54 bootstrap projections, terminal orientation, all-rule reachability and source AST properties. They do not execute or certify a complete binary machine. The historical unsuccessful seven-zero verification remains a failed proof obligation/bounded unresolved test, not a proved behavioral inequivalence.

Four further substantive investigations are already covered by the other reviewer's `machine-review/ancillary-review.json` and root's separate `fresh-aux/replay.json`. The latter currently records all four jobs PASS; this supplement cites that root-owned report without claiming to have independently replayed them:

| Entry point | Exact requested mode | Limited conclusion |
|---|---|---|
| `research/architecture/verify_permutation_selectors.py` | default | All 40,320 axiom-row orders and 322,560 selector cases in a finite symbolic stack model; a separate ordinary derivation argument gives the intended witness translation. No binary compiler theorem. |
| `research/architecture/verify_semantic_resegmentation.py` | `--write-report /absolute/fresh/semantic.json` | Equal expansion of 702-call and 533-call AX words to 1,270 finest closed tokens; 533 is optimal only for the fixed 44-atom vocabulary. Its 147-rule seed does not improve the existing 127-rule grammar. |
| `research/architecture/verify_affine_resources.py` | `--recompute --write-report /absolute/fresh/affine.json` | Regenerates 12 finite-field affine closures for primes 2,3,5,7, checks resource fibers and six exclusions. The interpretation is the original source/Prefix246 resource model, not a new invariant for the reassociated 245 paths. Abstract leastness does not imply concrete reachability. |
| `research/propositional/check_propositional_obstructions.py` | default | Two finite three-valued matrix obstructions for exactly the stated restricted propositional bases; no quantifier/membership/CP/GIC model and no failure of equiconsistency with ZFC. |

The permutation script overwrites its own `research/architecture/results/permutation_selector_results.json`; therefore it must run on the copy. The other two architecture checks use the named fresh report, and the propositional checker prints to stdout. None of these four investigations is a premise of the final candidate's unchanged axiom order and logical theory.

Discovery executables (`anneal_routes*`, `repair_scanner_grammar.py`, resource-merge search and associated generators) are outside substantive certificate replay. Their recorded proposal counts are time-bounded heuristic discovery, not exhaustive search counts or state lower bounds. Bootstrap-lock generation, source-table rendering without `--check`, and PDF rebuilding are also separate from the verification suite.

Exact historical source/input pins and the four ready commands are frozen in `historical-checks-preflight.json`. The portable `replay_164.py` reproduces the main driver's requested modes; the eight historical/ancillary investigations above remain explicit separate commands rather than silently expanding its default scope.
