# Exact-word grammar search on the revised complete layout

The bounded search **matches 268 working states and does not improve it**.
It preserves source 19's reviewed C2/G1/outer-order16/tree1 macro word exactly,
including GEN, all eight original equality-bearing logical rows in their
original order and parameter maps, original rho6, base-four coding, both
atomic vacuity arms, parameter acquisition, gates and cleanup. The bridge from
the original source to this revised conjunction layout is the ordinary
propositional/quantifier transport described in the source-19 intake. The new
operation certificate concerns exact execution of the revised word; it does
not replace that source bridge or prove a binary compiler/ZFC endpoint.

`layout_grammar_experiment.py` compares overlap-safe and inherited Re-Pair on
four tokenizations of exactly the same 186 primitive macro calls:

| Tokenization | Tokens | Minimum safe states | Minimum legacy states |
|---|---:|---:|---:|
| Original implication alias retained |185|268|268|
| Primitive macros |186|269|270|
| Greedy existing closed helpers, span at most four |95|279|279|
| Minimum-token parse with existing closed helpers |79|280|280|

The 79- and 95-token forms retain and charge the complete dependency subgraphs
of their existing helpers. A shorter token list is therefore not a state-cost
claim. Every tokenization expands to the delivered revised word, each token
passes the closed break/continue check, and every generated grammar expands
back to its tokenization. No binding operation, schema row, or formula code
is changed. An independent read-only review checked the dependency retention,
interner, root replacement and word-preservation reasoning.

The main comparison uses seeds 0–999 and frequency exponents 1, 2, 4, 8, 16 on
all four tokenizations: 40,000 DAG evaluations. An additional comparison uses
seeds 1000–1999 and exponents 3, 6, 12, 24 on the 185/186-token forms: another
16,000 evaluations. Across the 28,000 paired samples, 15,381 grammars differ
and 8,244 total state counts differ: safe counting wins 4,656 times, legacy
counting 3,588. The correction changes the sampled distribution, without
pointwise monotonicity or a better minimum. The two accepted runs took 160.8
seconds summed in the recorded environment. These are bounded results, not
lower bounds. The known seed 341 / exponent 4 268-state control is retained as an
extra baseline outside the reported trial counts.

## Whole-machine cost and a regression control

Wade's framework cost is **not uniformly 62 states**. In `TMBuilder.generate`,
`max_zeros` is the maximum number of consecutive first-child edges, and it
controls the number of `4.dispatch.*` states. With these unchanged register
and read-sensitive control leaves, the framework has 55 other states plus
that dispatcher depth. The driver checks that leaf signature for every DAG,
charges this whole cost for every candidate, and actually compiles and
re-extracts a representative of every encountered depth. Depths 6–10 give
framework sizes 61–65. The final winner is also compiled and checked directly.

The explicit regression is coarse legacy seed 445 / exponent 4: its 206 decision
nodes have depth 8 and require **63 framework states, hence 269 total**. Adding
62 would incorrectly report a 268-state tie. The initial comparison using
that fixed-overhead assumption was rejected by its final compiler check;
it is not part of the accepted evidence. This finding also corrected the
reviewer's source-18 PSC histogram calculation: compiling all 1,024 PSC
controls reproduces the delivered histogram exactly once dispatcher cost is
included. No defect in that delivered histogram remains alleged.

## Reproducible winner and verification scope

The selected winner is coarse legacy seed 130 / exponent 4, with 27 grammar
productions and 75 residual tokens. Actual backend compilation gives
**206 decision +62 framework =268 working states**. Its named source has
535 rows; the sole missing `1.inc/read1` row is totalized to write1/R/halt,
giving 536 rows, start 0 and terminal 268. This adds a final move under the
undefined-row-halting convention and preserves tape contents; it is not a
complete interpreter theorem. The total-table SHA-256 is
`07b7aa8db8f9fa0440f67db829fad116139409f182a52a3d0a5d92e867247b4a`.

A freshly derived 217-node reference has exactly the same node table as the
reviewed source-19 revised reference. The independent source-08 string/integer
path engine verifies 4,533 operation pairs against the 206-node winner:
2,601 increments, 1,931 decrement tests, one halt, including both decrement
successors. Both unfold to 6,460 operation/control sites; contracted control
chains have length at most four. Six certificate corruptions are rejected.
This is finite executable RM evidence, not a checked Lean instantiation or a
binary-TM theorem.

The fast recipe regenerates the same seven program artifacts byte-for-byte:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/layout_grammar_experiment.py \
  --output /tmp/zfc-layout-grammar-fixed --start-seed 130 --seeds 1 \
  --exponents 4 --lanes coarse
```

The full main run uses default seed/exponent/lane options and an outside
`--output`. The additional run uses `--start-seed 1000 --seeds 1000
--exponents 3 6 12 24 --lanes coarse primitive`. The driver refuses output
inside the checkout and assertion-disabled execution. All tables, DAGs,
grammars, maps and certificates remain outside the checkout because the
268-state baseline was not improved. `layout-grammar-safe-results.json`
records the two complete histograms, actual framework checks, winner,
certificate/mutations, fast replay and conservative table audit.

The auditor finds every working state graph-reachable, 268 singleton exact
step-bisimulation classes after 12 rounds, no startup reuse, and no safe
radius 4 / 64-step merge. Its 11 regression tests pass. No Lean or Coq build, new
literal-table installation, new calibration theorem or state record is
claimed.

The unchanged source-08 grammar/path tools, source-19 layout functions,
Mira-Cult/Jeff program data and Andrew James Wade MIT-0 backend retain their
existing attribution and licenses. Backend/data pin:
`297ab8df7e5de329605c3875b4934643b371a5e3`.

Final self-review on 16 October 2026 reran only the fast recipe. All seven
program artifacts matched the full search byte-for-byte; the independent
certificate and six rejection controls passed. Saved histogram totals and
every recorded dispatcher/framework cost were checked without repeating the
full sweeps. The corresponding JSON records the scratch output and result.
