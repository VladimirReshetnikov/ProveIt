# Overlap-safe grammar search on the complete frontend

The bounded comparison **matches 269 states and does not improve it**. It keeps
the original equality logic, CP/GIC theory, both atomic vacuity arms, four-tag
formula coding, parameter reads, gates and cleanup. This is the complete
original source frontend, distinct from the retired reduced equality-free
calculi. The public Wade binary compiler and blank initializer remain
unproved interfaces.

`full_grammar_experiment.py` compares overlap-safe Re-Pair with its inherited
version on two tokenizations: source 08's 185-token word of closed routines,
and the 186-token expansion into primitive macro roots. Their further
expansions are exactly the original macro word. The symbolic contract checks
GEN, all eight original logical rows, the nonlogical bundle, both vacuity
types and cleanup. Every token is closed under escaping break/continue.

For seeds 0–1999 and frequency exponents 1,2,4,8, each tokenization receives
8,000 safe and 8,000 legacy grammars: **32,000 DAG evaluations**. The table
entries now report minimum **whole-machine working-state costs**:

| Tokenization | Exponent | Safe | Legacy |
|---|---:|---:|---:|
| Coarse 185 |1|271|271|
| Coarse 185 |2|270|271|
| Coarse 185 |4|269|269|
| Coarse 185 |8|269|269|
| Expanded 186 |1|273|273|
| Expanded 186 |2|272|271|
| Expanded 186 |4|270|270|
| Expanded 186 |8|270|270|

The correction changes the sampled distribution. Overlapping equal-token
adjacencies can overstate the number of disjoint replacements, and the old
algorithm can stop while another reusable pair remains. Safe counting uses
actual disjoint occurrences; an explicit small negative control distinguishes
the algorithms. Across 16,000 paired samples, 13,473 grammars and 10,078 decision
counts differ. With whole-machine costs, 10,174 state counts differ: safe is
smaller 6,178 times, legacy 3,996. There is no pointwise cost monotonicity or
lower-bound claim.

## Dispatcher cost correction, 16 October 2026

The first comparison correctly reported **decision-node** histograms and
compiled its selected 269-state winner, but did not price dispatcher changes
for every other candidate. Its decision histograms reproduce exactly. They
are retained in `full-grammar-safe-results.json` under the dated historical
record; the original 269-state conclusion survives the correction.

The public `TMBuilder.generate` uses `max_zeros`, the maximum consecutive
first-child depth, to size `4.dispatch.*`. For these unchanged register and
read-sensitive control leaves, the full framework cost is **55 plus that
depth**, rather than uniformly 62. The driver checks the leaf signature for
every candidate, charges this cost, and actually compiles/re-extracts a
representative of each encountered depth. Depths 6–10 give frameworks 61–65.
The full 32,000-candidate corrected rerun took 122.4 seconds and still has
minimum 269. The separate revised-layout experiment records an explicit
206-node / depth 8 counterexample to blindly adding 62.

The corrected driver ranks both safe and legacy samples by total state cost.
Its selected tie is the attributed legacy coarse seed 341 / exponent 4:
**207 decision +62 framework =269 states**, with 26 productions and 77 residual
tokens. The previously selected safe seed 209 / exponent 4 remains a valid
269-state winner. Neither improves the prior result.

The current named source has 537 rows; its sole `1.inc/read1` missing row is
totalized with write1/R/halt to 538 rows, start 0, halt 269. This preserves tape
contents under undefined-row halting and adds a final move. The total-table
SHA-256 is `b40b90fdcf3a09475d3a2314dc3707bcf51a6302a3fdbba3c6afcde6ed1109de`.
The table is byte-identical to source 18's independently verified original 269
control; its conservative audit is reused on that explicit equality.

The independent source 08 checker verifies original 219 → candidate 207 at 4,533
operation pairs: 2,601 increments, 1,931 decrements and 1 halt, including both
decrement branches. Contracted control paths have length at most 4. Six
mutations are rejected, including wrong exits and entry. This supports
register-level halting equivalence from equal registers under the finite
path semantics; it is not a binary-interpreter theorem or internal ZFC
consistency endpoint.

The fast recipe regenerates the selected artifacts:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/full_grammar_experiment.py \
  --output /tmp/zfc-complete-cost-fixed --start-seed 341 --seeds 1 \
  --exponents 4 --compare-legacy
```

Use `--start-seed 0 --seeds 2000 --compare-legacy` with the default four
exponents for the full comparison. Outputs include exact grammars, both
DAGs, the certificate, independent verification/mutations, named and total
tables and relabelling. All artifacts remain outside the checkout because
this does not improve 269. The byte-identical table audit finds every state
graph-reachable, singleton exact-step classes after 12 rounds, no safe
radius 4 / 64-step merge, and 11 passing auditor regressions.

The unchanged attributed source 08 helpers live at
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/08-schema-machine-{rebracket_axioms,verify_rm_certificate}.py`.
The original program and Andrew James Wade MIT-0 backend come from immutable
upstream pin `297ab8df7e5de329605c3875b4934643b371a5e3`, retaining existing
Mira-Cult/Jeff/Wade attribution. No new vendor snapshot, Lean build or claimed
state record accompanies this experiment.

Final self-review on 16 October 2026 reran only the fast recipe. All seven
program artifacts matched the full search byte-for-byte; the independent
certificate and six rejection controls passed. Saved histogram totals and
every recorded dispatcher/framework cost were checked without repeating the
full sweeps. The corresponding JSON records the scratch output and result.
