# Grammar reassociation searches for a 193-state candidate

These are two completed, unsuccessful stochastic searches around the new
PA194AX11GH and PA194AX11GHS grammars. Both started at a penalized effective
reader score of **60**, sought **59 with zero penalty**, and finished at 60
without nominating a smaller machine. This is a finite search result, not a
lower bound.

## Scope and score

`search.cpp` replaces a shared binary subtree by a left or right reassociation
throughout the grammar, preserving its ordered macro word. Identical pairs are
interned. `screen.cpp` prices history-dependent reader folds and, near the
frontier, checks that the chosen disjoint folds work simultaneously. The
parameter-permutation mutations in this retained search are disabled
(`if(false)`). Structural scanner/height penalties guide exploration; they are
not proof certificates. The search does not exhaust the reassociation space.

Both supplied template files have **134 fixed controls** and one initial
grammar. For GHS this fixed part already includes the separately verified
`41 -> 330` controller fold. The effective reader score is the number of
interned AX reader controls minus the compatible reader folds. Thus 60 gives
`134 + 60 = 194` working controls; 59 is the nomination threshold for
`134 + 59 = 193`. A hypothetical hit would still require complete source,
simultaneous-fold, blank-startup, and logical validation.

| Family | PRNG seed | Time allowance | Iterations | Accepted mutations | Hits | Best penalized score |
|---|---:|---:|---:|---:|---:|---:|
| PA194AX11GH | 202611140371 | 300 s | 4,107,048 | 217,940 | 0 | 60 |
| PA194AX11GHS | 202611140368 | 300 s | 4,201,305 | 224,084 | 0 | 60 |

The observed durations were 300.005 and 300.006 seconds. `summary.json` and the
complete `*.log` files record these runs. Both CSVs contain only their header,
because no hit occurred. Each run saved 30 final `*.seedN.grammar.json` pool
entries: these are retained grammars, **not 30 independent PRNG-seeded runs**.

## Exact reproduction commands

Run from this directory after extracting the delivered archive. A GNU C++17
toolchain is sufficient. All inputs are bundled; neither network access nor a
repository checkout is needed. The output prefixes below preserve the recorded
results.

```sh
mkdir -p replay
g++ -std=c++17 -O3 search.cpp -o replay/grammar_search
replay/grammar_search PA194AX11GH.templates.txt leaf_attrs.txt replay/AX11GH_run 300 202611140371 > replay/AX11GH_run.log
replay/grammar_search PA194AX11GHS.templates.txt leaf_attrs.txt replay/AX11GHS_run 300 202611140368 > replay/AX11GHS_run.log
```

The positional arguments are `templates leaf_attributes output_prefix seconds
seed`. The output directory must already exist. `search.cpp` includes its
neighbor `screen.cpp` with the standalone screen main disabled; compile
`search.cpp`, not both translation units together. The standalone screen's
historical thresholds are not the nomination criterion of these runs.

Wall-clock stopping means that machine speed, scheduling, compiler, and library
implementation can change the number of iterations and final retained pool.
The commands reproduce the inputs, PRNG seeds, search method, and time limits;
they do not promise byte-identical timed logs. The recorded summaries remain
the evidence for the completed runs reported here.

## Provenance and offline portability

`search.cpp`, `screen.cpp`, and `leaf_attrs.txt` are **unchanged byte-for-byte
copies** of the corresponding `research/grammar/` members of the retained
`../../references/pa194_ax11g_research_2026-11-14.zip`, under its
`pa194_ax11g_research_2026-11-14/` wrapper. That archive is the attributed AX11G
research input and retains its upstream provenance and license notices. The
new template inputs and the two runs in this directory concern AX11GH/GHS;
they do not claim authorship of the inherited search algorithms.

`PROVENANCE.json` records the exact archive member paths and SHA-256 values.
The templates embed their fixed transition rows and grammar records; no
external paths are stored in them. All search file access uses the arguments
above, and the only source include is the local `screen.cpp`. No path adjustment
is required for independent offline use.
