# Reproduce the full equality-preserving grammar comparison

This directory contains the actual outputs of the report's bounded full-word
experiment. The necessary source driver and minimal pinned inputs are included,
so reproduction needs Python 3.10 or newer and no network, Git, Lean, or Coq.
Use ordinary Python without `-O`; the attributed checkers use assertions.

## Exact command

From the **root of this research archive**, run:

```sh
python -B code/search_full_grammar.py --archive . --output /tmp/zfc-full-grammar-270 --seeds 1000
```

This repeats 1,000 seeds for each of frequency exponents 1, 2, 4, and 8.
The selected minimum is exponent 4, seed 287. The `--archive .` argument
selects the packaged `vendor/ProveIt/` and `vendor/one_schema_machine/`
directories, preserving the relative path depth required by the unchanged
ProveIt loader. `-B` prevents bytecode files from appearing in those inputs.
Only the explicitly selected output directory is written by the generator.

The named table should have SHA-256:

```text
49013eb2d701779f12537b37aa2e553f14a063b8ec0a3eee690534aa13f6700e
```

The finite register-machine correspondence can be checked independently,
without importing the generator or binary backend:

```sh
python -B vendor/one_schema_machine/verify_rm_certificate.py \
  --source vendor/ProveIt/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v \
  --candidate data/full_grammar/candidate_dag.json \
  --certificate data/full_grammar/rm_bisimulation.json
```

The expected result has `verified: true`, 219 old nodes, 208 new nodes,
4,533 related operation sites, and matching labels for both decrement
outcomes. The original and new unfolded programs each have 6,460 operation
sites. `independent_rm_check.json` records the separately executed checker.

## Packaged output files

- `baseline_dag.json`: full original 219-node program and names.
- `candidate_dag.json`: 208-node grammar-transformed program and names.
- `grammar.json`: exact AX macro word, residual word, and Re-Pair productions.
- `rm_bisimulation.json`: the finite correspondence certificate.
- `full_equality_preserving_named.tm`: the actual named partial binary table.
- `results.json`: complete bounded-search histograms and generated counts.
- `pinned_inputs.json`: exact upstream pins and hashes of all supplied inputs.

The top-level `data/full_grammar_comparison.json` is the same recorded
`results.json`, provided for easy report lookup.

## Exact original input archive

The minimal vendor files were copied unchanged from the `vendor/` directory
inside this pinned repository archive:

- Repository path: `docs/incoming/zfc_small_machines_20261016.zip`
- ProveIt commit: `47f3a3602946dfe48803a91a910c646e74637ac8`
- ZIP root directory: `zfc_small_machines_20261016/`
- [Download the pinned ZIP](https://raw.githubusercontent.com/VladimirReshetnikov/ProveIt/47f3a3602946dfe48803a91a910c646e74637ac8/docs/incoming/zfc_small_machines_20261016.zip)
- [View the repository entry](https://github.com/VladimirReshetnikov/ProveIt/blob/47f3a3602946dfe48803a91a910c646e74637ac8/docs/incoming/zfc_small_machines_20261016.zip)

Its SHA-256 is:

```text
991268fdd2a62c0fcdd1e48674c4f7229f05afc466506ca3088c4ffc1222e7bd
```

To use an independently downloaded copy instead of the included inputs,
extract that ZIP to `/tmp/zfc-inputs` and run:

```sh
python -B code/search_full_grammar.py \
  --archive /tmp/zfc-inputs/zfc_small_machines_20261016 \
  --output /tmp/zfc-full-grammar-external \
  --seeds 1000
```

The ProveIt helper files originate at commit
`17d0f2eaa650901cda59764dfcc4661c199e49c8`; the program, symbolic
specification and Wade backend use upstream pin
`297ab8df7e5de329605c3875b4934643b371a5e3`. The incoming source-08 grammar
helpers originate in `docs/incoming/zfc_one_schema_research.zip`, introduced
at commit `39409c8c921cccdbd6162c8767c84cfb7df65df1`. The preserved source
notice and the precise boundaries are in `vendor/GRAMMAR_INPUTS_NOTICE.md`.

## Interpretation of the measurement

The AX macro word is unchanged, with all original equality, logical and
theory rows retained. The measured reduction is 219 to 208 decision nodes.
The public Wade backend contributes 62 framework states, yielding a named
**270-state output with 539 rows**. Its `1.inc/read1` transition is missing,
as in the inherited backend output. It is not a new total literal table or
a proved ZFC-consistency state bound. The finite register-machine certificate
does not constitute a binary Turing-machine simulation theorem.

Earlier source 08 already achieved 269 = 207 + 62 on the full unchanged word;
the present result is a bounded comparison, not an improvement over it.
Replacing 62 arithmetically by the framework count of a different interpreter
does not produce a smaller machine. No such substitution is claimed here.
