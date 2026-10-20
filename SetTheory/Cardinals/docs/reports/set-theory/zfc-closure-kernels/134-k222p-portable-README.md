# Offline reproduction of the 222-state candidate

The preferred machine is `machine/candidate222.tm`:222 working states,444 rows,start0,halt222,dispatcher22,blank binary tape,one-cell left/right moves only. Its SHA-256 is

```
3bcf4678c9c576ae99a108c32038f035b42204289267d05a34ba2b37b32b6476
```

Python3.10 or newer and its standard library are sufficient. Keep assertions enabled. From the extracted packet's top directory, choose an initially empty output directory outside the packet:

```sh
python3 -B portable/reproduce.py --output-dir /tmp/k222-quick
python3 -B portable/reproduce.py --full --output-dir /tmp/k222-full
python3 -B portable/reproduce.py --full --full-baseline --full-alternative --output-dir /tmp/k222-all
```

The default independently reconstructs the exact source, checks nine all-register macro contracts and the numerical emitter, checks both full guarded-control-flow resolvers, regenerates the schematic G proof DAG and seed-bundle transformations, checks that DAG with a separate parser, rebuilds the literal table, checks both folds, and executes the complete blank startup with separate sparse and dense simulators. Three deliberately corrupted fold certificates must be rejected. It then audits the supplied primary runtime derivations for exact input identity and complete coverage. The included alternative is also reconstructed by default.

`--full` additionally rederives all6167 primary runtime cases with arbitrary natural register values, arbitrary natural gap/first spare, and arbitrary finite remaining spare list. The newly generated case summaries must be byte-identical to the retained summaries. The full replay is expected to take a few minutes.

`--baseline` additionally runs the unchanged K224 archive's quick replay. `--full-baseline` additionally rederives its inherited K224/K225/K226 runtimes. These options are explicit:an ordinary new-machine replay does not claim to have freshly replayed the entire ancestry. `--full-alternative` additionally rederives the conditional variant's runtime. `--skip-alternative` restricts this driver to the primary machine.

Expected final status is `QUICK_K222_REPLAY_PASS` or `FULL_K222_REPLAY_PASS`. Every phase writes a separate log and the output directory receives `replay.json`. No mode downloads anything, modifies the supplied packet, or builds a new proof-assistant endpoint.

## Contents

- `machine/`:canonical,K-labelled and legacy-labelled final tables; their maps;the literal seed+G parent before the folds;the exact source;and complete startup data.
- `source/`:standalone deterministic source/emitter binding,schematic G derivations,and the mathematical calibration note.
- `verification/`:deterministic table constructor,independent fold checker,and separate finite-proof parser.
- `runtime/`:inherited induction engine and parameterized literal-table checker.
- `certificates/`:retained fresh runtime/case results,compiler/fold results,and negative controls.
- `alternative/`:the independently constructed conditional-K+G 222-state candidate and its replay.
- `theory/`:inherited seed-K calibration notes.
- `inputs/`:small pinned K224 table/numbering inputs.
- `vendor/`:the unchanged full K224 predecessor archive and inherited notices.

The report states how these layers compose into the ordinary mathematical equivalence between blank non-halting and Con(ZFC). Neither the local fold certificate nor the runtime receipt alone supplies the logical calibration.
