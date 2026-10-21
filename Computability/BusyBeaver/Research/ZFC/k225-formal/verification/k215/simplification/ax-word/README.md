# A checked macro word for the AX routine

The AX proof now composes the existing macro contracts with one induction over a
156-entry word. A kernel-checked finite test binds that word to the literal
`dagPerm` nodes, and symbolic evaluation proves the unchanged `ax_eval` statement.
The five-node gate contract is unchanged. `f236` uses the word evaluator;
`l236`, `c236`, and `ax_eval` retain their previous types.

The [replacement source](source.lean) is 10,091 bytes and 223 lines, down from
202,222 bytes and 1,196 lines. Its isolated kernel check passed in 38.660 seconds;
the [typed clients](Audit.lean) passed in 0.265 seconds. Both runs had no warnings.
`l236` and `ax_eval` use only `propext`, `Classical.choice`, and `Quot.sound`;
`c236` is axiom-free. See [source output](source.log), [client output](api.log),
and the [summary](result.json).

These are incremental checks against the pinned, previously compiled 204-module
baseline. They do not claim a fresh closure build or a new final-machine check.
The exact commands, source hashes, imported-object hashes, and unchanged-input
checks are preserved in [source-actual.json](source-actual.json) and
[api-actual.json](api-actual.json). The executed Python runners retain their
original scratch paths as historical records. The parent [portable Lean build](../../lean/README.md)
provides full endpoint reproduction from the current repository sources.

The [canonical generator](../../../../generate_l2axiomsdom.py) emits this
compact representation only in `perm` mode. The
[generation comparison](generation-review.json) confirms exact reproduction of
the checked source, unchanged Dom-mode output, and unchanged public statement
headers. From the repository root, regenerate into a fresh temporary file with:

```sh
python3 Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2axiomsdom.py \
  Computability/BusyBeaver/Research/ZFC/k225-formal/lean215/dagperm_nodes.json \
  /tmp/L2AxiomsPerm-word.lean perm
```

The original source remains in Git at revision
`f5b2db607f8cf1daccf601b4ce14d7cee38b6770`. History retains the
[first typed-caller failure](history/api-caller-v1/compiler.log), caused by its
namespace-opening syntax, and the [exact correction](history/api-caller-v1/repair.diff).
It also retains an unexecuted [generator formatting draft](history/generator-format-attempt1/note.txt)
with a Python string-escaping error. Neither changed the checked AX proof.
