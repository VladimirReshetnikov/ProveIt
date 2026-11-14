# PA194GH: explicit-binder AX with cached-head Shift

This is a new binary blank-start machine with **194 working states**,
composing PA194G's explicit AX binder with PA194H's cache-only Shift.
Successful MP retains G's no-push behavior. The machine is structurally
distinct from all 94 recognized 194-state graphs at ProveIt commit
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2`.

The table and all computational checks below are unconditional finite data.
`proof.tex` gives the ordinary mathematical command and scheduler argument
relative to the exact numerical calculus D4Q. The inherited translation
between D4Q refutations and PA refutations is a separate logical dependency.
An **absolute iPRA theorem has not been completed**. To conclude the desired
iPRA consistency equivalence, the source/tape and proof-translation
reductions must themselves be established in iPRA. Python verification does
not supply this missing calibration or a Lean kernel proof.

## Literal machine and material change

`machine/machine.tm` contains 388 rows in the format
`state read write direction successor`. Working states are 0 through 193,
the initial state is 0, and the external halt label is 194, with no outgoing
rows. The tape is bi-infinite and initially zero; the head starts at zero.
The alphabet is `{0,1}` and every transition moves `L` or `R`.

Dense table SHA-256:

    b9fadcb197c33895603c71b7119bc92b1772c01960804e8850e2a66dd39a995e

Native table SHA-256:

    bb35e0a61c48461d419323cbb4c1c25c47bb0e268bca97e2a22d967af4dbf51f

The native table starts at 74 and halts at 254. `machine/labels.json`
is the exact dense-to-native renaming; `machine/raw.native.tm` is the
201-state table before the seven compatible contextual folds.

For a command store `(t,w,d,h)`, AX saves `U(c,h)`, where `c` is its explicit
operand. Shift tests `h=1`, then otherwise replaces the visible theorem by
the cache and loads the next stack entry into the cache. Successful MP
returns `(b,w,b,0)` without pushing a dummy zero. Hence:

- Unlike G, a visible `t=1` with cache zero does not halt a single Shift.
- Unlike H, generalization needs no offset-setting command:
  `Gen_i = Push; Shift; AX_{i,0,0}; Shift^10`.
- `Pop = AX_{0,0,0}; Shift^11` halts exactly when the incoming visible
  theorem is one; otherwise it preserves that theorem and pops one entry.
- The uniform refutation detector is `AX_{0,0,0}; C(proof); Pop`.
  Appending only Shift would be incorrect for this protocol.

The five controller edits and one source DAG definition change are printed
in `proof.tex` and recorded in `machine/receipt.json`. The AX grammar and
the arithmetic register-engine rows are unchanged from G. The new design
is this checked composition and its command compiler; the individual G and
H ideas are attributed to the supplied packets.

## Offline reproduction

Python 3 and its standard library are sufficient. Assertions must be
enabled; do not use `python -O`. No repository checkout, network, Lean
installation, search engine, or external Python package is needed.

From this directory:

    python3 -B build.py --output /tmp/pa194gh-machine
    python3 -B check_commands.py --output /tmp/pa194gh-commands.json
    python3 -B independent/check.py /tmp/pa194gh-machine --output /tmp/pa194gh-independent

`build.py` deterministically regenerates the machine artifacts, checks all local folds
and the whole-tape startup, then checks every symbolic source outcome.
Use `--output DIRECTORY` to write elsewhere. `--quick` skips the symbolic
source-outcome pass and must not be used as a replacement for full validation.
The second command checks the entire G emitter over a free term algebra and
the GH command words over symbolic stores, including all zero aliases.
The third command imports no builder or arithmetic-box oracle: it rederives
four unbounded-list lemmas from the candidate's literal transition rows,
resolves the source independently in two ways, and verifies every outcome.

`python3 -B verify.py --output /tmp/pa194gh-replay.json` runs these commands
using a temporary output directory, compares the reproduced machine and
source artifacts with the frozen files, and writes only the explicitly
requested fresh receipt. It can take several minutes. Omitting `--output`
prints the receipt without saving it. `check_commands.py` and
`check_source_relation.py` use the same output convention. The source
relation check compares the exact inherited source and row changes without
executing the expensive runtime contracts. Replay does not mutate the
frozen package or its recorded evidence.

The comparison folder in the larger release contains the 94 retained
frontier representatives and its portable `check_frontier_novelty.py`.
Run that checker on `machine/machine.tm` to reproduce `novelty.json`.
It compares exact full tuples, allowing arbitrary state renaming, spanning
root, reflection, global symbol exchange, and ignored final halt effects.
Symbol exchange is used as a structural novelty test only.

## Recorded results

| Check | Result |
|---|---:|
| Fixed controls | 134 |
| AX reader controls | 67 |
| Simultaneous contextual folds | 7 |
| Final working states | 194 |
| Local fold cases | 28, all pass |
| Primitive source sites | 3,653 |
| Primitive source outcomes | 4,754 |
| Construction symbolic steps | 1,512,536 |
| Construction maximum per outcome | 479 |
| Independent symbolic steps | 1,102,232 |
| Independent maximum per outcome | 385 |
| Independent minimum positive duration constant | 3 |
| Independent literal list lemmas | 4, all pass |
| Whole-tape blank initialization | 57,922 transitions |
| Matches in the 94-graph structural frontier | 0 |

The unbounded symbolic domain contains nine arbitrary natural primary
registers, both decrement branches, any nonempty finite list of natural
spare values, and any nonnegative affine header gap, with complete blank
exteriors. Startup checks equality of the entire finite-support tape,
head, and state. It reaches source site 25 at native dispatcher 84, head
`-2`, logical registers `(2,0,...,0)`, and 26 spare values equal to one.
The nonzero logical register is the fresh-candidate counter.

Frozen records are `machine/receipt.json`,
`emitter_and_words_receipt.json`, `novelty.json`, and
`independent/results/PA194GH/receipt.json` with the associated contract,
list-lemma, and startup files. `PROVENANCE.json` maps inherited files to
the pinned repository and their byte identities. `inputs/proof.tex` and
`inputs/check_commands.py` are historical G inputs; GH's proof and checker
are the top-level files. The source engines retain their original notices
and the licenses in `licenses/` and `independent/reference/`.
