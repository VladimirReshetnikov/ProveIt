# Gap-clock runtime research artifact

This folder contains a **253-working-state prepared-frame runtime** with a
new seven-state loader and two phase-specific uses of inherited transitions.
It is **not** a machine below 252 states and it has **no working blank-tape
initializer**. In fact, its inherited start label 64 has a certified 102-step
prefix to an unconditional rightward escape. The files are intended as a
reproducible architecture experiment for further research.

The main new construction stores the next proof-candidate counter in the
zero gap between the program-counter marker and the register header. The
obsolete `N` register and its copy/restore fetch code are removed from the
source runtime. The first physical register is `L`, the residual command
word. The seven-state loader, entering from source PC `1` with `L=0`, has
the exact contract

```
gap g, first register 0, head h
  --> gap g+1, first register g+1, head h-g-2, empty PC.
```

Every other register cell, including every spare block, remains fixed in
absolute tape coordinates. The loader takes exactly `2*g*g + 15*g + 40`
literal transitions including its dispatcher entry. Its first subsequent
decrement gives command candidate `g`; the next exhausted attempt uses
candidate `g+1`. This final version has unit stride.

## Reproduce

Python 3.10 or later is sufficient; no third-party Python packages, network
access, repository checkout, or environment variables are needed. From this
folder, run:

```sh
python3 code/assemble_gap_runtime.py
python3 code/unit_loader.py
python3 code/gap_loader.py --fold-past
```

The assembler regenerates both tables, their label map and the verification
JSON. It checks all 8,381 ordinary guarded instruction cases with the inherited
affine checker, checks that the two old rows reused by the loader were absent
from those cases and the Box contracts, then repeats the whole instruction
audit and 288 exact-tape loader cases on the pruned 253-state table. Maximum
source depth is 36; runtime frames use gap at least 40.

`unit_loader.py` independently constructs the loader rows from a short literal
dictionary and checks 288 finite cases with several gaps, arbitrary register
suffixes, translated origins, and both direct and dispatcher entry. The
mathematical all-gap invariant is in `notes/gap_unit_loader_review.tex`.
Finite replay supplements that invariant and does not replace it.

`gap_loader.py --fold-past` reproduces the earlier nine-new-state version
with gap increment 2 and the same first-register result. That earlier version
requires a parity-completeness argument. It is retained as an intermediate
construction, separate from the final unit-stride table.

## Machine files and conventions

`machines/gap_clock_unit253_old.tm` keeps the original working-state labels
plus new labels 300, 302, 303, 305, 306, 307, 308, 310 and 311. Halt is old
label 254, which is not counted as a working state. Its 506 rows are complete.
The retained legacy states number 244; seven loader states and two scheduler
states give 253. Old rows `(27,1)` and `(33,0)` hold two additional loader
phases without adding states.

`machines/gap_clock_unit253.tm` is the same table with working labels
0 through 252 and halt label 253. `machines/renumbering.json` gives the exact
old-to-canonical map. Both tables explicitly carry a diagnostic status
comment. Their `start` directive records the tested inherited bootstrap;
it is not a successful initializer.

`machines/unit_loader_patch.tm` and `machines/gap_loader_9_states.tm` are
partial transducer patches referencing inherited states, not standalone
complete machines.

The eight active logical registers occupy physical slots as follows:

| Physical slot | Logical register |
|---:|---|
| 0 | L |
| 1 | W |
| 2 | T |
| 3 | D |
| 4 | A |
| 5 | Y |
| 6 | H |
| 7 | X |

The proof interface still requires at least nine physical blocks, with the
ninth and all following blocks treated as arbitrary spares. Removing the
unused ninth selector does not assert that the inherited Box theorem already
covers an eight-block tape.

## Proof status and remaining work

The ordinary-instruction certificate is a rule-by-rule symbolic argument
over arbitrary affine gaps and arbitrary register files satisfying the named
zero/nonzero guard. It is conditional on the four unchanged generic register
Box contracts. It is not a newly kernel-checked whole-machine theorem.
The loader has the separate universal tape invariant in the TeX note.

The inherited blank start is disproved as an initializer by a short exact
certificate: after 102 transitions, old state 42 is at head 12 and the only
ones are at 4, 6 and 10. Everything at and to the right of the head is blank.
The transition `42 0 1 R 42` consequently repeats forever, by induction.
The table from its supplied blank start is therefore an unconditional
nonhalting machine, not the requested consistency-calibrated construction.

Further work must save at least two runtime states, build a valid initializer
within the final budget, and connect the literal table to the complete source
enumeration and logical calibration. No claim that these tasks are easy,
automatic, or already discharged is made here.

## Sources and attribution

The reference repository is Vladimir Reshetnikov's ProveIt, inspected at
commit `85633fd2f57b5dca16f87667699134d1b500ebc0`. The literal original machine
is attributed to Mira-Cult; Jeff supplied its verification; Wade supplied the
compiler framework. The inherited 253-state work and the ProveIt
permutation252 development are preserved in the provenance notes.

`INHERITED-PROVENANCE.json` retains the previous package's source descriptions
and hashes verbatim; its older inspection commit is historical provenance,
not the inspection commit of this experiment. `PROVENANCE.json` records this
package's exact inputs and adaptation. The inherited helper code is bundled
with `LICENSE-ProveIt.txt` and `LICENSE-Wade.txt`. All new scripts here use
relative paths and do not publish, modify or merge repository content.
