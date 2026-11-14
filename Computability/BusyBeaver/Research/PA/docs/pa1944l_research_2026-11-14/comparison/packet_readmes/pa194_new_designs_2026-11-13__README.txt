# Two new 194-state PA consistency machines

This archive delivers **PA194C** and **PA194CS**, two materially different
194-state constructions. A verified machine with fewer than 194 states was
not obtained. PA194CS adds a new source-level simplification using the full
symmetry of a destructive equality routine, and is the stronger new design.

Both machines use a single two-way binary tape, initially all zero, with
head at cell zero and initial state 0. Working states are 0 through 193;
194 is the separate halt label. Every transition writes one bit and moves
one cell left or right. Each complete table has 388 rows.

## Read the report

`report/pa194_cached_research.pdf` contains the comparison, constructions,
ordinary mathematical proofs, formalization boundary, search record,
complete transition tables for both machines, and an archive-by-archive
ledger. Its complete LaTeX source and included fragments are beside it.

| Property | PA194C | PA194CS |
|---|---:|---:|
| Working states / transition rows | 194 / 388 | 194 / 388 |
| Primitive source sites | 3,649 | 3,646 |
| Universal primitive outcomes | 4,749 | 4,745 |
| Exact complete-tape blank startup | 57,922 | 57,768 |
| Independent verifier symbolic steps | 1,096,302 | 1,100,204 |
| Minimum certified physical-duration constant | 3 | 3 |

These symbolic checks quantify over arbitrary natural register values and
an arbitrary finite nonempty spare list; they are not bounded numerical
sampling. The startup counts are finite exact seed checks, not long-run
evidence of nonhalting.

## Exact tables

PA194C: `construction/candidate/pa194C.tm`

SHA-256:

```text
d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b
```

PA194CS: `secondary/pa194CS/machine/pa194CS.tm`

SHA-256:

```text
1c71002e5b8a2ddd1dd1311a2c54c424764624b611b69c8efbee1ac23c2e6f5f
```

A row is `state read_bit write_bit L_or_R next_state`. Native tables and
checked dense-to-native label maps accompany both tables.

## What changed

PA194C combines the supplied 67-reader/seven-fold decoder with the cached
controller used in 195C. Successful modus ponens returns its conclusion in
the cache, and Shift tests that cache. It has exactly the same resolved
3,649-instruction source graph as the pinned 195C parent, which the builder
reconstructs byte for byte.

PA194CS further shortens Shift. After clearing the old top and copying the
cache into the top and scratch, the previous controller restored scratch
to the cache, then compared `(cache,scratch)=(h,1)`. The new controller
increments the now-zero cache and compares `(1,h)`. On inequality, the
existing comparison clears **both** operands, so all surviving registers
agree. The local equivalence also holds for arbitrary incoming scratch.
This removes three primitive sites. A new reader initially costs one
state; the exact contextual identification `41 -> 330` recovers it, using
actions `0 L 31` and `1 L 46`. All four local cases have duration three.

Both control graphs are absent from the pinned corpus even under arbitrary
state renaming, a changed designated start, tape reflection, global symbol
complementation, or both. They are also distinct from each other. This
finite graph comparison is separate from the mathematical preservation
proofs.

## The theorem and its dependency

The accompanying ordinary mathematical argument establishes, for each
delivered machine M,

```text
PA proves: Nonhalting(M, blank tape) <-> Con(PA).
```

The new machine-specific results are exact finite-trace preservation:
PA194C has the same source as the supplied 195C machine, and PA194CS
preserves that source by the proved symmetric-Shift block replacement.
Complete physical simulation and exact initialization bind the source
results to the literal binary tables.

The logical calibration of the unchanged separate-diagonal-head numerical
calculus to PA is an **inherited ordinary mathematical dependency**, made
explicit and retained under `construction/logical_reference/`. There is
no claim of a newly kernel-checked end-to-end Lean or Rocq theorem, and the
repository's conditional iPRA endpoints remain conditional. The Python
certificates do not by themselves establish the logical calibration.

## Reproduce the accepted constructions

Python 3.10 or later and its standard library suffice. Run without `-O`
or `PYTHONOPTIMIZE`, since assertions check the certificates. From this
archive's root:

```sh
python3 -B construction/build_cached.py
python3 -B construction/verification/check_cached.py

python3 -B secondary/pa194CS/build.py
python3 -B secondary/pa194CS/verification/check.py

python3 -B comparison/check_symmetric_source.py \
  construction/candidate/pa194C.instructions.json \
  secondary/pa194CS/machine/pa194CS.instructions.json

python3 -B comparison/verify_novelty.py \
  construction/candidate/pa194C.tm --census comparison/census.json
python3 -B comparison/verify_novelty.py \
  secondary/pa194CS/machine/pa194CS.tm --census comparison/census.json
```

The independent literal-tape checks can take several minutes. Each derives
four generic list lemmas from the actual rows and checks every source
outcome; neither imports the compiler nor an arithmetic-box oracle.
Complete recorded outputs are included. Rerunning builders updates
receipts but must reproduce the published table hashes.

To rebuild the PDF using a standard TeX Live installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa194_cached_research.tex
pdflatex -interaction=nonstopmode -halt-on-error pa194_cached_research.tex
```

## Corpus and search scope

The source snapshot is
`VladimirReshetnikov/ProveIt@768c2be1a8e4d2fcf8aa3443c7b0f084d145734c`.
The fresh census traverses all 36 incoming archives, representing 49
distinct ZIP payloads and 77 references, plus direct PA tables. It finds
2,519 recognized numeric-table occurrences, 606 byte strings and 437
action-graph classes. These include rejected experiments and are not
counts of correct consistency machines. The report states the exact
parser convention and exclusions.

`comparison/` includes the census, all 36 archive hashes, family comparisons,
novelty receipts, independent mathematical reviews, and the source-binding
certificate. The census can be rerun from the pinned repository using
`census.py --repo PATH --output NEW_DIRECTORY`.

`search/decoder/` records seven stochastic searches with at least 24,295,755
mutation-proposal slots, a capped 5,000-root neighborhood search, three
completed bounded local-quotient closures, a 606-table broader merger
screen, and 1,440 fixed-shape head-order templates. Mutation slots are not
distinct machines. `search/controller/` records whole-source symbolic
context screening, including a final search covering all 194 controls.
`search/symmetric_shift/` records the targeted follow-up on the new source;
its largest completed bounded closure visited 576 tables.

Every search retained 194 as its best state count. Queue exhaustion is
claimed only for the stated finite rewrite rules; no global lower bound
or minimality claim is made. Discovery searches are unnecessary for
rebuilding and verifying either delivered machine.

## Integrity and attribution

`RESULTS.json` records the exact machine identities and result scopes.
`PROVENANCE.json` binds the pinned repository and parent archives.
`SHA256SUMS` covers all delivered files except itself. Check it before
regenerating evidence with `sha256sum -c SHA256SUMS`.

Inherited compilers, reference Lean sources, arithmetic and symbolic
engines retain their supplied provenance and license notices. The new
work consists of the controller/decoder composition, symmetric-guard
source proof and fold, verification bindings, current corpus comparison,
bounded searches, and this report. No repository changes were published.
