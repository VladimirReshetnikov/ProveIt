# PA machine comparison and exact novelty replay

Source snapshot: `VladimirReshetnikov/ProveIt` at commit
`2ca99e3d23a5397aae4c786f4da7dfe1cca87f85`.

This directory contains a fresh literal-table comparison, the attributed
mechanism/status ledger, and a portable exact novelty checker. A table
inventory does not establish a machine's consistency calibration.

## Completed census

The six current incoming ZIP archives were downloaded and each byte payload
was verified against its pinned Git blob SHA-1. Their exact identities are
in `archive_receipts.json`. Every `.tm` member was parsed, recursively
including nested ZIP archives. No arbitrary source generator was executed.

| Quantity | Result |
|---|---:|
| Literal table occurrences | 3,775 |
| Distinct literal byte payloads | 926 |
| Spanning 194-state table classes | 526 |
| Nonspanning 194-control byte forms, recorded separately | 2 |
| Spanning 193-state table classes | 55 |
| Literal parsing failures | 0 |
| Historical 194-state catalog classes recovered | 139 of 139 |
| Historical 193-state catalog classes recovered | 54 of 54 |

The historical catalog covers 93 filed research packets. The pinned
`docs/incoming` directory contains six additional current archives. The
historical table keys were checked against the freshly parsed archive
union, so no historical 194-state catalog class is omitted from the
comparison. The historical 139 includes 43 classes whose kept table does
not declare a start; their catalog identifiers begin `table:`. They are
included in the 139-key check, rather than excluded as unrooted tables.
The newly encountered 193-state class is the witness packet's
`research/runtime/header_feasibility/runtime193.native.tm`; it is a runtime
research artifact, not an accepted blank-start consistency construction.

`inventory.json` and `inventory.tsv` give every occurrence and its exact
source/member locator. `historical_MACHINES.tsv` preserves the repository's
original catalog. `representatives194/` contains one representative of each
of the 526 spanning classes, plus the two nonspanning byte forms.
`representatives194.json` supplies their exact hashes and source locations.

The complete 526-class ledger is `frontier194_526.csv` / `.json`.
`named_positive89.csv` / `.json` selects the 89 classes described as positive
constructions by their source reports. The full role breakdown is:

| Attributed role | Classes |
|---|---:|
| Reported principal constructions in the inherited ledger | 76 |
| Reported supplementary constructions in the inherited ledger | 7 |
| Additional released constructions in the latest two packets | 6 |
| Research auxiliaries | 419 |
| Research seeds | 4 |
| Rejected constructions | 14 |
| Total spanning 194-state classes | 526 |

The six additional released constructions are AX11GDH, AX11GDHS, AX11GDHF,
AX11GDHR, H5X, and JH5X. Principal/companion terminology for these six is
not forced into the older ledger's categories. Equivalently, the full
frontier comprises the old 139 classes, 15 later reported positive
realizations, and 372 additional research auxiliaries.

All role and mechanism labels are attributed descriptions. They are not
fresh proofs of 89 absolute consistency equivalences. The 33 groups in
`family_comparison33.csv` / `.json` are descriptive mechanism families,
not a canonical graph invariant or a mathematical lower bound.

## What counts as a table class

Rows have the form `state read write L-or-R next`. Every working control
has exactly two rows. A next label with no rows denotes halt. The
classifier traverses the graph from each possible root, reads 0 before 1,
and records the complete normalized transition tuple. For graphs with a
root reaching all working controls, this provides an exact classification
under arbitrary control renaming. Start-independent keys are useful for
the stronger novelty comparison; they do not identify the intended
blank-start state of a historical machine.

An explicit start comment is respected. Otherwise dense numbering uses
the packets' usual start-zero convention only as a recorded convention.
Some historical HAZ files have dense labels but a different actual start.
Their execution specification must be read with the corresponding label
map and report. No semantic conclusion is inferred from that convention.

The two nonspanning 194-control byte forms are kept separately. The
novelty checker verifies that neither has a spanning root. They therefore
cannot be isomorphic to a candidate whose initial root reaches all 194
controls. No incomplete-root hash is advertised as a full disconnected
graph isomorphism test.

## Portable offline novelty replay

Python 3 with the standard library is sufficient. Keep assertions enabled.
No repository checkout, network, or external package is needed.

```sh
python3 -B novelty.py TABLE.tm --output replay.json
python3 -B novelty.py FIRST.tm SECOND.tm --output pair_replay.json
```

Replace the uppercase input names with the actual machine-table paths.
The default corpus and index are the files beside `novelty.py`. Options
`--corpus DIRECTORY` and `--index FILE` select another complete indexed
corpus. Multiple candidates are checked individually against the prior
corpus and pairwise against one another.

The checker verifies every representative's SHA-256 and recomputes its
spanning-root property. It then compares exact transition tuples, allowing
arbitrary control names, every possible root, global left/right reflection,
global bit exchange, and ignored write/move actions on entry to halt.
Four positive orientation controls are checked for each candidate. Final
novelty decisions use exact tuples; they do not rely on digest equality.

Global bit exchange is an additional structural comparison. It is not
claimed to preserve a machine's all-zero blank specification.

`novelty_all.json` records a fresh completed replay for both delivered
candidates:

| Candidate | Prior-class comparisons | Exact root/orientation comparisons | Matches |
|---|---:|---:|---:|
| PA194C32 | 526 | 408,176 | 0 |
| PA194AX11HC4 | 526 | 408,176 | 0 |

The two candidates were also compared directly in 776 root/orientation
cases and are distinct. Their dense SHA-256 values are:

```text
PA194C32
3af42ea9d430e5df22b69e6fc540e3530f87263372580c7c554bae37ba524ac8

PA194AX11HC4
fe4253a42045c330a499d99cc33d55a14e116cae910eb624c499161a7a7ca755
```

Novelty is relative to this pinned recognized corpus, not a claim of
worldwide priority. The supplementary broad JSON scan was not completed;
tables encoded only in unrecognized JSON formats, unexecuted generators,
or prose are outside the fresh recognizer's scope. The catalog-key check
and source reports' explicit literal representatives cover all named
194-state constructions compared here.

## Mathematical proof status

The revised AX11H packet supplies an ordinary written mathematical iPRA
calibration, including uniform physical/source, source/command, numerical
proof, current Foundation adapter, and I-sigma-1 transfer arguments. It
explicitly distinguishes that written theorem from an unfinished
end-to-end Lean or Rocq formalization. These must not be conflated.

The new AX11HC4 construction preserves the exact calibrated AX11H source.
Its inherited absolute calibration and its new relative simulation are
separate components of the report's proof. C32 instead preserves the
original primary source; an ordinary PA calibration alone cannot be
silently promoted to an iPRA calibration.

The historical role ledger does not independently reprove every inherited
arithmetic calibration. Finite executable checks and structural novelty
checks also do not constitute an end-to-end proof-assistant theorem.

## Pinned source links

- [Historical machine catalog](https://github.com/VladimirReshetnikov/ProveIt/blob/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85/Computability/BusyBeaver/Research/PA/docs/MACHINES.md)
- [Historical machine table keys](https://github.com/VladimirReshetnikov/ProveIt/blob/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85/Computability/BusyBeaver/Research/PA/docs/MACHINES.tsv)
- [Current incoming directory](https://github.com/VladimirReshetnikov/ProveIt/tree/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85/docs/incoming)
- [Revised AX11H written theorem and interfaces](https://github.com/VladimirReshetnikov/ProveIt/blob/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85/Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/README.md)
- [Revised AX11H final mathematical composition](https://github.com/VladimirReshetnikov/ProveIt/blob/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85/Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/proof/consistency_equivalence.tex)
- [Positive primitive-recursive transport theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85/Computability/BusyBeaver/Research/PA/docs/pa194_ax11h_research_2026-11-14_2/proof/ipra_simulation_theorem.tex)
- [AX11GDH packet, including the inherited family/status ledger](https://github.com/VladimirReshetnikov/ProveIt/blob/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85/docs/incoming/pa194_ax11gdh_research_2026-11-15.zip)
- [Witness axiom packet](https://github.com/VladimirReshetnikov/ProveIt/blob/2ca99e3d23a5397aae4c786f4da7dfe1cca87f85/docs/incoming/pa194_witness_research_2026-11-15.zip)

The other four current archives and all six exact identities are listed
in `archive_receipts.json`. Their supplied licenses and authorship
notices remain applicable; the present inventory and novelty scripts are
new comparison code, and the role/family descriptions retain their
attribution to the source packets.
