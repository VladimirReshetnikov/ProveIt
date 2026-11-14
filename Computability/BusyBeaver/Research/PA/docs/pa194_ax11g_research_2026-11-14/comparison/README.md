# Pinned comparison of the PA machine designs

The repository snapshot is
`32d0d8b7d93a63ad4106c18cdb29b37927acdad2` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/32d0d8b7d93a63ad4106c18cdb29b37927acdad2).

The inventory covers all 675 tracked literal `.tm` files in the PA subtree
and every literal `.tm` member extracted from the five ZIPs then in
`docs/incoming`. All 680 downloaded or checked-out source payloads match
their pinned Git blob identities. The exact paths, Git identities, SHA-256
digests, and byte sizes are retained in `source_integrity.json.gz`.

Among these files there are 528 occurrences of complete tables with 194
working controls, 139 distinct labeled tables, and **94 spanning graph
classes**. Of those classes, 89 already occur in the filed PA material and
five are added by the current incoming packets. Earlier explicit-JSON
frontier tables are included through their supplied literal representatives.
Four occurrences of disconnected synthetic fixtures are recorded separately
in `census_summary.json`; they are not counted as spanning machines.
The recognizer does not execute arbitrary program generators or infer a
literal machine from unevaluated Lean or prose encodings.

The five incoming packets name six tables, but their AX11QH5 table repeats
the already filed AX11QH5 table byte for byte. Their five additional classes
are AX11H, AX11QH, AX11S, 4L, and HX. P5 denotes a five-register permutation;
it does not denote coefficient-five formula arithmetic.

## Delivered comparisons

`packet_ledger82.csv` and its JSON companion cover all 77 filed research
packets and all five current incoming archives. The descriptions distinguish
the packets' reported conclusions from this study's fresh checks.

`all_194_designs.csv` and its JSON companion give every one of the 94 classes,
with its name, mechanism, exact table, source locator, and evidence category:

| Category | Classes |
|---|---:|
| Reported principal construction | 51 |
| Supplementary construction | 7 |
| Research auxiliary | 25 |
| Research seed | 4 |
| Earlier rejected construction | 6 |
| Additional rejected even/runtime diagnostic | 1 |

These categories describe historical claims and uses. The graph census does
not prove their arithmetic calibrations. In particular, the pinned PA README
explicitly leaves the absolute physical-machine iPRA consistency calibration
unfinished. `principal194.md` gives the mechanism comparison of the 51
reported principal designs in a compact table.

## Exact novelty replay

Run, from the package root:

```sh
python3 -B comparison/verify_comparison.py
```

This reconstructs complete canonical tuples from every table in
`frontier194/`, checks the 94-way distinctness, and compares the new
`machine/machine.tm` against them. It considers every spanning initial
control, state relabeling, global symbol exchange, left-right reflection,
and arbitrary final writes and moves on entry to the halt label. Comparison
uses exact tuples; SHA-256 digests identify files and provide integrity
checks. Symbol exchange is a stronger structural novelty test, not a
semantic equivalence that necessarily preserves the zero blank.

The same command computes the coarsest ordinary control bisimulation of all
94 historical tables and AX11G. Every quotient has 194 controls. This excludes
ordinary control identifications; tape-context reductions remain possible.

To write a fresh receipt outside the release, add
`--receipt /tmp/pa194-comparison.json`. `verification.json` is the retained
successful replay. The code requires only Python 3.10+ and its standard
library. Keep assertions enabled.

The physical 193-control trials and their independently replayable rejection
certificates are under `../research/startup193/`. They are not counted as
smaller consistency machines and imply no general state-count lower bound.

## Attribution

Historical table bytes, names, and mechanisms remain attributed to the
linked ProveIt packets and their authors. The earlier 82-class mechanism
annotations came from the AX11H incoming packet's comparison ledger; they
were matched to the freshly computed exact tuples. The subsequent twelve
classes were identified from their current reports and exact tables.
The census, current reconciliation, canonical comparison implementation,
and fresh all-start replay are new work in this package.
