# Stride-two transfer: complete logical compiler, physical allocation separate

This research packet proves a new three-command proof-search language
equiconsistent with the inherited native calculus. Its transfer removes two
old stack heads, and deliberate successful MP(0) operations provide parity
padding. The full ordinary proof is `proof.md`; the report-ready LaTeX section
is `stride_two_section.tex`.

No 215- or 214-state physical claim is made by these files alone. A successful
allocation needs its own arbitrary-natural primitive runtime and exact blank
initialization. All sources here are exact register programs, not transition
tables.

## Core result

With native Cantor pairing, truth 0, falsity 1, and I(0,0)=0, retain MP and the
dominated-AX emitter. Replace the stack commands by DROP;NIP;NIP;NIP. It returns

    (t,[x,y;S],d,h) -> (h,S,d,y)

unless h=1, t=1, or x=1. The new compiler realizes every native theorem X with
the exact strong contract

    (t,S,0,0) -> halt or (X,S,0,0)

for arbitrary numerical t,S. An independent diagonal argument proves that the
MP=0/S2=1 increasing scheduler needs exactly two conservative theorem heads
above an arbitrary buried tail at cutoff N=1. Ten heads from a matched AX
startup therefore leave permanent margin eight.

The shorter clearTop;copyHtoTop;NIP;NIP command has the same return and only the
h=1 or x=1 guards. It has the same logical calibration. Its source variants
are separate under `direct/`; their physical contexts remain unverified.
The all-natural prefix proof and the reason the same compiler still detects
falsity are given in Section 10 of `proof.md` and in the LaTeX section. The
edited command body shrinks from 104 to 61 primitive leaves; each full source
still has 202 distinct subtrees. This is a source-size comparison only.

## Reproduce

Python 3.10+ and the standard library suffice. Run from this directory with
assertions enabled:

```sh
python3 -B build_source.py --parent inputs/mp0-transfer201.sites.json --out /tmp/stride2-source-fresh
python3 -B build_source.py --direct --parent inputs/mp0-transfer201.sites.json --out /tmp/stride2-direct-source-fresh
python3 -B check_stride2.py --output /tmp/stride2-interfaces.json
python3 -B check_source_command.py --output /tmp/stride2-source-command.json
python3 -B check_stride2.py --direct --output /tmp/stride2-direct-interfaces.json
python3 -B check_source_command.py --direct --source direct/direct2-0.sites.json --output /tmp/stride2-direct-source-command.json
```

The source builder verifies both complete CFGs and exact exterior ordinal
transport for all five Catalan associations. The stack checker passes 79
symbolic interface cases, 11,232 literal arithmetic non-detachment cases,
100,000 conservative candidate recurrences, and 444 full Cantor diagonals.
Mandatory and forbidden halts are explicit. The literal source checks cover
81 cases for each command form: 57 composite-guard halts and 45 direct-guard
halts. These finite checks corroborate the written proofs and do not replace
their universal quantifiers.

## Source identities and scope

The input source is the incoming MP0-transfer215 source, SHA-256
`8ddb942f0f1d8e2e3b12ab7217c7232eb553cd288fca38dbf9b0eded73893dd5`.
Its retained provenance is in `inputs/parent_provenance.md`; inherited notices
and licenses are under `licenses/`.

`stride2-0.sites.json` is the primary DNNN association, SHA-256
`ec77ca34f5c4d4c2f4fa9c5c914def6599108357f62754987bab55eda3092949`.
All five basic DNNN variants have 202 distinct subtrees, 4,801 primitive leaves,
6,245 guarded cases, depth 44, and maximum zero run 6. Their logical count is
not a physical TM state count.

The unbounded native-calculus/ZFC calibration and dominated-row recovery are
identified inherited results. The new content here is the stride-two strong
compiler, parity-padding construction, source splices, and two-head credit
proof. The parent independently reviewed the ordinary argument within this
research collaboration; this is not external refereeing or kernel checking.

`direct/` contains five exact 61-primitive direct-command variants (202 DAG
nodes, 4,758 leaves, 6,187 guarded cases). They are exploratory inputs for
physical allocation, not certified binary machines. The retained history
explains the earlier finite-grid step cap and the checker halt-policy
strengthening. This portable packet contains no rotated-search variants,
rebuild duplicates, or Python bytecode caches.

`source_build.json` and `direct/source_build.json` record the exact independent
reconstruction receipts. The `source_variants.json` files retain the original
construction metrics. `MANIFEST.sha256` identifies every shipped file except
itself; verify it with `sha256sum -c MANIFEST.sha256` from this directory.
