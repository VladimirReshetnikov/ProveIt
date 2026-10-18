# Attribution and source boundaries

This packet was prepared for Vladimir Reshetnikov's request to improve the
252-state ZFC consistency machine in ProveIt. The report, new experiment
drivers, ordinary proof notes, and independent checks were prepared during
this investigation. They are not attributed to the authors of the retained
machine or represented as previously checked Lean developments.

## Retained construction

* Mira-Cult designed and built the original 254-state Turing machine.
* Jeff (`jeff87654`, Jeff Ketchersid) supplied the imported Coq verification.
* Andrew James Wade supplied the public compiler backend.
* mira-emmy supplied the public 253-state reduction, pull request 20 in
  `jeff87654/busy-beaver`, head
  `0d544f2a2e3c18f12278441a74b7879f31cbe856`.
* ProveIt supplied the physical-register permutation, exact 252-state
  benchmark, maintained Lean endpoint, and inherited research/checker code.

The ProveIt pin is `43026ff42f0939f09b9e95495248cfadcad38e38`.
Its imported upstream benchmark pin is
`jeff87654/busy-beaver@297ab8df7e5de329605c3875b4934643b371a5e3`.

The retained `upstream/lib/jeff-busy-beaver-zfc254/README.proveit.md` gives
the exact provenance and license boundary. In particular, that imported
benchmark has no declared upstream-wide license and is excluded from
ProveIt's blanket MIT-0 grant. This packet does not relicense it.
`upstream/LICENSE` is the exact pinned ProveIt license, with the preceding
exception preserved. No new blanket license is asserted over the mixed
source material in this packet.

## Exact source copies outside upstream/

The following files retain inherited content, despite residing beside new
experimental code:

* `binary_experiments/Prog254.v` is an exact byte copy of the pinned literal
  register program under `upstream/lib/jeff-busy-beaver-zfc254/`.
* `binary_experiments/strict_affine.py` is an exact byte copy of the
  attributed closure-kernel source 27 strict affine executor.
* `binary_experiments/breakthrough_register_permutation.py` is retained
  inherited research code. Its historical filename does not describe a
  new breakthrough from the present investigation.

New code uses the four retained register-box contracts and selected pinned
source/control-graph helpers. Their authorship does not transfer to this
investigation. Conversely, the new ordinary simulation lemmas and Python
extensions are not presented as part of the preexisting checked theorem.

`PROVENANCE.json` lists the source URL, Git blob identity computed from the
delivered bytes, SHA-256, and size of each selected upstream file.
`MANIFEST.sha256` covers the completed research packet.
