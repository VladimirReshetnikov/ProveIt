# PA consistency machines: comparison and NEG18

**The requested construction below 196 states was not obtained.** This archive does not claim a 195-state machine, a general lower bound, or a newly completed Lean/Rocq consistency biconditional.

The new positive construction is an **18-instruction source implementation of encoded negation**, using existing engine entries. Its complete compiled machine has **197 working states**, 3,441 primitive source sites, and 4,468 successfully checked symbolic instruction contracts. The archive also contains a reproduced 196-state closing-row variant and a comparison of the supplied research corpus.

All imported material is pinned to ProveIt revision:

```
906367250a7f96c923147b10df392294bced7be5
```

Research date: 14 November 2026 (UTC). The source collection contains the 13 November research archives. The original repository was not modified.

## Read first

- `report/report.pdf`: complete report, including the literal 197-state table.
- `report/report.tex` and the adjacent `.tex` fragments: complete editable report source.
- `construction197/README.md`: exact new construction, model, proof scope, and replay.
- `construction197/macro_proof/proof.tex`: independent universal arithmetic proof and exact 18-instruction control-flow graph.
- `audit/ARCHIVE_COMPARISON.md`: all 27 top-level incoming archives, their main contributions, previous search coverage, and limitations.
- `theory/README.txt`: ordinary mathematical PA bridge with explicit implementation/calibration hypotheses, plus a reproduced 196-state closing variant.

## Main results

For Cantor pairing `p(a,b) = (a+b)(a+b+1)/2 + b`, encoded negation is `N(t) = 4*p(t,1)`. The identity `p(t,1) = p(0,t)+2` and the existing core contract

```
(T,S,Y) = (t,s,y)  ->  (4*(y+p(s,t)), 0, 0)
```

give the new clean-scratch implementation:

```
INC register7
INC register7
node64
```

This has 18 primitive source instructions, compared with the original 47 and a prior 20-site direct version. It preserves every unrelated register. The independent source-loop proof covers arbitrary natural inputs; its finite examples are supplementary controls.

Replacing all eight relevant occurrences in the separate-head emitter changes 3,673 source sites to 3,441. The exact new allocation is `134 + 68 - 5 = 197` physical states. The resulting source has an inductively closed 245,112-pair zero/positive abstraction proving both scratch registers zero at every replacement entry. The full blank startup, including every nonzero tape cell, agrees after 58,154 transitions.

The selected archive catalogue contains 22 distinct rooted 196-state graphs: one upstream, 17 manuscript-positive candidates, two experimental MP variants, and two rejected Shift layouts. The rejected layouts both first halt at step 43,563. The complete recursive inventory also includes failed experiments and ancestors; its 402 root-free classes are not 402 proven consistency machines.

## Replay

Python 3.10 or later, with the standard library, is sufficient for the principal checks. Do not run Python with `-O`; some inherited parsers use assertions.

From this archive's root:

```bash
python3 construction197/verify.py --check
python3 construction197/macro_proof/verify.py
python3 audit/verify_selected.py
python3 theory/reproduce.py
```

The first command checks the supplied construction byte-for-byte. Without `--check`, the construction driver regenerates its outputs. The independent macro verifier checks the primitive graph, loop invariants, exact entry-state bindings, whole new source, and scratch closure. The selected-table audit checks table identities and graph classes and replays the two finite blank halts. The theory replay checks the 196-state closing variant, including raw and folded symbolic contracts and exact startup.

The corpus-wide inventory can be regenerated from a checkout at the pinned commit:

```bash
python3 audit/audit_all_archives.py --repo /path/to/ProveIt --output /path/to/census
```

The original ZIP bodies are not duplicated here. Exact identities, archive member paths, and hashes are retained in `audit/inventory/`. Optional prefix/scanner experiments likewise accept their source directories explicitly; their stored receipts identify the inputs. This avoids silently treating the archive as a complete checkout of the large imported formal development.

## Rebuild the PDF

With a normal TeX Live installation containing the standard packages used in the preamble:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Run a third pass if LaTeX requests another pass for page references. The complete PDF is supplied, so a TeX installation is unnecessary for reading it.

## Search artifacts and interpretation

- `search/seven_heads/`: standalone C++17 searches with exact generated headers/JSON inputs, seeds, receipts, and best witnesses; see its README.
- `search/negation/`: arithmetic-mask search sources, fixed inputs, and receipts, with their own instructions.
- `search/physical/`: the portable radius-six/31-step contraction search and compact results of further helper scans.
- `audit/`: independent emitter checks, negative controls, full catalogue, and selected local-search scripts/receipts.
- `theory/experiments/`: finite closing-mode comparisons on archived ties and selected additional layouts.

Search scores are discovery criteria. A low score does not itself verify a physical machine. None of the completed searches establishes that 196 is minimal.

The arithmetic bridge is an ordinary mathematical argument with explicitly stated hypotheses, including exact startup, uniform contracts, source interpretation, and PA-refutation compilation. It is not a new trusted-kernel export. The pinned upstream formal endpoint and the unformalized converse obligation are distinguished in the report and subpackage READMEs.

## Provenance and licenses

The four requested source areas were:

- https://github.com/VladimirReshetnikov/ProveIt/tree/906367250a7f96c923147b10df392294bced7be5/Computability/BusyBeaver/Research/PA
- https://github.com/VladimirReshetnikov/ProveIt/tree/906367250a7f96c923147b10df392294bced7be5/docs/incoming
- https://github.com/VladimirReshetnikov/ProveIt/tree/906367250a7f96c923147b10df392294bced7be5/Computability/BusyBeaver/Research/ZFC
- https://github.com/VladimirReshetnikov/ProveIt/tree/906367250a7f96c923147b10df392294bced7be5/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

Imported materials retain their existing licenses and attribution. Subpackage notices distinguish the ProveIt sources, James Chang's upstream compiler, older generated research contributions, and the additions made in this investigation. Nothing in this archive relicenses upstream work.

`SHA256SUMS` binds the delivered files. The principal dense table's SHA-256 is:

```
15f8b3e96d6adae76236ab0960d288b9537e39294ef1ab65f8fdd2e16dc2a9b6
```

That table has 197 working states, start 0, halt 197, and initially blank binary tape. A machine below 196 states remains the unresolved objective.
