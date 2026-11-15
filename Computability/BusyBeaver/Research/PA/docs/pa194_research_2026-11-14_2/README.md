# Two new 194-state machines for Con(PA)

Research snapshot: **14 November 2026**. ProveIt commit:
`1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

## Result

No blank-start machine with fewer than 194 working states was established.
The requested fallback is supplied as **two materially different 194-state
tables**, each with a written iPRA consistency-equivalence proof using the
explicitly identified latest incoming AX11H/QAX11H mathematical calibration:

    iPRA proves Con(PA) <-> not Halt_blank(M).

The complete written proof is not a newly completed end-to-end Lean theorem.
The inherited calibration is included unchanged, its critical arguments were
reviewed, and its full finite verification suite was freshly rerun. The new
machine-specific symbolic and finite certificates were also run. These
different kinds of evidence are distinguished throughout the report.

| New machine | Working states | Exact blank initialization | Main change |
|---|---:|---:|---|
| PA194AX11QGH | 194 | 57,922 transitions | Eleven-entry, four-operand AX combined with direct-binder generalization and cached-theorem halting; inherited Q head orientation |
| PA194AX11HR | 194 | 48,320 transitions | Ten active routing changes and a different physical allocation of the nine logical registers |

Both use one two-way infinite binary tape, initially entirely zero, with
the head at coordinate zero. Each dense table has working states 0..193,
start 0, halt label 194 with no rows, and 388 transitions. Every transition
writes one bit and moves exactly one cell left or right. The halt label is
excluded from the state count.

Each `.tm` line is:

    state read_symbol write_symbol L_or_R next_state

### Exact dense tables

- `construction/AX11QGH/machine/machine.tm`
  - SHA256 `513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1`
- `construction/AX11HR/machine/machine.tm`
  - SHA256 `b3c07bf7a750e1e9529929ef392fc0543645ccc34a7a39c3360ec41201f0e980`

Native labels, dense/native maps, source sites, source instructions,
construction receipts, exact literal contracts, and local closure audits
are included alongside them. The full dense tables also appear in the PDF.

## Start here

- **`report/report.pdf`**: the complete comparison, both new constructions,
  iPRA proof arguments and dependencies, unsuccessful searches, research
  directions, complete 110-class comparison appendix, and both full tables.
- **`report/report.tex`** and its included `.tex` fragments: the corresponding
  editable report sources. All required report fragments are included.
- **`claims.json`**: machine-readable statement of the result, evidence
  status, exact hashes, scope, and negative-search limitations.
- **`comparison/README.md`**: complete corpus ledgers, exact structural
  novelty replay, proof-status audit, and fresh inherited verification.
- **`construction/AX11QGH/README.txt`** and **`construction/AX11HR/README.txt`**:
  standalone reconstruction and verification instructions.

## What is different

### AX11QGH: a different recurring command interface

With store `(t,w,d,h)`, AX has the exact transformation

    AX(c,x,y,z)(t,w,d,h) = (0, [q0,...,q9,t;w], z, 0),
    D = d+x, H = h+y, q9 = U(c,h).

Its fourth operand is genuinely read. The last generated theorem uses the
explicit binder `c` and the original incoming cache `h`. Shift halts iff its
cached theorem is code 1. Successful MP has no dummy push. The new exact
generalization word is:

    Push; Shift; AX(i,0,0,0); Shift^11.

It works even when the input theorem has code 1. The proof compiler reserves
one zero underneath MP premises and ends a returned contradiction with Pop;
these details preserve the arbitrary underlying stack and handle the
cache-only halt test. The proof includes a bounded primitive-recursive
majorant so its all-store assertion is justified by quantifier-free
induction, rather than an unbounded universal-store induction.

The state accounting is 134 fixed controls + 67 reader controls - 7 compatible
folds = 194. All 28 local fold cases and the final simultaneous table are
checked. The entire source graph is compared with the accepted QAX11H
association after the one binder macro change. Earlier construction logs
use AX11GH as an alias for this exact table; the full name records the
already inherited Q orientation explicitly.

### AX11HR: a different physical register layout

For logical register order `(N,T,W,A,D,H,X,Y,L)`, physical positions change
from `[6,2,0,4,3,7,8,5,1]` to `[6,1,5,7,4,8,2,0,3]`. The arithmetic engine
and source instruction graph stay the same. Ten non-box routing transitions
change, and every changed row is used during blank initialization.

The complete initial frame is reached 9,602 transitions earlier than in
AX11H, a 16.58% reduction for that initialization. This is not a claim of
faster eventual proof enumeration or of globally optimal initialization.
The proof re-establishes all source contracts for the new representation
and composes their explicit positive physical durations in iPRA.

## Verification performed

For **each new table** the independent literal engine rederived four generic
list-sweep lemmas from its actual transitions and checked all **4,778 outcomes
at 3,671 source sites**. Its scope is arbitrary nine natural-number register
values, both decrement outcomes, arbitrary nonempty finite spare lists, and
arbitrary additional header gap. It imports neither the builder nor an
arithmetic-box oracle. Complete finite-support blank-start tape equality,
head, native dispatcher, register values, source address, and spare tail
were checked independently.

The extra endpoint audit checks all 4,777 nonhalting source successors,
zero address overflow, zero affine head motion, nonnegative physical-duration
coefficients, and duration constants at least 3. The unique halting source
outcome has duration exactly 3. These are symbolic contracts, not a bounded
sample of small register values or a long simulation presented as a proof.

The current literal corpus contains 110 catalog classes at 194 states.
Both new tables differ from every recognized class, and from each other,
under arbitrary state renaming, any spanning initial root, tape reflection,
symbol exchange, and ignored terminal write/move actions. Exact canonical
tuples are compared; novelty is not inferred merely from unequal hashes.
Symbol exchange is an additional structural test, not a claim that it
preserves zero-blank semantics. Nonspanning diagnostics are identified
separately and cannot be isomorphic to these spanning tables.

The original AX11H and QAX11H dependency tables were also freshly rebuilt
and fully replayed. This included 1,186 manifest entries, both independent
literal replays, source-command bindings, finite Foundation constructors,
119 current/historical coding comparisons, and premise exchange. The
receipt explicitly says `kernel_checked=false` and
`arithmetic_derivation_checked_by_this_script=false`.

## Reproduce the checks

Use Python 3.10 or later with assertions enabled; do not use `-O` or set
`PYTHONOPTIMIZE`. The construction and comparison checkers use only Python's
standard library. Run these commands from the unpacked archive root:

```sh
python3 -B verify.py
python3 -B verify.py --full --novelty
```

The first command checks every packaged SHA256 identity, reconstructs both
machines, checks complete blank startup and recorded endpoint/duration
bindings, and verifies AX11QGH's command equations. It explicitly skips the
expensive per-site symbolic tape replays. The second repeats those replays
and exact corpus novelty comparisons. Both write `fresh_verification.json`
by default; `--output PATH` changes the receipt path. Neither mode claims
to kernel-check the mathematical proof or to rerun the research searches.
The supplied full-run evidence is already included.

For separate reconstruction and verification commands, see each construction's
README. For the full inherited calibration suite, unpack
`reference/ax11h_written_calibration.zip` and follow its own README. Its exact
original archive is retained, including its TeX/PDF proof, approximately
700 Lean reference files, verification scripts, source pins, and notices.

To compile this report using a standard LaTeX installation:

```sh
make report
```

This runs `pdflatex` twice. The source uses common packages including
`lmodern`, `microtype`, AMS math, `geometry`, `booktabs`, `longtable`,
`tabularx`, `enumitem`, `xurl`, `hyperref`, and `fancyhdr`.

## Comparison scope

The pinned filed catalog has 82 research packets, 13,006 historical literal
table occurrences, and 682 catalog classes. Fresh parsing of the four current
incoming ZIPs contributes 22 further classes, giving 704 total classes.
There are 110 classes at 194 and 53 research classes at 193. These totals
include auxiliary searches, failed candidates, and diagnostics; they do not
mean that every table has the required consistency property.

`comparison/frontier194_ledger.{json,csv}` and the PDF appendix cover all 110
classes. Their mechanisms and reported proof status are attributed, and the
actual scope of the present review is recorded. The filed census is inherited
from pinned manifests; incoming `.tm` files and both candidates' comparisons
were freshly parsed. The scope is explicitly a literal `.tm` census, augmented
by report review, rather than an exhaustive parser for arbitrary code/JSON
expressions of transition tables.

## Searches below 194

- `search/contractions/`: exact inputs, C++17 programs and 22 completed main
  screens on 11 inputs. All 37,442 ordered direct contractions and all 18,721
  unordered pairs with arbitrary rewrites of the kept state's two rows were
  screened per input under the stated local bounds. All were unsuccessful.
  In addition, 302,252 single-row edits produced 422 locally neutral
  preconditions; their 15,800,524 subsequent direct contraction checks also
  found no survivor. The provided positive control recovers a real merge.
- `search/modal_heads/`: two logically equivalent new first-head schemas,
  their proof translations, and 6,666,025 completed grammar-search proposals.
  No design at or below 194 resulted. Best totals 199/202/199 are optimistic
  search scores, not certified machines.
- `search/search_layout.cpp` and its result files: all 40,320 physical
  permutations fixing the initially nonzero register, for both AX11H and
  primary PA194, under a 100,000-transition and fixed-window screen. The
  principal AX11H result is the fully verified AX11HR construction. A faster
  primary-layout result is retained as exploratory evidence only.

These searches concern finite certificate families. They do not establish
194 as a lower bound. The known 193-state runtime splice still fails blank
initialization in the exceptional read-zero case. The report gives precise
remaining synthesis targets and discusses the requested ZFC,
DiophantineConsistency, and ConciseIPRA source areas.

## Provenance and attribution

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot: `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.

Main source areas: `Computability/BusyBeaver/Research/PA`, `docs/incoming`,
`Computability/BusyBeaver/Research/ZFC`, `Computability/DiophantineConsistency`,
and `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA`.

`comparison/source_identity_manifest.json` retains Git blob and SHA256
identities for the source manifests and current incoming archives.
`reference/calibration_provenance.json` identifies the exact unchanged
mathematical dependency. Construction inputs have separate input hashes.
`SHA256SUMS` covers every deliverable file except itself.

Upstream ProveIt, James Chang, and Wade notices are retained with the adapted
code and within the unchanged inherited archive. New work consists of the
combined command design, physical allocation, their preservation proofs,
candidate-specific certificates, fresh comparisons, and stated searches.
The repository was not modified or published.
