# PA consistency machines: comparison and reduction experiments

**The requested construction with fewer than 196 working states was not obtained.**
This archive contains a complete comparison of the supplied designs, two new
verified 196-state variants, and a shorter logical source program with a verified
203-state implementation. It makes no minimality claim for 196.

Start with **report.pdf**. Its full editable source is **report.tex**, with the
included TeX chapters and transition-table appendix.

## Positive machine artifacts

All machines are deterministic binary one-tape machines with a tape infinite in
both directions, start state 0, and an all-zero initial tape. A halting control
label is additional to the working-state count.

| Table | Working states | Halt label | Source sites | Uniform contracts | Exact blank startup |
|---|---:|---:|---:|---:|---:|
| `sources/BusyBeaver/data/pa196.tm` | 196 | 196 | 3,812 | 4,959 | 58,154 |
| `comparison/audit/rebracketed196_dense.tm` | 196 | 196 | 3,812 | 4,959 | 58,154 |
| `comparison/audit/h_catalan_node170_3_133_37.tm` | 196 | 196 | 3,811 | 4,958 | 57,922 |
| `comparison/audit/integrated_gate206_dense.tm` | 206 | 206 | 3,745 | 4,872 | 59,164 |
| `comparison/audit/integrated_gate203_dense.tm` | 203 | 203 | 3,745 | 4,872 | 58,154 |

The startup count is the literal number of tape transitions to the complete
initial source frame. Source sites, source contracts, macro tokens, and physical
working states are different quantities. In particular, the shortened AX word
has **196 macro tokens**, which is **not a 196-state construction**.

Each noncomment line of a `.tm` file has five fields:

```text
current_state scanned_symbol written_symbol direction next_state
```

Direction is `L` or `R`. Both scanned-symbol rows are present for every working
state. The distinguished halt label has no outgoing rows. The integrated-gate
tables use **state 196 as an ordinary working state**; their halt labels are
**206** and **203**, respectively.

## Reproduce the release checks

Python 3.10 or newer and its standard library are sufficient:

```sh
python3 verify_release.py
python3 -O verify_release.py
```

The release checks cover pinned input hashes, exact source reconstruction,
unchanged unbounded-engine rows, every symbolic source contract, full blank-tape
startup configurations, simultaneous reader folds, complete state relabelings,
the 20-class census of accepted 208-state graphs, and the retained negative
counterexamples. The script writes `receipts/verification.json` and prints an
explicit statement that no verified sub-196 construction is claimed.

The symbolic register file and padding represent arbitrary natural values;
these checks are not bounded register sampling. Four register-engine summaries
rely on the corresponding published unbounded runtime lemmas. The new proof
arguments are mathematical proofs with primitive-recursive proof recipes.
**No new Lean build or kernel-checked formalization was performed.**

The comparison reproduces the finite graph and helper checks for the old 208
tables. It does not rerun every older package's full symbolic proof development.

## Contents

- `report.pdf`, `report.tex`, and the included TeX chapters: complete report.
- `transition_table.tex`: every row of the new rebracketed 196-state table.
- `comparison/audit/inputs/`: all 27 designated 208-state presentations, the
  published 209/196 tables, helper baselines, and provenance manifest.
- `comparison/audit/`: audited graph classes, new dense tables, source-site
  files, startup and conjugacy receipts, comparison and independent interpreters.
- `verification/`: symbolic source verifier, grammar compiler, and selected
  accepted/rejected candidates.
- `math_reduction/`: the PA-internal converse argument, integrated-witness proof,
  exact macro-word construction, compatible-fold certificates, and search tools.
- `reduction196/`: local reduction searches, abstract grammar MILP, binarizers,
  and scoped result receipts. The MILP research tools additionally require SciPy;
  they are not dependencies of the release verifier.
- `sources/BusyBeaver/`: pinned upstream source snapshot, including the Lean
  statements used to justify the tape engine and command language.
- `sources/ProveIt_reference/`: selected referenced ConciseIPRA material with
  exact provenance.
- `source_pins.json`, `input_hashes.json`, `SHA256SUMS`: revision and file identities.
- `licenses/`: upstream MIT and MIT-0 license notices.

Files retained under research directories can be incomplete or explicitly
rejected. Their existence does not make them positive constructions. The table
above and `receipts/verification.json` identify the positive release results.
In particular `warm_physical_61_8047.tm` is a rejected 195-state candidate with
an exact four-step cycle on a valid source frame. Historical search scores in
filenames are not certified state counts.

## Main findings

The 27 accepted 208-state presentations form 20 rooted, action-preserving graph
classes. The nine original presentations form only two such classes and use the
same one-state reduction of historical native states 172 and 211. Both states
are already absent from PA196, so the old deletion cannot be applied again.

The new rebracketing leaves all primitive instructions and their ordinal control
graph unchanged. Its pure 202-state reader table is reduced by six compatible
context folds, with all 24 local cases verified simultaneously.

The h-only variant changes five literal rows and removes one source instruction.
The report proves preservation of the consistency-search property by an explicit
translation of finite command executions.

The integrated equality-witness gate derives the old standalone fifth head from
the modified gate. It has primitive-recursive proof translations in both
directions. The exact AX edit removes 67 primitive sites, but its verified
best verified physical compilation presently has 203 states.

The PA-internal converse is established by interpreting membership as binary-bit
membership, using finite-comprehension proof templates available in full PA, and
translating a finite numerical-calculus refutation to a PA refutation. This is a
syntactic proof argument, separate from the upstream external soundness theorem.

No search timeout, failed local family, or integer-program bound is presented as
a proof that a sub-196 machine cannot exist.

## Rebuild the PDF

On a standard TeX Live installation:

```sh
pdflatex report.tex
pdflatex report.tex
```

Alternatively:

```sh
python3 build_report.py
```

The helper uses the normal installed format when available. On the execution
environment's incomplete TeX cache, it builds a local format from installed
sources and does not change the global TeX installation. It requires the
standard packages named in `report.tex` and Latin Modern fonts.

## Pinned sources

- BusyBeaver PA196: `407cdc356f6b586635e71ac92be394255f4bfea4`.
- BusyBeaver PA209: `69d98241a721ead20b4f0b17df9062950b40fbfe`.
- ProveIt incoming and ConciseIPRA: `6ce5acc401f0c84be90dc5c38dc1487e391122c6`.

The report supplies immutable GitHub links and the manifests identify individual
files. Upstream source notices are retained. New report text and research scripts
in this archive may be reused under the MIT license in `LICENSE`.
