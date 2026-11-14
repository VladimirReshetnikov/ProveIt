# PA194HS: a different 194-state PA-consistency machine

**Result:** This package constructs **PA194HS**, with **PA194H** as a second
literal implementation. Both have 194 working states. **No machine below
194 states was established.**

The ordinary mathematical result, using the explicitly retained inherited
syntactic PA calibration, is

    PA proves: Nonhalting(M, blank tape) iff Con(PA).

The new contribution is the combination of **no-push MP returning its result
in the visible top** with **Shift testing only the cached head**, its complete
proof-word compiler, and two freshly verified literal realizations. PA194HS
uses symmetric comparison. The component optimizations are credited to the
supplied research; they are not claimed as new individually.

## Read first

- `report/main.pdf`: complete report, mathematical proof, corpus comparison,
  negative-search analysis, full primary transition table, 46-packet ledger,
  and all 28 prior 194-state graph classes.
- `report/main.tex` and its local TeX inputs: complete article sources.
- `machines/PA194HS/machine.tm`: primary transition table.
- `machines/PA194H/machine.tm`: companion transition table.
- `RESULTS.json`: exact counts and evidence boundaries.

The two ordinary mathematical PA proofs use the inherited numerical-calculus
calibration preserved in `references/logical/`. This release does **not**
claim a newly compiled end-to-end Lean or Rocq theorem, a completed
machine-specific iPRA reduction, or a global state-count lower bound.

## Machine convention and hashes

Both tables have working controls 0 through 193, initial control 0, and a
separate terminal halt label 194. The tape is binary, two-way infinite, and
initially all zero. The head begins at coordinate zero. Each of the 388 rows
has format `state read write L-or-R next-state`; halt has no outgoing row.
No preloaded program or additional initialization machine is assumed.

PA194HS dense SHA-256:

    19935635f2c5722f5a72977d20a7019764a28573e12d1d0bce398245576c33b1

PA194H dense SHA-256:

    3276a34fd0388102dad87a8b12c70e88b2bcccf6b068cb034ce78d33536adcc1

Native tables instead use start 74 and halt 254. `labels.json` binds them
exactly to the dense tables, including the terminal label.

| Verified quantity | PA194H | PA194HS |
|---|---:|---:|
| Working states / transition rows | 194 / 388 | 194 / 388 |
| Source sites | 3,653 | 3,650 |
| Universal source outcomes | 4,754 | 4,750 |
| Independent symbolic steps | 1,097,251 | 1,101,153 |
| Maximum independent case | 403 | 403 |
| Minimum positive-duration constant | 3 | 3 |
| Exact blank initialization | 57,922 | 57,768 |

The independent checker rederives four register-list lemmas from literal
transition rows. Contracts cover arbitrary natural registers, both
decrement branches, arbitrary affine header gap, and arbitrary nonempty
finite lists of natural spare values. Startup compares the whole tape,
head, control, register blocks, spare blocks, and zero exterior.

## Reproduce without a checkout or network

Python 3.10+ and its standard library suffice. Keep assertions enabled.

    python3 verify.py
    python3 verify.py --full

The default reconstructs both tables, checks all construction contracts,
exact startup, complete source splices, symbolic command identities, recorded
independent bindings, provenance, and exact corpus novelty. The full option
also reruns the independent literal-tape engines and compares their complete
results byte for byte. New evidence goes to a temporary directory; release
files remain unchanged. Use `--receipt /absolute/path/result.json` to save a
separate replay receipt. `verification/release_check.json` records the fresh
full release replay.

To repeat the unsuccessful reduction experiments:

    cd search
    python3 verify_reductions.py
    python3 verify_reductions.py --search-merges

These check the rejected shortened scanner, its finite alignment witness,
and two 62,073-candidate state-sharing searches. Their scope and fuel limits
are explicit in `search/SUMMARY.md`. A failure to close a symbolic contract
within a bound is not a proof of nonhalting or a general lower bound.

To regenerate the article's data tables and PDF:

    cd report
    python3 generate_tables.py
    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex

The report uses standard TeX Live packages listed in its preamble.

## Comparison and provenance

The comparison is pinned to

    VladimirReshetnikov/ProveIt
    1e407ae841e4666f932777fad977ba784ebbcfd5

It covers 41 filed packets and five current incoming archives. The literal
census recognizes 3,741 occurrences, 666 byte forms, and 476 root-spanning
action graphs, including research and rejected objects. At 194 states there
are 51 byte forms in 28 action-graph classes. Both new graphs are absent even
after arbitrary working-state renaming, choice of spanning root, tape
reflection and global bit exchange. The comparator compares full tuples,
not only hash values.

The recognizer accepts complete numeric tables in `.tm`, `.txt`, `.tsv`, and
`.csv` and recursively inspects ZIPs. It visits identical ZIP payloads once.
Source-only or JSON-only encodings are outside the literal count; packet
descriptions are separately covered by the ledger. Full census inputs and
scope are preserved under `comparison/`. The ledger records prior claims;
it does not assert that every historical theorem was independently reproved.

Five reports repeat the same principal PA194C table. The latest PA194X is
byte-identical to the earlier PA194CSZ. These are accounted for in the current
comparison, which uses a later snapshot than the supplied packets' own audits.

`PROVENANCE.json` binds the 26 unchanged inherited inputs and identifies all
adaptations. Original licenses are retained alongside copied source and
runtime files. `SHA256SUMS` binds the release's complete contents other than
the manifest itself. The theoretical proof review is in
`verification/hybrid_review.md`.
