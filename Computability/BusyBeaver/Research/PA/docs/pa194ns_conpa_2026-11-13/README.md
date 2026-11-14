# PA194NS: a different 194-state PA consistency machine

**No machine below 194 states was established.** This packet supplies the
requested fallback: a materially different, fully specified **194-working-state**
binary Turing machine and an ordinary mathematical proof of

```text
PA proves: not Halt(PA194NS, blank tape) if and only if Con(PA).
```

The proof retains the supplied numerical-calculus/PA calibration and gives a new
complete command compiler, exact source binding, two symbolic physical audits,
and complete blank initialization. It does **not** claim a new end-to-end Lean or
Rocq theorem, a completed iPRA consistency equivalence, or state minimality.

## Read first

- `report/pa194ns_report.pdf`: the construction, full command proof, comparison,
  explicit transition table, all 28 old 194-state graph classes, and 46-packet ledger.
- `report/pa194ns_report.tex`: complete editable report, with all local TeX inputs.
- `machine/machine.tm`: the authoritative dense transition table.
- `RESULTS.json`: machine identities, verification results, scope and provenance.

## Exact machine

The single tape is two-way infinite and initially zero everywhere. The head
starts at coordinate zero in state 0. Working controls are 0 through 193;
terminal label 194 has no outgoing row. Every transition writes a bit and moves
one cell left or right. There are 388 rows in this format:

```text
state read_symbol write_symbol L_or_R next_state
```

Dense table SHA-256:

```text
19935635f2c5722f5a72977d20a7019764a28573e12d1d0bce398245576c33b1
```

The native presentation starts at 74 and halts at 254. Its SHA-256 is
`0b72fc7decfe10ffe30c967f59ddfc570bc7f92177f67b72735b82a0d2fe9fb8`.
`machine/labels.json` maps dense labels to native labels, including halt.

## What changes

Relative to PA194CS, the single native row `(164, 1)` changes from `1 R 130` to
`1 R 114`. Successful modus ponens now returns the consequent in the current
top, retains its numerical offset, and does not push a dummy zero. Shift tests
only the cached formula. The source has 3,650 sites and 4,750 outcomes.

The composition needs a new proof compiler. A plain Shift can discard a current
top equal to contradiction. The compiler reserves the needed zero on its own
stack and uses `AX(0,0,0); Shift^11` to detect a false current top. The proof
handles arbitrary carried stores and the numerical aliases `[0;0]=0` and
`I(0,0)=0` explicitly.

The count is `135 fixed + 67 AX readers - 7 AX folds - 1 controller fold = 194`.
The eight simultaneous folds have 32 checked local cases. This table is absent
from all 51 prior 194-state byte forms / 28 graph classes, allowing control
renaming, every spanning start root, reflection, and global bit exchange.

## Observed checks

| Check | Result |
|---|---:|
| Source sites / outcomes | 3,650 / 4,750 |
| Construction symbolic steps / maximum per outcome | 1,514,674 / 508 |
| Independent symbolic steps / maximum per outcome | 1,101,153 / 403 |
| Minimum physical-duration constant | 3 |
| Generic literal list lemmas rederived independently | 4 |
| Simultaneous local fold cases | 32 |
| Exact blank-to-source initialization | 57,768 transitions |

Both physical checks cover arbitrary natural primary registers, both decrement
branches, an arbitrary header-gap parameter, and an arbitrary finite nonempty
spare list. The independent implementation reconstructs the new source by an
address splice, checks two CFG resolvers, and derives its list lemmas from the
literal rows. These are symbolic universal checks, not bounded samples.
The trusted symbolic rules and ordinary arithmetic arguments are explained in
the report; successful Python execution is not a proof-assistant theorem.

## Reproduce

Python 3.10+ and its standard library suffice. Do not disable assertions.
The default verification runs both physical symbolic implementations:

```sh
python3 -B verify_all.py
```

The quicker check omits those two long symbolic replays. It still checks release
integrity, construction and exact source/table identities, 32 local fold cases,
whole startup, symbolic command identities, and graph novelty:

```sh
python3 -B verify_all.py --quick
```

Fresh receipts go into a new temporary directory. Use `--work NEW_DIRECTORY` to
choose it; the directory must not already exist. Recorded evidence is retained
under `construction/recorded`, `verification/recorded`, `proof`, and `comparison`.

Individual checks:

```sh
python3 -B construction/build.py --output /tmp/pa194ns-construction
python3 -B verification/check.py --output /tmp/pa194ns-independent
python3 -B proof/check_commands.py --output /tmp/pa194ns-commands.json
python3 -B comparison/check_novelty.py machine/machine.tm
```

`verify.py` is the retained construction-stage entry point; `verify_all.py` is
the complete release check described above. To rebuild the report, run twice:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error pa194ns_report.tex
```

Regeneration can change elapsed times or PDF metadata. Verify `MANIFEST.json`
before regenerating files. The accepted machine does not depend on repeating
any heuristic discovery search.

## Corpus and limitations

The comparison is pinned to
`VladimirReshetnikov/ProveIt@1e407ae841e4666f932777fad977ba784ebbcfd5`.
It covers 41 filed packets and five incoming archives, with 3,741 recognized
literal-table occurrences, 666 byte identities, and 476 action-graph classes.
The 28 old 194-state graph classes include 16 reported principal designs, six
supplementary designs, three research seeds, and three rejected experiments.
The corpus count is not a count of valid consistency theorems. In particular,
the differently named PA194X and PA194CSZ have exactly the same dense bytes.

The scanner recognizes complete numeric binary tables in `.tm`, `.txt`, `.tsv`,
and `.csv`, including nested ZIPs; arbitrary encodings found only in code or prose
are outside that literal-table count. All 46 packet narratives are represented
in the ledger. Historical proofs were reviewed and compared, not all replayed.

Optional searches in `research/` produced no verified 193-state machine. Their
time, window and template bounds are documented, and imply no lower bound.
The report also explains why a direct scanner deletion fails a legal source
contract and why a top-only Shift alternative uses 195 states.

## Attribution

This work preserves the source/compiler and arithmetic-calibration attribution
to the supplied ProveIt research, the imported James Chang development, and the
inherited runtime authors. No-push MP, symmetric Shift, known-zero closing, and
the primary AX grammar are supplied ideas. The new result is the exact PA194NS
composition and its complete verification/proof interface. Notices and licenses
are retained in `licenses/` and beside reference code; `PROVENANCE.json` and the
comparison ledger identify the pinned inputs. No changes were published to the
external repository.
