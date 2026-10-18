# A 250-state ZFC consistency machine

This package gives an exact **250-working-state, two-symbol, one-tape Turing machine starting on a completely blank tape**, together with an ordinary mathematical proof and executable finite certificates for

\[
\mathrm{ZFC}\vdash
\bigl[\neg\operatorname{Halt}(M_{250},\mathrm{blank})
\leftrightarrow\operatorname{Con}(\mathrm{ZFC})\bigr].
\]

The complete argument is in [report.pdf](report.pdf) and [report.tex](report.tex). **The exact 250-state endpoint has not been newly checked by a Lean or Rocq kernel.** The report identifies the inherited formal results, proves the new operation and simulation arguments, and explains the specific set-coded ZFC composition. It does not supply a serialized first-order ZFC derivation or the repository's stronger internal PA formalization.

The prefix-carry and pulse-retiming lead was recovered from earlier working research for this task. Its retained source is under [sources/prior/](sources/prior/). This package freezes the resulting machine against the current repository, independently reconstructs and audits it, and supplies the detailed proof composition. It does not claim that the idea was discovered in this audit or establish worldwide priority.

## Exact machine

| Artifact | Interpretation | SHA-256 |
|---|---|---|
| [machine/zfc_prefix250.tm](machine/zfc_prefix250.tm) | Working states 0–249; start 0; separate halt label 250 | `0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e` |
| [machine/zfc_prefix250_old.tm](machine/zfc_prefix250_old.tm) | Original labels; start 97; halt 254 | `fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43` |
| [machine/renumbering.json](machine/renumbering.json) | Exact bijection between the two tables | `ecfd4cd23ab90a4050189b21a79b1fc6a33e5e8d70ad47d9b5416afa056f222a` |

The tape is indexed by the integers; every cell initially contains 0, and the head starts at coordinate 0. Each row has the form `state read write L-or-R successor`. The final write and movement into halt are retained. There are **500 transition rows and one halting transition**. Both input rows of every working state are present; initialization uses the same counted table.

Starting with ProveIt's original-label permutation252 table, the reconstruction deletes states 43, 59, and 85, modifies seven surviving rows, and adds two rows for state 255. Hence the count is `252 - 3 + 1 = 250`. The complete nine-row recipe appears in the report and [code/rebuild_machines.py](code/rebuild_machines.py); every other surviving row is unchanged. The baseline already omits labels 5 and 8. [results/rebuild.json](results/rebuild.json) records the exact table census and source identities.

## Mechanism and bootstrap

The logical proof search and its register permutation are preserved. The saving comes from sharing a carry circuit between register operations: a positive decrement shifts the register prefix right by one; a zero test rolls that prefix back; increment appends a harmless spare block of value 1. A temporary tape bit distinguishes runtime entry into state 97 from its blank-tape entry, making its read-zero transition available for initialization.

After exactly **585,431 literal transitions**, the final machine reaches original state 96, head −3, marker −4, and header 225. The program counter is empty. Its first nine physical register values are `(0,2,0,4,0,0,1,0,0)`, followed by 210 spare blocks of value 1. Thus its logical registers are

```text
(N,T,W,A,D,H,X,Y,L) = (1,0,0,0,4,0,0,0,2).
```

The complete final tape has 438 one-cells, all listed in [results/pulse-bootstrap.json](results/pulse-bootstrap.json). Every other cell is blank. This root satisfies the inherited safe dirty-start theorem: the top and retained formula are truth, and the stack is empty; the six numerical fields are allowed to be arbitrary.

The recurrent invariant requires a clean program counter, total head-to-header distance at least 40, and at least one spare block. Increment appends a spare, and the other operations preserve the suffix. Positive decrement and program-counter overflow increase the available distance. These conditions therefore hold for arbitrarily long runs, without a finite-capacity assumption. The report distinguishes the physical spare suffix from logical registers at indices at least 9, whose encoded values remain zero.

## Reproduce

From the package root, using Python 3 with its standard library:

```sh
python3 -B code/verify.py
```

The verifier uses the bundled inputs, performs no network access or search, and writes its check results under `results/`, with a consolidated record in [results/verification-summary.json](results/verification-summary.json). The included record has all nine checks passing. Do not run it with Python's `-O` option: assertions are part of the checks. To rebuild the PDF with a TeX installation containing the packages listed in `report.tex`, run:

```sh
make pdf
```

This runs pdfLaTeX twice. `make verify` runs the Python verifier. Individual mathematical checks can also be run from the package root:

```sh
python3 -B code/rebuild_machines.py --check
python3 -B code/check_macro_inductions.py
python3 -B code/check_instructions.py
python3 -B code/check_pulse_boot.py
python3 -B code/audit_marking_transport.py --baseline sources/baseline252_old.tm --candidate machine/zfc_prefix250_old.tm --output results/marking-transport.json
python3 -B code/verify_retiming_independent.py --table machine/zfc_prefix250_old.tm --output results/retiming-independent.json
```

## What the evidence establishes

| Layer | Evidence and scope |
|---|---|
| Current source identity | [results/current-source-audit.json](results/current-source-audit.json) compares 56 included maintained source files with immutable GitHub blob identities at the ProveIt pin. This identifies the source; it is not a proof-assistant build. |
| Register operations | The word-induction proofs and [results/macro-inductions.json](results/macro-inductions.json) cover arbitrary register values and finite block lists. The executable induction checker uses literal rows, unary-loop induction, list induction, and explicit word identities. |
| Marking | [results/marking-transport.json](results/marking-transport.json) checks all 24 supporting rows. The accompanying block proof covers all nine physical selectors and arbitrary exterior contexts. |
| Pulse retiming | The local identity checks both possible probe symbols, its exact read/write footprint, and the incoming-edge premises. The report proves the resulting unbounded comparison and the one-time use of initialization. |
| Complete instructions | [results/instructions.json](results/instructions.json) covers all 6,460 leaves and 8,391 guarded cases, reparsed from all 6,459 program nodes. It is uniform in nonnegative extra distance, the primary values satisfying the named guard, and every nonempty finite spare suffix. Every case has positive literal progress. |
| Literal regressions | [results/literal-macros.json](results/literal-macros.json) records 16,200 cases and 8,359,100 transitions; [results/literal-instructions.json](results/literal-instructions.json) records 33,564 cases and 14,197,744 transitions. These detect implementation errors. They are finite tests, not the justification for the universal statements. |
| Global and logical endpoint | The report combines complete-frame preservation and induction on finite halting time with `Bisim254`, `DirtyProgram254`, and the inherited native/ZF/ZFC calibration. The ZFC argument uses set-coded completeness, the internal well-founded subdomain, and the internal constructible subdomain. |

The symbolic checker is ordinary Python with an explained mathematical semantics. A successful run is not being represented as a new Lean or Rocq kernel result. The supplied Lean sources are reference snapshots; their complete proof-assistant dependency closure is intentionally not bundled, and this package does not claim to rebuild the inherited endpoints.

## Sources and attribution

The maintained reference revision is [ProveIt `80e26b89e905bf3e5dfc322befdc1c6eaf25a109`](https://github.com/VladimirReshetnikov/ProveIt/tree/80e26b89e905bf3e5dfc322befdc1c6eaf25a109). The supplied `zf-254` branch of [jeff87654/busy-beaver](https://github.com/jeff87654/busy-beaver/tree/c132d7eae8158cd3a9850ea3eb7251158c3dd821/ZF/m254) was pinned at `c132d7eae8158cd3a9850ea3eb7251158c3dd821`; ProveIt's attributed upstream import is `297ab8df7e5de329605c3875b4934643b371a5e3`. Mira-emmy's [public 253-state reduction, PR 20](https://github.com/jeff87654/busy-beaver/pull/20), is pinned at head `0d544f2a2e3c18f12278441a74b7879f31cbe856`.

Mira-Cult designed the original machine and compact calculus; Jeff Ketchersid supplied its verification; Andrew James Wade supplied the compiler framework. The public 253-state reduction, ProveIt's physical permutation and formal developments, and the earlier working prefix/pulse research retain their respective attribution. The strict affine checker descends from the attributed source-27 development. See [PROVENANCE.json](PROVENANCE.json), the preserved [upstream attribution](sources/research/upstream-attribution.md), and [licenses/](licenses/). Preserving these files does not relicense the upstream snapshot.

## Integration next steps

The package can be incorporated as a research construction and its reproducible audit. A closed formal endpoint for this exact 250-state table still requires porting the new register identities, strengthening the spare invariant, adding the one-cell boundary effect to the symbolic file rule, regenerating all instruction proofs, and kernel-checking the new blank prefix. The generic dirty-root theorem and identified calibration can then be composed with those binary results.

The displayed ZFC equivalence is the mathematical claim of the report. Unconditional nonhalting, a proof of `Con(ZFC)`, state-count minimality, and a bound for 249 states are not established. Under consistency, Gödel's second incompleteness theorem excludes a ZFC proof of this nonhalting statement; full two-sided independence requires an appropriate additional soundness assumption, as explained in the report.
