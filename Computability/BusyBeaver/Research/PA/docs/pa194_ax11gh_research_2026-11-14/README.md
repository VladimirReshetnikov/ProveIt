# PA194AX11GH and PA194AX11GHS

**Result: two new 194-state binary blank-start machines. No valid sub-194 construction was obtained.**

Read `report/main.pdf`. Its complete LaTeX source, included fragments and generated tables are present. The PDF prints both complete transition tables and all 110 historical 194-state graph classes. The comparison is pinned to ProveIt commit `1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`. A separate late-update audit extends coverage through `19b9ea945cc95fe25535d44d949904843f4a824a`; the later snapshot has the same 110 recognized 194-state graph classes.

Both machines combine the four-operand, eleven-entry AX protocol with an explicit generalization binder, Q-oriented distribution, no-push MP, and a cache-only Shift halt test. The symmetric companion uses a different primitive comparison and an additional contextual fold. Both graphs differ from all 110 prior classes and from one another even under state renaming, arbitrary spanning roots, left/right reflection, global bit exchange, and ignored halt-entry decoration.

## Exact conventions

Each machine has working states 0 through 193, initial state 0, and a separate terminal halt label 194. The head begins at coordinate 0 on an all-zero two-way infinite binary tape. Every transition writes one bit and moves one cell left or right. There are 388 transition rows and no rows for the halt label. All working states are graph-reachable. Native tables use start 74, source-boundary state 84, and halt 254; label maps are provided.

| Property | PA194AX11GH | PA194AX11GHS |
|---|---:|---:|
| Working states / rows | 194 / 388 | 194 / 388 |
| Fixed + readers - folds | 134 + 67 - 7 | 135 + 67 - 8 |
| Primitive source sites | 3,671 | 3,668 |
| Universal source outcomes | 4,778 | 4,774 |
| Exact blank initialization | 57,922 steps | 57,768 steps |
| Independent literal symbolic operations | 1,106,693 | 1,110,639 |
| Independent source-template instances | 947 | 945 |

Dense table SHA-256:

```text
PA194AX11GH  513e9c8b28e0dd41e6003bb8d82c80ff3dac5fb3c5274cd2f709a3bba8c3e9e1
PA194AX11GHS 7a4738a9eedd3f53674d67568b3197d38237d11d0fc08fa3d41251a8faf8052c
```

## Proof scope

The new contribution proves relative preservation in iPRA by explicit command compilation, primitive recursive source clocks, and literal-tape segment proofs:

```text
iPRA proves Halt_blank(AX11GH) iff Halt_blank(QAX11H).
iPRA proves Halt_blank(AX11GHS) iff Halt_blank(QAX11H).
```

The reference is the exact QAX11H table in the updated incoming AX11H manuscript. Composing with that manuscript's written absolute calibration gives, for both new tables:

```text
iPRA proves Con(PA) iff not Halt_blank(M).
```

The absolute PA calibration is an explicit inherited mathematical dependency. It is not an assumption that PA is consistent. The new relative proof does not independently reprove every part of that extensive calibration, and this package does not claim a new end-to-end Lean or Rocq kernel build. All ten inherited mathematical proof fragments and exact calibrated table are included for inspection. The current project's formal status and the updated incoming written claim are distinguished in the report.

The compiler treats Pop as “halt if its saved top is one, otherwise pop,” rather than reusing the parent sum-guard identity. A returned top-one contradiction is detected by `Push; Shift; Shift` (or Pop), since a single Shift with cache zero is insufficient. All four AX fields are included in the candidate encoding. Correctness inductions use bounded primitive recursive Boolean invariants, not unbounded all-store induction formulas.

## Verification and reproduction

Python 3.10+ and the standard library suffice. Keep assertions enabled:

```sh
python3 -B verify_all.py
```

The full replay rebuilds both literal tables, reruns the construction contracts and independent literal contracts, rechecks every source instruction and outgoing edge against independent arithmetic templates, checks symbolic commands, verifies source-frame closure and positive exact durations, and repeats the complete 110-class novelty comparison. Fresh literal contracts must match the retained bytes. No original checkout, network, Lean installation or third-party Python package is required.

```sh
python3 -B verify_all.py --quick
```

Quick mode explicitly skips the expensive construction and independent literal replays while checking retained certificate bindings and all other checks. It is useful for delivery integrity, and is not described as a full literal rerun. Both modes write to a fresh directory; `--output PATH` selects one.

The late repository supplement can be checked separately, using its default adjacent baseline directory:

```sh
python3 -B comparison_latest_head/verify_latest_head.py
```

Its retained full receipt also includes the Git relocation and retention checks. Those optional Git checks require both repository snapshots; the graph and archive replay above runs offline.

The source frame permits nine arbitrary natural register values, both decrement branches, arbitrary nonempty finite spare files, and an arbitrary affine nonnegative header gap. The independent checker imports no constructor or arithmetic-box oracle: four generic list lemmas are rederived from the actual transition rows. Whole finite-support startup tapes are compared exactly. A separate audit checks every nonhalting padded endpoint and all duration vectors.

`SHA256SUMS` covers the final deliverables. To rebuild the PDF in a standard TeX installation:

```sh
cd report
python3 generate.py
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Comparison and unsuccessful searches

The fresh inventory checked 10,495 tracked source payloads without missing blobs and covers 82 filed deliveries plus all four current incoming archives. It records 110 distinct 194-state spanning graph classes, including rejected and diagnostic tables. Every historical class has a representative, mechanism, exact source location and attributed status. The 53 encountered 193-state graph classes are not accepted consistency machines.

The late-update supplement in `comparison_latest_head/` verifies that all 869 newly filed files match the original incoming ZIP members. Its one additional retrospective frontier archive adds no new graph class. The later snapshot therefore has 87 deliveries (86 filed and one incoming), while the original 86-delivery ledger stays pinned to its baseline. The older frontier report does not audit the stronger updated AX11H written calibration.

New reduction work includes 10,441,656 targeted two-row repair specifications, conservative control-merger and state-elimination screens on AX11GH, a sound zero/positive register analysis, and 5,492,757 joint grammar/permutation proposals across the two new fixed parts. No accepted sub-194 candidate emerged. A transplanted ZFC marker relay has an exact 117-step outward-ray counterexample. Nine other bounded startup exits are explicitly not treated as divergence proofs. These results impose no global state lower bound.

`research/physical/README.md` and `research/grammar/README.md` give optional C++17 search commands and exact scopes. The positive machines do not depend on repeating stochastic searches.

## Attribution

The PA runtime, numerical calculus, existing state reductions, source compilers and logical calibration are inherited from the supplied ProveIt packets and their cited authors, including James Chang and the credited runtime authors. Original licenses are preserved. `PROVENANCE.json`, the per-directory notes and the reference audit identify the copied material and new adaptations. The contributions here are the exact AX11GH/GHS compositions, their adjusted command/source proofs, complete binding checks, current comparison and the recorded new searches.
