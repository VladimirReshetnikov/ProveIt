# K215-R41: a rebalanced 215-state ZFC-consistency machine

This packet supplies a **materially different 215-state binary Turing machine**. It changes 19 transition rows and 4,120 source addresses relative to the pinned primary K215; maximum address depth falls from 47 to 41. Its rooted, action-preserving transition graph is not a state renaming of the primary, commands120, or composed 215-state graphs. No 214-state construction is claimed.

At the ordinary mathematical proof level of the accepted ProveIt K215, the new source bisimulation, complete symbolic runtime derivation, and exact blank prefix give

\[
\mathrm{ZFC}\vdash \neg\mathrm{Halt}(\mathrm{K215\text{-}R41},\mathrm{blank})
\leftrightarrow \mathrm{Con}(\mathrm{ZFC}).
\]

The numerical-calculus/ZFC reduction is inherited, with explicit pinned references. This packet does not claim a new proof-assistant kernel endpoint, an internal-PA certificate, an unconditional nonhalting proof, or a state-count lower bound. The formalism experiments in `research/` are separate and do not supply assumptions to the main result.

## Start here

- `K215_Rebalanced_Report.pdf` — complete report, proof structure, exact patch, verification scope, formalism experiment, and search boundaries.
- `K215_Rebalanced_Report.tex` — editable LaTeX source; includes the formalism supplement and the supplied figure PDF.
- `machine/k215r.tm` — complete dense machine: working states 0–214, start 0, halt 215.
- `machine/k215r.native.tm` — the same machine in native sparse labels: start 0, dispatcher 84, halt 254.
- `machine/sites215r.json` — all 4,751 source leaves, in ordinal order.
- `verification/independent_review.md` — independent finite review and audit of the actual runtime records.

The tape is two-way infinite, initially all zero, with the head at coordinate zero. Each row is `state read write L-or-R next-state`. The state count includes initialization and excludes the separate halt. Native dispatcher 84 corresponds to dense state 23.

## Main measurements

| Quantity | Primary K215 | K215-R41 |
|---|---:|---:|
| Working states | 215 | 215 |
| Transition rows | 430 | 430 |
| Distinct source subtrees | 202 | 202 |
| Primitive occurrences | 4,751 | 4,751 |
| Guarded primitive cases | 6,176 | 6,176 |
| Maximum address depth | 47 | **41** |
| Sum of address lengths | 160,305 | **149,265** |
| Maximum zero run | 6 | 6 |
| Exact blank initialization | 95,714 steps | 95,714 steps |

The address sum decreases by 11,040 bits, or 6.8869%. This is a static encoding improvement, **not a uniform runtime speedup**. For corresponding primitive cases, duration constants decrease in 1,427 cases, increase in 3,827, and stay equal in 922; nonconstant coefficients are unchanged. The unweighted sum of constant differences is +15,528.

## Exact identities

```text
native SHA-256  8cfb95be77f8f8819ac7dc5c92297cf32b5104cbdf22aea925ab38de9c4443b9
dense SHA-256   27a2a4f452f9fcb1e84ba6f78d0f952ea438eca00d415cc6b0ef4298d35086a4
source SHA-256  46ab3fdabc6ade3c6e4b5f08a0a59af66eb96f3992124ab6b71b8c3f1a05bf35
```

The repository baseline is pinned at commit `75716498437bfc7291d5900cab2983a11fd54bac`. Copies of the exact primary source and table and two comparison tables are included. `baseline/README-upstream.md`, `baseline/proof-upstream.md`, `baseline/command-calibration-upstream.md`, and `baseline/dominated-calibration-upstream.md` retain the predecessor exposition. Relative links inside those unchanged upstream texts may refer to other files in the pinned ProveIt tree; see `baseline/UPSTREAM.md` for permanent URLs. The packet does not duplicate the entire predecessor logical-calibration development.

## Reproduce the accepted machine checks

Use Python 3.10 or later, with assertions enabled. The main checks use only the standard library and require no network, optimizer, or repository checkout. From this packet's root:

```bash
python3 -B code/verify.py --quick --output /tmp/k215r-quick-new
python3 -B code/verify.py --output /tmp/k215r-full-new
python3 -B code/review_depth41.py --packet . --output /tmp/k215r-independent-new.json
```

The first command rebuilds the candidate from the ten-step recipe, checks exact bytes and state count, compares canonical graphs, and executes the complete blank prefix against an independently constructed expected tape. The second additionally rederives all 6,176 symbolic runtime cases. Use a **fresh output directory** for each `verify.py` run. The saved complete symbolic run took approximately 134 seconds in the research environment; other machines may differ.

The third command is a separate implementation of finite reconstruction and an audit of the saved actual runtime records. It independently resolves source control flow twice, replays every internal decoder prefix, checks every saved blank transition, compares the native/dense graphs and accepted alternatives, and checks case order, input/code hashes, positive clocks, four block traces, and row coverage. It is not an independent reimplementation of the entire symbolic induction checker.

The saved runtime status is `UNIVERSAL_MATHEMATICAL_PASS`: all 6,176 cases passed, using 1,640,317 symbolic rules; the minimum affine duration constant is 6. The quantified contracts cover arbitrary natural registers at each guard, arbitrary natural gap, nonempty arbitrary finite spare lists with natural entries, and the whole zero exterior. This is executable ordinary mathematical proof machinery, not a proof-assistant kernel check.

The exact blank endpoint is native dispatcher 84, head −8, header 57, gap one, logical registers `[4,0,0,0,0,0,0,0,0]`, forty spare values all one, and exactly 95 one-cells with every other cell zero. The inherited command compiler handles the finite enumeration cutoff four.

## Research supplements

| Directory | Concrete result | Remaining boundary |
|---|---|---|
| `research/formalism/` | Late matrix inflation removes 13 source primitives; ordinary FOL padding lemma and raw-code reset block | Native atomic-vacuity/ZFC lower bridge open; 206 source subtrees; no accepted binary allocation |
| `research/source/zero5/` | Exact word/CFG-equivalent source with maximum zero run 5 | 205 subtrees; restricted allocation failed; no smaller machine |
| `research/source/register-swap08/` | N/L-exchanged interpreter passes all runtime cases | Blank run halts after 15,607 steps; excluded as a consistency candidate |
| `research/spares/` | Increment appends zero-valued spare; all runtime cases pass with that contract | Blank run provably diverges into an outward ray after 78 steps; excluded as a consistency candidate |
| `research/encoding/` | Bounded contextual fold search on 32 earlier depth-44/45 tables, with controls | No survivor in the specified family; not a lower bound and not a search of the final depth-41 table |

Each supplement contains its own exact scope and reproduction instructions. In particular, source-only metrics and successful interpreter contracts are not silently promoted to blank consistency-machine claims.

## Build the report

```bash
pdflatex -interaction=nonstopmode -halt-on-error K215_Rebalanced_Report.tex
pdflatex -interaction=nonstopmode -halt-on-error K215_Rebalanced_Report.tex
```

Standard LaTeX packages are sufficient. The figure PDF is already included. Optional `python3 code/plot_addresses.py` regenerates it from the source data and requires matplotlib. It is unrelated to the machine verifier.

`SHA256SUMS` fixes all delivered files except the checksum list itself. The original actual-run receipts are preserved; some record original research paths as provenance, while the portable entry points above use packet-relative paths. This is a standalone packet for repository incorporation; no GitHub publication was performed.

## Attribution

See `NOTICE.md` and `licenses/`. The accepted compact theory, interpreter, compiler, runtime induction checker, and predecessor constructions retain their original authorship. Separate review here means independent work within this research collaboration, not an external human endorsement.
