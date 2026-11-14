# PA194C: a different 194-state PA consistency machine

The principal result is a binary, deterministic, single-tape Turing machine
with **194 working states** for which the accompanying ordinary mathematical
proof establishes

> PA proves: nonhalting(PA194C, blank tape) if and only if Con(PA).

This meets the requested fallback of a materially different 194-state design.
No machine below 194 states is established here. No global minimality claim
or newly elaborated end-to-end Lean/Rocq theorem is made.

## Read first

- `report/pa194c_conpa.pdf` — complete report, proof, comparison, and all transitions.
- `report/pa194c_conpa.tex` — main LaTeX source; neighboring inputs are included.
- `construction/tables/pa194c.tm` — definitive dense transition table.
- `verification/reproduction.json` — acceptance-check summary.

The machine starts in state 0 with the head at cell 0 on a two-way infinite
all-zero tape. Working states are 0 through 193. The separate terminal halt
label is 194. The tape alphabet is {0,1}; every move is L or R. Each of the
388 rows has five columns:

```
state  read_symbol  write_symbol  direction  next_state
```

Dense-table SHA-256:

```
d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b
```

## What changed

The supplied PA194-67 decoder and seven simultaneous folds are retained.
Six native rows install the Combined command controller: Shift tests the
cached formula for contradiction, and successful modus ponens puts its
conclusion in that cache. This removes 24 primitive source instructions.

The complete new 3,649-instruction graph, including every successor, is
identical to the already calibrated PA195C source from the pinned incoming
archive. The physical implementation has 134 fixed controls plus 67 raw
axiom readers minus seven compatible folds, giving 194 states.

The resulting graph is absent from all seven prior 194-state byte forms
at the pinned revision, even allowing arbitrary renaming, forgetting the
start, tape reflection, and global symbol exchange. Its command semantics
also differ from all three supplied positive 194-state designs.

## Reproduce the accepted machine

From this directory, using Python 3.10 or later with its standard library:

```sh
python3 -B reproduce.py
```

Run with assertions enabled. The wrapper reconstructs the exact tables,
checks the full source graph, replays all 4,749 universal outcomes for raw
and folded tables, independently verifies literal tape behavior and four
generic list lemmas, checks exact whole-tape startup after 57,922 steps,
checks 188 command-algebra cases, and repeats exact corpus graph novelty.
Logs are written under `verification/logs/`.

No network, external repository, solver, or proof assistant is required for
these acceptance checks. The optional search programs and whole-corpus
census have their own instructions and are not required for acceptance.

## Proof status

The report composes syntactic translations of refutations, a uniform
command-word compiler, an exact source binding, and positive physical
simulations. It explicitly treats early halts, arbitrary preserved stack
tails, code-zero aliases, and the finite-history requirements of folds.
The physical audits cover arbitrary natural register values and arbitrary
finite nonempty spare lists, not bounded numerical samples.

The independent checker rederives its four list lemmas from literal rows
and does not use the first checker's arithmetic-box oracle. Both are
ordinary executable supporting certificates; neither is a new foundational
proof kernel. The repository's conditional iPRA endpoint remains distinct
from this ordinary PA proof.

## Contents and provenance

The source repository is `VladimirReshetnikov/ProveIt`, revision
`768c2be1a8e4d2fcf8aa3443c7b0f084d145734c`. All 36 incoming ZIPs and relevant
direct PA tables were compared; exact archive and member identities are in
`comparison/`. The census includes unsuccessful search tables, which are
classified separately from supported consistency constructions.

The `construction/` directory retains required supplied PA194 and PA195S
inputs. Files named `pa194.tm` there are inherited baselines; the newly
delivered principal machine is **`pa194c.tm`**. The supplementary `pa194cz`
files are an additional zero-register-jump search seed, described in
`README_PA194C.txt`; they are not the principal result or a state reduction.

Inherited logical proofs are under `references/` and
`reference/logical_calibration/`. Attribution, original license notices,
and exact source hashes are preserved. `research/` contains the optional
below-194 searches and the unsuccessful scanner-shortening experiment.

To compile the article, from `report/`:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error pa194c_conpa.tex
```

`SHA256SUMS` binds the delivered files other than itself. Run
`sha256sum -c SHA256SUMS` before reproduction to check the delivered archive.
Reproduction logs and optional newly generated search output are additional
working files; their timing and output locations need not match old runs.
