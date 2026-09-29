# Lipparini report consolidation — 2026-09-29

The destination retains its original source path and every original label.
Snapshot: `5804c7aff`. Source A is `lipparini-minimal-infinitary-sum` from
`lipparini_problem_6_2_proposed_solution.zip`; source B is
`lipparini-minimal-operation-formula` from `ordinal_operation_research.zip`.
The sources name the literature versions rather than a ProveIt pin. The snapshot
above is the editorial merge base, not an invented author-provided pin.

## Decisions

Both reports use arbitrary ordinal entries in omega-indexed sequences, the same
positive threshold and exceptional multiset with multiplicities, and the same
e-special strictness condition referring to the smaller sequence. Their three
cases agree term by term. A is the base because it develops the profile quotient
and absorption estimate in full; B supplies a distinct coordinate/block proof.

The shared main formula, imported S theorem, correction classification and
constant-value result occur once. The profile-rank theorem already includes the
sequence-rank characterization; B's descending-threshold argument and
rank-minimality argument are the same arguments supplied there. The exact
finite-cap formula is shared under `(n,E) -> (n+1,{t+1:t in E})`; its different
predecessor proof is preserved. B's unrestricted block-state rank theorem,
equality criterion, cardinality theorem, examples and negative controls remain.
The block proof preserves its essential finite-part restoration step and does
not assume permutation invariance of an arbitrary admissible operation.

No theorem's hypotheses were weakened. The ordinary `1+d` and natural `S # omega`
operations stay distinct. B's candidate A is renamed U (A already denotes natural
multiplication by omega in the base); d_b(a) is displayed as d(b,a). Proof-local
letters keep their meanings. Neither formal verification nor priority is claimed.

## Source-label concordance

B's labels were local to a different document and many collide with A's labels.
Shared labels resolve to the single maintained statement. Retained distinct
material receives `block:` labels. No destination label is removed or renamed.
Every B label has a destination below, including equations and boundary notes.

| B label | Unified label |
|---|---|
| `sec:prelim` | `subsec:notation` |
| `eq:natural-product` | `eq:Acnf` |
| `eq:finite-add` | `lem:arith` |
| `eq:omega-sup` | `block:eq:omega-sup` |
| `eq:diff` | `eq:remainder` |
| `eq:diff-near` | `block:eq:diff-near` |
| `eq:diff-far` | `block:eq:diff-far` |
| `eq:one-plus-infinite` | `block:eq:one-plus-infinite` |
| `eq:one-plus-finite` | `block:eq:one-plus-finite` |
| `eq:epsilon` | `eq:cut` |
| `lem:threshold` | `lem:cutfacts` |
| `def:admissible` | `eq:weak` |
| `eq:M` | `eq:weak` |
| `eq:E` | `eq:strict` |
| `sec:known` | `prop:importedS` |
| `eq:hat` | `eq:lastmonomial` |
| `eq:S-formula` | `eq:Sformula` |
| `thm:known` | `prop:importedS` |
| `sec:formula` | `thm:main` |
| `eq:chi` | `eq:chi` |
| `def:A` | `eq:U` |
| `eq:A-formula` | `thm:main` |
| `thm:main` | `thm:main` |
| `prop:correction` | `cor:correction` |
| `eq:correction` | `eq:correction` |
| `eq:k` | `eq:k` |
| `sec:block` | `block:sec:block` |
| `eq:B` | `block:eq:B` |
| `eq:R` | `block:eq:R` |
| `eq:c` | `block:eq:c` |
| `lem:block` | `block:lem:block` |
| `eq:block` | `block:eq:block` |
| `eq:S-block` | `block:eq:S-block` |
| `sec:upper` | `block:sec:upper` |
| `lem:fixed` | `block:lem:fixed` |
| `lem:ordinary-source` | `block:lem:ordinary-source` |
| `lem:corrected-source` | `block:lem:corrected-source` |
| `prop:admissible` | `block:prop:admissible` |
| `sec:lower` | `block:sec:lower` |
| `lem:lower-bottom` | `block:lem:lower-bottom` |
| `eq:q` | `block:eq:q` |
| `eq:restore-target` | `block:eq:restore-target` |
| `eq:core-lower` | `block:eq:core-lower` |
| `lem:lower-first` | `block:lem:lower-first` |
| `lem:lower-induction` | `block:lem:lower-induction` |
| `sec:consequences` | `block:sec:consequences` |
| `cor:equality` | `block:cor:equality` |
| `cor:invariance` | `block:cor:invariance` |
| `cor:constant` | `cor:constant` |
| `eq:constant` | `eq:constant` |
| `cor:low-order` | `cor:correction` |
| `cor:cardinality` | `block:cor:cardinality` |
| `sec:rank` | `thm:rank` |
| `eq:prec` | `eq:strict` |
| `lem:well-founded` | `lem:profile-wf` |
| `eq:rank-rec` | `thm:rank` |
| `thm:rank` | `thm:rank` |
| `sec:examples` | `block:sec:examples` |
| `eq:near-example` | `block:eq:near-example` |
| `eq:limit-exponent` | `block:eq:limit-exponent` |
| `sec:computation` | `block:sec:computation` |
| `app:finite` | `block:app:finite` |
| `prop:unbounded-model` | `block:prop:unbounded-model` |
| `prop:finite-model` | `thm:finitecap` |
| `app:audit` | `block:app:audit` |
| `app:reproduce` | `sec:implementation` |

## Byte-preserved supporting files

| Former path in B | Path in destination |
|---|---|
| `code\ordinals.py` | `code\block\ordinals.py` |
| `code\verify.py` | `code\block\verify.py` |
| `proof_audit.md` | `02-block-proof_audit.md` |
| `results\quality_report.txt` | `data\block\quality_report.txt` |
| `results\verification.json` | `data\block\verification.json` |
| `results\verification.txt` | `data\block\verification.txt` |
| `sources.md` | `02-block-sources.md` |

The two historical READMEs are available in Git at the snapshot above; the live
README consolidates their scope and commands. The retired build script compiled
B's retired article; use the destination build.sh for the unified article.
Delivered audit prose still names the old paths and PDF and is historical.
See the collection's CONSOLIDATION.md for fresh build, rendering and rerun evidence.
