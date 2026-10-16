# Batch 144 manuscript 03 intake dossier

Package: `zfc_subset_only_machine_research.zip`, inner wrapper
`zfc_small_machine_research`. Review used the untouched extraction under
`/tmp/zfc-intake-144-6ye0stcm/03-zfc_subset_only_machine_research/`.
Every execution and the PDF rebuild ran on the separate copy
`/tmp/zfc-review144-03`. No checksum manifest or line-ending checks were run.
`verify_release.py` was read and skipped: it only checks SHA256SUMS.

## Pins and placement

The delivery explicitly uses the three distinct ProveIt pins
`b07d1a27bbe2814f2fd84cc55feef71c4de5b2db`,
`83ef1da6b717338f710277c2744fb4ec644cedbc`, and
`67086c8d8802ea7b3625a2fc0765d39e2181e335`.
Its base article/metric are pinned to the second. The imported benchmark
uses upstream commit `297ab8df7e5de329605c3875b4934643b371a5e3`.
It distinguishes inspected base material from companions assessed only through
the reconciliation/interface; it makes no historical-priority claim.

Recommend **addition to existing**
`SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels`, probably
local source06 if batch144 manuscripts01/02 take04/05. This directly resolves
and re-derives the source02 membership-arm deletion question and continues
its exact schema/metric. It should not become a rival report. Preserve the
delivered files unchanged, including their explicit dated review boundary.

## Mathematical review

No material mathematical flaw found in the new theorem or its dependency
ledger. For a fixed logically reflexive seed, constant subset-bounded classes
give exact singletons without Extensionality. The gated singleton/subset
switching relation is locally subset-bounded by pure equality logic. From an
active nonsingleton input x and y∈x, it first outputs a singleton of y and then
decodes that singleton to y. This gives both transitivity and A⊆C, without
requiring A∈C or prior Separation/Union. A cover of a mixed local bound b
therefore converts y∈b or y⊆b into y⊆C. No simultaneous choice of bounds or
covers is used. Hence pure and mixed schemas are uniformly equivalent for
logically reflexive seeds, without Extensionality.

The full calibration proofs correctly retain Extensionality for ZF0 and
equality elimination, use the Russell root r∉A for functional Replacement,
and use unique exact fibers in the converse. Converse iteration additionally
requires set-sized seed classes; the report explicitly separates this from
logical reflexivity alone. ZF0 excludes Foundation, Choice and an additional
unrestricted Collection schema. The equality-free route retains EC. The IR
augmentation is an explicit optional theory change; the executed checker
uses an actual closed logical contradiction instead of an unguarded diagonal
membership target. Formula-node totals 65/68/79 are correctly separated from
machine states. The finite-consequence obstruction and finite deletion models
are correctly scoped.

## Current-tree reconciliation (HEAD at review: 17d0f2eaa)

The historical deletion gap is real at the delivery's pin: preserved
`zfc-closure-kernels/article.tex:403–406` says deletion requires a new bootstrap.
It is already closed by subsequent repository work:

- `Computability/BusyBeaver/Research/ZFC/subset_only.md:5–7` states the same
  membership-arm deletion and positive-cover observation; `:94–102` gives the
  same switch proof.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PositiveClosure.lean:109`
  declares `switch_subset_bounded`; `:172` declares
  `positive_decoder_cover`; `:189` and `:202` give Separation/Union consequences.
- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/PSCCalibration.lean:171–177`
  declares `psc_iff_zf0` and `psc_consistency_iff_zf0` for the actual equality-
  bearing subset-seeded first-order theory. Its `:8–13` explicitly limits the
  result: functional Replacement, no Foundation/Choice proof-code bridge and
  no machine endpoint.
- `zfc-closure-kernels/README.md:158–169` already records these subsequent
  developments. The report's claims of additional work are relative to its
  stated older pin, not new gaps at current HEAD.
- `Computability/BusyBeaver/Research/ZFC/README.md:49–55` already records the
  same four-node savings and a further one-sided congruence saving. The
  delivery uses the symmetric EC control, so 79 is not the repository's best
  current same-basis equality-free count (71 with one-sided congruence).

Point-seeded and equality-free full calibrations remain mathematical in the
current documented boundary; the archive itself supplies no Lean code.
Its historical statement that the original author bundle is absent remains
correct, but the current repository additionally has reconstructed public
backend and experimental252-table work not inspected by the delivery.

## Executed verification

On the scratch copy:

```
uv run --no-project python build.py --tests --skip-pdf --table /home/codex/.codex/worktrees/ec20/Proofs/lib/jeff-busy-beaver-zfc254/ZF/m254/machine/zfc_254.tm
uv run --no-project python build.py
```

The first command runs all advertised Python suites, identity checker,
codec10000 search, metrics, finite experiments and optional table audit.
Results: 20 unittest methods pass; identity is valid, 5 lines, not refutation;
10000 search candidates contain0 valid certificates and do not halt (finite
prefix only). Tests include1000 codec roundtrips and120 independent formula-
semantics comparisons. Experiments check4096 HF roots,531429 switch outputs,
555186 positive-cover members,2168917 membership edges and7153 mixed-bound
cases;66066 graphs/1052740 seed pairs/263714 point seeds all pass.
Metrics reproduce69→65,72→68,83→79; optionalIR variant83.

The table audit finds508 rows/254 working states, all graph reachable,
254 singleton congruence classes and no context-free merges. Its264982-step
prefix reaches state96/head−8/149ones and is explicitly not a nonhalting
proof. This agrees with the current repository's independent audit.

The PDF-only build uses three pdflatex passes and succeeds at24 pages. No
overfull boxes, undefined references or LaTeX errors were found;9 underfull
hbox warnings occur in the path/bibliography tables. Rendered/reviewed page7
(main constant/switch/cover proofs) is readable and unclipped. All rewritten
logs, outputs and PDF stayed on the scratch copy.

## Operational boundary

The reference checker has explicit negation, capture-avoiding simultaneous
renaming, closed parameterized SC generation, alpha comparisons, strict
backward references and Boolean-label rejection. No unchecked conclusion or
semantic boundedness oracle is accepted. The ideal shortlex search is fair;
the finite-resource Python demonstrator is explicitly not promoted to a
verified unbounded implementation and does not swallow resource exceptions.
No new literal machine, sub254 bound, verified compiler, exported ZFC proof
translation, Coq replay or global minimality theorem is delivered.
